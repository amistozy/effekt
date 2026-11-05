// Capability scopes.
//
// Mirrors `effekt/typer/CapabilityScope.scala`. The capability scope tracks
// which capabilities (block parameters of interface type) are in scope for a
// given effect, which is how effect operations find their receiver.

///|
/// A canonical key for an interface (effect) type, used to look capabilities
/// up in a `Map`.
pub fn interface_key(t : BlockType) -> String {
  match t {
    @symbols.BlockType::InterfaceType(c, args) =>
      "\{c.uid()}[\{args.map(value_type_key).join(",")}]"
    @symbols.BlockType::FunctionType(_, _, _, _, _, _) => "fn:\{t}"
  }
}

///|
pub fn value_type_key(t : ValueType) -> String {
  match t {
    @symbols.ValueType::ValueTypeRef(s) => "t\{s.uid()}"
    @symbols.ValueType::ValueTypeApp(c, args) =>
      "c\{c.uid()}[\{args.map(value_type_key).join(",")}]"
    @symbols.ValueType::BoxedType(b, c) =>
      "@source.TermKind::Box(\{interface_key(b)},\{c})"
  }
}

///|
/// The capability scope: a stack of frames.
///   - `BindSome` fixes the capabilities for a set of effects (a `try ... with`
///     or an object / block literal that handles them).
///   - `BindDeclared` fixes the capabilities for the *declared* effects of a
///     definition. They are not handlers: a use of the effect inside the
///     definition still escapes it, and an implementation created in the body
///     must not capture them (`pos/issue603/issue603_5`).
///   - `BindAll` hands out fresh capabilities on demand (an unannotated
///     function: all effects it performs are handled by itself).
pub(all) enum CapScope {
  GlobalCap
  BindDeclared(Map[String, Sym], CapScope)
  BindSome(Map[String, Sym], CapScope)
  BindAll(Map[String, Sym], CapScope)
}

///|
pub fn CapScope::parent(self : CapScope) -> CapScope {
  match self {
    GlobalCap => GlobalCap
    BindDeclared(_, p) => p
    BindSome(_, p) => p
    BindAll(_, p) => p
  }
}

///|
/// All capabilities bound by the frames of this scope, innermost first.
pub fn CapScope::all_capabilities(self : CapScope) -> Array[Sym] {
  let out : Array[Sym] = []
  let mut scope = self
  while !scope.is_global() {
    match scope {
      GlobalCap => scope = GlobalCap
      BindDeclared(caps, parent)
      | BindSome(caps, parent)
      | BindAll(caps, parent) => {
        for _, cap in caps {
          out.push(cap)
        }
        scope = parent
      }
    }
  }
  out
}

///|
/// Looks up the capability for an effect by comparing the *substituted* types.
///
/// A capability can be created while one of the effect's type arguments is
/// still an unsolved unification variable (e.g. `emit[?T]`); once that variable
/// has been solved (to `emit[T]`) the capability still has to be found, so the
/// comparison is done on `subst`-ed types rather than on the key the frame was
/// created with.
pub fn CapScope::capability_for_matching(
  self : CapScope,
  tpe : BlockType,
  subst : (BlockType) -> BlockType,
) -> Sym? {
  let target = subst(tpe)
  for cap in self.all_capabilities() {
    match capability_type(cap) {
      Some(t) => if interface_type_equal(subst(t), target) { return Some(cap) }
      None => ()
    }
  }
  None
}

///|
/// The capability an enclosing *handler* bound explicitly for `tpe` (a
/// `BindSome` frame). `BindAll` and `BindDeclared` frames are skipped on
/// purpose: `BindAll` hands out fresh capabilities on demand, and `BindDeclared`
/// only models the effects a definition promises to perform, so reusing one
/// would make an implementation capture a capability that the enclosing context
/// does not actually provide (`pos/issue603/issue603_5`: an object whose
/// operation performs the function's own declared effect must not capture it).
pub fn CapScope::bound_capability_for(self : CapScope, tpe : BlockType) -> Sym? {
  let key = interface_key(tpe)
  match self {
    GlobalCap => None
    BindSome(caps, parent) =>
      match caps.get(key) {
        Some(cap) => Some(cap)
        None => parent.bound_capability_for(tpe)
      }
    BindDeclared(_, parent) => parent.bound_capability_for(tpe)
    BindAll(_caps, parent) => parent.bound_capability_for(tpe)
  }
}

///|
/// Looks up (or, in a `BindAll` frame, creates) the capability for an effect.
/// Fails for `GlobalCap`, which is the "no handler in scope" case.
pub fn CapScope::capability_for(self : CapScope, tpe : BlockType) -> Sym? {
  let key = interface_key(tpe)
  match self {
    GlobalCap => None
    BindDeclared(caps, parent) | BindSome(caps, parent) =>
      match caps.get(key) {
        Some(cap) => Some(cap)
        None => parent.capability_for(tpe)
      }
    BindAll(caps, _parent) =>
      match caps.get(key) {
        Some(cap) => Some(cap)
        None => {
          // A fresh capability is allocated lazily and remembered.
          let name = match tpe {
            @symbols.BlockType::InterfaceType(c, _) => c.name()
            @symbols.BlockType::FunctionType(_, _, _, _, _, _) =>
              Name::local("cap")
          }
          let capture = Sym::capture_param(name)
          let cap = Sym::block_param(
            name,
            Some(tpe),
            capture,
            false,
            Span::missing(),
          )
          caps.set(key, cap)
          Some(cap)
        }
      }
  }
}

///|
/// All concrete interface types in scope that have the same type constructor as
/// `tpe`; used for better error messages.
pub fn CapScope::relevant_in_scope_for(
  self : CapScope,
  tpe : BlockType,
) -> Array[String] {
  let ctor = match tpe {
    @symbols.BlockType::InterfaceType(c, _) => Some(c)
    @symbols.BlockType::FunctionType(_, _, _, _, _, _) => None
  }
  let out : Array[String] = []
  match ctor {
    None => ()
    Some(c) => {
      let mut scope = self
      while !scope.is_global() {
        match scope {
          BindDeclared(caps, parent)
          | BindSome(caps, parent)
          | BindAll(caps, parent) => {
            for _, cap in caps {
              match cap_type(cap) {
                Some(@symbols.BlockType::InterfaceType(other, _)) =>
                  if other == c {
                    out.push("\{cap_type(cap).unwrap()}")
                  }
                _ => ()
              }
            }
            scope = parent
          }
          GlobalCap => scope = GlobalCap
        }
      }
    }
  }
  out
}

///|
pub fn CapScope::is_global(self : CapScope) -> Bool {
  match self {
    GlobalCap => true
    _ => false
  }
}

///|
/// The block (interface) type of a capability.
pub fn capability_type(cap : Sym) -> BlockType? {
  match cap {
    @symbols.Sym::BlockParam(p) => p.tpe
    @symbols.Sym::ExternResource(r) => Some(r.tpe)
    _ => cap.annotated_type()
  }
}

///|
fn cap_type(cap : Sym) -> BlockType? {
  capability_type(cap)
}
