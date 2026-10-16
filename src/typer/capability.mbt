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
      c.uid().to_string() + "[" + args.map(value_type_key).join(",") + "]"
    @symbols.BlockType::FunctionType(_, _, _, _, _, _) =>
      "fn:" + show_block_type(t)
  }
}

///|
pub fn value_type_key(t : ValueType) -> String {
  match t {
    @symbols.ValueType::ValueTypeRef(s) => "t" + s.uid().to_string()
    @symbols.ValueType::ValueTypeApp(c, args) =>
      "c" + c.uid().to_string() + "[" + args.map(value_type_key).join(",") + "]"
    @symbols.ValueType::BoxedType(b, c) =>
      "@source.TermKind::Box(" + interface_key(b) + "," + show_captures(c) + ")"
  }
}

///|
/// The capability scope: a stack of frames.
///   - `BindSome` fixes the capabilities for a set of effects (a `try ... with`
///     or an annotated function).
///   - `BindAll` hands out fresh capabilities on demand (an unannotated
///     function: all effects it performs are handled by itself).
pub(all) enum CapScope {
  GlobalCap
  BindSome(Map[String, Sym], CapScope)
  BindAll(Map[String, Sym], CapScope)
}

///|
pub fn CapScope::parent(self : CapScope) -> CapScope {
  match self {
    GlobalCap => GlobalCap
    BindSome(_, p) => p
    BindAll(_, p) => p
  }
}

///|
pub fn CapScope::copy(self : CapScope) -> CapScope {
  match self {
    GlobalCap => GlobalCap
    BindSome(caps, parent) => BindSome(caps.copy(), parent.copy())
    BindAll(caps, parent) => BindAll(caps.copy(), parent.copy())
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
      BindSome(caps, parent) | BindAll(caps, parent) => {
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
/// Looks up (or, in a `BindAll` frame, creates) the capability for an effect.
/// Fails for `GlobalCap`, which is the "no handler in scope" case.
pub fn CapScope::capability_for(self : CapScope, tpe : BlockType) -> Sym? {
  let key = interface_key(tpe)
  match self {
    GlobalCap => None
    BindSome(caps, parent) =>
      match caps.get(key) {
        Some(cap) => Some(cap)
        None => parent.capability_for(tpe)
      }
    BindAll(caps, parent) =>
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
          BindSome(caps, parent) | BindAll(caps, parent) => {
            for _, cap in caps {
              match cap_type(cap) {
                Some(@symbols.BlockType::InterfaceType(other, _)) =>
                  if sym_eq(other, c) {
                    out.push(show_block_type(cap_type(cap).unwrap()))
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
