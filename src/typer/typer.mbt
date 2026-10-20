// The type checker.
//
// Mirrors `effekt/Typer.scala` (the driver, expression / statement / definition
// checking) plus the state that upstream keeps in `Context` (`TyperOps`) and
// `Constraints`.
//
// Preconditions: all symbols are resolved by the Namer (`Context.symbol_of`)
// and every definition reachable from this module has been type checked.
//
// Postconditions: the local annotation tables are committed into the
// `Context` (inferred value / block types, effects, captures, and the
// elaboration info consumed by `ExplicitCapabilities`).

///|
/// Local annotations. Upstream keeps these in a backtrackable local table and
/// only commits them into the global DB when the phase finishes; we do the
/// same, which makes overload resolution (backtracking) sound.
pub(all) struct Annotations {
  /// Inferred value types (terms, patterns, definitions).
  value : Map[Int32, ValueType]
  /// Inferred block types.
  block : Map[Int32, BlockType]
  /// Inferred effects.
  effect : Map[Int32, Effects]
  /// Inferred captures.
  capt : Map[Int32, Captures]
  /// Inferred type arguments at call sites.
  type_args : Map[Int32, Array[ValueType]]
  /// Capabilities a binder has to bind (see `ExplicitCapabilities`).
  bound_caps : Map[Int32, Array[Sym]]
  /// The capability a `Do` dispatches on.
  cap_receiver : Map[Int32, Sym]
  /// Capabilities passed to a call (bidirectional effects).
  cap_args : Map[Int32, Array[Sym]]
  /// Implicit value arguments inserted at a call site.
  impl_vargs : Map[Int32, Array[Term]]
  /// Implicit block arguments inserted at a call site.
  impl_bargs : Map[Int32, Array[Term]]
}

///|
pub fn Annotations::new() -> Annotations {
  {
    value: Map([]),
    block: Map([]),
    effect: Map([]),
    capt: Map([]),
    type_args: Map([]),
    bound_caps: Map([]),
    cap_receiver: Map([]),
    cap_args: Map([]),
    impl_vargs: Map([]),
    impl_bargs: Map([]),
  }
}

///|
pub fn Annotations::copy(self : Annotations) -> Annotations {
  {
    value: self.value.copy(),
    block: self.block.copy(),
    effect: self.effect.copy(),
    capt: self.capt.copy(),
    type_args: self.type_args.copy(),
    bound_caps: self.bound_caps.copy(),
    cap_receiver: self.cap_receiver.copy(),
    cap_args: self.cap_args.copy(),
    impl_vargs: self.impl_vargs.copy(),
    impl_bargs: self.impl_bargs.copy(),
  }
}

///|
/// Everything that has to be backtracked when an overload candidate fails.
pub(all) struct TyperState {
  mut u : Unification
  mut scope : UnifScope
  mut cap_scope : CapScope
  mut current : Captures
  vt : Map[Int32, ValueType]
  bt : Map[Int32, BlockType]
  ct : Map[Int32, Captures]
  ann : Annotations
}

///|
pub fn TyperState::backup(self : TyperState) -> TyperState {
  {
    u: self.u.copy(),
    scope: self.scope.deep_copy(),
    // The capability scope is monotone (capabilities are only ever added), so
    // it is shared between a state and its backups: a candidate that is rolled
    // back may leave a capability behind, but the successful path binds every
    // capability it used from the enclosing frame's map anyway. Copying it
    // would orphan the frame installed by `binding_all_capabilities`, because
    // installing a successful candidate replaces the whole state.
    cap_scope: self.cap_scope,
    current: self.current,
    vt: self.vt.copy(),
    bt: self.bt.copy(),
    ct: self.ct.copy(),
    ann: self.ann.copy(),
  }
}

///|
pub fn UnifScope::deep_copy(self : UnifScope) -> UnifScope {
  match self {
    GlobalScope => GlobalScope
    LocalScope(ts, cs, parent) =>
      LocalScope(ts.copy(), cs.copy(), parent.deep_copy())
  }
}

///|
/// The type checker. A `Typer` is created per module and threaded through
/// every checking function (upstream passes `Context` and the current
/// `Captures` implicitly).
pub struct Typer {
  ctx : Context
  mut st : TyperState
  /// While set, diagnostics are not reported but only recorded in
  /// `muted_messages`; used to try overload candidates without side effects.
  mut muting : Bool
  mut muted_error : Bool
  /// The diagnostics that were suppressed while trying an overload candidate.
  mut muted_messages : Array[String]
  /// The span of the tree currently being checked.
  mut focus : Span
}

///|
pub fn Typer::new(ctx : Context) -> Typer {
  {
    ctx,
    st: {
      u: Unification::new(),
      scope: GlobalScope,
      cap_scope: GlobalCap,
      current: Captures::empty(),
      vt: Map([]),
      bt: Map([]),
      ct: Map([]),
      ann: Annotations::new(),
    },
    muting: false,
    muted_error: false,
    muted_messages: [],
    focus: Span::missing(),
  }
}

// ---------------------------------------------------------------------------
// Diagnostics
// ---------------------------------------------------------------------------

///|
/// Renders a span for a muted diagnostic.
fn render_span(span : Span) -> String {
  if span.origin == @util.Origin::Missing {
    ""
  } else {
    "\{span.source.name}:\{span.position().line}:\{span.position().column}: "
  }
}

///|
fn Typer::error(self : Typer, span : Span, msg : String) -> Unit {
  if self.muting {
    self.muted_error = true
    self.muted_messages.push(render_span(span) + msg)
  } else {
    self.ctx.error(span, msg)
  }
}

///|
fn Typer::warning(self : Typer, span : Span, msg : String) -> Unit {
  if self.muting {
    self.muted_error = true
  } else {
    self.ctx.warning(span, msg)
  }
}

///|
fn Typer::info(self : Typer, msg : String) -> Unit {
  if !self.muting {
    self.ctx.info(msg)
  }
}

///|
/// Reports an error and stops type checking. Generic in the result type so
/// that it can be used in any position.
fn[T] Typer::abort(
  self : Typer,
  span : Span,
  msg : String,
) -> T raise EffektError {
  if self.muting {
    self.muted_error = true
    self.muted_messages.push(render_span(span) + msg)
  } else {
    self.ctx.error(span, msg)
  }
  raise EffektError::Fatal(msg)
}

///|
fn[T] Typer::panic(self : Typer, msg : String) -> T raise EffektError {
  if self.muting {
    self.muted_error = true
    self.muted_messages.push(msg)
  } else {
    self.ctx.info("Internal compiler error: \{msg}")
  }
  raise EffektError::Internal(msg)
}

// ---------------------------------------------------------------------------
// Symbols and the typing context
// ---------------------------------------------------------------------------

///|
/// The symbol of a reference. `what` is used in the diagnostic.
fn Typer::symbol_of(
  self : Typer,
  uid : Int32,
  what : String,
) -> Sym raise EffektError {
  match self.ctx.symbol_of(uid) {
    Some(s) => s
    None => self.panic("No symbol resolved for \{what} (uid \{uid})")
  }
}

///|
fn Typer::symbol_of_id(self : Typer, id : IdRef) -> Sym raise EffektError {
  self.symbol_of(id.uid, id.name)
}

///|
/// Like `symbol_of_id`, but returns `None` instead of reporting an error.
fn Typer::symbol_of_id_opt(self : Typer, id : IdRef) -> Sym? {
  self.ctx.symbol_of(id.uid)
}

///|
fn Typer::symbol_of_def(self : Typer, id : IdDef) -> Sym raise EffektError {
  self.symbol_of(id.uid, id.name)
}

///|
/// Types of a symbol are looked up in the local typing context first and then
/// on the symbol itself (definitions of already checked dependencies).
pub fn Typer::bind_value(self : Typer, s : Sym, t : ValueType) -> Unit {
  self.st.vt.set(s.uid(), t)
}

///|
pub fn Typer::bind_block(self : Typer, s : Sym, t : BlockType) -> Unit {
  self.st.bt.set(s.uid(), t)
}

///|
pub fn Typer::bind_capture(self : Typer, s : Sym, c : Captures) -> Unit {
  self.st.ct.set(s.uid(), c)
}

///|
fn symbol_value_type(s : Sym) -> ValueType? {
  match s {
    @symbols.Sym::ValueParam(p) => p.tpe
    @symbols.Sym::ValBinder(v) => v.tpe
    @symbols.Sym::RegBinder(r) => r.tpe
    @symbols.Sym::VarBinder(v) => v.tpe
    @symbols.Sym::Hole(_) => Some(t_bottom())
    _ => None
  }
}

///|
fn symbol_block_type(s : Sym) -> BlockType? {
  match s {
    @symbols.Sym::BlockParam(p) => p.tpe
    @symbols.Sym::ExternResource(r) => Some(r.tpe)
    _ => s.annotated_type()
  }
}

///|
/// Types of a symbol are looked up in the local typing context first, then on
/// the symbol itself (declared annotations), and finally in the context
/// annotations committed by the module that *defined* it. The last step is what
/// makes a definition without an explicit result type usable across modules:
/// its inferred type was recorded by its own module's `commit`.
pub fn Typer::lookup_first_value(self : Typer, s : Sym) -> ValueType? {
  match self.st.vt.get(s.uid()) {
    Some(t) => Some(t)
    None =>
      match symbol_value_type(s) {
        Some(t) => Some(t)
        None => self.ctx.value_type_of(s.uid())
      }
  }
}

///|
pub fn Typer::lookup_value(
  self : Typer,
  s : Sym,
) -> ValueType raise EffektError {
  match self.lookup_first_value(s) {
    Some(t) => t
    None =>
      self.abort(
        s.decl(),
        "Cannot find type for \{s.name().name} -- forward uses and recursive functions need annotated return types.",
      )
  }
}

///|
pub fn Typer::lookup_block(
  self : Typer,
  s : Sym,
) -> BlockType raise EffektError {
  match self.st.bt.get(s.uid()) {
    Some(t) => t
    None =>
      match symbol_block_type(s) {
        Some(t) => t
        None =>
          match self.ctx.block_type_of(s.uid()) {
            Some(t) => t
            None =>
              self.abort(s.decl(), "Cannot find type for \{s.name().name}.")
          }
      }
  }
}

///|
pub fn Typer::lookup_function_type(
  self : Typer,
  s : Sym,
) -> BlockType raise EffektError {
  let t = self.st.u.prune_block(self.lookup_block(s))
  match t {
    @symbols.BlockType::FunctionType(_, _, _, _, _, _) => t
    _ => self.abort(s.decl(), "Expected function type, but got \{t}.")
  }
}

///|
pub fn Typer::lookup_capture(self : Typer, s : Sym) -> Captures {
  match self.st.ct.get(s.uid()) {
    Some(c) => c
    None =>
      match s {
        @symbols.Sym::BlockParam(p) =>
          @symbols.Captures::CaptureSetOf([p.capture])
        @symbols.Sym::ExternResource(r) =>
          @symbols.Captures::CaptureSetOf([r.capture])
        @symbols.Sym::VarBinder(v) =>
          @symbols.Captures::CaptureSetOf([v.capture])
        @symbols.Sym::RegBinder(r) =>
          @symbols.Captures::CaptureSetOf([r.region])
        _ => Captures::empty()
      }
  }
}

// ---------------------------------------------------------------------------
// Annotations
// ---------------------------------------------------------------------------

///|
pub fn Typer::annotate_value(self : Typer, uid : Int32, t : ValueType) -> Unit {
  self.st.ann.value.set(uid, t)
}

///|
pub fn Typer::annotate_block(self : Typer, uid : Int32, t : BlockType) -> Unit {
  self.st.ann.block.set(uid, t)
}

///|
pub fn Typer::annotate_effects(self : Typer, uid : Int32, e : Effects) -> Unit {
  self.st.ann.effect.set(uid, e)
}

///|
pub fn Typer::annotate_capture(self : Typer, uid : Int32, c : Captures) -> Unit {
  self.st.ann.capt.set(uid, c)
}

// ---------------------------------------------------------------------------
// Unification scopes and capabilities
// ---------------------------------------------------------------------------

///|
fn Typer::fresh_type_var(self : Typer, underlying : Sym) -> Sym {
  let x = self.st.u.fresh_type_var(underlying)
  self.st.scope.register_type_var(x)
  x
}

///|
fn Typer::fresh_capt_var(self : Typer, role : String) -> Sym {
  let x = self.st.u.fresh_capt_var(role)
  self.st.scope.register_capt_var(x)
  x
}

///|
fn[T] Typer::with_unification_scope(
  self : Typer,
  additional : Array[Sym],
  f : () -> T raise EffektError,
) -> T raise EffektError {
  let parent = self.st.scope
  self.st.scope = LocalScope([], [], parent)
  let inner = self.st.scope
  let result = f() catch {
    EffektError::Fatal(m) => {
      self.st.scope = parent
      raise EffektError::Fatal(m)
    }
    EffektError::Internal(m) => {
      self.st.scope = parent
      raise EffektError::Internal(m)
    }
  }
  self.st.scope = parent
  // Unification variables that went out of scope are solved (captures) or
  // reported (types).
  let capts = inner.capt_vars() + additional
  for msg in self.st.u.solve_all(capts) {
    self.error(self.focus, msg)
  }
  for x in inner.type_vars() {
    if !self.st.u.types.contains(x.uid()) {
      let underlying = self.st.u.underlying(x)
      self.error(
        self.focus,
        "Cannot infer type argument \{underlying.name().name}, maybe consider annotating it?",
      )
    }
  }
  result
}

///|
/// Creates a capability for the given effect and binds it.
fn Typer::fresh_capability_for(
  self : Typer,
  tpe : BlockType,
  capt : Sym,
) -> Sym {
  let name = match tpe {
    @symbols.BlockType::InterfaceType(c, _) => c.name()
    @symbols.BlockType::FunctionType(_, _, _, _, _, _) => Name::local("cap")
  }
  let param = Sym::block_param(name, Some(tpe), capt, false, Span::missing())
  self.bind_block(param, tpe)
  self.bind_capture(param, @symbols.Captures::CaptureSetOf([capt]))
  param
}

///|
fn capture_of_capability(cap : Sym) -> Sym {
  match cap {
    @symbols.Sym::BlockParam(p) => p.capture
    @symbols.Sym::ExternResource(r) => r.capture
    _ => cap
  }
}

///|
/// Checks whether two value types can be unified without recording anything
/// (upstream `DummyUnifier.checkSubtype`): the state and the diagnostics are
/// restored afterwards.
fn Typer::types_compatible(
  self : Typer,
  inferred : ValueType,
  concrete : ValueType,
) -> Bool {
  let before = self.st.backup()
  let muting_before = self.muting
  let error_before = self.muted_error
  let messages_before = self.muted_messages
  self.muting = true
  self.muted_error = false
  self.muted_messages = []
  let mut ok = true
  self.unify_value_types(inferred, concrete, MergeTypes(inferred, concrete)) catch {
    _ => ok = false
  }
  if self.muted_error {
    ok = false
  }
  self.st = before
  self.muting = muting_before
  self.muted_error = error_before
  self.muted_messages = messages_before
  ok
}

///|
/// Upstream `BindSome.tryLexicalCapabilityFor` (PR #1194): a capability can be
/// requested while a type argument of the effect is still an unsolved
/// unification variable (`do emit(Nil())` performs `emit[List[?T]]` although
/// the declaration says `emit[List[A]]`). If exactly one capability in scope
/// has the same type constructor and its arguments unify with the requested
/// ones, use it and commit the constraints so the effect becomes concrete.
fn Typer::lexical_capability(
  self : Typer,
  tpe : BlockType,
) -> Sym? raise EffektError {
  let target = self.st.u.prune_block(tpe)
  let (ctor, args) = match target {
    @symbols.BlockType::InterfaceType(c, a) => (c, a)
    _ => return None
  }
  if self.unknowns_block(target).length() == 0 {
    return None
  }
  let compatible : Array[Sym] = []
  for cap in self.st.cap_scope.all_capabilities() {
    match capability_type(cap) {
      Some(cap_tpe) =>
        match self.st.u.prune_block(cap_tpe) {
          @symbols.BlockType::InterfaceType(c2, args2) =>
            if ctor == c2 && args.length() == args2.length() {
              let mut ok = true
              for i = 0; i < args.length() && ok; i = i + 1 {
                if !self.types_compatible(args[i], args2[i]) {
                  ok = false
                }
              }
              if ok {
                compatible.push(cap)
              }
            }
          _ => ()
        }
      None => ()
    }
  }
  if compatible.length() != 1 {
    return None
  }
  let cap = compatible[0]
  // Commit the argument constraints (upstream `C.requireSubtype`).
  match capability_type(cap) {
    Some(cap_tpe) =>
      match self.st.u.prune_block(cap_tpe) {
        @symbols.BlockType::InterfaceType(_, args2) =>
          for i = 0; i < args.length(); i = i + 1 {
            self.unify_value_types(
              args[i],
              args2[i],
              MergeTypes(args[i], args2[i]),
            )
          }
        _ => ()
      }
    None => ()
  }
  Some(cap)
}

///|
fn Typer::capability_for(
  self : Typer,
  tpe : BlockType,
  span : Span,
) -> Sym raise EffektError {
  let target = self.st.u.prune_block(tpe)
  match self.st.cap_scope.capability_for(target) {
    Some(cap) => cap
    None =>
      // The effect may still contain an unsolved type argument (`emit[?T]`):
      // try the lexical resolution upstream uses for exactly that case.
      match self.lexical_capability(target) {
        Some(cap) => cap
        None =>
          // Otherwise the capability may have been created while a type
          // argument was still unsolved; compare the substituted types.
          match
            self.st.cap_scope.capability_for_matching(target, t => {
              self.st.u.prune_block(t)
            }) {
            Some(cap) => cap
            None => {
              for hint in self.st.cap_scope.relevant_in_scope_for(tpe) {
                self.info(
                  "Did you mean to use an operation of the concrete interface \{hint}?",
                )
              }
              let message =
                $|Effect \{tpe} is not allowed in this context.
                $|
                $|Maybe try annotating the function with the effect?
              self.abort(span, message)
            }
          }
      }
  }
}

///|
/// Binds `caps` and runs `f` with a capability scope that resolves their
/// effects to them.
fn[T] Typer::binding_capabilities(
  self : Typer,
  uid : Int32,
  caps : Array[Sym],
  f : () -> T raise EffektError,
) -> T raise EffektError {
  self.bind_capabilities(uid, caps)
  let map : Map[String, Sym] = Map([])
  for cap in caps {
    // The capability's own type may still mention a unification variable that
    // has been solved since it was created; lookups prune, so the key has to
    // be computed on the pruned type as well.
    match capability_type(cap) {
      Some(t) => map.set(interface_key(self.st.u.prune_block(t)), cap)
      None => ()
    }
  }
  let parent = self.st.cap_scope
  self.st.cap_scope = BindSome(map, parent)
  let result = f()
  self.st.cap_scope = parent
  result
}

///|
/// Binds capabilities and remembers them for `ExplicitCapabilities`.
fn Typer::bind_capabilities(
  self : Typer,
  uid : Int32,
  caps : Array[Sym],
) -> Unit raise EffektError {
  for cap in caps {
    // A capability handed out by `CapScope::capability_for` has never been
    // registered in the typing context (the scope cannot reach it); take the
    // type from the symbol and register it.
    match capability_type(cap) {
      Some(t) => {
        self.bind_block(cap, t)
        self.assert_concrete_effect(t, cap.decl())
      }
      None => self.panic("Capability type needs to be known.")
    }
  }
  self.st.ann.bound_caps.set(uid, caps)
}

///|
/// Runs `f` with a fresh `BindAll` frame: all effects are handled by the
/// enclosing definition, capabilities are created on demand.
fn[T] Typer::binding_all_capabilities(
  self : Typer,
  uid : Int32,
  f : () -> T raise EffektError,
) -> (T, Map[String, Sym]) raise EffektError {
  let parent = self.st.cap_scope
  let caps : Map[String, Sym] = Map([])
  self.st.cap_scope = BindAll(caps, parent)
  let result = f()
  // Installing a successful overload candidate replaces the whole state, so the
  // frame installed above is not necessarily the one that is current now; read
  // the map back from the live frame. (The capability scope itself is shared
  // between a state and its backups, so this is normally the very same map.)
  let (caps, frame_parent) = match self.st.cap_scope {
    BindAll(caps, parent) => (caps, parent)
    _ => (caps, parent)
  }
  self.st.cap_scope = frame_parent
  self.st.ann.bound_caps.set(uid, [])
  (result, caps)
}

// ---------------------------------------------------------------------------
// Captures
// ---------------------------------------------------------------------------

///|
fn[T] Typer::flowing_into(
  self : Typer,
  c : Captures,
  f : () -> T raise EffektError,
) -> T raise EffektError {
  let saved = self.st.current
  self.st.current = c
  let r = f()
  self.st.current = saved
  r
}

///|
fn Typer::using_capture(self : Typer, c : Captures) -> Unit {
  self.require_subregion(c, self.st.current, self.focus)
}

///|
fn Typer::using_capture_without(
  self : Typer,
  c : Captures,
  filter : Array[Sym],
) -> Unit {
  self.flows_into_without(c, self.st.current, filter, self.focus)
}

///|
fn Typer::flows_into(
  self : Typer,
  from : Captures,
  to : Captures,
  span : Span,
) -> Unit {
  self.require_subregion(from, to, span)
}

///|
fn Typer::flows_into_without(
  self : Typer,
  from : Captures,
  to : Captures,
  filter : Array[Sym],
  span : Span,
) -> Unit {
  let from = self.without(from, filter)
  self.require_subregion(from, to, span)
}

///|
/// `caps - others`
fn Typer::without(
  self : Typer,
  caps : Captures,
  others : Array[Sym],
) -> Captures {
  if others.length() == 0 {
    return caps
  }
  match caps {
    @symbols.Captures::CaptureSetOf(cs) =>
      @symbols.Captures::CaptureSetOf(cs.filter(c => !others.contains(c)))
    @symbols.Captures::CaptVar(x) => {
      let y = self.fresh_capt_var("without")
      self.st.u.link(y.uid(), x.uid(), others.copy())
      let _ = self.st.u.propagate()
      @symbols.Captures::CaptVar(y)
    }
  }
}

///|
/// `from <: to`, mirrored from `Unification.requireSubregion`.
pub fn Typer::require_subregion(
  self : Typer,
  from : Captures,
  to : Captures,
  span : Span,
) -> Unit {
  let from = self.st.u.prune_captures(from)
  let to = self.st.u.prune_captures(to)
  if from == to {
    return
  }
  match (from, to) {
    (@symbols.Captures::CaptureSetOf(ls), _) if ls.length() == 0 => return
    (@symbols.Captures::CaptureSetOf(ls), @symbols.Captures::CaptureSetOf(us)) => {
      let not_allowed = ls.filter(c => !us.contains(c))
      if not_allowed.length() > 0 {
        self.error(
          span,
          "Used captures \{@symbols.Captures::CaptureSetOf(not_allowed)} are not in the allowed set \{to}",
        )
      }
    }
    (@symbols.Captures::CaptVar(x), @symbols.Captures::CaptureSetOf(us)) =>
      match self.st.u.require_upper(us, x) {
        Some(msg) => self.error(span, msg)
        None => ()
      }
    (@symbols.Captures::CaptureSetOf(ls), @symbols.Captures::CaptVar(y)) =>
      match self.st.u.require_lower(ls, y) {
        Some(msg) => self.error(span, msg)
        None => ()
      }
    (@symbols.Captures::CaptVar(x), @symbols.Captures::CaptVar(y)) => {
      self.st.u.link(x.uid(), y.uid(), [])
      match self.st.u.propagate() {
        Some(msg) => self.error(span, msg)
        None => ()
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Wellformedness of inferred types
// ---------------------------------------------------------------------------

///|
/// Effects need to be fully known before capabilities are passed for them.
pub fn Typer::assert_concrete_effect(
  self : Typer,
  eff : BlockType,
  span : Span,
) -> Unit raise EffektError {
  let eff = self.st.u.prune_block(eff)
  match self.unknowns_block(eff) {
    us if us.length() > 0 => {
      let message =
        $|Effects need to be fully known, but effect \{eff}'s type parameter(s) \{us.join(", ")} could not be inferred.
        $|
        $|Maybe try annotating them?
      self.abort(span, message)
    }
    _ => ()
  }
}

///|
pub fn Typer::assert_concrete_effects(
  self : Typer,
  effs : Effects,
  span : Span,
) -> Unit raise EffektError {
  for e in effs.distinct().effects {
    self.assert_concrete_effect(e, span)
  }
}

///|
fn Typer::assert_concrete_function(
  self : Typer,
  id : IdDef,
  tpe : BlockType,
) -> Unit raise EffektError {
  match self.unknowns_block(tpe) {
    us if us.length() > 0 =>
      self.abort(id.span, "Cannot fully infer type for \{id.name}: \{tpe}")
    _ => ()
  }
}

///|
/// The names of type unification variables occurring in a type.
///
/// The type is pruned first: a unification variable that has already been
/// solved is *concrete* and must not be reported (upstream always inspects
/// substituted types).
fn Typer::unknowns_value(self : Typer, t : ValueType) -> Array[String] {
  match self.st.u.prune_value(t) {
    @symbols.ValueType::ValueTypeRef(x) =>
      if self.st.u.is_type_var(x) {
        let u = self.st.u.underlying(x)
        [u.name().name]
      } else {
        []
      }
    @symbols.ValueType::ValueTypeApp(_, args) => {
      let out : Array[String] = []
      for a in args {
        for u in self.unknowns_value(a) {
          out.push(u)
        }
      }
      out
    }
    @symbols.ValueType::BoxedType(b, c) =>
      self.unknowns_block(b) + self.unknowns_captures(c)
  }
}

///|
fn Typer::unknowns_block(self : Typer, t : BlockType) -> Array[String] {
  match self.st.u.prune_block(t) {
    @symbols.BlockType::InterfaceType(_, args) => {
      let out : Array[String] = []
      for a in args {
        for u in self.unknowns_value(a) {
          out.push(u)
        }
      }
      out
    }
    @symbols.BlockType::FunctionType(_, capts, vps, bps, ret, effs) => {
      let out : Array[String] = []
      for v in vps {
        for u in self.unknowns_value(v) {
          out.push(u)
        }
      }
      for b in bps {
        for u in self.unknowns_block(b) {
          out.push(u)
        }
      }
      for e in effs.effects {
        for u in self.unknowns_block(e) {
          out.push(u)
        }
      }
      for c in capts {
        for u in self.unknowns_captures(c) {
          out.push(u)
        }
      }
      for u in self.unknowns_value(ret) {
        out.push(u)
      }
      dedup_syms_strings(out)
    }
  }
}

///|
fn dedup_syms_strings(xs : Array[String]) -> Array[String] {
  let out : Array[String] = []
  for x in xs {
    if !out.any(y => y == x) {
      out.push(x)
    }
  }
  out
}

///|
fn Typer::unknowns_captures(self : Typer, c : Captures) -> Array[String] {
  match c {
    @symbols.Captures::CaptVar(x) =>
      if self.st.u.capts.contains(x.uid()) {
        []
      } else {
        [x.name().name]
      }
    @symbols.Captures::CaptureSetOf(_) => []
  }
}

// ---------------------------------------------------------------------------
// The driver
// ---------------------------------------------------------------------------

///|
/// Type-checks the (already name-resolved) module. Annotations (inferred
/// types, effects, capture sets) are written into `context`.
///
/// Upstream's pipeline is `Parser andThen Namer andThen UnboxInference andThen
/// Typer`, so the caller is expected to pass the tree returned by
/// `unbox_inference`. To stay robust when a caller drops that result (and type
/// checks the original tree anyway), unboxing is repeated here and the
/// rewritten definitions are written back into `module` — the `defs` array is
/// mutated in place, so the caller's module (and everything downstream that
/// walks it) sees the rewritten tree together with the annotations produced
/// below.
pub fn typecheck(
  module : ModuleDecl,
  context : Context,
) -> Unit raise EffektError {
  let rewritten = unbox_inference(module, context)
  if rewritten.defs.length() == module.defs.length() {
    for i = 0; i < rewritten.defs.length(); i = i + 1 {
      module.defs[i] = rewritten.defs[i]
    }
  }
  let t = Typer::new(context)
  t.check_module(rewritten)
}

///|
pub fn Typer::check_module(
  self : Typer,
  module : ModuleDecl,
) -> Unit raise EffektError {
  // (1) pre-check: store the annotated types of all definitions, so that
  // mutually recursive and forward references work.
  for d in module.defs {
    self.precheck_def(d)
  }
  // (2) check
  for d in module.defs {
    let res = self.synth_def(d)
    if res.effs.non_empty() {
      self.error(d.span, "Unhandled effects \{res.effs}")
    }
  }
  self.commit()
  self.check_main(module)
}

///|
/// Commits the local annotations into the context, applying the final
/// substitution (upstream `commitTypeAnnotations`).
///
/// Two kinds of annotations are committed, both keyed by uid (nodes and
/// symbols draw from the same `fresh_uid` counter, so they never collide):
///   - the *typing context*: the type and capture of every symbol that was
///     bound while checking. Later phases look symbols up this way, e.g.
///     `context.block_type_of(resume.uid())` in the core transformation.
///   - the inferred types / effects / captures of tree nodes, plus the
///     elaboration info consumed by `ExplicitCapabilities`.
pub fn Typer::commit(self : Typer) -> Unit {
  let u = self.st.u
  // the typing context (symbols)
  for uid, t in self.st.vt {
    self.ctx.assign_value_type(uid, u.prune_value(t))
  }
  for uid, t in self.st.bt {
    self.ctx.assign_block_type(uid, u.prune_block(t))
  }
  for uid, c in self.st.ct {
    self.ctx.assign_capture(uid, u.prune_captures(c))
  }
  // inferred annotations (tree nodes)
  for uid, t in self.st.ann.value {
    self.ctx.assign_value_type(uid, u.prune_value(t))
  }
  for uid, t in self.st.ann.block {
    self.ctx.assign_block_type(uid, u.prune_block(t))
  }
  for uid, e in self.st.ann.effect {
    self.ctx.assign_effects(uid, u.prune_effects(e))
  }
  for uid, c in self.st.ann.capt {
    self.ctx.assign_capture(uid, u.prune_captures(c))
  }
  for uid, targs in self.st.ann.type_args {
    self.ctx.assign_type_arguments(uid, targs.map(t => u.prune_value(t)))
  }
  for uid, caps in self.st.ann.bound_caps {
    self.ctx.assign_bound_capabilities(uid, caps)
  }
  for uid, cap in self.st.ann.cap_receiver {
    self.ctx.assign_capability_receiver(uid, cap)
  }
  for uid, caps in self.st.ann.cap_args {
    self.ctx.assign_capability_arguments(uid, caps)
  }
  for uid, args in self.st.ann.impl_vargs {
    self.ctx.assign_implicit_value_args(uid, args)
  }
  for uid, args in self.st.ann.impl_bargs {
    self.ctx.assign_implicit_block_args(uid, args)
  }
}

///|
/// The top-level `main` functions of a module, including the ones inside
/// namespaces.
///
/// Upstream `Context.findMain` walks the exported bindings: the terms of the
/// module itself first, then its namespaces — the order shows up in the
/// "Multiple main functions defined" message.
fn collect_mains(ctx : Context, defs : Array[Def], out : Array[Sym]) -> Unit {
  for d in defs {
    match d.kind {
      @source.DefKind::FunDef(id, _, _, _, _, _, _) =>
        if id.name == "main" {
          match ctx.symbol_of(id.uid) {
            Some(sym) => out.push(sym)
            None => ()
          }
        }
      _ => ()
    }
  }
  for d in defs {
    match d.kind {
      @source.DefKind::NamespaceDef(_, inner) => collect_mains(ctx, inner, out)
      _ => ()
    }
  }
}

///|
/// Checks the module's `main` functions (upstream `Typer.checkMain`): there is
/// at most one, and it takes no arguments, performs no effects and returns
/// `Unit`. This runs for every module; whether one *exists* is checked by the
/// backend (`Context.ensureMainExists`), which only knows the main module.
pub fn Typer::check_main(
  self : Typer,
  module : ModuleDecl,
) -> Unit raise EffektError {
  let mains : Array[Sym] = []
  collect_mains(self.ctx, module.defs, mains)
  if mains.length() > 1 {
    let names = mains.map(s => s.name().qualified_name()).join(", ")
    self.abort(module.span, "Multiple main functions defined: \{names}")
  }
  if mains.length() == 1 {
    let main = mains[0]
    match self.ctx.block_type_of(main.uid()) {
      Some(
        @symbols.BlockType::FunctionType(
          _,
          _,
          vparams,
          bparams,
          result,
          effects
        )
      ) => {
        if vparams.length() > 0 || bparams.length() > 0 {
          self.abort(main.decl(), "Main does not take arguments")
        }
        if effects.non_empty() {
          self.abort(
            main.decl(),
            "Main cannot have effects, but includes effects: \{effects}",
          )
        }
        if value_type_equal(result, t_int()) {
          self.abort(
            main.decl(),
            "Main must return Unit, please use `exit(n)` to return an error code.",
          )
        }
        if !value_type_equal(result, t_unit()) {
          self.match_expected(result, t_unit(), Some(main.decl()))
        }
      }
      _ => ()
    }
  }
}

// ---------------------------------------------------------------------------
// Definitions
// ---------------------------------------------------------------------------

///|
/// Stores the annotated types of definitions (needed for mutual recursion).
/// Does not check the bodies.
pub fn Typer::precheck_def(self : Typer, d : Def) -> Unit raise EffektError {
  match d.kind {
    @source.DefKind::FunDef(id, _, _, _, captures, _, _) => {
      let fun = self.symbol_of_def(id)
      // (1) fresh capture variable, or the annotated captures
      let cap = match captures {
        Some(cst) => self.resolve_captures(cst)
        None => @symbols.Captures::CaptVar(self.fresh_capt_var("function"))
      }
      self.bind_capture(fun, cap)
      // (2) store the annotated type
      match fun.annotated_type() {
        Some(tpe) => self.bind_block(fun, tpe)
        None => ()
      }
    }
    @source.DefKind::DefDef(id, captures, _, body) => {
      let obj = self.symbol_of_def(id)
      let cap = match captures {
        Some(cst) => self.resolve_captures(cst)
        None => @symbols.Captures::CaptVar(self.fresh_capt_var("block"))
      }
      match body.kind {
        @source.TermKind::New(implementation) => {
          let tpe = self.resolve_block_ref(implementation.interface)
          self.bind_block(obj, tpe)
          self.bind_capture(obj, cap)
        }
        _ => self.bind_capture(obj, cap)
      }
    }
    @source.DefKind::ExternDef(id, _, _, _, _, _, _) => {
      let fun = self.symbol_of_def(id)
      match fun.annotated_type() {
        Some(tpe) => {
          self.bind_block(fun, tpe)
          let capture = match fun {
            @symbols.Sym::ExternFunction(f) => f.capture
            _ => []
          }
          self.bind_capture(fun, @symbols.Captures::CaptureSetOf(capture))
          match tpe {
            @symbols.BlockType::FunctionType(_, _, _, _, _, effs) =>
              if effs.distinct().non_empty() {
                self.abort(
                  d.span,
                  "Unhandled control effects on extern defs not allowed",
                )
              }
            _ => ()
          }
        }
        None => self.abort(d.span, "Extern defs need a type annotation.")
      }
    }
    @source.DefKind::ExternResource(id, _) => {
      let res = self.symbol_of_def(id)
      self.bind_block(res, self.lookup_block(res))
      self.bind_capture(res, self.lookup_capture(res))
    }
    @source.DefKind::InterfaceDef(id, _, ops) => {
      ignore(id)
      for op in ops {
        let sym = self.symbol_of_def(op.id)
        match sym.annotated_type() {
          Some(tpe) => self.bind_block(sym, tpe)
          None =>
            self.abort(op.span, "Cannot find type for operation \{op.id.name}.")
        }
        // Bidirectional effects that mention the same effect recursively are
        // not (yet) supported.
        match sym {
          @symbols.Sym::Operation(o) =>
            if eff_contains(
                o.effects,
                @symbols.BlockType::InterfaceType(
                  o.interface,
                  o.tparams.map(t => @symbols.ValueType::ValueTypeRef(t)),
                ),
              ) {
              self.error(
                op.span,
                "Bidirectional effects that mention the same effect recursively are not (yet) supported.",
              )
            }
          _ => ()
        }
      }
    }
    @source.DefKind::DataDef(_, _, ctors) =>
      for c in ctors {
        let sym = self.symbol_of_def(c.id)
        match sym.annotated_type() {
          Some(tpe) => self.bind_block(sym, tpe)
          None =>
            self.abort(c.span, "Cannot find constructor type for \{c.id.name}.")
        }
        self.bind_capture(sym, Captures::empty())
      }
    @source.DefKind::RecordDef(id, _, fields) => {
      ignore(fields)
      let rec = self.symbol_of_def(id)
      match rec {
        @symbols.Sym::Record(r) => {
          let ctor = r.constructor
          match ctor.annotated_type() {
            Some(tpe) => self.bind_block(ctor, tpe)
            None => ()
          }
          self.bind_capture(ctor, Captures::empty())
          match ctor.as_callable() {
            Some(c) =>
              for v in c.vparams {
                match v {
                  @symbols.Sym::ValueParam(_p) =>
                    self.bind_capture(v, Captures::empty())
                  _ => ()
                }
              }
            None => ()
          }
        }
        _ => ()
      }
    }
    @source.DefKind::NamespaceDef(_, defs) =>
      for inner in defs {
        self.precheck_def(inner)
      }
    _ => ()
  }
}

///|
/// Checks a definition. Returns the effects that are not handled by the
/// definition itself.
pub fn Typer::synth_def(self : Typer, d : Def) -> TyRes[Unit] raise EffektError {
  self.focus = d.span
  match d.kind {
    @source.DefKind::FunDef(id, _, _, _, _, _, body) => {
      let sym = self.symbol_of_def(id)
      let function_capture = self.lookup_capture(sym)
      // Provide the capture variable to the unification scope, so that it is
      // solved when the function has been checked.
      let capt_vars = match function_capture {
        @symbols.Captures::CaptVar(x) => [x]
        @symbols.Captures::CaptureSetOf(_) => []
      }
      let (unhandled, result) = self.with_unification_scope(capt_vars, () => {
        let view = sym.as_callable()
        match view {
          None => self.abort(d.span, "Expected a function symbol.")
          Some(v) => {
            for vp in v.vparams {
              match self.lookup_first_value(vp) {
                Some(t) => self.bind_value(vp, t)
                None => ()
              }
            }
            for bp in v.bparams {
              match symbol_block_type(bp) {
                Some(t) => self.bind_block(bp, t)
                None => ()
              }
            }
            let inferred = @symbols.Captures::CaptVar(
              self.fresh_capt_var("function"),
            )
            self.flowing_into(inferred, () => {
              match sym.annotated_type() {
                Some(annotated) => {
                  // Upstream `Typer.synthDef`: `val bound = annotated.effects`
                  // — *only* the effects the function declares. The effects
                  // of a block parameter are not bound by the function that
                  // takes it: whoever calls the block provides the capability,
                  // and an effect the body performs without declaring it has
                  // to be handled inside the body (otherwise the effect would
                  // escape). Folding the parameter effects in here used to add
                  // capability parameters that the call sites never passed,
                  // so the generated JavaScript was one argument short.
                  let (cps, bound, ret_t) = match annotated {
                    @symbols.BlockType::FunctionType(_, capts, _, _, ret, effs) =>
                      (capture_params_of(capts), effs, ret)
                    _ => ([], Effects::empty(), t_unit())
                  }
                  let capabilities = canonical_order(bound.distinct().effects).map(e => {
                      self.fresh_capability_for(
                        e,
                        Sym::capture_param(effect_name(e)),
                      )
                    },
                  )
                  // Only the declared effects are bound as capabilities. A
                  // result annotation without a `/ ...` clause is parsed as
                  // `T / {}` (upstream `Parser.effectful` "pretends the effect
                  // set is empty", and `src/source` does the same), so it binds
                  // no capabilities and every effect of the body escapes the
                  // definition -- including the effects of *nested* definitions,
                  // which is what makes an unannotated effect of a local `def`
                  // visible to an enclosing handler (see the `stop` and `fail`
                  // loops of the standard library).
                  let res = self.binding_capabilities(d.uid, capabilities, () => {
                    self.check_stmt(body, Some(ret_t))
                  })
                  self.annotate_value(d.uid, res.tpe)
                  self.annotate_effects(d.uid, res.effs)
                  let filter = cps +
                    capabilities.map(c => capture_of_capability(c))
                  self.flows_into_without(
                    inferred,
                    function_capture,
                    filter,
                    d.span,
                  )
                  self.annotate_capture(d.uid, function_capture)
                  // The inferred effects can still mention unification
                  // variables (instantiating the declared effect `Exception[E]`
                  // of a call gives `Exception[?E]`); prune before comparing,
                  // otherwise the declared effect is never recognised.
                  // Everything the body performs beyond the declared effects is
                  // *not* handled by this definition: it escapes and is
                  // attributed to the enclosing statement (upstream:
                  // `Result(annotated, effs -- bound)`).
                  let unhandled = eff_diff(
                    self.st.u.prune_effects(res.effs),
                    bound,
                  )
                  (unhandled, annotated)
                }
                None => {
                  // All effects are handled by the function itself.
                  let (res, caps) = self.binding_all_capabilities(d.uid, () => {
                    self.check_stmt(body, None)
                  })
                  // The capabilities in `caps` were created (and keyed) by the
                  // *pruned* effect type the body asked for, while `res.effs`
                  // may still mention a unification variable that has been
                  // solved since. Prune before matching: otherwise the lookup
                  // misses, a second capability is created for the definition,
                  // and the body keeps referring to the first one — which then
                  // is never bound in the generated code.
                  let effects = self.st.u.prune_effects(res.effs)
                  let capabilities = canonical_order(effects.distinct().effects).map(e => {
                      match caps.get(interface_key(e)) {
                        Some(cap) => cap
                        None =>
                          self.fresh_capability_for(
                            e,
                            Sym::capture_param(effect_name(e)),
                          )
                      }
                    },
                  )
                  self.bind_capabilities(d.uid, capabilities)
                  self.annotate_value(d.uid, res.tpe)
                  self.annotate_effects(d.uid, effects)
                  let filter = match view {
                    Some(v) => v.bparams.map(b => capture_of_capability(b))
                    None => []
                  }
                  self.flows_into_without(
                    inferred,
                    function_capture,
                    filter + capabilities.map(c => capture_of_capability(c)),
                    d.span,
                  )
                  self.annotate_capture(d.uid, function_capture)
                  let fun_type = self.user_function_type(
                    sym,
                    res.tpe,
                    effects,
                    capabilities,
                  )
                  (Effects::empty(), fun_type)
                }
              }
            })
          }
        }
      })
      let substituted = self.st.u.prune_block(result)
      self.assert_concrete_function(id, substituted)
      self.bind_block(sym, substituted)
      self.annotate_block(d.uid, substituted)
      TyRes::new((), unhandled)
    }
    @source.DefKind::ValDef(id, _, binding) => {
      let sym = self.symbol_of_def(id)
      let res = match self.lookup_first_value(sym) {
        Some(t) => {
          let r = self.check_stmt(binding, Some(t))
          TyRes::new(t, r.effs)
        }
        None => self.check_stmt(binding, None)
      }
      self.bind_value(sym, res.tpe)
      self.annotate_value(d.uid, res.tpe)
      self.annotate_effects(d.uid, res.effs)
      TyRes::new((), res.effs)
    }
    @source.DefKind::RegDef(id, _, reg, binding) => {
      let sym = self.symbol_of_def(id)
      // A region may be introduced as a `RegBinder` (a `region r { ... }`)
      // or as a tracked parameter of type `Region` (a `var x in r = ...` whose
      // region is a block parameter); upstream accepts both by looking at the
      // block type of the symbol.
      let reg_sym = self.symbol_of_id(reg)
      let st_capt = match reg_sym {
        @symbols.Sym::RegBinder(r) =>
          @symbols.Captures::CaptureSetOf([r.region])
        _ =>
          if interface_type_equal(
              self.st.u.prune_block(self.lookup_block(reg_sym)),
              @symbols.t_region(),
            ) {
            self.lookup_capture(reg_sym)
          } else {
            self.abort(reg.span, "Expected a region.")
          }
      }
      self.bind_capture(sym, st_capt)
      let res = match self.lookup_first_value(sym) {
        Some(t) => {
          let r = self.check_stmt(binding, Some(t))
          TyRes::new(t, r.effs)
        }
        None => self.check_stmt(binding, None)
      }
      // to allocate into the region, it needs to be live
      self.using_capture(st_capt)
      self.bind_value(sym, res.tpe)
      self.annotate_value(d.uid, res.tpe)
      self.annotate_effects(d.uid, res.effs)
      TyRes::new((), res.effs)
    }
    @source.DefKind::DefDef(id, _, _, binding) => {
      let sym = self.symbol_of_def(id)
      let symbol_captures = self.lookup_capture(sym)
      let capt_vars = match symbol_captures {
        @symbols.Captures::CaptVar(x) => [x]
        @symbols.Captures::CaptureSetOf(_) => []
      }
      let declared = self.st.bt.get(sym.uid())
      let res = self.with_unification_scope(capt_vars, () => {
        self.flowing_into(symbol_captures, () => {
          let r = self.check_expr_as_block(binding, declared, None)
          self.bind_block(sym, r.tpe)
          self.annotate_block(d.uid, r.tpe)
          self.annotate_effects(d.uid, r.effs)
          TyRes::new((), r.effs)
        })
      })
      res
    }
    @source.DefKind::ExternDef(id, _, _, _, _, _, bodies) => {
      let sym = self.symbol_of_def(id)
      let view = sym.as_callable()
      self.with_unification_scope([], () => {
        match view {
          None => ()
          Some(v) => {
            for vp in v.vparams {
              match self.lookup_first_value(vp) {
                Some(t) => self.bind_value(vp, t)
                None => ()
              }
            }
            for bp in v.bparams {
              match symbol_block_type(bp) {
                Some(t) => self.bind_block(bp, t)
                None => ()
              }
            }
          }
        }
        let function_capture = self.lookup_capture(sym)
        let inferred = @symbols.Captures::CaptVar(self.fresh_capt_var("extern"))
        let block_captures = match view {
          Some(v) => v.bparams.map(b => capture_of_capability(b))
          None => []
        }
        self.flows_into_without(
          inferred,
          function_capture,
          block_captures,
          d.span,
        )
        self.flowing_into(inferred, () => {
          let expected_return = match sym.annotated_type() {
            Some(@symbols.BlockType::FunctionType(_, _, _, _, ret, _)) => ret
            _ => t_unit()
          }
          for body in bodies {
            match body {
              @source.ExternBody::StringExternBody(_, template) =>
                for arg in template.args {
                  let _ = self.check_expr(arg, None)
                }
              @source.ExternBody::EffektExternBody(_, stmt) => {
                let _ = self.check_stmt(stmt, Some(expected_return))
              }
              @source.ExternBody::Unsupported(_) => ()
            }
          }
        })
        self.annotate_effects(d.uid, Effects::empty())
      })
      TyRes::new((), Effects::empty())
    }
    @source.DefKind::NamespaceDef(_, defs) => {
      let mut acc = Effects::empty()
      for inner in defs {
        let r = self.synth_def(inner)
        acc = eff_union(acc, r.effs)
      }
      TyRes::new((), acc)
    }
    // all other definitions have already been prechecked
    _ => TyRes::new((), Effects::empty())
  }
}

///|
/// The name used for the capture parameter of an effect.
fn effect_name(e : BlockType) -> Name {
  match e {
    @symbols.BlockType::InterfaceType(c, _) => c.name()
    @symbols.BlockType::FunctionType(_, _, _, _, _, _) => Name::local("cap")
  }
}

///|
/// The type of a user function: `(vparams) { bparams } => result / effects`,
/// where the captures are the block parameters followed by the capabilities.
fn Typer::user_function_type(
  self : Typer,
  sym : Sym,
  result : ValueType,
  effs : Effects,
  capabilities : Array[Sym],
) -> BlockType {
  let view = sym.as_callable()
  match view {
    None =>
      @symbols.BlockType::FunctionType([], [], [], [], result, effs.distinct())
    Some(v) => {
      let capts : Array[Captures] = []
      let bps : Array[BlockType] = []
      for b in v.bparams {
        match symbol_block_type(b) {
          Some(t) => {
            bps.push(t)
            capts.push(
              @symbols.Captures::CaptureSetOf([capture_of_capability(b)]),
            )
          }
          None => ()
        }
      }
      let vps : Array[ValueType] = []
      for p in v.vparams {
        match self.lookup_first_value(p) {
          Some(t) => vps.push(t)
          None => ()
        }
      }
      for c in capabilities {
        capts.push(@symbols.Captures::CaptureSetOf([capture_of_capability(c)]))
      }
      @symbols.BlockType::FunctionType(
        v.tparams,
        capts,
        vps,
        bps,
        result,
        effs.distinct(),
      )
    }
  }
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
pub fn Typer::check_stmt(
  self : Typer,
  s : Stmt,
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  self.focus = s.span
  let res = self.check_stmt_kind(s, expected)
  self.annotate_value(s.uid, res.tpe)
  self.annotate_effects(s.uid, res.effs)
  match expected {
    Some(exp) => self.match_expected(res.tpe, exp, Some(s.span))
    None => ()
  }
  res
}

///|
fn Typer::check_stmt_kind(
  self : Typer,
  s : Stmt,
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  match s.kind {
    @source.StmtKind::DefStmt(d, rest) =>
      match d.kind {
        @source.DefKind::VarDef(id, _, binding) => {
          let sym = self.symbol_of_def(id)
          let st_capt = @symbols.Captures::CaptureSetOf([
            capture_of_capability(sym),
          ])
          let bind_res = match self.lookup_first_value(sym) {
            Some(t) => self.check_stmt(binding, Some(t))
            None => self.check_stmt(binding, None)
          }
          let st_tpe = bind_res.tpe
          self.bind_value(sym, st_tpe)
          self.bind_capture(sym, st_capt)
          let inferred = @symbols.Captures::CaptVar(self.fresh_capt_var("var"))
          self.using_capture(inferred)
          let rest_res = self.flowing_into(
            self.without(inferred, [capture_of_capability(sym)]),
            () => self.check_stmt(rest, expected),
          )
          self.annotate_value(d.uid, st_tpe)
          TyRes::new(rest_res.tpe, eff_union(bind_res.effs, rest_res.effs))
        }
        _ => {
          let bind_res = {
            let _r = self.precheck_def(d)
            self.synth_def(d)
          }
          let rest_res = self.check_stmt(rest, expected)
          TyRes::new(rest_res.tpe, eff_union(bind_res.effs, rest_res.effs))
        }
      }
    @source.StmtKind::ExprStmt(e, rest) => {
      let r1 = self.check_expr(e, None)
      let r2 = self.check_stmt(rest, expected)
      TyRes::new(r2.tpe, eff_union(r1.effs, r2.effs))
    }
    @source.StmtKind::Return(e) => self.check_expr(e, expected)
    @source.StmtKind::BlockStmt(inner) => self.check_stmt(inner, expected)
  }
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

///|
pub fn Typer::check_expr(
  self : Typer,
  e : Term,
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  self.focus = e.span
  let res = self.check_expr_kind(e, expected)
  self.annotate_value(e.uid, res.tpe)
  self.annotate_effects(e.uid, res.effs)
  match expected {
    Some(exp) => self.match_expected(res.tpe, exp, Some(e.span))
    None => ()
  }
  res
}

///|
fn Typer::check_expr_kind(
  self : Typer,
  e : Term,
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  match e.kind {
    @source.TermKind::Literal(_, tpe) => TyRes::new(tpe, Effects::empty())
    @source.TermKind::If(guards, thn, els) => {
      let geffs = self.check_guards(guards)
      let thn_res = self.check_stmt(thn, expected)
      let els_res = self.check_stmt(els, expected)
      let joined = self.join(expected, [
        (thn_res.tpe, Some(thn.span)),
        (els_res.tpe, Some(els.span)),
      ])
      TyRes::new(joined, eff_union_of([geffs, thn_res.effs, els_res.effs]))
    }
    @source.TermKind::While(guards, body, default) => {
      let geffs = self.check_guards(guards)
      let expected_type = match default {
        Some(_) => expected
        None => Some(t_unit())
      }
      let body_res = self.check_stmt(body, expected_type)
      let default_res = match default {
        Some(d) => self.check_stmt(d, expected_type)
        None => TyRes::new(t_unit(), Effects::empty())
      }
      let joined = self.join(expected, [
        (body_res.tpe, Some(body.span)),
        (default_res.tpe, None),
      ])
      TyRes::new(joined, eff_union_of([geffs, body_res.effs, default_res.effs]))
    }
    @source.TermKind::Var(id) => {
      let sym = self.symbol_of_id(id)
      match sym {
        @symbols.Sym::RegBinder(r) => {
          let tpe = self.lookup_value(sym)
          self.using_capture(@symbols.Captures::CaptureSetOf([r.region]))
          TyRes::new(tpe, Effects::empty())
        }
        @symbols.Sym::VarBinder(v) => {
          let tpe = self.lookup_value(sym)
          self.using_capture(@symbols.Captures::CaptureSetOf([v.capture]))
          TyRes::new(tpe, Effects::empty())
        }
        _ =>
          if sym.is_block_symbol() {
            self.abort(e.span, "Expected an expression, but got a block.")
          } else {
            TyRes::new(self.lookup_value(sym), Effects::empty())
          }
      }
    }
    @source.TermKind::Assign(id, expr) => {
      let sym = self.symbol_of_id(id)
      match sym {
        @symbols.Sym::RegBinder(r) => {
          let tpe = self.lookup_value(sym)
          self.using_capture(@symbols.Captures::CaptureSetOf([r.region]))
          let r_res = self.check_expr(expr, Some(tpe))
          TyRes::new(t_unit(), r_res.effs)
        }
        @symbols.Sym::VarBinder(v) => {
          let tpe = self.lookup_value(sym)
          self.using_capture(@symbols.Captures::CaptureSetOf([v.capture]))
          let r_res = self.check_expr(expr, Some(tpe))
          TyRes::new(t_unit(), r_res.effs)
        }
        _ => self.abort(e.span, "Expected a mutable variable in assignment.")
      }
    }
    @source.TermKind::Box(annotated, block) => {
      let expected_tpe = match expected {
        Some(@symbols.ValueType::BoxedType(t, _)) => Some(t)
        _ => None
      }
      let inferred_cap = match annotated {
        Some(cst) => self.resolve_captures(cst)
        None => @symbols.Captures::CaptVar(self.fresh_capt_var("box"))
      }
      let res = self.flowing_into(inferred_cap, () => {
        self.check_expr_as_block(block, expected_tpe, None)
      })
      let tpe = @symbols.ValueType::BoxedType(res.tpe, inferred_cap)
      match expected {
        Some(exp) => self.match_expected(tpe, exp, None)
        None => ()
      }
      TyRes::new(tpe, res.effs)
    }
    @source.TermKind::Unbox(_) =>
      self.abort(
        e.span,
        "Expected an expression, but got an unbox (which is a block).",
      )
    @source.TermKind::Select(receiver, field) => {
      let call = { uid: e.uid, span: e.span, name: field.name, }
      self.check_overloaded_function_call(
        call,
        field,
        [],
        [ValueArg::unnamed(receiver)],
        [],
        expected,
      )
    }
    @source.TermKind::Do(id, targs, vargs, bargs) => {
      let call = { uid: e.uid, span: e.span, name: id.name, }
      let resolved_targs = targs.map(t => self.resolve_value_type(t))
      let res = self.check_overloaded_function_call(
        call, id, resolved_targs, vargs, bargs, expected,
      )
      // find the capability that handles this operation
      let operation = self.symbol_of_id(id)
      let type_args = self.st.ann.type_args.get(e.uid).unwrap_or([])
      let tparams = match operation.as_callable() {
        Some(v) => v.tparams
        None => []
      }
      let subst = Substitutions::types(tparams, type_args)
      // The instantiated type arguments can still be unification variables
      // (e.g. `Exception[?E]` when calling an operation of a parameterized
      // interface); the effect that is recorded has to be the *concrete*
      // capability type, otherwise `eff_diff` against the declared effects
      // never recognises it as handled ("Unhandled effects {Exception[?E]}").
      let effect = self.st.u.prune_block(
        subst.substitute_block(applied_interface(operation)),
      )
      let capability = self.capability_for(effect, e.span)
      self.st.ann.cap_receiver.set(e.uid, capability)
      self.using_capture(
        @symbols.Captures::CaptureSetOf([capture_of_capability(capability)]),
      )
      TyRes::new(res.tpe, eff_union(res.effs, Effects::new([effect])))
    }
    @source.TermKind::Call(target, targs, vargs, bargs) => {
      let resolved_targs = targs.map(t => self.resolve_value_type(t))
      match target {
        @source.CallTarget::IdTarget(id) => {
          let call = { uid: e.uid, span: e.span, name: id.name, }
          self.check_overloaded_function_call(
            call, id, resolved_targs, vargs, bargs, expected,
          )
        }
        @source.CallTarget::ExprTarget(callee) => {
          let hint : (Int32, ValueType)? = match expected {
            Some(t) =>
              if bargs.length() == 0 {
                Some((vargs.length(), t))
              } else {
                None
              }
            None => None
          }
          let callee_res = self.check_expr_as_block(callee, None, hint)
          match callee_res.tpe {
            @symbols.BlockType::FunctionType(_, _, _, _, _, _) => {
              let call = { uid: e.uid, span: e.span, name: "function", }
              let res = self.check_call_to(
                call,
                [],
                [],
                [],
                callee_res.tpe,
                resolved_targs,
                vargs,
                bargs,
                expected,
                None,
              )
              TyRes::new(res.tpe, eff_union(res.effs, callee_res.effs))
            }
            _ => self.abort(e.span, "Cannot infer function type for callee.")
          }
        }
      }
    }
    @source.TermKind::MethodCall(receiver, id, targs, vargs, bargs) => {
      let resolved_targs = targs.map(t => self.resolve_value_type(t))
      self.check_overloaded_method_call(
        e, receiver, id, resolved_targs, vargs, bargs, expected,
      )
    }
    @source.TermKind::Region(id, body) => {
      let reg = self.symbol_of_def(id)
      let capture = match reg {
        @symbols.Sym::RegBinder(r) => r.region
        _ => Sym::capture_param(Name::local("region"))
      }
      self.bind_capture(reg, @symbols.Captures::CaptureSetOf([capture]))
      let inferred = @symbols.Captures::CaptVar(self.fresh_capt_var("region"))
      self.using_capture(inferred)
      let res = self.flowing_into(self.without(inferred, [capture]), () => {
        self.check_stmt(body, expected)
      })
      TyRes::new(res.tpe, res.effs)
    }
    @source.TermKind::TryHandle(prog, handlers) =>
      self.check_try_handle(e, prog, handlers, expected)
    @source.TermKind::Match(scs, clauses, default) => {
      let results = scs.map(sc => self.check_expr(sc, None))
      let mut res_eff = eff_union_of(results.map(r => r.effs))
      let arity = scs.length()
      for cls in clauses {
        match cls.pattern.kind {
          @source.PatternKind::MultiPattern(patterns) =>
            if patterns.length() != arity {
              self.error(
                cls.span,
                "Number of patterns (\{patterns.length()}) does not match number of parameters / scrutinees (\{arity}).",
              )
            }
          _ =>
            if arity != 1 {
              self.error(
                cls.span,
                "Number of patterns (1) does not match number of parameters / scrutinees (\{arity}).",
              )
            }
        }
      }
      let tpes_and_terms : Array[(ValueType, Span?)] = []
      for cls in clauses {
        match cls.pattern.kind {
          @source.PatternKind::MultiPattern(patterns) =>
            for i = 0; i < patterns.length() && i < results.length(); i = i + 1 {
              let bindings = self.check_pattern(results[i].tpe, patterns[i])
              self.bind_all(bindings)
            }
          _ =>
            if results.length() > 0 {
              let bindings = self.check_pattern(results[0].tpe, cls.pattern)
              self.bind_all(bindings)
            }
        }
        let guard_effs = self.check_guards(cls.guards)
        let body_res = self.check_stmt(cls.body, expected)
        res_eff = eff_union_of([res_eff, guard_effs, body_res.effs])
        tpes_and_terms.push((body_res.tpe, Some(cls.body.span)))
      }
      match default {
        Some(d) => {
          let default_res = self.check_stmt(d, expected)
          res_eff = eff_union(res_eff, default_res.effs)
          tpes_and_terms.push((default_res.tpe, Some(d.span)))
        }
        None => ()
      }
      let joined = self.join(expected, tpes_and_terms)
      // exhaustivity (only for a single scrutinee without a default branch)
      match default {
        None =>
          if scs.length() == 1 {
            self.check_exhaustive(scs[0], clauses, e.span)
          }
        Some(_) => ()
      }
      TyRes::new(joined, res_eff)
    }
    @source.TermKind::Hole(id, template) => {
      let sym = self.symbol_of_def(id)
      match sym {
        @symbols.Sym::Hole(h) => {
          let arg_types : Array[ValueType?] = []
          for arg in template.args {
            let r = self.check_stmt(arg, None)
            arg_types.push(Some(r.tpe))
          }
          h.expected_type = expected
          h.arg_types = arg_types
          TyRes::new(expected.unwrap_or(t_bottom()), Effects::empty())
        }
        _ => self.abort(e.span, "Expected a hole.")
      }
    }
    @source.TermKind::New(_) =>
      self.abort(
        e.span,
        "Expected an expression, but got an object implementation (which is a block).",
      )
    @source.TermKind::BlockLiteral(_, _, _, _) =>
      self.abort(e.span, "Expected an expression, but got a block literal.")
  }
}

///|
fn applied_interface(op : Sym) -> BlockType {
  match op {
    @symbols.Sym::Operation(o) => {
      let iface = match o.interface {
        @symbols.Sym::Interface(i) => i
        _ => {
          let base = o.interface.base()
          { base, tparams: [], operations: [], }
        }
      }
      @symbols.BlockType::InterfaceType(
        o.interface,
        iface.tparams.map(t => @symbols.ValueType::ValueTypeRef(t)),
      )
    }
    _ => @symbols.BlockType::InterfaceType(op, [])
  }
}

// ---------------------------------------------------------------------------
// Guards and patterns
// ---------------------------------------------------------------------------

///|
pub fn Typer::check_guards(
  self : Typer,
  guards : Array[MatchGuard],
) -> Effects raise EffektError {
  let mut effs = Effects::empty()
  for g in guards {
    let (bindings, guard_effs) = self.check_guard(g)
    self.bind_all(bindings)
    effs = eff_union(effs, guard_effs)
  }
  effs
}

///|
fn Typer::check_guard(
  self : Typer,
  g : MatchGuard,
) -> (Array[(Sym, ValueType)], Effects) raise EffektError {
  match g.kind {
    @source.GuardKind::BooleanGuard(cond) => {
      let r = self.check_expr(cond, Some(t_bool()))
      ([], r.effs)
    }
    @source.GuardKind::PatternGuard(scrutinee, pattern) => {
      let r = self.check_expr(scrutinee, None)
      (self.check_pattern(r.tpe, pattern), r.effs)
    }
  }
}

///|
fn Typer::bind_all(self : Typer, bindings : Array[(Sym, ValueType)]) -> Unit {
  for b in bindings {
    let (sym, tpe) = b
    self.bind_value(sym, tpe)
  }
}

///|
/// Infers the types of the variables bound by a pattern and checks the
/// pattern against the scrutinee type.
pub fn Typer::check_pattern(
  self : Typer,
  sc : ValueType,
  pattern : MatchPattern,
) -> Array[(Sym, ValueType)] raise EffektError {
  let res = self.check_pattern_kind(sc, pattern)
  self.annotate_value(pattern.uid, sc)
  res
}

///|
fn Typer::check_pattern_kind(
  self : Typer,
  sc : ValueType,
  pattern : MatchPattern,
) -> Array[(Sym, ValueType)] raise EffektError {
  match pattern.kind {
    IgnorePattern => []
    @source.PatternKind::AnyPattern(id) => {
      let sym = self.symbol_of_def(id)
      [(sym, sc)]
    }
    @source.PatternKind::LiteralPattern(_, tpe) => {
      self.match_pattern(sc, tpe, pattern.span)
      []
    }
    @source.PatternKind::TagPattern(id, patterns) => {
      let sym = self.symbol_of_id(id)
      let all_tparams = constructor_tparams(sym)
      let universals_count = match datatype_tparams(sym) {
        Some(ts) => ts.length()
        None => 0
      }
      let universals = all_tparams[0:universals_count].to_owned()
      let existentials = all_tparams[universals_count:].to_owned()
      let targs : Array[ValueType] = universals.map(t => {
        @symbols.ValueType::ValueTypeRef(self.fresh_type_var(t))
      })
      for e in existentials {
        targs.push(@symbols.ValueType::ValueTypeRef(e))
      }
      let ctor_type = match sym.annotated_type() {
        Some(t) => t
        None => self.abort(pattern.span, "Cannot find constructor type.")
      }
      let (vps, ret) = self.instantiate_value(ctor_type, all_tparams, targs, [])
      self.match_pattern(sc, ret, pattern.span)
      let mut bindings : Array[(Sym, ValueType)] = []
      if patterns.length() != vps.length() {
        self.abort(
          pattern.span,
          "Wrong number of pattern arguments, given \{patterns.length()}, expected \{vps.length()}.",
        )
      }
      for i = 0; i < patterns.length(); i = i + 1 {
        bindings = bindings + self.check_pattern(vps[i], patterns[i])
      }
      bindings
    }
    @source.PatternKind::MultiPattern(_) =>
      self.panic("Multi-pattern should have been split at the match.")
  }
}

///|
fn datatype_tparams(ctor : Sym) -> Array[Sym]? {
  match ctor {
    @symbols.Sym::Constructor(c) =>
      match c.tpe {
        @symbols.Sym::DataType(d) => Some(d.tparams)
        @symbols.Sym::Record(r) => Some(r.tparams)
        _ => None
      }
    _ => None
  }
}

// ---------------------------------------------------------------------------
// Subtyping
// ---------------------------------------------------------------------------

///|
/// The context of a type comparison; only used to produce better messages.
pub(all) enum ErrCtx {
  Expected(ValueType, ValueType)
  MergeTypes(ValueType, ValueType)
  Declaration(ValueType, ValueType)
  PatternMatch
  CaptureFlow
  Other
}

///|
fn explain_mismatch(left : String, right : String, ctx : ErrCtx) -> String {
  match ctx {
    Expected(_, _) =>
      (
        $|Expected type
        $|  \{right}
        $|but got type
        $|  \{left}
      )
    MergeTypes(_, _) =>
      (
        $|Different arms of a conditional/match have incompatible types.
        $|
        $|One arm has type
        $|  \{left}
        $|while another one has type
        $|  \{right}
      )
    Declaration(_, _) =>
      "Type \{left} does not match the declared type \{right}."
    PatternMatch =>
      "Pattern matches against type \{right} but scrutinee has type \{left}."
    CaptureFlow => "Capture flow error: \{left} is not included in \{right}."
    Other => "Type mismatch between \{left} and \{right}."
  }
}

///|
pub fn Typer::require_subtype_value(
  self : Typer,
  got : ValueType,
  expected : ValueType,
  ctx : ErrCtx,
) -> Unit raise EffektError {
  self.unify_value_types(
    self.st.u.prune_value(got),
    self.st.u.prune_value(expected),
    ctx,
  )
}

///|
fn Typer::match_expected(
  self : Typer,
  got : ValueType,
  expected : ValueType,
  span : Span?,
) -> Unit raise EffektError {
  ignore(span)
  let ctx = Expected(
    self.st.u.prune_value(got),
    self.st.u.prune_value(expected),
  )
  self.unify_value_types(
    self.st.u.prune_value(got),
    self.st.u.prune_value(expected),
    ctx,
  )
}

///|
fn Typer::match_pattern(
  self : Typer,
  scrutinee : ValueType,
  pattern_tpe : ValueType,
  span : Span,
) -> Unit raise EffektError {
  ignore(span)
  self.unify_value_types(
    self.st.u.prune_value(scrutinee),
    self.st.u.prune_value(pattern_tpe),
    PatternMatch,
  )
}

///|
/// Mirrors `TypeComparer.unifyValueTypes`. Coercions (`Any` / `Nothing`) are
/// checked structurally but not recorded, see the report.
///
/// Note: only *unification variables* are solved. A rigid type parameter
/// (e.g. `R` while checking `extern def f[R](x: R)`) is not — it takes part in
/// the structural comparison, and a unification variable on the *other* side is
/// solved instead. (Getting this wrong makes `f(x)` fail whenever the argument
/// has a rigid type.)
pub fn Typer::unify_value_types(
  self : Typer,
  tpe1 : ValueType,
  tpe2 : ValueType,
  ctx : ErrCtx,
) -> Unit raise EffektError {
  if tpe1 == tpe2 {
    return
  }
  // solve the unification variable, whichever side it is on
  match tpe1 {
    @symbols.ValueType::ValueTypeRef(x) =>
      if self.st.u.is_type_var(x) {
        self.learn(x, tpe2, ctx)
        return
      }
    _ => ()
  }
  match tpe2 {
    @symbols.ValueType::ValueTypeRef(x) =>
      if self.st.u.is_type_var(x) {
        self.learn(x, tpe1, ctx)
        return
      }
    _ => ()
  }
  // coercions: `Nothing <: T` and `T <: Any`. Upstream only admits these in
  // covariant positions and records a coercion; we accept them everywhere and
  // do not record them (see the report).
  if tpe1 == t_bottom() || tpe2 == t_top() {
    return
  }
  match (tpe1, tpe2) {
    (
      @symbols.ValueType::ValueTypeApp(c1, args1),
      @symbols.ValueType::ValueTypeApp(c2, args2),
    ) =>
      if !(c1 == c2) {
        self.unify_fail(tpe1, tpe2, ctx)
      } else if args1.length() != args2.length() {
        self.abort(
          self.focus,
          "Argument count does not match \{tpe1} vs. \{tpe2}",
        )
      } else {
        for i = 0; i < args1.length(); i = i + 1 {
          self.unify_value_types(args1[i], args2[i], ctx)
        }
      }
    (
      @symbols.ValueType::BoxedType(b1, c1),
      @symbols.ValueType::BoxedType(b2, c2),
    ) => {
      self.unify_block_types(b1, b2, ctx)
      self.unify_captures(c1, c2, ctx)
    }
    _ =>
      if tpe1 == t_bottom() || tpe2 == t_top() {
        ()
      } else {
        self.unify_fail(tpe1, tpe2, ctx)
      }
  }
}

///|
fn Typer::unify_fail(
  self : Typer,
  tpe1 : ValueType,
  tpe2 : ValueType,
  ctx : ErrCtx,
) -> Unit {
  self.error(self.focus, explain_mismatch("\{tpe1}", "\{tpe2}", ctx))
}

///|
fn Typer::learn(
  self : Typer,
  x : Sym,
  t : ValueType,
  ctx : ErrCtx,
) -> Unit raise EffektError {
  match self.st.u.types.get(x.uid()) {
    Some(existing) =>
      self.unify_value_types(
        self.st.u.prune_value(existing),
        self.st.u.prune_value(t),
        MergeTypes(self.st.u.prune_value(existing), self.st.u.prune_value(t)),
      )
    None => {
      ignore(ctx)
      self.st.u.set_type(x, t)
    }
  }
}

///|
pub fn Typer::unify_block_types(
  self : Typer,
  tpe1 : BlockType,
  tpe2 : BlockType,
  ctx : ErrCtx,
) -> Unit raise EffektError {
  let tpe1 = self.st.u.prune_block(tpe1)
  let tpe2 = self.st.u.prune_block(tpe2)
  match (tpe1, tpe2) {
    (
      @symbols.BlockType::FunctionType(_, capts1, vps1, bps1, ret1, effs1),
      @symbols.BlockType::FunctionType(_, capts2, vps2, bps2, ret2, effs2),
    ) => {
      if vps1.length() != vps2.length() {
        self.abort(
          self.focus,
          "Value parameter count does not match \{tpe1} vs. \{tpe2}",
        )
      }
      if bps1.length() != bps2.length() {
        self.abort(
          self.focus,
          "Block parameter count does not match \{tpe1} vs. \{tpe2}",
        )
      }
      if capts1.length() != capts2.length() {
        self.abort(self.focus, "Capture parameter count does not match.")
      }
      // map the capture parameters of the expected type to the given ones
      let params2 = capture_params_of(capts2)
      let subst = Substitutions::captures(params2, capts1)
      for i = 0; i < vps1.length(); i = i + 1 {
        self.unify_value_types(vps1[i], subst.substitute_value(vps2[i]), ctx)
      }
      for i = 0; i < bps1.length(); i = i + 1 {
        self.unify_block_types(bps1[i], subst.substitute_block(bps2[i]), ctx)
      }
      self.unify_value_types(ret1, subst.substitute_value(ret2), ctx)
      self.unify_effects(effs1, subst.substitute_effects(effs2), ctx)
    }
    (
      @symbols.BlockType::InterfaceType(c1, args1),
      @symbols.BlockType::InterfaceType(c2, args2),
    ) =>
      if !(c1 == c2) {
        self.error(self.focus, explain_mismatch("\{tpe1}", "\{tpe2}", ctx))
      } else {
        for i = 0; i < args1.length() && i < args2.length(); i = i + 1 {
          self.unify_value_types(args1[i], args2[i], ctx)
        }
      }
    _ => self.error(self.focus, explain_mismatch("\{tpe1}", "\{tpe2}", ctx))
  }
}

///|
/// Effects are compared for equality; if either side still mentions
/// unification variables the check is deferred.
pub fn Typer::unify_effects(
  self : Typer,
  effs1 : Effects,
  effs2 : Effects,
  ctx : ErrCtx,
) -> Unit {
  // compare the *substituted* effect sets: two effects that only differ in an
  // already solved unification variable are the same effect
  let l1 = self.st.u.prune_effects(effs1).distinct()
  let l2 = self.st.u.prune_effects(effs2).distinct()
  let has_unknowns = l1.effects.any(e => self.unknowns_block(e).length() > 0) ||
    l2.effects.any(e => self.unknowns_block(e).length() > 0)
  if !(l1 == l2) && !has_unknowns {
    self.error(self.focus, explain_mismatch("\{l1}", "\{l2}", ctx))
  }
}

///|
pub fn Typer::unify_captures(
  self : Typer,
  c1 : Captures,
  c2 : Captures,
  ctx : ErrCtx,
) -> Unit {
  ignore(ctx)
  self.require_subregion(c1, c2, self.focus)
  self.require_subregion(c2, c1, self.focus)
}

///|
/// The join of all types, used to merge the arms of `if` and `match`.
pub fn Typer::join(
  self : Typer,
  expected : ValueType?,
  tpes_and_terms : Array[(ValueType, Span?)],
) -> ValueType raise EffektError {
  let mut result : ValueType? = None
  for entry in tpes_and_terms {
    let (tpe, span) = entry
    ignore(span)
    match result {
      None => result = Some(tpe)
      Some(acc) =>
        result = Some(self.merge_value_types(acc, tpe, MergeTypes(acc, tpe)))
    }
  }
  match result {
    None =>
      match expected {
        Some(t) => t
        None => t_bottom()
      }
    Some(t) => t
  }
}

///|
/// Mirrors `TypeMerger.mergeValueTypes`.
pub fn Typer::merge_value_types(
  self : Typer,
  old : ValueType,
  new : ValueType,
  ctx : ErrCtx,
) -> ValueType raise EffektError {
  let old = self.st.u.prune_value(old)
  let new = self.st.u.prune_value(new)
  if old == new {
    return old
  }
  if old == t_top() || new == t_top() {
    return t_top()
  }
  if old == t_bottom() {
    return new
  }
  if new == t_bottom() {
    return old
  }
  match (old, new) {
    (@symbols.ValueType::ValueTypeRef(x), t) =>
      if self.st.u.is_type_var(x) {
        self.learn(x, t, ctx)
        old
      } else {
        // the *other* side might be the unification variable
        match t {
          @symbols.ValueType::ValueTypeRef(y) =>
            if self.st.u.is_type_var(y) {
              self.learn(y, old, ctx)
              new
            } else {
              self.abort(self.focus, explain_mismatch("\{old}", "\{t}", ctx))
            }
          _ => self.abort(self.focus, explain_mismatch("\{old}", "\{t}", ctx))
        }
      }
    (t, @symbols.ValueType::ValueTypeRef(x)) =>
      if self.st.u.is_type_var(x) {
        self.learn(x, t, ctx)
        new
      } else {
        self.abort(self.focus, explain_mismatch("\{old}", "\{t}", ctx))
      }
    (
      @symbols.ValueType::ValueTypeApp(c1, args1),
      @symbols.ValueType::ValueTypeApp(c2, args2),
    ) => {
      if !(c1 == c2) {
        self.abort(
          self.focus,
          "Cannot merge different constructors: \{old} vs. \{new}",
        )
      }
      for i = 0; i < args1.length() && i < args2.length(); i = i + 1 {
        self.unify_value_types(args1[i], args2[i], ctx)
      }
      old
    }
    (
      @symbols.ValueType::BoxedType(b1, c1),
      @symbols.ValueType::BoxedType(b2, c2),
    ) => {
      self.unify_block_types(b1, b2, ctx)
      self.unify_captures(c1, c2, ctx)
      old
    }
    _ => self.abort(self.focus, "Cannot merge \{old} with \{new}")
  }
}

// ---------------------------------------------------------------------------
// Instantiating type schemes
// ---------------------------------------------------------------------------

///|
/// The result of instantiating a function type.
pub(all) struct Instantiated {
  vparams : Array[ValueType]
  bparams : Array[BlockType]
  ret : ValueType
  effs : Effects
}

///|
/// `instantiate(tpe, tparams, targs, cargs)`: substitutes the type parameters
/// of a function type by the given type arguments and the capture parameters
/// by the given capture sets (upstream `Unification.instantiate`).
///
/// NOTE: in this port the first field of `BlockType::FunctionType` holds the
/// *type parameters* (see `Sym::annotated_type`), while the second holds one
/// capture set per block parameter and per effect.
pub fn Typer::instantiate(
  self : Typer,
  tpe : BlockType,
  tparams : Array[Sym],
  targs : Array[ValueType],
  cargs : Array[Captures],
) -> (Array[ValueType], Array[BlockType], ValueType, Effects) raise EffektError {
  match self.st.u.prune_block(tpe) {
    @symbols.BlockType::FunctionType(_, capts, vps, bps, ret, effs) => {
      if cargs.length() != capts.length() {
        self.abort(
          self.focus,
          "Capture arguments and parameter size mismatch: \{cargs.length()} vs. \{capts.length()}",
        )
      }
      if capts.length() != bps.length() + effs.distinct().size() {
        self.abort(
          self.focus,
          "Capture param count \{capts.length()} is not equal to bparam \{bps.length()} + control effects \{effs.distinct().size()}.\n  \{tpe}",
        )
      }
      let params : Array[Sym] = []
      for i = 0; i < capts.length(); i = i + 1 {
        match capture_param_of(capts[i]) {
          Some(x) => params.push(x)
          None => params.push(Sym::wildcard())
        }
      }
      let subst = Substitutions::types(tparams, targs).compose(
        Substitutions::captures(params, cargs),
      )
      (
        vps.map(v => subst.substitute_value(v)),
        bps.map(b => subst.substitute_block(b)),
        subst.substitute_value(ret),
        subst.substitute_effects(effs),
      )
    }
    _ => self.abort(self.focus, "Expected function type.")
  }
}

///|
/// Instantiation of a constructor type: type arguments only.
pub fn Typer::instantiate_value(
  self : Typer,
  tpe : BlockType,
  tparams : Array[Sym],
  targs : Array[ValueType],
  cargs : Array[Captures],
) -> (Array[ValueType], ValueType) raise EffektError {
  let (vps, _, ret, _) = self.instantiate(tpe, tparams, targs, cargs)
  (vps, ret)
}

///|
/// Instantiation with fresh unification variables and capture variables.
pub fn Typer::instantiate_fresh(
  self : Typer,
  tpe : BlockType,
  tparams : Array[Sym],
) -> (Array[ValueType], Array[Captures], Instantiated) raise EffektError {
  let pruned = self.st.u.prune_block(tpe)
  match pruned {
    @symbols.BlockType::FunctionType(_, capts, _, _, _, _) => {
      let type_args = tparams.map(t => {
        @symbols.ValueType::ValueTypeRef(self.fresh_type_var(t))
      })
      let capt_args = capts.map(_c => {
        @symbols.Captures::CaptVar(self.fresh_capt_var("instantiation"))
      })
      let (vps, bps, ret, effs) = self.instantiate(
        pruned, tparams, type_args, capt_args,
      )
      (type_args, capt_args, { vparams: vps, bparams: bps, ret, effs, })
    }
    _ => self.abort(self.focus, "Expected function type.")
  }
}

// ---------------------------------------------------------------------------
// Type trees
// ---------------------------------------------------------------------------

///|
/// Resolves a source type to a value type.
pub fn Typer::resolve_value_type(
  self : Typer,
  t : TypeTree,
) -> ValueType raise EffektError {
  match t.kind {
    @source.TypeKind::ValueTypeTree(v) => v
    @source.TypeKind::BoxedType(inner, capts) => {
      let b = self.resolve_block_type(inner)
      let c = self.resolve_captures(capts)
      @symbols.ValueType::BoxedType(b, c)
    }
    @source.TypeKind::TypeRef(id, args) => {
      let sym = self.symbol_of_id(id)
      let resolved = args.map(a => self.resolve_value_type(a))
      self.type_symbol_application(sym, resolved, t.span)
    }
    @source.TypeKind::Effectful(_, _) =>
      self.abort(t.span, "Expected a value type, but got an effectful type.")
    @source.TypeKind::FunctionType(_, _, _, _, _) =>
      self.abort(t.span, "Expected a value type, but got a function type.")
    @source.TypeKind::BlockTypeTree(_) =>
      self.abort(t.span, "Expected a value type, but got a block type.")
  }
}

///|
pub fn Typer::resolve_block_type(
  self : Typer,
  t : TypeTree,
) -> BlockType raise EffektError {
  match t.kind {
    @source.TypeKind::ValueTypeTree(_) =>
      self.abort(t.span, "Expected a block type, but got a value type.")
    @source.TypeKind::BlockTypeTree(b) => b
    @source.TypeKind::TypeRef(id, args) => {
      let sym = self.symbol_of_id(id)
      let resolved = args.map(a => self.resolve_value_type(a))
      // An interface in block position keeps its type arguments, i.e.
      // `Exc[String]` resolves to `InterfaceType(Exc, [String])` (upstream:
      // `Namer.resolveBlockRef`). `type_symbol_application` is for value
      // positions and erases them, which used to make every handler for a
      // parameterized interface unable to find its own capability.
      if sym.is_block_type_constructor() {
        @symbols.BlockType::InterfaceType(sym, resolved)
      } else {
        match self.type_symbol_application(sym, resolved, t.span) {
          @symbols.ValueType::ValueTypeApp(_) as v =>
            self.abort(t.span, "Expected a block type, but got \{v}.")
          @symbols.ValueType::BoxedType(_, _) as v =>
            self.abort(t.span, "Expected a block type, but got \{v}.")
          @symbols.ValueType::ValueTypeRef(s) =>
            self.abort(
              t.span,
              "Expected a block type, but got \{@symbols.ValueType::ValueTypeRef(s)}.",
            )
        }
      }
    }
    @source.TypeKind::FunctionType(tparams, vparams, bparams, ret, effs) => {
      // capture parameters: one per block parameter and one per effect
      let cps : Array[Sym] = []
      let capts : Array[Captures] = []
      let bps : Array[BlockType] = []
      for vp in vparams {
        ignore(vp)
      }
      let tparam_syms : Array[Sym] = tparams.map(p => self.symbol_of_def(p))
      for (id, bpt) in bparams {
        let b = self.resolve_block_type(bpt)
        let capture = match id {
          Some(i) =>
            match self.ctx.symbol_of(i.uid) {
              Some(@symbols.Sym::BlockParam(bp)) => bp.capture
              _ => Sym::capture_param(Name::local("anon"))
            }
          None => Sym::capture_param(Name::local("anon"))
        }
        cps.push(capture)
        capts.push(@symbols.Captures::CaptureSetOf([capture]))
        bps.push(b)
      }
      let resolved_effs : Array[BlockType] = []
      for e in effs.effs {
        let b = self.resolve_block_type(e)
        resolved_effs.push(b)
      }
      let distinct_effs = dedup_block_types(resolved_effs)
      for e in distinct_effs {
        let capture = Sym::capture_param(effect_name(e))
        cps.push(capture)
        capts.push(@symbols.Captures::CaptureSetOf([capture]))
      }
      let vps = vparams.map(v => self.resolve_value_type(v))
      let r = self.resolve_value_type(ret)
      ignore(tparam_syms)
      @symbols.BlockType::FunctionType(
        tparam_syms,
        capts,
        vps,
        bps,
        r,
        Effects::new(distinct_effs),
      )
    }
    @source.TypeKind::Effectful(inner, effs) => {
      // `T / E` in block position: the type of a block with effects
      let b = self.resolve_block_type(inner)
      let resolved_effs : Array[BlockType] = []
      for e in effs.effs {
        resolved_effs.push(self.resolve_block_type(e))
      }
      match b {
        @symbols.BlockType::FunctionType(
          tparams,
          capts,
          vps,
          bps,
          ret,
          inner_effs
        ) =>
          @symbols.BlockType::FunctionType(
            tparams,
            capts,
            vps,
            bps,
            ret,
            eff_union(
              inner_effs,
              Effects::new(dedup_block_types(resolved_effs)),
            ),
          )
        _ => b
      }
    }
    @source.TypeKind::BoxedType(_, _) =>
      self.abort(t.span, "Expected a block type, but got a boxed value type.")
  }
}

///|
pub fn Typer::resolve_block_ref(
  self : Typer,
  t : TypeTree,
) -> BlockType raise EffektError {
  let b = self.resolve_block_type(t)
  match b {
    @symbols.BlockType::InterfaceType(_, _) => b
    _ => self.abort(t.span, "Expected an interface type, but got \{b}.")
  }
}

///|
pub fn Typer::resolve_captures(self : Typer, c : CaptureSetTree) -> Captures {
  let out : Array[Sym] = []
  for id in c.captures {
    match self.ctx.symbol_of(id.uid) {
      Some(s) => if !out.contains(s) { out.push(s) }
      None => ()
    }
  }
  @symbols.Captures::CaptureSetOf(out)
}

///|
fn dedup_block_types(xs : Array[BlockType]) -> Array[BlockType] {
  let out : Array[BlockType] = []
  for x in xs {
    if !out.any(y => interface_type_equal(x, y)) {
      out.push(x)
    }
  }
  out
}

///|
/// Applies a type constructor symbol to arguments.
fn Typer::type_symbol_application(
  self : Typer,
  sym : Sym,
  args : Array[ValueType],
  span : Span,
) -> ValueType raise EffektError {
  match sym {
    @symbols.Sym::TypeParam(_) | @symbols.Sym::UnificationVar(_) =>
      if args.length() > 0 {
        self.abort(span, "Type parameter cannot be applied to arguments.")
      } else {
        @symbols.ValueType::ValueTypeRef(sym)
      }
    @symbols.Sym::DataType(_)
    | @symbols.Sym::Record(_)
    | @symbols.Sym::ExternType(_)
    | @symbols.Sym::ErrorValueType(_) =>
      @symbols.ValueType::ValueTypeApp(sym, args)
    @symbols.Sym::Interface(_)
    | @symbols.Sym::ExternInterface(_)
    | @symbols.Sym::ErrorBlockType(_) =>
      if args.length() == 0 {
        @symbols.ValueType::ValueTypeRef(sym)
      } else {
        // An interface used in a value position only makes sense through
        // `FunctionType` / `BoxedType`; keep it as a zero-argument reference.
        @symbols.ValueType::ValueTypeRef(sym)
      }
    @symbols.Sym::TypeAlias(a) => {
      if a.tparams.length() != args.length() {
        self.abort(span, "Wrong number of type arguments for the type alias.")
      }
      let subst = Substitutions::types(a.tparams, args)
      subst.substitute_value(a.tpe)
    }
    @symbols.Sym::EffectAlias(_) =>
      self.abort(span, "Expected a value type, but got an effect alias.")
    _ =>
      self.abort(
        span,
        "Expected a type constructor, but got \{sym.name().name}.",
      )
  }
}
