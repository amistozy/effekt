// The compiler context: diagnostics, cached annotations about type-checked
// phases, and compiler configuration.
//
// Upstream stores annotations in a side table keyed by object identity
// (`effekt/context/Annotations.scala`). Here every tree node has a unique
// `uid`, so plain maps do the job.

///|
pub(all) struct Config {
  /// Feature flags enabled for the current backend, e.g. ["js", "jsNode"].
  feature_flags : Array[String]
  /// Emit debug information into the generated code.
  debug : Bool
  /// Whether the optimizer runs.
  optimize : Bool
}

///|
pub fn Config::default() -> Config {
  { feature_flags: ["js", "jsNode"], debug: false, optimize: true, }
}

///|
pub(all) struct Context {
  mut messages : Array[Message]
  /// Resolved symbol of definition/reference nodes.
  symbols : Map[Int32, Sym]
  /// Inferred / resolved value types.
  value_types : Map[Int32, ValueType]
  /// Inferred / resolved block types.
  block_types : Map[Int32, BlockType]
  /// Types of nodes that can be either (e.g. `FunctionType` trees).
  types : Map[Int32, Sym] // unused placeholder, kept for symmetry
  /// Resolved capture sets.
  captures : Map[Int32, Captures]
  /// Effect annotations on function types and effectful trees.
  effects : Map[Int32, Effects]
  // -- Annotations produced by the type checker and consumed by
  //    ExplicitCapabilities (mirroring `context.Annotations` upstream).
  /// Block parameters that a function / block literal / op clause has to bind
  /// because of the effects it performs.
  bound_capabilities : Map[Int32, Array[Sym]]
  /// Implicit *value* arguments to be inserted at a call site.
  implicit_value_args : Map[Int32, Array[Term]]
  /// Implicit *block* arguments to be inserted at a call site.
  implicit_block_args : Map[Int32, Array[Term]]
  /// The capability a `do op()` dispatches on.
  capability_receiver : Map[Int32, Sym]
  /// Additional capabilities passed to a bidirectional operation call.
  capability_arguments : Map[Int32, Array[Sym]]
  /// Type arguments to be inserted at a call site.
  type_arguments : Map[Int32, Array[ValueType]]
  /// The lexical scope at a call site. The namer records it so that the type
  /// checker can resolve name-based implicit arguments, which is the only
  /// phase that needs to look a name up without an `IdRef`.
  call_scopes : Map[Int32, Scope]
  /// The module produced by the namer phase (exports and includes), if the
  /// namer has run. See `resolve`/`resolve_module` in `src/namer`.
  mut resolved_module : @symbols.Module?
  config : Config
}

///|
pub fn Context::new(config : Config) -> Context {
  {
    messages: [],
    symbols: Map([]),
    value_types: Map([]),
    block_types: Map([]),
    types: Map([]),
    captures: Map([]),
    effects: Map([]),
    bound_capabilities: Map([]),
    implicit_value_args: Map([]),
    implicit_block_args: Map([]),
    capability_receiver: Map([]),
    capability_arguments: Map([]),
    type_arguments: Map([]),
    call_scopes: Map([]),
    resolved_module: None,
    config,
  }
}

///|
pub fn Context::has_errors(self : Context) -> Bool {
  self.messages.any(m => m.severity == Error)
}

// Diagnostics
// -----------

///|
pub fn Context::report(self : Context, msg : Message) -> Unit {
  self.messages.push(msg)
}

///|
pub fn Context::error(self : Context, span : Span, msg : String) -> Unit {
  self.messages.push(Message::error(span, msg))
}

///|
pub fn Context::warning(self : Context, span : Span, msg : String) -> Unit {
  self.messages.push(Message::warning(span, msg))
}

///|
pub fn Context::info(self : Context, msg : String) -> Unit {
  self.messages.push(Message::info(msg))
}

///|
/// Reports an error and aborts the current phase.
pub fn Context::abort(
  self : Context,
  span : Span,
  msg : String,
) -> Unit raise EffektError {
  self.error(span, msg)
  raise EffektError::Fatal(msg)
}

///|
/// Reports an internal invariant violation. These are compiler bugs.
pub fn Context::panic(self : Context, msg : String) -> Unit raise EffektError {
  self.info("Internal compiler error: \{msg}")
  raise EffektError::Internal(msg)
}

// Annotations
// -----------

///|
pub fn Context::assign_symbol(self : Context, uid : Int32, sym : Sym) -> Unit {
  self.symbols.set(uid, sym)
}

///|
pub fn Context::symbol_of(self : Context, uid : Int32) -> Sym? {
  self.symbols.get(uid)
}

///|
pub fn Context::symbol_of_or(
  self : Context,
  uid : Int32,
  fallback : Sym,
) -> Sym {
  self.symbols.get(uid).unwrap_or(fallback)
}

///|
pub fn Context::assign_value_type(
  self : Context,
  uid : Int32,
  tpe : ValueType,
) -> Unit {
  self.value_types.set(uid, tpe)
}

///|
pub fn Context::value_type_of(self : Context, uid : Int32) -> ValueType? {
  self.value_types.get(uid)
}

///|
pub fn Context::assign_block_type(
  self : Context,
  uid : Int32,
  tpe : BlockType,
) -> Unit {
  self.block_types.set(uid, tpe)
}

///|
pub fn Context::block_type_of(self : Context, uid : Int32) -> BlockType? {
  self.block_types.get(uid)
}

///|
pub fn Context::assign_capture(
  self : Context,
  uid : Int32,
  capt : Captures,
) -> Unit {
  self.captures.set(uid, capt)
}

///|
pub fn Context::capture_of(self : Context, uid : Int32) -> Captures? {
  self.captures.get(uid)
}

///|
pub fn Context::assign_effects(
  self : Context,
  uid : Int32,
  effs : Effects,
) -> Unit {
  self.effects.set(uid, effs)
}

///|
pub fn Context::effects_of(self : Context, uid : Int32) -> Effects? {
  self.effects.get(uid)
}

///|
/// Copies a single annotation entry, keeping an existing annotation at `to`
/// (upstream `copyAnnotations`: `annotate(to, source ++ existing)`).
fn[V] copy_entry(
  from_map : Map[Int32, V],
  to_map : Map[Int32, V],
  from : Int32,
  to : Int32,
) -> Unit {
  if to_map.get(to) is None {
    match from_map.get(from) {
      Some(v) => to_map.set(to, v)
      None => ()
    }
  }
}

///|
/// Copies the *typing* annotations from one tree node to another (used by tree
/// rewriting passes that create new nodes, upstream `Context.copyAnnotations`).
/// Annotations the target already has are kept: a pass that replaced a node
/// with a more specific one wins over the node it replaces.
///
/// The elaboration annotations of `ExplicitCapabilities` are deliberately not
/// copied: they are *instructions* — "bind a capability for this block", "pass
/// these implicit arguments here" — and the hook that replaces the node has
/// already carried them out. Copying them would make a second traversal of the
/// same subtree (handler implementations are rewritten by `TryHandle` on top of
/// the generic traversal) apply them twice, e.g. adding a capability parameter
/// to a block literal twice and thus generating JavaScript with duplicate
/// parameter names.
pub fn Context::copy_annotations(
  self : Context,
  from : Int32,
  to : Int32,
) -> Unit {
  if from == to {
    return
  }
  copy_entry(self.symbols, self.symbols, from, to)
  copy_entry(self.value_types, self.value_types, from, to)
  copy_entry(self.block_types, self.block_types, from, to)
  copy_entry(self.captures, self.captures, from, to)
  copy_entry(self.effects, self.effects, from, to)
  copy_entry(self.type_arguments, self.type_arguments, from, to)
}

///|
pub fn Context::feature_flags(self : Context) -> Array[String] {
  self.config.feature_flags
}

///|
pub fn Context::supports(self : Context, flag : String) -> Bool {
  self.config.feature_flags.any(f => f == flag)
}

// The result of the namer phase
// -----------------------------

///|
/// Publishes the module symbol produced by the namer phase.
pub fn Context::set_resolved_module(
  self : Context,
  module : @symbols.Module,
) -> Unit {
  self.resolved_module = Some(module)
}

///|
/// The module symbol produced by the namer phase, if the namer has run.
pub fn Context::resolved_module(self : Context) -> @symbols.Module? {
  self.resolved_module
}

// Capability / implicit-argument annotations
// ------------------------------------------

///|
pub fn Context::assign_bound_capabilities(
  self : Context,
  uid : Int32,
  caps : Array[Sym],
) -> Unit {
  self.bound_capabilities.set(uid, caps)
}

///|
pub fn Context::bound_capabilities_of(
  self : Context,
  uid : Int32,
) -> Array[Sym] {
  self.bound_capabilities.get(uid).unwrap_or([])
}

///|
pub fn Context::assign_implicit_value_args(
  self : Context,
  uid : Int32,
  args : Array[Term],
) -> Unit {
  self.implicit_value_args.set(uid, args)
}

///|
pub fn Context::implicit_value_args_of(
  self : Context,
  uid : Int32,
) -> Array[Term] {
  self.implicit_value_args.get(uid).unwrap_or([])
}

///|
pub fn Context::assign_implicit_block_args(
  self : Context,
  uid : Int32,
  args : Array[Term],
) -> Unit {
  self.implicit_block_args.set(uid, args)
}

///|
pub fn Context::implicit_block_args_of(
  self : Context,
  uid : Int32,
) -> Array[Term] {
  self.implicit_block_args.get(uid).unwrap_or([])
}

///|
pub fn Context::assign_call_scope(
  self : Context,
  uid : Int32,
  scope : Scope,
) -> Unit {
  self.call_scopes.set(uid, scope)
}

///|
pub fn Context::call_scope_of(self : Context, uid : Int32) -> Scope? {
  self.call_scopes.get(uid)
}

///|
pub fn Context::assign_capability_receiver(
  self : Context,
  uid : Int32,
  cap : Sym,
) -> Unit {
  self.capability_receiver.set(uid, cap)
}

///|
pub fn Context::capability_receiver_of(self : Context, uid : Int32) -> Sym? {
  self.capability_receiver.get(uid)
}

///|
pub fn Context::assign_capability_arguments(
  self : Context,
  uid : Int32,
  caps : Array[Sym],
) -> Unit {
  self.capability_arguments.set(uid, caps)
}

///|
pub fn Context::capability_arguments_of(
  self : Context,
  uid : Int32,
) -> Array[Sym] {
  self.capability_arguments.get(uid).unwrap_or([])
}

///|
pub fn Context::assign_type_arguments(
  self : Context,
  uid : Int32,
  args : Array[ValueType],
) -> Unit {
  self.type_arguments.set(uid, args)
}

///|
pub fn Context::type_arguments_of(
  self : Context,
  uid : Int32,
) -> Array[ValueType] {
  self.type_arguments.get(uid).unwrap_or([])
}

// Diagnostics access
// ------------------

///|
/// All messages reported so far (errors, warnings, infos), in order.
pub fn Context::messages(self : Context) -> Array[Message] {
  self.messages
}
