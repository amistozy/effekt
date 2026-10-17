// The source-to-core transformer: an ANF (administrative normal form)
// translation.
//
// Mirrors `effekt/core/Transformer.scala`. `Expr` (pure) and `Stmt` (effectful)
// are distinguished and the `Binding` monad of `src/core/bind.mbt` sequences
// statements.
//
// Upstream threads its state through the compiler `Context` (`Context.emit`,
// `Context.bind`, `Context.withBindings`); here that state lives in the
// `Transformer` struct, which is passed explicitly.
//
// The typer's annotations are read from the source `Context`:
// `value_type_of(uid)`, `block_type_of(uid)`, `symbol_of(uid)`,
// `capture_of(uid)` and `type_arguments_of(uid)`.

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

///|
/// A toplevel entry of a core module: upstream's
/// `Toplevel | Declaration | Extern`.
pub(all) enum CoreToplevel {
  CoreToplevelDef(Toplevel)
  CoreToplevelDecl(Declaration)
  CoreToplevelExtern(Extern)
}

///|
/// The `infixEq` used to compile literal patterns. Since neither the source
/// module nor the source `Context` give access to the prelude's exports, the
/// driver can install the symbol here; `transform` additionally looks for an
/// `infixEq` extern in the module being transformed.
let pattern_equality_function : Ref[Sym?] = Ref(None)

///|
/// Installs the prelude's `infixEq`, used to compare literals in patterns.
pub fn set_pattern_equality_function(sym : Sym) -> Unit {
  pattern_equality_function.val = Some(sym)
}

///|
pub fn clear_pattern_equality_function() -> Unit {
  pattern_equality_function.val = None
}

///|
/// Translates a typechecked *source* module into core.
///
/// `module_path` is the Effekt include path, e.g. "examples/hello". It is used
/// when the source module does not carry a path itself.
pub fn transform(
  module : @source.ModuleDecl,
  module_path : String,
  ctx : @source.Context,
) -> ModuleDecl raise EffektError {
  transform_with_exports(module, module_path, ctx, [])
}

///|
/// Like [[transform]], but also sets the exports of the resulting core module.
///
/// Upstream takes the exports from the namer's `Module` (`mod.exports`), which
/// is not reachable from the source tree; use this entry point to pass them.
pub fn transform_with_exports(
  module : @source.ModuleDecl,
  module_path : String,
  ctx : @source.Context,
  exports : Array[Sym],
) -> ModuleDecl raise EffektError {
  let t = Transformer::new(ctx, module_path, find_equality_function(module))
  let toplevels : Array[CoreToplevel] = []
  for d in module.defs {
    for x in t.transform_toplevel(d) {
      toplevels.push(x)
    }
  }
  let declarations : Array[Declaration] = []
  let externs : Array[Extern] = []
  let definitions : Array[Toplevel] = []
  for x in toplevels {
    match x {
      CoreToplevelDef(d) => definitions.push(d)
      CoreToplevelDecl(d) => declarations.push(d)
      CoreToplevelExtern(e) => externs.push(e)
    }
  }
  t.assert_no_bindings()
  let path = if module.path != "" { module.path } else { module_path }
  let includes = module.includes.map(i => i.path)
  ModuleDecl::new(path, includes, declarations, externs, definitions, exports)
}

///|
/// The equality function to use for literal patterns: the one installed by the
/// driver, or an `infixEq` extern declared in the module itself.
fn find_equality_function(module : @source.ModuleDecl) -> Sym? {
  match pattern_equality_function.val {
    Some(sym) => Some(sym)
    None => {
      for d in module.defs {
        match d.kind {
          @source.ExternDef(id, _, _, _, _, _, _) =>
            if id.name == "infixEq" {
              return Some(
                Sym::ExternFunction({
                  base: {
                    uid: d.uid,
                    name: Name::local(id.name),
                    decl: d.span,
                  },
                  tparams: [],
                  vparams: [],
                  bparams: [],
                  result: t_bool(),
                  effects: Effects::empty(),
                  capture: [],
                }),
              )
            }
          _ => ()
        }
      }
      None
    }
  }
}

///|
/// The calling convention of a callable. Upstream resolves the preferred extern
/// body (`ResolveExternDefs.findPreferred`); the port's symbols do not carry the
/// bodies, so we approximate by the capture set.
pub(all) enum CallingConvention {
  ConvPure
  ConvDirect
  ConvControl
}

///|
fn calling_convention(sym : Sym) -> CallingConvention {
  match sym {
    ExternFunction(f) => {
      let capt : Captures = CaptureSetOf(f.capture)
      if capt.is_pure() {
        ConvPure
      } else if captures_pure_or_io(capt) {
        ConvDirect
      } else {
        ConvControl
      }
    }
    _ => ConvControl
  }
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

///|
fn[T] array_drop(xs : Array[T], n : Int32) -> Array[T] {
  let out : Array[T] = []
  let mut i = n
  while i < xs.length() {
    if i >= 0 {
      out.push(xs[i])
    }
    i = i + 1
  }
  out
}

// ---------------------------------------------------------------------------
// The transformer
// ---------------------------------------------------------------------------

///|
/// The state of a single source-to-core translation.
pub(all) struct Transformer {
  ctx : @source.Context
  /// The Effekt include path of the module, used for qualified signatures.
  module_path : String
  /// The prelude's `infixEq`, if known.
  eq_function : Sym?
  /// Bindings to be inserted at the current scope (upstream's mutable
  /// `ListBuffer` of the same name).
  mut bindings : Array[Binding]
  /// capture uid -> the core captures it has to be replaced by.
  mut capture_substitution : Map[Int32, Captures]
  /// Synthesized capture parameters of regions: the port's `Sym` has no
  /// `LexicalRegion.capture`, so we memoize one per region symbol.
  region_captures : Map[Int32, Sym]
  /// The type constructor used for prompts (`Type.TPrompt` upstream, which the
  /// port's type language does not have).
  prompt_ctor : Sym
}

///|
pub fn Transformer::new(
  ctx : @source.Context,
  module_path : String,
  eq_function : Sym?,
) -> Transformer {
  {
    ctx,
    module_path,
    eq_function,
    bindings: [],
    capture_substitution: Map([]),
    region_captures: Map([]),
    prompt_ctor: Sym::ErrorBlockType({
      base: {
        uid: @util.fresh_uid(),
        name: Name::local("Prompt"),
        decl: Span::missing(),
      },
      tparams: [],
    }),
  }
}

///|
/// The type of a prompt delimited by `reset`.
fn Transformer::prompt_type(
  self : Transformer,
  answer : ValueType,
) -> BlockType {
  InterfaceType(self.prompt_ctor, [answer])
}

// ---------------------------------------------------------------------------
// Bindings (upstream: TransformerOps on Context)
// ---------------------------------------------------------------------------

///|
/// Records a binding at the current scope. Block parameters give rise to a
/// capture substitution (mirrors `ContextOps.record`).
fn Transformer::emit(self : Transformer, binding : Binding) -> Unit {
  self.bindings.push(binding)
  match binding {
    BindingDef(id, block) =>
      match id {
        BlockParam(p) =>
          self.capture_substitution.set(p.capture.uid(), block_captures(block))
        _ => ()
      }
    _ => ()
  }
}

///|
/// Introduces a binding for the given expression.
fn Transformer::bind_expr(self : Transformer, e : Expr) -> Expr {
  match e {
    ValueVar(_, _) => e
    _ => {
      let x = Sym::tmp_value("r")
      self.emit(BindingLet(x, e))
      ValueVar(x, expr_type_hint(e))
    }
  }
}

///|
/// Introduces a binding for the given statement.
fn Transformer::bind_stmt(self : Transformer, s : Stmt) -> Expr {
  match s {
    Return(e) => self.bind_expr(e)
    _ => {
      let x = Sym::tmp_value("r")
      self.emit(BindingVal(x, s))
      ValueVar(x, unknown_value_type())
    }
  }
}

///|
/// Introduces a binding for an impure application.
fn Transformer::bind_impure_app(
  self : Transformer,
  callee : BlockVar,
  targs : Array[ValueType],
  vargs : Array[Expr],
  bargs : Array[Block],
) -> Expr {
  let x = Sym::tmp_value("r")
  self.emit(BindingImpureApp(x, callee, targs, vargs, bargs))
  ValueVar(x, unknown_value_type())
}

///|
/// Introduces a block binding with the given name.
fn Transformer::bind_block(
  self : Transformer,
  name : Sym,
  b : Block,
) -> BlockVar {
  self.emit(BindingDef(name, b))
  match b {
    BlockVar(bv) => BlockVar::new(name, bv.annotated_tpe, bv.annotated_capt)
    _ => BlockVar::new(name, unknown_block_type(), Captures::empty())
  }
}

///|
/// Runs `f` with a fresh binding list and returns the bindings it emitted
/// together with the result.
///
/// NOTE: upstream restores the state in a `finally`; MoonBit has no
/// `try`/`finally`, so a raising `f` leaves the transformer in the nested
/// state. This is harmless: a raise aborts the whole translation, and the
/// transformer is discarded.
fn[T] Transformer::with_bindings(
  self : Transformer,
  f : () -> T raise EffektError,
) -> (T, Array[Binding]) raise EffektError {
  let before = self.bindings
  let substitution_before = self.capture_substitution
  let collected : Array[Binding] = []
  self.bindings = collected
  self.capture_substitution = Map([])
  let result = f()
  self.bindings = before
  self.capture_substitution = substitution_before
  (result, collected)
}

///|
/// Collects the bindings emitted while computing the statement and prefixes
/// them to it.
fn Transformer::insert_bindings(
  self : Transformer,
  f : () -> Stmt raise EffektError,
) -> Stmt raise EffektError {
  let (body, bindings) = self.with_bindings(f)
  bindings_to_stmt(bindings, body)
}

///|
fn Transformer::assert_no_bindings(
  self : Transformer,
) -> Unit raise EffektError {
  if self.bindings.length() != 0 {
    raise EffektError::Internal(
      "There should not be any bindings left on the toplevel! Got: \{self.bindings.length()}",
    )
  }
}

///|
/// The capture parameter of a lexical region (see `Transformer.region_captures`).
fn Transformer::region_capture(self : Transformer, region : Sym) -> Sym {
  match self.region_captures.get(region.uid()) {
    Some(c) => c
    None => {
      let c = Sym::capture_param(region.name())
      self.region_captures.set(region.uid(), c)
      c
    }
  }
}

// ---------------------------------------------------------------------------
// Annotations
// ---------------------------------------------------------------------------

///|
fn Transformer::sym_of_def(
  self : Transformer,
  d : @source.Def,
) -> Sym raise EffektError {
  match self.ctx.symbol_of(d.uid) {
    Some(s) => s
    None => self.sym_of_id_def(d.id_def())
  }
}

///|
fn Transformer::sym_of_id_def(
  self : Transformer,
  id : @source.IdDef,
) -> Sym raise EffektError {
  match self.ctx.symbol_of(id.uid) {
    Some(s) => s
    None => raise EffektError::Internal("No symbol annotated for `\{id.name}`.")
  }
}

///|
fn Transformer::sym_of_ref(
  self : Transformer,
  id : @source.IdRef,
) -> Sym raise EffektError {
  match self.ctx.symbol_of(id.uid) {
    Some(s) => s
    None => raise EffektError::Internal("No symbol annotated for `\{id.name}`.")
  }
}

///|
fn Transformer::value_type_of_sym(self : Transformer, sym : Sym) -> ValueType {
  match self.ctx.value_type_of(sym.uid()) {
    Some(t) => t
    None =>
      match sym {
        ValueParam(p) => p.tpe.unwrap_or(unknown_value_type())
        ValBinder(v) => v.tpe.unwrap_or(unknown_value_type())
        VarBinder(v) => v.tpe.unwrap_or(unknown_value_type())
        RegBinder(r) => r.tpe.unwrap_or(unknown_value_type())
        _ => unknown_value_type()
      }
  }
}

///|
fn Transformer::block_type_of_sym(self : Transformer, sym : Sym) -> BlockType {
  match self.ctx.block_type_of(sym.uid()) {
    Some(t) => t
    None =>
      match sym {
        BlockParam(p) => p.tpe.unwrap_or(unknown_block_type())
        DefBinder(d) => d.tpe.unwrap_or(unknown_block_type())
        ExternResource(r) => r.tpe
        LexicalRegion(_) => t_region()
        // Upstream computes the block type of a reference binder from its
        // value type: a `var` (in the current region or in an explicit one)
        // has type `Ref[S]`, a region is a `Region`.
        VarBinder(v) => t_state(v.tpe.unwrap_or(unknown_value_type()))
        RegBinder(r) => t_state(r.tpe.unwrap_or(unknown_value_type()))
        _ => sym.annotated_type().unwrap_or(unknown_block_type())
      }
  }
}

///|
/// The type of the state a reference binder refers to, i.e. `S` in `Ref[S]`.
///
/// Upstream `TState.extractType`; we reproduce the check (and improve the
/// diagnostic) instead of calling `@symbols.t_state_extract`, which cannot
/// report the offending type.
fn Transformer::state_type_of(
  self : Transformer,
  sym : Sym,
) -> ValueType raise EffektError {
  let tpe = self.block_type_of_sym(sym)
  match tpe {
    InterfaceType(i, args) =>
      if i.uid() == @symbols.state_effect_sym().uid() && args.length() == 1 {
        args[0]
      } else {
        raise EffektError::Internal(
          "Expected the builtin mutable state `Ref[S]` for `\{sym.name().name}` (a " +
          "\{sym_kind(sym)}), but the block type is \{show_core_block_type(tpe)}.",
        )
      }
    _ =>
      raise EffektError::Internal(
        "Expected the builtin mutable state `Ref[S]` for `\{sym.name().name}` (a " +
        "\{sym_kind(sym)}), but the block type is \{show_core_block_type(tpe)}.",
      )
  }
}

///|
fn Transformer::capture_of_sym(self : Transformer, sym : Sym) -> Captures {
  match self.ctx.capture_of(sym.uid()) {
    Some(c) => c
    None =>
      match sym {
        BlockParam(p) => CaptureSetOf([p.capture])
        VarBinder(v) => CaptureSetOf([v.capture])
        ExternResource(r) => CaptureSetOf([r.capture])
        ExternFunction(f) => CaptureSetOf(f.capture)
        LexicalRegion(_) => CaptureSetOf([self.region_capture(sym)])
        _ => Captures::empty()
      }
  }
}

///|
/// The inferred type of a tree node, or an unknown type if the typer did not
/// annotate it.
fn Transformer::type_of_uid(self : Transformer, uid : Int32) -> ValueType {
  self.ctx.value_type_of(uid).unwrap_or(unknown_value_type())
}

///|
fn Transformer::inferred_type_of(
  self : Transformer,
  t : @source.Term,
) -> ValueType {
  self.type_of_uid(t.uid)
}

///|
/// The inferred capture set of a tree node. Upstream's `inferredCapture`.
fn Transformer::capture_of_uid(self : Transformer, uid : Int32) -> Captures {
  self.ctx.capture_of(uid).unwrap_or(Captures::empty())
}

///|
fn Transformer::inferred_capture(
  self : Transformer,
  t : @source.Term,
) -> Captures {
  self.capture_of_uid(t.uid)
}

///|
fn Transformer::type_arguments_of(
  self : Transformer,
  t : @source.Term,
) -> Array[ValueType] {
  self.ctx.type_arguments_of(t.uid)
}

///|
/// Is this tree pure (no captures)? Upstream consults the typer's inferred
/// capture set and conservatively answers `false` when there is none.
fn Transformer::is_pure_uid(self : Transformer, uid : Int32) -> Bool {
  match self.ctx.capture_of(uid) {
    Some(capt) => capt.is_pure()
    None => false
  }
}

///|
fn Transformer::is_pure_or_io_uid(self : Transformer, uid : Int32) -> Bool {
  match self.ctx.capture_of(uid) {
    Some(capt) => captures_pure_or_io(capt)
    // The type checker records capture sets on *symbols*; a binding statement
    // therefore usually has no capture annotation. Fall back to its effect
    // annotation, which is always available: an empty (or absent) effect set
    // means the binding is pure and may sit on the toplevel.
    None =>
      match self.ctx.effects_of(uid) {
        Some(effs) => effects_pure_or_io(effs)
        None => true
      }
  }
}

///|
/// Mirrors the effect-level part of `CaptureSet.pureOrIO`: only `IO` effects
/// may escape to the toplevel.
fn effects_pure_or_io(effs : Effects) -> Bool {
  let io : Sym? = match @symbols.t_io() {
    InterfaceType(ctor, _) => Some(ctor)
    _ => None
  }
  match io {
    None => false
    Some(io_sym) =>
      effs
      .to_list()
      .all(e => {
        match e {
          InterfaceType(ctor, _) => ctor.uid() == io_sym.uid()
          _ => false
        }
      })
  }
}

///|
/// Mirrors `CaptureSet.pureOrIO`: mutable state and async are not IO, but IO
/// and (other) resources are.
fn captures_pure_or_io(capt : Captures) -> Bool {
  capt
  .to_array()
  .all(c => {
    let is_io = c.uid() == @symbols.io_capture().uid()
    let is_async = c.uid() == @symbols.async_capture().uid()
    let is_mutable_state = match c {
      LexicalRegion(_) => true
      _ => false
    }
    let is_resource = match c {
      Resource(_) => true
      _ => false
    }
    !(is_async || is_mutable_state) && (is_io || is_resource)
  })
}

// ---------------------------------------------------------------------------
// Translation on types
// ---------------------------------------------------------------------------

///|
fn Transformer::transform_value_type(
  self : Transformer,
  tpe : ValueType,
) -> ValueType {
  match tpe {
    BoxedType(t, capt) =>
      BoxedType(self.transform_block_type(t), self.transform_captures(capt))
    ValueTypeRef(tvar) => ValueTypeRef(tvar)
    ValueTypeApp(tc, args) =>
      if args.length() == 0 && core_builtin_to_string(tc) == Some("Any") {
        // We translate to Unit in core, to be consistent with coercions
        // introducing unit values.
        t_unit()
      } else {
        ValueTypeApp(tc, args.map(t => self.transform_value_type(t)))
      }
  }
}

///|
/// Capabilities materialize as extra block parameters, so the resulting block
/// type carries no effects anymore.
fn Transformer::transform_block_type(
  self : Transformer,
  tpe : BlockType,
) -> BlockType {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result, effects) => {
      let capability_types = @symbols.canonical_order(effects.to_list()).map(e => {
        self.transform_block_type(e)
      })
      let all_block_params = bparams.map(b => self.transform_block_type(b)) +
        capability_types
      // upstream asserts cparams.size == allBlockParams.size here; the port
      // cannot, since the typer's annotations are not guaranteed to be complete.
      FunctionType(
        tparams,
        cparams,
        vparams.map(t => self.transform_value_type(t)),
        all_block_params,
        self.transform_value_type(result),
        Effects::empty(),
      )
    }
    InterfaceType(tc, args) =>
      InterfaceType(tc, args.map(t => self.transform_value_type(t)))
  }
}

///|
fn Transformer::transform_captures(
  self : Transformer,
  capt : Captures,
) -> Captures {
  match capt {
    // upstream: Context.panic("... should be a concrete capture set in this phase.")
    CaptVar(_) => capt
    CaptureSetOf(cs) => {
      let out : Array[Sym] = []
      for c in cs {
        match self.capture_substitution.get(c.uid()) {
          Some(replacement) =>
            for x in replacement.to_array() {
              out.push(x)
            }
          None => out.push(c)
        }
      }
      CaptureSetOf(dedup_syms(out))
    }
  }
}

// ---------------------------------------------------------------------------
// Types of symbols
// ---------------------------------------------------------------------------

///|
fn Transformer::transform_value_param(
  self : Transformer,
  p : @source.ValueParam,
) -> ValueParam {
  let sym = match self.ctx.symbol_of(p.id.uid) {
    Some(s) => s
    None => Sym::value_param(Name::local(p.id.name), None, p.id.span)
  }
  ValueParam::new(sym, self.transform_value_type(self.value_type_of_sym(sym)))
}

///|
fn Transformer::transform_block_param(
  self : Transformer,
  p : @source.BlockParam,
) -> BlockParam {
  let sym = match self.ctx.symbol_of(p.id.uid) {
    Some(s) => s
    None =>
      Sym::block_param(
        Name::local(p.id.name),
        None,
        Sym::capture_param(Name::local(p.id.name)),
        false,
        p.id.span,
      )
  }
  BlockParam::new(
    sym,
    self.transform_block_type(self.block_type_of_sym(sym)),
    self.transform_captures(self.capture_of_sym(sym)),
  )
}

///|
/// A typed value variable.
fn Transformer::value_var(self : Transformer, sym : Sym) -> Expr {
  ValueVar(sym, self.transform_value_type(self.value_type_of_sym(sym)))
}

///|
/// A typed block variable.
fn Transformer::block_var(self : Transformer, sym : Sym) -> BlockVar {
  BlockVar::new(
    sym,
    self.transform_block_type(self.block_type_of_sym(sym)),
    self.transform_captures(self.capture_of_sym(sym)),
  )
}

// ---------------------------------------------------------------------------
// Toplevel definitions
// ---------------------------------------------------------------------------

///|
fn Transformer::transform_toplevel(
  self : Transformer,
  d : @source.Def,
) -> Array[CoreToplevel] raise EffektError {
  let result : Array[CoreToplevel] = []
  match d.kind {
    @source.FunDef(_id, tps, vps, bps, _cpt, _ret, body) => {
      let sym = self.sym_of_def(d)
      let tparams : Array[Sym] = []
      for p in tps {
        tparams.push(self.sym_of_id_def(p))
      }
      let cparams : Array[Sym] = []
      for b in bps {
        cparams.push(self.block_param_capture(b))
      }
      let vparams : Array[ValueParam] = []
      for p in vps {
        vparams.push(self.transform_value_param(p))
      }
      let bparams : Array[BlockParam] = []
      for p in bps {
        bparams.push(self.transform_block_param(p))
      }
      let body = self.insert_bindings(fn() raise EffektError {
        self.transform_stmt(body)
      })
      result.push(
        CoreToplevelDef(
          ToplevelDef(
            sym,
            BlockLit(BlockLit::new(tparams, cparams, vparams, bparams, body)),
          ),
        ),
      )
    }
    @source.DataDef(_id, tparams, ctors) => {
      let datatype = self.sym_of_def(d)
      let dt_tparams = self.type_constructor_tparams_of(datatype, tparams)
      let ctors_of_symbol = type_constructor_constructors(datatype)
      let ctor_syms = if ctors_of_symbol.length() > 0 {
        ctors_of_symbol
      } else {
        let out : Array[Sym] = []
        for c in ctors {
          out.push(self.sym_of_constructor(c))
        }
        out
      }
      let core_ctors : Array[Constructor] = []
      for c in ctor_syms {
        core_ctors.push(self.transform_constructor(c))
      }
      result.push(
        CoreToplevelDecl(DeclarationData(datatype, dt_tparams, core_ctors)),
      )
    }
    @source.RecordDef(_id, tparams, _params) => {
      let rec = self.sym_of_def(d)
      let rec_tparams = self.type_constructor_tparams_of(rec, tparams)
      let ctor_syms = type_constructor_constructors(rec)
      let core_ctors : Array[Constructor] = []
      for c in ctor_syms {
        core_ctors.push(self.transform_constructor(c))
      }
      result.push(
        CoreToplevelDecl(DeclarationData(rec, rec_tparams, core_ctors)),
      )
    }
    @source.ValDef(_id, _tpe, binding) =>
      if self.is_pure_or_io_uid(binding.uid) {
        let transformed = self.insert_bindings(fn() raise EffektError {
          self.transform_stmt(binding)
        })
        // TODO what to do with the potentially annotated type here?
        result.push(
          CoreToplevelDef(ToplevelVal(self.sym_of_def(d), transformed)),
        )
      } else {
        self.ctx.abort(d.span, "Effectful bindings not allowed on the toplevel")
      }
    @source.DefDef(_id, _captures, _annot, binding) => {
      let sym = self.sym_of_def(d)
      let (definition, bindings) = self.with_bindings(fn() raise EffektError {
        CoreToplevelDef(ToplevelDef(sym, self.transform_as_block(binding)))
      })
      for b in bindings {
        result.push(CoreToplevelDef(b.to_toplevel()))
      }
      result.push(definition)
    }
    @source.VarDef(_, _, _) =>
      self.ctx.abort(
        d.span,
        "Mutable variable bindings not allowed on the toplevel",
      )
    @source.RegDef(_, _, _, _) =>
      self.ctx.abort(
        d.span,
        "Mutable variable bindings not allowed on the toplevel",
      )
    @source.InterfaceDef(_id, _tparams_interface, ops) => {
      let interface = self.sym_of_def(d)
      let tparams = interface_tparams(interface)
      let ops_of_symbol = interface_operations(interface)
      let op_syms = if ops_of_symbol.length() > 0 {
        ops_of_symbol
      } else {
        let out : Array[Sym] = []
        for op in ops {
          out.push(self.sym_of_id_def(op.id))
        }
        out
      }
      let properties : Array[Property] = []
      for op in op_syms {
        properties.push(
          Property::new(op, self.operation_at_declaration(tparams, op)),
        )
      }
      result.push(
        CoreToplevelDecl(DeclarationInterface(interface, tparams, properties)),
      )
    }
    @source.ExternDef(_id, _tparams, vps, bps, _capt, _ret, bodies) => {
      let sym = self.sym_of_def(d)
      match sym {
        ExternFunction(f) => {
          if f.effects.non_empty() {
            raise EffektError::Internal(
              "Extern functions should not have effects.",
            )
          }
          let qualified = QualifiedSignature::from_extern_function(
            self.module_path,
            sym,
          )
          let cps : Array[Sym] = []
          for b in bps {
            cps.push(self.block_param_capture(b))
          }
          let vparams : Array[ValueParam] = []
          for p in vps {
            vparams.push(self.transform_value_param(p))
          }
          let bparams : Array[BlockParam] = []
          for p in bps {
            bparams.push(self.transform_block_param(p))
          }
          let tbody = self.transform_extern_bodies(bodies, "ExternDef")
          result.push(
            CoreToplevelExtern(
              ExternDef(
                sym,
                qualified,
                f.tparams,
                cps,
                vparams,
                bparams,
                self.transform_value_type(f.result),
                self.transform_captures(CaptureSetOf(f.capture)),
                tbody,
              ),
            ),
          )
        }
        _ =>
          raise EffektError::Internal(
            "Extern definitions should be extern functions.",
          )
      }
    }
    @source.ExternType(_id, _tparams, bodies) => {
      let sym = self.sym_of_def(d)
      let tps = match sym {
        ExternType(t) => t.tparams
        _ => []
      }
      let tbody = self.transform_extern_bodies(bodies, "ExternType")
      result.push(CoreToplevelExtern(ExternData(sym, tps, tbody)))
    }
    @source.ExternInclude(ff, path, contents) => {
      let contents = match contents {
        Some(c) => c
        None =>
          raise EffektError::Internal(
            "Extern include `\{path}` should have been resolved before core.Transformer.",
          )
      }
      result.push(CoreToplevelExtern(ExternInclude(ff, contents)))
    }
    @source.NamespaceDef(_name, defs) =>
      for inner in defs {
        for x in self.transform_toplevel(inner) {
          result.push(x)
        }
      }

    // For now we forget about all of the following definitions in core:
    @source.ExternResource(_, _) => ()
    @source.ExternInterface(_, _, _) => ()
    @source.TypeDef(_, _, _) => ()
    @source.EffectDef(_, _, _) => ()
  }
  result
}

///|
/// The capture parameter introduced by a block parameter.
fn Transformer::block_param_capture(
  self : Transformer,
  b : @source.BlockParam,
) -> Sym {
  let sym = match self.ctx.symbol_of(b.id.uid) {
    Some(s) => s
    None =>
      Sym::block_param(
        Name::local(b.id.name),
        None,
        Sym::wildcard(),
        false,
        b.id.span,
      )
  }
  match sym {
    BlockParam(p) => p.capture
    _ => self.region_capture(sym)
  }
}

///|
fn Transformer::sym_of_constructor(
  self : Transformer,
  c : @source.Constructor,
) -> Sym raise EffektError {
  match self.ctx.symbol_of(c.uid) {
    Some(s) => s
    None => self.sym_of_id_def(c.id)
  }
}

///|
fn type_constructor_tparams(sym : Sym) -> Array[Sym] {
  match sym {
    DataType(d) => d.tparams
    Record(r) => r.tparams
    ExternType(t) => t.tparams
    Interface(i) => i.tparams
    ExternInterface(i) => i.tparams
    ErrorValueType(t) => t.tparams
    ErrorBlockType(t) => t.tparams
    _ => []
  }
}

///|
fn type_constructor_constructors(sym : Sym) -> Array[Sym] {
  match sym {
    DataType(d) => d.constructors
    Record(r) => [r.constructor]
    _ => []
  }
}

///|
fn interface_tparams(sym : Sym) -> Array[Sym] {
  match sym {
    Interface(i) => i.tparams
    _ => []
  }
}

///|
fn interface_operations(sym : Sym) -> Array[Sym] {
  match sym {
    Interface(i) => i.operations
    _ => []
  }
}

///|
fn Transformer::type_constructor_tparams_of(
  self : Transformer,
  sym : Sym,
  from_source : Array[@source.IdDef],
) -> Array[Sym] {
  let tparams = type_constructor_tparams(sym)
  if tparams.length() > 0 {
    return tparams
  }
  let out : Array[Sym] = []
  for t in from_source {
    match self.ctx.symbol_of(t.uid) {
      Some(s) => out.push(s)
      None => ()
    }
  }
  out
}

///|
/// `core.Constructor(c, c.tparams.drop(c.tpe.tparams.size), fields)`: the
/// leading type parameters are the universals of the data type, the remaining
/// ones are existentials.
fn Transformer::transform_constructor(
  self : Transformer,
  ctor : Sym,
) -> Constructor raise EffektError {
  match ctor {
    Constructor(c) => {
      let universals = type_constructor_tparams(c.tpe).length()
      let tparams = array_drop(c.tparams, universals)
      let fields : Array[Field] = []
      for f in c.fields {
        fields.push(
          Field::new(f, self.transform_value_type(field_return_type(f))),
        )
      }
      Constructor::new(ctor, tparams, fields)
    }
    _ =>
      raise EffektError::Internal(
        "Constructors can only be part of data types or records.",
      )
  }
}

///|
/// Transforms the resolved extern bodies of an `ExternType` or `ExternDef`.
fn Transformer::transform_extern_bodies(
  self : Transformer,
  bodies : Array[@source.ExternBody],
  what : String,
) -> ExternBody[Expr] raise EffektError {
  if bodies.length() != 1 {
    raise EffektError::Internal(
      "Externs should be resolved and desugared before core.Transformer (\{what}).",
    )
  }
  match bodies[0] {
    @source.StringExternBody(ff, body) =>
      StringExternBody(
        ff,
        body.map_raise(fn(a) raise EffektError { self.transform_as_expr(a) }),
      )
    @source.Unsupported(msg) => Unsupported(EffektError::Fatal(msg))
    @source.EffektExternBody(_, _) =>
      raise EffektError::Internal(
        "Externs should be resolved and desugared before core.Transformer (\{what}).",
      )
  }
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
/// `transform(tree: source.Stmt)`.
fn Transformer::transform_stmt(
  self : Transformer,
  tree : @source.Stmt,
) -> Stmt raise EffektError {
  match tree.kind {
    // { e; stmt } --> { stmt }
    @source.ExprStmt(e, rest) =>
      if self.is_pure_uid(e.uid) {
        self.transform_stmt(rest)
      } else {
        // { e; stmt } --> { val _ = e; stmt }
        let _ = self.transform_as_expr(e)
        self.transform_stmt(rest)
      }

    // return e
    @source.Return(e) => self.transform_as_stmt(e)

    // simply drop superfluous {}s
    @source.BlockStmt(b) => self.transform_stmt(b)
    @source.DefStmt(d, rest) =>
      match d.kind {
        @source.FunDef(_id, tps, vps, bps, _cpt, _ret, body) => {
          let tparams : Array[Sym] = []
          for p in tps {
            tparams.push(self.sym_of_id_def(p))
          }
          let cparams : Array[Sym] = []
          for b in bps {
            cparams.push(self.block_param_capture(b))
          }
          let vparams : Array[ValueParam] = []
          for p in vps {
            vparams.push(self.transform_value_param(p))
          }
          let bparams : Array[BlockParam] = []
          for p in bps {
            bparams.push(self.transform_block_param(p))
          }
          let body = self.insert_bindings(fn() raise EffektError {
            self.transform_stmt(body)
          })
          self.emit(
            BindingDef(
              self.sym_of_def(d),
              BlockLit(BlockLit::new(tparams, cparams, vparams, bparams, body)),
            ),
          )
          self.transform_stmt(rest)
        }
        @source.ValDef(_id, _tpe, binding) => {
          let transformed = self.insert_bindings(fn() raise EffektError {
            self.transform_stmt(binding)
          })
          self.emit(BindingVal(self.sym_of_def(d), transformed))
          self.transform_stmt(rest)
        }
        @source.DefDef(_id, _captures, _annot, binding) => {
          self.emit(
            BindingDef(self.sym_of_def(d), self.transform_as_block(binding)),
          )
          self.transform_stmt(rest)
        }
        @source.RegDef(_id, _tpe, _reg, binding) => {
          let sym = self.sym_of_def(d)
          let init = self.bind_stmt(self.transform_stmt(binding))
          self.emit(BindingAlloc(sym, init, self.reg_binder_region(sym)))
          self.transform_stmt(rest)
        }
        @source.VarDef(_id, _tpe, binding) => {
          let sym = self.sym_of_def(d)
          let init = self.bind_stmt(self.transform_stmt(binding))
          self.emit(BindingVar(sym, init, self.var_binder_capture(sym)))
          self.transform_stmt(rest)
        }
        @source.ExternDef(_, _, _, _, _, _, _) =>
          raise EffektError::Internal(
            "Extern definitions are only allowed on the toplevel.",
          )
        @source.ExternType(_, _, _) =>
          raise EffektError::Internal(
            "Extern types are only allowed on the toplevel.",
          )
        @source.ExternResource(_, _) =>
          raise EffektError::Internal(
            "Extern resources are only allowed on the toplevel.",
          )
        @source.ExternInterface(_, _, _) =>
          raise EffektError::Internal(
            "Extern interfaces are only allowed on the toplevel.",
          )
        @source.ExternInclude(_, _, _) =>
          raise EffektError::Internal(
            "Extern includes are only allowed on the toplevel.",
          )
        @source.InterfaceDef(_, _, _) =>
          raise EffektError::Internal(
            "Interface definitions are only allowed on the toplevel.",
          )
        @source.DataDef(_, _, _) =>
          raise EffektError::Internal(
            "Data definitions are only allowed on the toplevel.",
          )
        @source.RecordDef(_, _, _) =>
          raise EffektError::Internal(
            "Record definitions are only allowed on the toplevel.",
          )
        @source.NamespaceDef(_, _) =>
          raise EffektError::Internal(
            "Namespace definitions are only allowed on the toplevel.",
          )

        // For now we forget about all of the following definitions in core:
        @source.TypeDef(_, _, _) => self.transform_stmt(rest)
        @source.EffectDef(_, _, _) => self.transform_stmt(rest)
      }
  }
}

///|
fn Transformer::reg_binder_region(_self : Transformer, sym : Sym) -> Sym {
  match sym {
    RegBinder(r) => r.region
    _ => sym
  }
}

///|
fn Transformer::var_binder_capture(_self : Transformer, sym : Sym) -> Sym {
  match sym {
    VarBinder(v) => v.capture
    _ => sym
  }
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

///|
/// `transformUnbox`.
fn Transformer::transform_unbox(
  self : Transformer,
  tree : @source.Term,
) -> Block raise EffektError {
  match tree.kind {
    @source.Unbox(b) => Unbox(self.transform_as_expr(b))
    _ => Unbox(self.transform_as_expr(tree))
  }
}

///|
/// `transformBox`.
fn Transformer::transform_box(
  self : Transformer,
  tree : @source.Term,
) -> Expr raise EffektError {
  match tree.kind {
    @source.Box(_capt, block) =>
      Box(
        self.transform_as_block(tree),
        self.transform_captures(self.inferred_capture(block)),
      )
    _ =>
      Box(
        self.transform_as_block(tree),
        self.transform_captures(self.inferred_capture(tree)),
      )
  }
}

///|
/// Transforms the source to a function, expecting to be called using
/// `Stmt.App` or through an interface.
fn Transformer::transform_as_block(
  self : Transformer,
  tree : @source.Term,
) -> Block raise EffektError {
  match tree.kind {
    @source.Var(id) => {
      let sym = self.sym_of_ref(id)
      // an unannotated block variable is treated as a function
      match self.block_type_of_sym(sym) {
        FunctionType(_, _, _, _, _, _) => self.transform_as_control_block(tree)
        InterfaceType(_, _) => self.transform_as_object(tree)
      }
    }
    @source.BlockLiteral(_, _, _, _) => self.transform_as_control_block(tree)
    @source.New(_) => self.transform_as_object(tree)
    _ => self.transform_unbox(tree)
  }
}

///|
/// Transforms the source to an interface block.
fn Transformer::transform_as_object(
  self : Transformer,
  tree : @source.Term,
) -> Block raise EffektError {
  match tree.kind {
    @source.Var(id) => BlockVar(self.block_var(self.sym_of_ref(id)))
    @source.BlockLiteral(_, _, _, _) =>
      raise EffektError::Internal(
        "Using a block literal where an object was expected.",
      )
    @source.New(implementation) =>
      New(self.transform_implementation(implementation, None))
    _ => self.transform_unbox(tree)
  }
}

///|
/// Transforms the source to a function block that expects to be called using
/// `Stmt.App`.
fn Transformer::transform_as_control_block(
  self : Transformer,
  tree : @source.Term,
) -> Block raise EffektError {
  match tree.kind {
    @source.Var(id) => {
      let sym = self.sym_of_ref(id)
      let tpe = self.block_type_of_sym(sym)
      match tpe {
        FunctionType(tparams, _cparams, vparamtps, bparamtps, restpe, _effects) => {
          // if this block argument expects to be called using PureApp or
          // ImpureApp, make sure it is by wrapping it in a BlockLit.
          let targs : Array[ValueType] = tparams.map(t => ValueTypeRef(t))
          let vparams : Array[ValueParam] = []
          for t in vparamtps {
            vparams.push(
              ValueParam::new(
                Sym::tmp_value("valueParam"),
                self.transform_value_type(t),
              ),
            )
          }
          let vargs = vparams.map(p => ValueVar(p.id, p.tpe))

          // [[ f ]] = { (x) => f(x) }
          let eta_expand_pure = fn(f : Sym) raise EffektError {
            BlockLit(
              BlockLit::new(
                tparams,
                [],
                vparams,
                [],
                Return(PureApp(self.block_var(f), targs, vargs)),
              ),
            )
          }

          // [[ f ]] = { [A](x) => make f[A](x) }
          let eta_expand_constructor = fn(
            f : Sym,
            data : Sym,
          ) raise EffektError {
            BlockLit(
              BlockLit::new(
                tparams,
                [],
                vparams,
                [],
                Return(Make(data, f, targs, vargs)),
              ),
            )
          }

          // [[ f ]] = { (x){g} => let r = f(x){g}; return r }
          let eta_expand_direct = fn(f : Sym) raise EffektError {
            let bparams : Array[BlockParam] = []
            for t in bparamtps {
              let id = Sym::tmp_block("etaParam")
              bparams.push(
                BlockParam::new(
                  id,
                  self.transform_block_type(t),
                  CaptureSetOf([id]),
                ),
              )
            }
            let bargs = bparams.map(b => {
              BlockVar(BlockVar::new(b.id, b.tpe, b.capt))
            })
            let result_id = Sym::tmp_value("etaBinding")
            let callee = self.block_var(f)
            let body = ImpureApp(
              result_id,
              callee,
              targs,
              vargs,
              bargs,
              Return(ValueVar(result_id, self.transform_value_type(restpe))),
            )
            BlockLit(
              BlockLit::new(
                tparams,
                bparams.map(b => b.id),
                vparams,
                bparams,
                body,
              ),
            )
          }

          if sym.is_value_symbol() {
            self.transform_unbox(tree)
          } else {
            match sym {
              Constructor(c) => eta_expand_constructor(sym, c.tpe)
              ExternFunction(_) =>
                match calling_convention(sym) {
                  ConvPure => eta_expand_pure(sym)
                  ConvDirect => eta_expand_direct(sym)
                  ConvControl => BlockVar(self.block_var(sym))
                }
              _ => BlockVar(self.block_var(sym))
            }
          }
        }
        InterfaceType(_, _) =>
          raise EffektError::Internal("Expected a function but got an object.")
      }
    }
    @source.BlockLiteral(tps, vps, bps, body) => {
      let tparams : Array[Sym] = []
      for t in tps {
        tparams.push(self.sym_of_id_def(t))
      }
      let cparams : Array[Sym] = []
      for b in bps {
        cparams.push(self.block_param_capture(b))
      }
      let vparams : Array[ValueParam] = []
      for p in vps {
        vparams.push(self.transform_value_param(p))
      }
      let bparams : Array[BlockParam] = []
      for p in bps {
        bparams.push(self.transform_block_param(p))
      }
      let body = self.insert_bindings(fn() raise EffektError {
        self.transform_stmt(body)
      })
      BlockLit(BlockLit::new(tparams, cparams, vparams, bparams, body))
    }
    @source.New(_) =>
      raise EffektError::Internal(
        "Expected a function but got an object instantiation.",
      )
    _ => self.transform_unbox(tree)
  }
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

///|
/// `transformAsExpr`.
fn Transformer::transform_as_expr(
  self : Transformer,
  tree : @source.Term,
) -> Expr raise EffektError {
  match tree.kind {
    @source.Var(id) => {
      let sym = self.sym_of_ref(id)
      if sym.is_ref_binder() {
        let tpe = self.state_type_of(sym)
        let state_id = Sym::tmp_value("s")
        // emits `let s = !ref; return s`
        self.emit(
          BindingGet(
            state_id,
            self.transform_value_type(tpe),
            sym,
            self.transform_captures(self.capture_of_sym(sym)),
          ),
        )
        ValueVar(state_id, self.transform_value_type(tpe))
      } else if sym.is_value_symbol() {
        self.value_var(sym)
      } else {
        self.transform_box(tree)
      }
    }
    @source.Literal(value, tpe) =>
      Literal(value, self.transform_value_type(tpe))
    @source.Box(_capt, block) => self.transform_box(block)
    @source.New(_) => self.transform_box(tree)
    @source.Unbox(_) => self.transform_box(tree)
    @source.BlockLiteral(_, _, _, _) => self.transform_box(tree)
    @source.Assign(id, expr) => {
      let sym = self.sym_of_ref(id)
      // emits `ref := value; return ()`
      self.emit(
        BindingPut(
          sym,
          self.transform_captures(self.capture_of_sym(sym)),
          self.transform_as_expr(expr),
        ),
      )
      Literal(LUnit, t_unit())
    }
    @source.Do(_, _, _, _) =>
      raise EffektError::Internal(
        "Should have been translated away (to explicit selection) by capability passing.",
      )
    @source.If(_, _, _)
    | @source.While(_, _, _)
    | @source.TryHandle(_, _)
    | @source.Hole(_, _)
    | @source.MethodCall(_, _, _, _, _)
    | @source.Region(_, _)
    | @source.Match(_, _, _)
    | @source.Select(_, _)
    | @source.Call(_, _, _, _) => {
      let stmt = self.transform_as_stmt(tree)
      match stmt {
        Return(expr) => expr
        _ => self.bind_stmt(stmt)
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Statements from terms
// ---------------------------------------------------------------------------

///|
/// If the guard list is exactly one boolean guard, return its condition.
fn single_boolean_guard(guards : Array[@source.MatchGuard]) -> @source.Term? {
  if guards.length() != 1 {
    return None
  }
  match guards[0].kind {
    @source.BooleanGuard(cond) => Some(cond)
    @source.PatternGuard(_, _) => None
  }
}

///|
/// `transformAsStmt`.
fn Transformer::transform_as_stmt(
  self : Transformer,
  tree : @source.Term,
) -> Stmt raise EffektError {
  match tree.kind {
    @source.If(guards, thn, els) =>
      match single_boolean_guard(guards) {
        Some(cond) => {
          let c = self.transform_as_expr(cond)
          let then_stmt = self.insert_bindings(fn() raise EffektError {
            self.transform_stmt(thn)
          })
          let else_stmt = self.insert_bindings(fn() raise EffektError {
            self.transform_stmt(els)
          })
          If(c, then_stmt, else_stmt)
        }
        None => {
          let thn_clause = self.preprocess_patterns(
            "thn",
            [],
            guards,
            self.insert_bindings(fn() raise EffektError {
              self.transform_stmt(thn)
            }),
          )
          let els_clause = self.preprocess_patterns(
            "els",
            [],
            [],
            self.insert_bindings(fn() raise EffektError {
              self.transform_stmt(els)
            }),
          )
          let tpe = self.transform_value_type(self.inferred_type_of(tree))
          pm_compile([thn_clause, els_clause], tpe)
        }
      }

    // [[ while(cond) { body } ]] =
    //   def loop$ = if ([[cond]]) { [[ body ]]; loop$() } else { return () }
    //   loop$()
    @source.While(guards, body, default) => {
      let loop_name = Sym::tmp_block("while")
      let loop_type : BlockType = FunctionType(
        [],
        [],
        [],
        [],
        t_unit(),
        Effects::empty(),
      )
      let loop_capt = self.transform_captures(self.capture_of_uid(body.uid))
      let loop_call = App(
        BlockVar(BlockVar::new(loop_name, loop_type, loop_capt)),
        [],
        [],
        [],
      )

      let then_branch = Val(
        Sym::tmp_value("while_thn"),
        self.insert_bindings(fn() raise EffektError {
          self.transform_stmt(body)
        }),
        loop_call,
      )
      let else_branch = self.insert_bindings(fn() raise EffektError {
        match default {
          Some(d) => self.transform_stmt(d)
          None => Return(Literal(LUnit, t_unit()))
        }
      })

      let loop_body = match single_boolean_guard(guards) {
        Some(cond) =>
          self.insert_bindings(fn() raise EffektError {
            If(self.transform_as_expr(cond), then_branch, else_branch)
          })
        None =>
          self.insert_bindings(fn() raise EffektError {
            let then_clause = self.preprocess_patterns(
              "guard_thn",
              [],
              guards,
              then_branch,
            )
            let else_clause = self.preprocess_patterns(
              "guard_els",
              [],
              [],
              else_branch,
            )
            pm_compile([then_clause, else_clause], unknown_value_type())
          })
      }

      let _ = self.bind_block(
        loop_name,
        BlockLit(BlockLit::new([], [], [], [], loop_body)),
      )
      loop_call
    }

    // [[ sc.field ]] = val x = sc match { tag: { (_, _, x, _) => return x } }; ...
    @source.Select(receiver, selector) => {
      let field = self.sym_of_ref(selector)
      let constructor = match field {
        Field(f) => f.constructor
        _ => raise EffektError::Internal("Selection should refer to a field.")
      }
      let universals = type_constructor_tparams(
        match constructor {
          Constructor(c) => c.tpe
          _ => constructor
        },
      )
      let scrutinee_type_args = match self.inferred_type_of(receiver) {
        ValueTypeApp(_, args) => args
        _ =>
          raise EffektError::Internal(
            "Should not happen: selection from a non ValueTypeApp.",
          )
      }
      let vsubst : Map[Int32, ValueType] = Map([])
      for i = 0; i < universals.length(); i = i + 1 {
        if i < scrutinee_type_args.length() {
          vsubst.set(universals[i].uid(), scrutinee_type_args[i])
        }
      }
      let selected = Sym::value_param(Name::local("x"), None, tree.span)
      let tpe = self.transform_value_type(self.inferred_type_of(tree))
      let params : Array[ValueParam] = []
      for f in constructor_fields(constructor) {
        let ftpe = self.transform_value_type(
          substitute_value_type_with(field_return_type(f), vsubst, Map([])),
        )
        if f.uid() == field.uid() {
          params.push(ValueParam::new(selected, ftpe))
        } else {
          params.push(
            ValueParam::new(
              Sym::value_param(Name::local("_"), Some(ftpe), tree.span),
              ftpe,
            ),
          )
        }
      }
      let clause = Clause::new(
        constructor,
        BlockLit::new([], [], params, [], Return(ValueVar(selected, tpe))),
      )
      Match(self.transform_as_expr(receiver), tpe, [clause], None)
    }

    // Empty match (matching on Nothing)
    @source.Match(scs, cs, None) =>
      if scs.length() == 1 && cs.length() == 0 {
        let scrutinee = self.bind_expr(self.transform_as_expr(scs[0]))
        let tpe = self.transform_value_type(self.inferred_type_of(tree))
        Match(scrutinee, tpe, [], None)
      } else {
        self.transform_match(tree, scs, cs, None)
      }
    @source.Match(scs, cs, default) =>
      self.transform_match(tree, scs, cs, default)
    @source.TryHandle(prog, handlers) => {
      let answer_type = self.transform_value_type(self.type_of_uid(prog.uid))
      // create a fresh prompt, a variable referring to it, and a parameter
      // binding it
      let prompt_id = Sym::tmp_block("p")
      let prompt_capt = Sym::capture_param(Name::local("pCapt"))
      let prompt_tpe = self.prompt_type(answer_type)
      let prompt_var = BlockVar::new(
        prompt_id,
        prompt_tpe,
        CaptureSetOf([prompt_capt]),
      )
      let prompt_param = BlockParam::new(
        prompt_id,
        prompt_tpe,
        CaptureSetOf([prompt_capt]),
      )

      let body = self.insert_bindings(fn() raise EffektError {
        for h in handlers {
          match h.capability {
            Some(cap) => {
              let id = self.sym_of_id_def(cap.id)
              self.emit(
                BindingDef(
                  id,
                  New(
                    self.transform_implementation(
                      h.implementation,
                      Some(prompt_var),
                    ),
                  ),
                ),
              )
            }
            None => ()
          }
        }
        self.transform_stmt(prog)
      })
      Reset(BlockLit::new([], [prompt_capt], [], [prompt_param], body))
    }
    @source.Region(name, body) => {
      let region = self.sym_of_id_def(name)
      let cap = self.region_capture(region)
      let tpe = self.block_type_of_sym(region)
      let param = BlockParam::new(
        region,
        self.transform_block_type(tpe),
        CaptureSetOf([cap]),
      )
      let body = self.insert_bindings(fn() raise EffektError {
        self.transform_stmt(body)
      })
      Region(BlockLit::new([], [cap], [], [param], body))
    }

    // methods are dynamically dispatched, so we have to assume they are
    // `control`, hence no PureApp.
    @source.MethodCall(receiver, id, _targs, vargs, bargs) => {
      let rec = self.transform_as_object(receiver)
      let type_args = self
        .type_arguments_of(tree)
        .map(t => self.transform_value_type(t))
      let value_args : Array[Expr] = []
      for a in vargs {
        value_args.push(self.transform_as_expr(a.value))
      }
      let block_args : Array[Block] = []
      for b in bargs {
        block_args.push(self.transform_as_block(b))
      }
      let receiver_type = self.ctx
        .block_type_of(receiver.uid)
        .unwrap_or(unknown_block_type())
      let operation = self.sym_of_ref(id)
      let op_type = self.operation_at_callsite(receiver_type, operation)
      // Do not pass type arguments for the type constructor of the receiver.
      let remaining = array_drop(
        type_args,
        type_constructor_tparams(operation_interface(operation)).length(),
      )
      Invoke(
        rec,
        operation,
        self.transform_block_type(op_type),
        remaining,
        value_args,
        block_args,
      )
    }
    @source.Hole(_, _) =>
      Hole(self.transform_value_type(self.inferred_type_of(tree)), tree.span)
    @source.Call(target, _targs, vargs, bargs) =>
      match target {
        @source.IdTarget(id) =>
          self.make_function_call(tree, self.sym_of_ref(id), vargs, bargs)
        @source.ExprTarget(t) =>
          match t.kind {
            @source.Unbox(expr) => {
              let (fun_tpe, capture) = match self.inferred_type_of(expr) {
                BoxedType(s, c) => (s, c)
                _ =>
                  raise EffektError::Internal(
                    "Should be a boxed function type with a known capture set.",
                  )
              }
              let _ = fun_tpe
              let _ = capture
              let e = self.transform_as_expr(expr)
              let type_args = self
                .type_arguments_of(tree)
                .map(t => self.transform_value_type(t))
              let value_args : Array[Expr] = []
              for a in vargs {
                value_args.push(self.transform_as_expr(a.value))
              }
              let block_args : Array[Block] = []
              for b in bargs {
                block_args.push(self.transform_as_block(b))
              }
              App(Unbox(e), type_args, value_args, block_args)
            }
            _ =>
              raise EffektError::Internal(
                "Should not happen. Unbox should have been inferred.",
              )
          }
      }
    @source.Var(_)
    | @source.Literal(_, _)
    | @source.Box(_, _)
    | @source.Unbox(_)
    | @source.New(_)
    | @source.BlockLiteral(_, _, _, _)
    | @source.Assign(_, _)
    | @source.Do(_, _, _, _) => Return(self.transform_as_expr(tree))
  }
}

///|
fn Transformer::transform_match(
  self : Transformer,
  tree : @source.Term,
  scs : Array[@source.Term],
  cs : Array[@source.MatchClause],
  default : @source.Stmt?,
) -> Stmt raise EffektError {
  // (1) Bind scrutinee and all clauses so we do not have to deal with sharing
  //     on demand.
  let scrutinees : Array[Expr] = []
  for sc in scs {
    scrutinees.push(self.bind_expr(self.transform_as_expr(sc)))
  }
  let clauses : Array[PMClause] = []
  for i = 0; i < cs.length(); i = i + 1 {
    clauses.push(self.preprocess("k\{i}", scrutinees, cs[i]))
  }
  match default {
    Some(stmt) =>
      clauses.push(
        self.preprocess_patterns(
          "k_els",
          [],
          [],
          self.insert_bindings(fn() raise EffektError {
            self.transform_stmt(stmt)
          }),
        ),
      )
    None => ()
  }
  let tpe = self.transform_value_type(self.inferred_type_of(tree))
  pm_compile(clauses, tpe)
}

///|
fn operation_interface(op : Sym) -> Sym {
  match op {
    Operation(o) => o.interface
    _ => op
  }
}

///|
fn constructor_fields(sym : Sym) -> Array[Sym] {
  match sym {
    Constructor(c) => c.fields
    _ => []
  }
}

///|
/// `makeFunctionCall`: translates a call to a named function.
fn Transformer::make_function_call(
  self : Transformer,
  call : @source.Term,
  sym : Sym,
  vargs : Array[@source.ValueArg],
  bargs : Array[@source.Term],
) -> Stmt raise EffektError {
  let targs = self
    .type_arguments_of(call)
    .map(t => self.transform_value_type(t))
  let value_args : Array[Expr] = []
  for a in vargs {
    value_args.push(self.transform_as_expr(a.value))
  }
  let block_args : Array[Block] = []
  for b in bargs {
    block_args.push(self.transform_as_block(b))
  }

  match sym {
    ExternFunction(_) =>
      match calling_convention(sym) {
        ConvPure => Return(PureApp(self.block_var(sym), targs, value_args))
        ConvDirect =>
          Return(
            self.bind_impure_app(
              self.block_var(sym),
              targs,
              value_args,
              block_args,
            ),
          )
        ConvControl =>
          App(BlockVar(self.block_var(sym)), targs, value_args, block_args)
      }
    Constructor(c) => {
      if bargs.length() > 0 {
        self.ctx.abort(call.span, "Constructors cannot take block arguments.")
      }
      let universals = type_constructor_tparams(c.tpe).length()
      let existentials = array_drop(targs, universals)
      Return(Make(c.tpe, sym, existentials, value_args))
    }
    Operation(_) =>
      raise EffektError::Internal(
        "Operations should have been translated to a method call.",
      )
    Field(_) =>
      raise EffektError::Internal(
        "Fields should have been translated to a select.",
      )
    _ =>
      if sym.is_block_symbol() {
        App(BlockVar(self.block_var(sym)), targs, value_args, block_args)
      } else {
        App(Unbox(self.value_var(sym)), targs, value_args, block_args)
      }
  }
}

// ---------------------------------------------------------------------------
// Implementations
// ---------------------------------------------------------------------------

///|
/// Establishes a canonical ordering of methods by using the order in which they
/// are declared in the signature (like with handlers).
fn Transformer::transform_implementation(
  self : Transformer,
  implementation : @source.Implementation,
  prompt : BlockVar?,
) -> Implementation raise EffektError {
  let members : Map[Int32, @source.OpClause] = Map([])
  for cl in implementation.clauses {
    let op = self.sym_of_ref(cl.id)
    members.set(op.uid(), cl)
  }

  let interface_tpe = match self.ctx.block_type_of(implementation.uid) {
    Some(t) => t
    None =>
      match implementation.interface.kind {
        @source.TypeRef(id, _) =>
          match self.ctx.symbol_of(id.uid) {
            Some(s) => InterfaceType(s, [])
            None =>
              raise EffektError::Internal(
                "Implementation should have an interface type.",
              )
          }
        _ =>
          raise EffektError::Internal(
            "Implementation should have an interface type.",
          )
      }
  }

  let sig = match interface_tpe {
    InterfaceType(i, _) => i
    _ => raise EffektError::Internal("Should be an interface type.")
  }

  let core_type : BlockType = match self.transform_block_type(interface_tpe) {
    InterfaceType(i, args) => InterfaceType(i, args)
    _ => raise EffektError::Internal("Should be an interface type.")
  }

  let operations : Array[Operation] = []
  for op_sym in interface_operations(sig) {
    match members.get(op_sym.uid()) {
      Some(cl) => operations.push(self.transform_op_clause(cl, prompt))
      None =>
        raise EffektError::Internal(
          "Missing implementation of operation \{op_sym.name().name}.",
        )
    }
  }
  Implementation::new(core_type, operations)
}

///|
/// Transforms one operation clause of a handler.
fn Transformer::transform_op_clause(
  self : Transformer,
  cl : @source.OpClause,
  prompt : BlockVar?,
) -> Operation raise EffektError {
  let op = self.sym_of_ref(cl.id)
  let vps : Array[ValueParam] = []
  for p in cl.vparams {
    vps.push(self.transform_value_param(p))
  }
  let tps : Array[Sym] = []
  for p in cl.tparams {
    tps.push(self.sym_of_id_def(p))
  }

  match prompt {
    Some(prompt) => {
      let resume_symbol = self.sym_of_id_def(cl.resume)
      match self.block_type_of_sym(resume_symbol) {
        // uni-directional
        // ---------------
        // [[ def op(x) = ... resume123(...) ... ]]
        //   =
        // def op(x) = shift(p) { k =>
        //   def resume123(y) = resume(k) { return y };
        //   ... resume123(...) ...
        // }
        FunctionType(_, _, [result], _, answer, _) => {
          let result_tpe = self.transform_value_type(result)
          let answer_tpe = self.transform_value_type(answer)
          // (1) bind the continuation (k) itself
          let resume_capture = self.transform_captures(
            self.capture_of_sym(resume_symbol),
          )
          let resume_id = Sym::tmp_block("k")
          // upstream types the continuation as `Type.TResume(result, answer)`,
          // which the port's type language does not have; `(result) => answer`
          // carries the same information.
          let resume_type : BlockType = FunctionType(
            [],
            [],
            [result_tpe],
            [],
            answer_tpe,
            Effects::empty(),
          )
          let resume_param = BlockParam::new(
            resume_id, resume_type, resume_capture,
          )
          let resume_var = BlockVar::new(resume_id, resume_type, resume_capture)
          // (2) eta-expand and bind continuation as a function
          let resume_arg_id = Sym::tmp_value("a")
          let resume_arg_param = ValueParam::new(resume_arg_id, result_tpe)
          let resume_fun = BlockLit::new(
            [],
            [],
            [resume_arg_param],
            [],
            Resume(resume_var, Return(ValueVar(resume_arg_id, result_tpe))),
          )
          Operation::new(
            op,
            tps,
            [],
            vps,
            [],
            Shift(
              prompt,
              resume_param,
              Def(
                resume_symbol,
                BlockLit(resume_fun),
                self.insert_bindings(fn() raise EffektError {
                  self.transform_stmt(cl.body)
                }),
              ),
            ),
          )
        }

        // bi-directional
        // --------------
        // [[ def op(x) = ... resume123 { {f} => ... } ... ]]
        //   =
        // def op(x) {g} = shift(p) { k =>
        //   def resume123 {h} = resume(k) { h {g} }
        //   ... resume123 { {f} => ... } ...
        // }
        FunctionType(_, _, _, [arg_tpe], answer, _) => {
          let result_tpe = match arg_tpe {
            FunctionType(_, _, _, _, result, _) =>
              self.transform_value_type(result)
            _ => unknown_value_type()
          }
          let answer_tpe = self.transform_value_type(answer)
          let arg_tpe_core = self.transform_block_type(arg_tpe)
          let (cps, bps) : (Array[Captures], Array[BlockType]) = match
            arg_tpe_core {
            FunctionType(_, cps, _, bps, _, _) => (cps, bps)
            _ => ([], [])
          }
          // (0) compute the block parameters from the type of the continuation
          let bparams : Array[BlockParam] = []
          for i = 0; i < cps.length(); i = i + 1 {
            let tpe = if i < bps.length() {
              bps[i]
            } else {
              unknown_block_type()
            }
            bparams.push(
              BlockParam::new(
                Sym::tmp_block("g"),
                tpe,
                self.transform_captures(cps[i]),
              ),
            )
          }
          let bvars = bparams.map(b => {
            BlockVar(BlockVar::new(b.id, b.tpe, b.capt))
          })

          // (1) bind the continuation (k) itself
          let resume_capture = self.transform_captures(
            self.capture_of_sym(resume_symbol),
          )
          let resume_id = Sym::tmp_block("k")
          let resume_type : BlockType = FunctionType(
            [],
            [],
            [result_tpe],
            [],
            answer_tpe,
            Effects::empty(),
          )
          let resume_param = BlockParam::new(
            resume_id, resume_type, resume_capture,
          )
          let resume_var = BlockVar::new(resume_id, resume_type, resume_capture)

          // (2) eta-expand and bind continuation as a function
          let resume_arg_id = Sym::tmp_block("h")
          let resume_arg_capture = Sym::capture_param(Name::local("h"))
          let resume_arg_param = BlockParam::new(
            resume_arg_id,
            arg_tpe_core,
            CaptureSetOf([resume_arg_capture]),
          )
          let resume_arg_var = BlockVar::new(
            resume_arg_id,
            arg_tpe_core,
            CaptureSetOf([resume_arg_capture]),
          )
          let resume_fun = BlockLit::new(
            [],
            [resume_arg_capture],
            [],
            [resume_arg_param],
            Resume(resume_var, App(BlockVar(resume_arg_var), [], [], bvars)),
          )

          Operation::new(
            op,
            tps,
            cps.map(c => capture_of_captures(self.transform_captures(c))),
            vps,
            bparams,
            Shift(
              prompt,
              resume_param,
              Def(
                resume_symbol,
                BlockLit(resume_fun),
                self.insert_bindings(fn() raise EffektError {
                  self.transform_stmt(cl.body)
                }),
              ),
            ),
          )
        }
        other =>
          raise EffektError::Internal(
            "The type of the resumption should be a function type, but is \{show_core_block_type(other)}.",
          )
      }
    }
    None => {
      let bps : Array[BlockParam] = []
      for p in cl.bparams {
        bps.push(self.transform_block_param(p))
      }
      let cps : Array[Sym] = []
      for b in cl.bparams {
        cps.push(
          capture_of_captures(
            self.transform_captures(
              self.capture_of_sym(self.sym_of_id_def(b.id)),
            ),
          ),
        )
      }
      Operation::new(
        op,
        tps,
        cps,
        vps,
        bps,
        self.insert_bindings(fn() raise EffektError {
          self.transform_stmt(cl.body)
        }),
      )
    }
  }
}

// ---------------------------------------------------------------------------
// Signatures
// ---------------------------------------------------------------------------

///|
/// Computes the block type of the selected symbol.
///
/// For instance, receiver can be `State[Int]`, the interface could be the
/// symbol of `State` and the member could be `get`. If `member` is an
/// operation, the type arguments of the receiver are substituted for the
/// leading type parameters, while the remaining type parameters are kept.
fn Transformer::operation_at_callsite(
  self : Transformer,
  receiver : BlockType,
  member : Sym,
) -> BlockType raise EffektError {
  match receiver {
    InterfaceType(_i, targs) =>
      match member {
        Operation(o) => {
          let vsubst : Map[Int32, ValueType] = Map([])
          for idx = 0; idx < o.tparams.length(); idx = idx + 1 {
            if idx < targs.length() {
              vsubst.set(o.tparams[idx].uid(), targs[idx])
            }
          }
          let remaining = array_drop(o.tparams, targs.length())
          let cparams = o.bparams.map(b => self.capture_of_sym(b)) +
            @symbols.canonical_order(o.effects.to_list()).map(t => {
              CaptureSetOf([capture_param_of_type(t)])
            })
          let vparam_tpes = o.vparams.map(p => {
            substitute_value_type_with(
              self.value_type_of_sym(p),
              vsubst,
              Map([]),
            )
          })
          let bparam_tpes = o.bparams.map(b => {
            substitute_block_type_with(
              self.block_type_of_sym(b),
              vsubst,
              Map([]),
            )
          })
          FunctionType(
            remaining,
            cparams,
            vparam_tpes,
            bparam_tpes,
            substitute_value_type_with(o.result_type, vsubst, Map([])),
            Effects::empty(),
          )
        }
        ExternInterface(_) =>
          raise EffektError::Internal("Cannot select from an extern interface.")
        _ => raise EffektError::Internal("Expected an operation.")
      }
    _ => raise EffektError::Internal("Cannot select from a non-interface type.")
  }
}

///|
/// `operationAtDeclaration`: the block type of an operation as declared in an
/// interface.
fn Transformer::operation_at_declaration(
  self : Transformer,
  tparams_interface : Array[Sym],
  op : Sym,
) -> BlockType raise EffektError {
  match op {
    Operation(o) => {
      // like in asSeenFrom we need to make up cparams, they cannot occur free
      // in the result type
      let capabilities = @symbols.canonical_order(o.effects.to_list())
      let tparams = array_drop(o.tparams, tparams_interface.length())
      let bparams_blocks = o.bparams.map(b => {
        self.transform_block_type(self.block_type_of_sym(b))
      })
      let bparams_capabilities = capabilities.map(t => {
        self.transform_block_type(t)
      })
      let vparams = o.vparams.map(p => {
        self.transform_value_type(self.value_type_of_sym(p))
      })
      let cparams = o.bparams.map(b => self.capture_of_sym(b)) +
        capabilities.map(t => CaptureSetOf([capture_param_of_type(t)]))
      FunctionType(
        tparams,
        cparams,
        vparams,
        bparams_blocks + bparams_capabilities,
        self.transform_value_type(o.result_type),
        Effects::empty(),
      )
    }
    _ => raise EffektError::Internal("Expected an operation.")
  }
}

///|
/// The capture parameter standing in for an effect in a block type.
fn capture_param_of_type(t : BlockType) -> Sym {
  match t {
    InterfaceType(c, _) => Sym::capture_param(c.name())
    FunctionType(_, _, _, _, _, _) => Sym::capture_param(Name::anon())
  }
}

///|
/// The single capture parameter underlying a capture set. Core's
/// `BlockType.Function` stores capture *symbols* upstream, while the port's
/// type language stores (singleton) capture sets.
fn capture_of_captures(c : Captures) -> Sym {
  match c {
    CaptureSetOf(cs) =>
      if cs.length() > 0 {
        cs[0]
      } else {
        Sym::capture_param(Name::anon())
      }
    CaptVar(s) => s
  }
}

// ---------------------------------------------------------------------------
// Pattern matching
// ---------------------------------------------------------------------------

///|
/// A scrutinee together with the pattern that is matched against it.
pub(all) struct ScrutineePattern {
  scrutinee : Expr
  pattern : @source.MatchPattern
}

///|
/// Prepares a source match clause for the pattern matching compiler.
fn Transformer::preprocess(
  self : Transformer,
  label : String,
  scs : Array[Expr],
  clause : @source.MatchClause,
) -> PMClause raise EffektError {
  let patterns : Array[ScrutineePattern] = []
  match clause.pattern.kind {
    @source.MultiPattern(ps) =>
      for i = 0; i < scs.length() && i < ps.length(); i = i + 1 {
        patterns.push({ scrutinee: scs[i], pattern: ps[i], })
      }
    _ =>
      if scs.length() == 1 {
        patterns.push({ scrutinee: scs[0], pattern: clause.pattern, })
      } else {
        self.ctx.abort(clause.span, "Malformed multi-match")
      }
  }
  let body = self.insert_bindings(fn() raise EffektError {
    self.transform_stmt(clause.body)
  })
  self.preprocess_patterns(label, patterns, clause.guards, body)
}

///|
fn Transformer::preprocess_patterns(
  self : Transformer,
  label : String,
  patterns : Array[ScrutineePattern],
  guards : Array[@source.MatchGuard],
  body : Stmt,
) -> PMClause raise EffektError {
  // create joinpoint
  let tparams : Array[Sym] = []
  let params : Array[ValueParam] = []
  for p in patterns {
    for vp in self.bound_in_pattern(p.pattern) {
      params.push(vp)
    }
  }
  for g in guards {
    match g.kind {
      @source.PatternGuard(_, pattern) =>
        for vp in self.bound_in_pattern(pattern) {
          params.push(vp)
        }
      @source.BooleanGuard(_) => ()
    }
  }
  let joinpoint = self.bind_block(
    Sym::tmp_block(label),
    BlockLit(BlockLit::new(tparams, [], params, [], body)),
  )

  let transformed_patterns : Map[Int32, PMVarPattern] = Map([])
  for p in patterns {
    let sc = as_pm_var(p.scrutinee)
    transformed_patterns.set(
      sc.id.uid(),
      PMVarPattern::new(sc, self.transform_pattern(p.pattern)),
    )
  }

  let conditions : Array[PMCondition] = []
  if transformed_patterns.length() > 0 {
    conditions.push(PMPatterns(transformed_patterns))
  }
  for g in guards {
    for c in self.transform_guard(g) {
      conditions.push(c)
    }
  }

  let targs : Array[ValueType] = tparams.map(t => ValueTypeRef(t))
  let args = params.map(p => PMVar::new(p.id, p.tpe))
  PMClause::new(conditions, joinpoint, targs, args)
}

///|
fn as_pm_var(e : Expr) -> PMVar raise EffektError {
  match e {
    ValueVar(id, tpe) => PMVar::new(id, tpe)
    _ => raise EffektError::Internal("Expected a value variable.")
  }
}

///|
/// The value parameters bound by a pattern.
fn Transformer::bound_in_pattern(
  self : Transformer,
  p : @source.MatchPattern,
) -> Array[ValueParam] {
  match p.kind {
    @source.AnyPattern(id) => {
      let sym = match self.ctx.symbol_of(id.uid) {
        Some(s) => s
        None => Sym::value_param(Name::local(id.name), None, id.span)
      }
      [
        ValueParam::new(
          sym,
          self.transform_value_type(self.value_type_of_sym(sym)),
        ),
      ]
    }
    @source.TagPattern(_id, patterns) => {
      let out : Array[ValueParam] = []
      for inner in patterns {
        for vp in self.bound_in_pattern(inner) {
          out.push(vp)
        }
      }
      out
    }
    @source.MultiPattern(patterns) => {
      let out : Array[ValueParam] = []
      for inner in patterns {
        for vp in self.bound_in_pattern(inner) {
          out.push(vp)
        }
      }
      out
    }
    @source.LiteralPattern(_, _) => []
    @source.IgnorePattern => []
  }
}

///|
fn Transformer::transform_pattern(
  self : Transformer,
  p : @source.MatchPattern,
) -> PMPattern raise EffektError {
  match p.kind {
    @source.AnyPattern(id) => PMAny(self.sym_of_id_def(id))
    @source.TagPattern(id, patterns) => {
      let tag = self.sym_of_ref(id)
      let all_variants = match tag {
        Constructor(c) =>
          match c.tpe {
            DataType(dt) => dt.constructors
            Record(r) => [r.constructor]
            _ =>
              raise EffektError::Internal(
                "Constructors can only be part of data types or records.",
              )
          }
        _ => raise EffektError::Internal("Can only use constructors as tags.")
      }
      // NOTE: upstream additionally passes the existential type parameters
      // annotated on the pattern (`Annotations.TypeParameters`), which the
      // source `Context` of this port does not carry.
      let sub : Array[PMSubPattern] = []
      for inner in patterns {
        sub.push(
          PMSubPattern::new(
            self.transform_pattern(inner),
            self.transform_value_type(self.inferred_type_of_pattern(inner)),
          ),
        )
      }
      PMTag(tag, [], all_variants, sub)
    }
    @source.IgnorePattern => PMIgnore
    @source.LiteralPattern(value, tpe) =>
      PMLiteral(value, self.transform_value_type(tpe), self.equals_for(tpe))
    @source.MultiPattern(_) =>
      raise EffektError::Internal("Multi-pattern should have been split.")
  }
}

///|
fn Transformer::inferred_type_of_pattern(
  self : Transformer,
  p : @source.MatchPattern,
) -> ValueType {
  self.ctx.value_type_of(p.uid).unwrap_or(unknown_value_type())
}

///|
/// The equality function for a literal pattern of the given type.
fn Transformer::equals_for(
  self : Transformer,
  tpe : ValueType,
) -> PMEquals? raise EffektError {
  match self.eq_function {
    None => None
    Some(sym) =>
      match sym.as_callable() {
        // generic version: pass the type of the literal
        Some(c) =>
          if c.tparams.length() == 1 {
            Some(PMEquals::new(sym, [self.transform_value_type(tpe)]))
          } else {
            Some(PMEquals::new(sym, []))
          }
        None => None
      }
  }
}

///|
fn Transformer::transform_guard(
  self : Transformer,
  g : @source.MatchGuard,
) -> Array[PMCondition] raise EffektError {
  let (cond, bindings) = self.with_bindings(fn() raise EffektError {
    match g.kind {
      @source.BooleanGuard(condition) =>
        PMPredicate(self.transform_as_expr(condition))
      @source.PatternGuard(scrutinee, pattern) => {
        let x = as_pm_var(self.bind_expr(self.transform_as_expr(scrutinee)))
        let m : Map[Int32, PMVarPattern] = Map([])
        m.set(x.id.uid(), PMVarPattern::new(x, self.transform_pattern(pattern)))
        PMPatterns(m)
      }
    }
  })
  let out : Array[PMCondition] = []
  for b in bindings {
    out.push(PMRun(b))
  }
  out.push(cond)
  out
}

///|
fn sym_kind(s : Sym) -> String {
  match s {
    ValueParam(_) => "ValueParam"
    ValBinder(_) => "ValBinder"
    Hole(_) => "Hole"
    Wildcard(_) => "Wildcard"
    TmpValue(_) => "TmpValue"
    BlockParam(_) => "BlockParam"
    ExternResource(_) => "ExternResource"
    ResumeParam(_) => "ResumeParam"
    UserFunction(_) => "UserFunction"
    Lambda(_) => "Lambda"
    RegBinder(_) => "RegBinder"
    VarBinder(_) => "VarBinder"
    DefBinder(_) => "DefBinder"
    CallTarget(_) => "CallTarget"
    Operation(_) => "Operation"
    Constructor(_) => "Constructor"
    Field(_) => "Field"
    ExternFunction(_) => "ExternFunction"
    TmpBlock(_) => "TmpBlock"
    TypeParam(_) => "TypeParam"
    UnificationVar(_) => "UnificationVar"
    TypeAlias(_) => "TypeAlias"
    DataType(_) => "DataType"
    Record(_) => "Record"
    ExternType(_) => "ExternType"
    ErrorValueType(_) => "ErrorValueType"
    Interface(_) => "Interface"
    ExternInterface(_) => "ExternInterface"
    ErrorBlockType(_) => "ErrorBlockType"
    EffectAlias(_) => "EffectAlias"
    CaptUnificationVar(_) => "CaptUnificationVar"
    CaptureParam(_) => "CaptureParam"
    LexicalRegion(_) => "LexicalRegion"
    Resource(_) => "Resource"
  }
}
