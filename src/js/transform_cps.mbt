// The CPS-to-JavaScript translation.
//
// Mirrors `effekt/generator/js/TransformerCps.scala`.
//
// Deviations from the Scala original (documented on purpose):
//   * `C.errors.report(err)` for an `ExternBody.Unsupported` becomes a `raise`
//     (this port has no error-collecting `Context`);
//   * the constructor tag of a `cps.Clause` is read through `@cps.clause_tag`,
//     since the CPS tree's `Clause` has no tag field of its own (see the note
//     in `cps/prelude.mbt` and in `cps/transform.mbt`).

///|
/// `RUN_TOPLEVEL`, defined in `effekt_runtime.js`.
fn run_toplevel() -> Expr {
  Variable(JSName::new("RUN_TOPLEVEL"))
}

///|
/// `RESET`, defined in `effekt_runtime.js`.
fn reset_fn() -> Expr {
  Variable(JSName::new("RESET"))
}

///|
/// `SHIFT`, defined in `effekt_runtime.js`.
fn shift_fn() -> Expr {
  Variable(JSName::new("SHIFT"))
}

///|
/// `RESUME`, defined in `effekt_runtime.js`.
fn resume_fn() -> Expr {
  Variable(JSName::new("RESUME"))
}

///|
/// `VAR`, defined in `effekt_runtime.js`.
fn var_fn() -> Expr {
  Variable(JSName::new("VAR"))
}

///|
/// `REGION`, defined in `effekt_runtime.js`.
fn region_fn() -> Expr {
  Variable(JSName::new("REGION"))
}

///|
fn min2(a : Int32, b : Int32) -> Int32 {
  if a < b {
    a
  } else {
    b
  }
}

// ---------------------------------------------------------------------------
// Transformer context
// ---------------------------------------------------------------------------

///|
/// Whether a self-reference of the enclosing recursive definition was actually
/// jumped to (upstream: `class RecursiveUsage(var jumped: Boolean)`; `Ref` makes
/// the flag shared between all copies of the context).
priv struct RecursiveUsage {
  jumped : Ref[Bool]
}

///|
/// The innermost enclosing function *in direct style* (used to rewrite a
/// definition to a loop).
priv struct RecursiveDefInfo {
  id : Sym
  label : Sym
  vparams : Array[Sym]
  bparams : Array[Sym]
  ks : Sym
  k : Sym
  used : RecursiveUsage
}

///|
/// The direct-style continuation, if available.
///
/// Upstream carries a third field `ks` here (`ContinuationInfo(k, vparams,
/// ks)`); it is written but never read there, so it is dropped instead of
/// keeping dead state around.
priv struct ContinuationInfo {
  k : Sym
  vparams : Array[Sym]
}

///|
/// Mirrors `TransformerCps.TransformerContext`.
priv struct TransformerContext {
  requires_thunk : Bool
  /// The `ExternDef`s of the module, used to inline them.
  externs : Map[Int32, @cps.Extern]
  recursive : RecursiveDefInfo?
  direct_style : ContinuationInfo?
  /// Keeps track of the function scope we are in, to correctly back up function
  /// parameters which are used in nested definitions (see `Stmt.LetDef`).
  scope : Array[(Sym, @cps.Block)]
  /// The current direct-style metacontinuation.
  metacont : Sym?
  /// The original declaration context (used to compile pattern matching).
  declarations : @core.DeclarationContext
}

///|
fn TransformerContext::with_requires_thunk(
  self : TransformerContext,
  value : Bool,
) -> TransformerContext {
  { ..self, requires_thunk: value, }
}

///|
/// `recursive(id, ...)`: entering the body of a recursive definition.
fn TransformerContext::with_recursive(
  self : TransformerContext,
  info : RecursiveDefInfo,
) -> TransformerContext {
  {
    ..self,
    recursive: Some(info),
    direct_style: None,
    metacont: Some(info.ks),
  }
}

///|
/// `nonrecursive(ks)`.
fn TransformerContext::nonrecursive(
  self : TransformerContext,
  ks : Sym,
) -> TransformerContext {
  { ..self, recursive: None, direct_style: None, metacont: Some(ks), }
}

///|
/// `markDirectStyle(id, params, ks)` (the upstream `ks` argument is unused).
fn TransformerContext::mark_direct_style(
  self : TransformerContext,
  id : Sym,
  params : Array[Sym],
) -> TransformerContext {
  { ..self, direct_style: Some({ k: id, vparams: params, }), }
}

///|
/// `requiringThunk { prog }`.
fn[T] requiring_thunk(
  ctx : TransformerContext,
  prog : (TransformerContext) -> T raise EffektError,
) -> T raise EffektError {
  prog(ctx.with_requires_thunk(true))
}

///|
/// `maybeThunking(expr)`.
fn maybe_thunking_expr(ctx : TransformerContext, e : Expr) -> Expr {
  if ctx.requires_thunk {
    lambda([], e)
  } else {
    e
  }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

///|
/// Messages about externs for which no body applies to the current backend,
/// collected during code generation. `@backend` drains them after `compile_cps`
/// returns and reports them as warnings (upstream does the same from
/// `TransformerCps`, which has the compiler context at hand; here the code
/// generator does not, so the messages travel back to the driver).
let unsupported_messages : Array[String] = []

///|
pub fn take_unsupported_messages() -> Array[String] {
  let out = unsupported_messages.copy()
  unsupported_messages.clear()
  out
}

///|
/// Reports an extern definition for which no body applies to the current
/// backend. Upstream treats this as a *warning* (`ResolveExternDefs` builds the
/// `Unsupported` body from a `Severities.Warning` message) and still generates a
/// function that traps, so the module only fails if that function is called.
fn report_unsupported(ctx : TransformerContext, err : EffektError) -> Unit {
  let _ = ctx
  let message = match err {
    EffektError::Fatal(m) => m
    EffektError::Internal(m) => "Internal error: \{m}"
  }
  unsupported_messages.push(message)
}

///|
/// `RUN_TOPLEVEL` calls the entry point with exactly the (metacontinuation,
/// continuation) pair, so `main` must not declare value or block parameters.
///
/// Upstream enforces this in `Typer.checkMain` ("Main does not take arguments",
/// "Main cannot have effects, but includes effects: ..."). This port does not
/// check it in the frontend yet, and a `main` with an (unhandled) effect would
/// otherwise be called with *shifted* arguments — every value ends up bound to
/// the wrong parameter, which surfaces as an inscrutable runtime error
/// (`k_0 is not a function`) far away from the cause. Refuse to generate that.
fn check_main_signature(
  core_module : @core.ModuleDecl,
  main : Sym,
) -> Unit raise EffektError {
  for d in core_module.definitions {
    match d {
      @core.ToplevelDef(id, @core.Block::BlockLit(lit)) =>
        if id.uid() == main.uid() {
          if lit.vparams.length() > 0 {
            raise EffektError::Fatal(
              "Main does not take arguments, but takes \{lit.vparams.length()}.",
            )
          }
          if lit.bparams.length() > 0 {
            let effects : Array[String] = []
            for p in lit.bparams {
              effects.push(@core.show_core_block_type(p.tpe))
            }
            raise EffektError::Fatal(
              "Main cannot have effects, but includes effects: {\{effects.join(", ")}}.",
            )
          }
        }
      _ => ()
    }
  }
}

///|
/// `input` = contified CPS module, `core_module` = the aggregated core module
/// (needed for `DeclarationContext`), `main` = the `main` symbol.
pub fn compile_cps(
  input : @cps.ModuleDecl,
  core_module : @core.ModuleDecl,
  main : Sym,
) -> String raise EffektError {
  reset_naming()
  check_main_signature(core_module, main)
  let module = input
  let declarations = @core.DeclarationContext::new(
    core_module.declarations,
    core_module.externs,
  )
  // The exports are generated first, so that the name of `main` is allocated
  // before the names of the definitions (as in the Scala original).
  let exports : Array[Export] = [
    Export::new(
      JSName::new("main"),
      lambda([], call(run_toplevel(), [name_ref(main)])),
    ),
  ]
  let extern_defs : Map[Int32, @cps.Extern] = Map::new()
  for e in module.externs {
    match e {
      @cps.ExternDef(id, _, _, _, _) => extern_defs.set(id.uid(), e)
      _ => ()
    }
  }
  let ctx : TransformerContext = {
    requires_thunk: false,
    externs: extern_defs,
    recursive: None,
    direct_style: None,
    scope: [],
    metacont: None,
    declarations,
  }
  let js_externs : Array[Stmt] = []
  for e in module.externs {
    if !can_inline(e) {
      js_externs.push(to_js_extern(e, ctx))
    }
  }
  let js_declarations : Array[Stmt] = []
  for d in module.declarations {
    js_declarations.append(to_js_declaration(d))
  }
  let stmts : Array[Stmt] = []
  for d in module.definitions {
    stmts.push(to_js_toplevel(d, ctx))
  }
  let js_module = Module::new(
    JSName::new(js_module_name(module.path)),
    [],
    exports,
    js_declarations + js_externs + stmts,
  )
  show_stmts(js_module.commonjs())
}

// ---------------------------------------------------------------------------
// Toplevel definitions
// ---------------------------------------------------------------------------

///|
fn to_js_toplevel(
  d : @cps.ToplevelDefinition,
  ctx : TransformerContext,
) -> Stmt raise EffektError {
  match d {
    @cps.ToplevelDef(id, block) => {
      let ctx2 : TransformerContext = {
        ..ctx,
        scope: [(id, block)] + ctx.scope,
      }
      js_const(
        name_def(id),
        requiring_thunk(ctx2, c => to_js_block(id, block, c)),
      )
    }
    @cps.ToplevelVal(id, ks, k, binding) =>
      js_const(
        name_def(id),
        call(run_toplevel(), [
          lambda_stmts(
            [name_def(ks), name_def(k)],
            to_js_stmt(binding, ctx).stmts(),
          ),
        ]),
      )
    @cps.ToplevelLet(id, binding) =>
      js_const(name_def(id), to_js_cps_expr(binding, ctx))
  }
}

///|
fn to_js_param(id : Sym) -> JSName {
  name_def(id)
}

// ---------------------------------------------------------------------------
// Externs
// ---------------------------------------------------------------------------

///|
fn to_js_extern(
  e : @cps.Extern,
  ctx : TransformerContext,
) -> Stmt raise EffektError {
  match e {
    @cps.ExternDef(id, vps, bps, true, body) =>
      match body {
        @cps.StringExternBody(_, contents) => {
          let ks = fresh_name("ks_")
          let k = fresh_name("k_")
          let params : Array[JSName] = []
          for p in vps + bps {
            params.push(to_js_param(p))
          }
          Stmt::Function(name_def(id), params + [ks, k], [
            Return(
              call(to_js_template(contents, ctx), [Variable(ks), Variable(k)]),
            ),
          ])
        }
        // Mirrors upstream: an extern that no body applies to is reported as a
        // *warning* and compiles to a call to `$effekt.unreachable`.
        @cps.Unsupported(err) => {
          report_unsupported(ctx, err)
          let ks = fresh_name("ks_")
          let k = fresh_name("k_")
          let params : Array[JSName] = []
          for p in vps + bps {
            params.push(to_js_param(p))
          }
          Stmt::Function(name_def(id), params + [ks, k], [
            Return(call(effekt_field("unreachable"), [])),
          ])
        }
      }
    @cps.ExternDef(id, vps, bps, false, body) => {
      let params : Array[JSName] = []
      for p in vps + bps {
        params.push(to_js_param(p))
      }
      match body {
        @cps.StringExternBody(_, contents) =>
          Stmt::Function(name_def(id), params, [
            Return(to_js_template(contents, ctx)),
          ])
        @cps.Unsupported(err) => {
          report_unsupported(ctx, err)
          Stmt::Function(name_def(id), params, [
            Return(call(effekt_field("unreachable"), [])),
          ])
        }
      }
    }
    @cps.ExternData(id, tps, body) =>
      match body {
        @cps.StringExternBody(_, contents) =>
          raw_stmt(
            "// extern type \{id.name().qualified_name()}\{show_tparams(tps)} = \{render_template(contents)}",
          )
        @cps.Unsupported(_) =>
          raw_stmt(
            "// unsupported extern type \{id.name().qualified_name()} = \{show_tparams(tps)}",
          )
      }
    @cps.ExternInterface(id, tps, body) =>
      match body {
        @cps.StringExternBody(_, contents) =>
          raw_stmt(
            "// extern type \{id.name().qualified_name()}\{show_tparams(tps)} = \{render_template(contents)}",
          )
        @cps.Unsupported(_) =>
          raw_stmt(
            "// unsupported extern type \{id.name().qualified_name()} = \{show_tparams(tps)}",
          )
      }
    @cps.ExternInclude(_, contents) => raw_stmt(contents)
  }
}

///|
fn show_tparams(tps : Array[Sym]) -> String {
  if tps.length() == 0 {
    ""
  } else {
    tps.map(t => t.name().qualified_name()).join(", ")
  }
}

///|
/// Renders a template whose arguments are only ever empty (extern data and
/// interface bodies carry no expressions).
fn render_template(template : Template[@cps.Expr]) -> String {
  template.render(_ => "?")
}

///|
fn to_js_template(
  t : Template[@cps.Expr],
  ctx : TransformerContext,
) -> Expr raise EffektError {
  let args : Array[Expr] = []
  for a in t.args {
    args.push(to_js_cps_expr(a, ctx))
  }
  RawExpr(t.strings, args)
}

// ---------------------------------------------------------------------------
// Declarations
// ---------------------------------------------------------------------------

///|
fn to_js_declaration(d : @core.Declaration) -> Array[Stmt] {
  match d {
    @core.DeclarationData(_, _, ctors) => {
      let out : Array[Stmt] = []
      for i = 0; i < ctors.length(); i = i + 1 {
        out.push(generate_constructor(ctors[i], i))
      }
      out
    }
    // interfaces are structurally typed at the moment, no need to generate
    // anything
    @core.DeclarationInterface(_, _, _) => []
  }
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

///|
fn to_js_block(
  id : Sym,
  b : @cps.Block,
  ctx : TransformerContext,
) -> Expr raise EffektError {
  match b {
    @cps.Block::BlockLit(lit) => maybe_to_loop(id, lit, ctx)
    other => to_js_block_expr(other, ctx)
  }
}

///|
fn maybe_to_loop(
  id : Sym,
  lit : @cps.BlockLit,
  ctx : TransformerContext,
) -> Expr raise EffektError {
  let used : RecursiveUsage = { jumped: Ref(false), }
  let label = id
  let info : RecursiveDefInfo = {
    id,
    label,
    vparams: lit.vparams,
    bparams: lit.bparams,
    ks: lit.ks,
    k: lit.k,
    used,
  }
  let translated_body = to_js_stmt(lit.body, ctx.with_recursive(info)).stmts()
  let params : Array[JSName] = []
  for p in lit.vparams + lit.bparams {
    params.push(name_def(p))
  }
  let all_params = params + [name_def(lit.ks), name_def(lit.k)]
  if used.jumped.val {
    lambda_stmts(all_params, [
      While(raw_expr("true"), translated_body, Some(unique_name(label))),
    ])
  } else {
    lambda_stmts(all_params, translated_body)
  }
}

///|
fn to_js_block_expr(
  b : @cps.Block,
  ctx : TransformerContext,
) -> Expr raise EffektError {
  match b {
    @cps.Block::BlockVar(v) => name_ref(v)
    @cps.Block::Unbox(e) => to_js_cps_expr(e, ctx)
    @cps.Block::New(handler) => to_js_implementation(handler, ctx)
    @cps.Block::BlockLit(lit) => {
      let params : Array[JSName] = []
      for p in lit.vparams + lit.bparams {
        params.push(name_def(p))
      }
      lambda_stmts(
        params + [name_def(lit.ks), name_def(lit.k)],
        to_js_stmt(lit.body, ctx).stmts(),
      )
    }
  }
}

///|
fn argument_to_js(
  b : @cps.Block,
  ctx : TransformerContext,
) -> Expr raise EffektError {
  match b {
    @cps.Block::BlockLit(lit) => to_js_block_expr(b, ctx.nonrecursive(lit.ks))
    _ => to_js_block_expr(b, ctx)
  }
}

///|
fn to_js_implementation(
  handler : @cps.Implementation,
  ctx : TransformerContext,
) -> Expr raise EffektError {
  let properties : Array[ObjectProperty] = []
  for op in handler.operations {
    let params : Array[JSName] = []
    for p in op.vparams + op.bparams {
      params.push(name_def(p))
    }
    properties.push(
      ObjectProperty::new(
        name_def(op.name),
        lambda_stmts(
          params + [name_def(op.ks), name_def(op.k)],
          to_js_stmt(op.body, ctx.nonrecursive(op.ks)).stmts(),
        ),
      ),
    )
  }
  Object(properties)
}

// ---------------------------------------------------------------------------
// Continuations
// ---------------------------------------------------------------------------

///|
fn to_js_metacont(ks : @cps.MetaCont, ctx : TransformerContext) -> Expr {
  let _ = ctx
  name_ref(ks.id)
}

///|
fn to_js_cont(
  k : @cps.Cont,
  ctx : TransformerContext,
) -> Expr raise EffektError {
  match k {
    @cps.Cont::ContVar(id) => name_ref(id)
    @cps.Cont::ContLam(lam) =>
      lambda_stmts(
        lam.results.map(name_def) + [name_def(lam.ks)],
        to_js_stmt(lam.body, ctx.nonrecursive(lam.ks)).stmts(),
      )
    @cps.Cont::Abort => undefined()
  }
}

///|
/// `maintainDirectStyle(ks, body)`: ensures let-bound continuations can stay in
/// direct style by aligning metacont scopes.
///
/// ```
/// ks | let k1 x1 ks1 = { let k2 x2 ks2 = jump k v ks2 }; ... = jump k v ks
/// ```
fn maintain_direct_style(
  ks : Sym,
  body : @cps.Stmt,
  ctx : TransformerContext,
) -> @cps.Stmt raise EffektError {
  let outer = match ctx.metacont {
    Some(m) => m
    None => internal_error("Metacontinuation missing...")
  }
  let metaconts : Map[Int32, @cps.MetaCont] = Map([])
  metaconts.set(ks.uid(), @cps.MetaCont::new(outer))
  let values : Map[Int32, @cps.Expr] = Map([])
  let blocks : Map[Int32, @cps.Block] = Map([])
  let conts : Map[Int32, @cps.Cont] = Map([])
  @cps.substitute_stmt(
    body,
    @cps.Substitution::new(values, blocks, conts, metaconts),
  )
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

///|
fn literal_to_js(value : LiteralValue) -> Expr {
  match value {
    LUnit => effekt_field("unit")
    LBool(b) => raw_expr(b.to_string())
    LInt(i) => raw_expr(i.to_string())
    LDouble(d) => raw_expr(d.to_string())
    LString(s) => js_string(escape(s))
    // A `Char` is an `Int` at runtime: upstream renders every other literal
    // with `value.toString`, and the prelude's `showBuiltin(Char)` is
    // `String.fromCodePoint(${value})`, which needs the numeric code point.
    LChar(c) => raw_expr(c.to_string())
    LByte(b) => raw_expr(byte_to_hex_string(b))
  }
}

///|
/// `UByte.unsafeFromByte(b).toHexString`, e.g. `0x0F`.
fn byte_to_hex_string(b : Int32) -> String {
  let digits : Array[Char] = []
  for c in "0123456789ABCDEF" {
    digits.push(c)
  }
  let v = b & 0xFF
  let buf = StringBuilder()
  buf.write_string("0x")
  buf.write_char(digits[v / 16])
  buf.write_char(digits[v % 16])
  buf.to_string()
}

///|
fn to_js_cps_expr(
  e : @cps.Expr,
  ctx : TransformerContext,
) -> Expr raise EffektError {
  match e {
    @cps.Expr::ValueVar(id) => name_ref(id)
    @cps.Expr::Literal(value, _tpe) => literal_to_js(value)
    @cps.Expr::PureApp(id, vargs) => inline_extern(id, vargs, ctx)
    @cps.Expr::Make(_data, tag, vargs) => {
      let args : Array[Expr] = []
      for v in vargs {
        args.push(to_js_cps_expr(v, ctx))
      }
      New(name_ref(tag), args)
    }
    @cps.Expr::Box(b) => argument_to_js(b, ctx)
  }
}

// ---------------------------------------------------------------------------
// Inlining externs
// ---------------------------------------------------------------------------

///|
/// A non-async `ExternDef` with value parameters only, together with its
/// template.
fn extern_inline_template(
  extern_def : @cps.Extern,
) -> (Array[Sym], Template[@cps.Expr])? {
  match extern_def {
    @cps.ExternDef(_id, params, bparams, is_async, body) =>
      if !is_async && bparams.length() == 0 {
        match body {
          @cps.StringExternBody(_, template) => Some((params, template))
          @cps.Unsupported(_) => None
        }
      } else {
        None
      }
    _ => None
  }
}

///|
fn can_inline(extern_def : @cps.Extern) -> Bool {
  extern_inline_template(extern_def).is_some()
}

///|
fn inline_extern(
  id : Sym,
  args : Array[@cps.Expr],
  ctx : TransformerContext,
) -> Expr raise EffektError {
  let extern_def = match ctx.externs.get(id.uid()) {
    Some(d) => d
    None => return call(name_ref(id), args.map(a => to_js_cps_expr(a, ctx)))
  }
  match extern_inline_template(extern_def) {
    Some((params, template)) => {
      let values : Map[Int32, @cps.Expr] = Map([])
      for i = 0; i < min2(params.length(), args.length()); i = i + 1 {
        values.set(params[i].uid(), args[i])
      }
      let blocks : Map[Int32, @cps.Block] = Map([])
      let conts : Map[Int32, @cps.Cont] = Map([])
      let metaconts : Map[Int32, @cps.MetaCont] = Map([])
      let subst = @cps.Substitution::new(values, blocks, conts, metaconts)
      let substituted : Array[Expr] = []
      for arg in template.args {
        substituted.push(to_js_cps_expr(@cps.substitute_expr(arg, subst), ctx))
      }
      RawExpr(template.strings, substituted)
    }
    None => call(name_ref(id), args.map(a => to_js_cps_expr(a, ctx)))
  }
}

// ---------------------------------------------------------------------------
// Direct style
// ---------------------------------------------------------------------------

///|
fn can_be_direct(
  k : Sym,
  stmt : @cps.Stmt,
  ctx : TransformerContext,
) -> Bool raise EffektError {
  match stmt {
    @cps.Stmt::Jump(k2, vargs, ks2) => {
      let args_ok = vargs.all(v => !v.free().contains(k))
      let metacont_ok = match ctx.metacont {
        Some(m) => m.uid() == ks2.id.uid()
        None => false
      }
      if k2.uid() == k.uid() {
        args_ok && metacont_ok
      } else {
        args_ok
      }
    }
    @cps.Stmt::App(_, _, _, _, _) => !stmt.free().contains(k)
    @cps.Stmt::Invoke(_, _, _, _, _, _) => !stmt.free().contains(k)
    @cps.Stmt::If(_cond, thn, els) =>
      can_be_direct(k, thn, ctx) && can_be_direct(k, els, ctx)
    @cps.Stmt::Match(_scrutinee, clauses, default) => {
      let clauses_ok = clauses.all(c => can_be_direct(k, c.body, ctx))
      let default_ok = match default {
        Some(body) => can_be_direct(k, body, ctx)
        None => true
      }
      clauses_ok && default_ok
    }
    @cps.Stmt::LetDef(_id, binding, body) =>
      !binding.free().contains(k) && can_be_direct(k, body, ctx)
    @cps.Stmt::LetExpr(_id, binding, body) =>
      !binding.free().contains(k) && can_be_direct(k, body, ctx)
    @cps.Stmt::ImpureApp(_id, _callee, vargs, bargs, body) =>
      vargs.all(v => !v.free().contains(k)) &&
      bargs.all(b => !b.free().contains(k)) &&
      can_be_direct(k, body, ctx)
    // TODO this could be a tail call!
    @cps.Stmt::LetCont(id, binding, body2) => {
      let will_be_direct_itself = can_be_direct(id, body2, ctx) &&
        can_be_direct(
          k,
          maintain_direct_style(binding.ks, binding.body, ctx),
          ctx,
        )
      let not_free_in_continuation = !binding.body.free().contains(k) &&
        can_be_direct(k, body2, ctx)
      will_be_direct_itself || not_free_in_continuation
    }
    @cps.Stmt::Region(_id, _ks, body) => !body.free().contains(k)
    @cps.Stmt::Alloc(_id, init, _region, body) =>
      !init.free().contains(k) && can_be_direct(k, body, ctx)
    @cps.Stmt::Var(_id, init, _ks, body) =>
      !init.free().contains(k) && can_be_direct(k, body, ctx)
    @cps.Stmt::Dealloc(_ref, body) => can_be_direct(k, body, ctx)
    @cps.Stmt::Get(_ref, _id, body) => can_be_direct(k, body, ctx)
    @cps.Stmt::Put(_ref, value, body) =>
      !value.free().contains(k) && can_be_direct(k, body, ctx)
    @cps.Stmt::Reset(_, _, _) => !stmt.free().contains(k)
    @cps.Stmt::Shift(_, _, _, _) => !stmt.free().contains(k)
    @cps.Stmt::Resume(_, _, _, _) => !stmt.free().contains(k)
    @cps.Stmt::Hole(_) => true
  }
}

// ---------------------------------------------------------------------------
// Pattern matching
// ---------------------------------------------------------------------------

///|
/// The `(tag, statements)` of one `match` clause: the fields that the clause
/// actually uses are extracted from the scrutinee.
fn to_js_clause(
  scrutinee : Expr,
  clause : @cps.Clause,
  ctx : TransformerContext,
) -> (Expr, Binding[Array[Stmt]]) raise EffektError {
  let variant = @cps.clause_tag(clause)
  let fields = ctx.declarations.get_constructor(variant).fields
  let tag = raw_expr(ctx.declarations.get_constructor_tag(variant).to_string())

  let free_vars = clause.body.free()
  let extracted : Array[Stmt] = []
  for i = 0; i < min2(clause.vparams.length(), fields.length()); i = i + 1 {
    let p = clause.vparams[i]
    if free_vars.contains(p) {
      extracted.push(
        Const(
          PatternVariable(name_def(p)),
          Member(scrutinee, member_name_ref(fields[i].id)),
        ),
      )
    }
  }
  let body = to_js_stmt(clause.body, ctx)
  (tag, { run: fn(k) raise EffektError { extracted + (body.run)(k) }, })
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
/// The `RecursiveDefInfo` of the enclosing definition, if `b` is a
/// self-reference of it (upstream `Recursive.unapply`).
fn recursive_info_of(
  b : @cps.Block,
  ctx : TransformerContext,
) -> RecursiveDefInfo? {
  match b {
    @cps.Block::BlockVar(id) =>
      match ctx.recursive {
        Some(info) => if info.id.uid() == id.uid() { Some(info) } else { None }
        None => None
      }
    _ => None
  }
}

///|
fn to_js_stmt(
  s : @cps.Stmt,
  ctx : TransformerContext,
) -> Binding[Array[Stmt]] raise EffektError {
  match s {
    @cps.Stmt::LetDef(id, block, body) =>
      {
        run: fn(k) raise EffektError {
          let stmts : Array[Stmt] = []

          // (1) determine all bound function parameters that may be subsequently
          // altered when preparing calls to a tail-recursive function
          let bound : Array[Sym] = []
          for entry in ctx.scope {
            let (_id, scoped_block) = entry
            match scoped_block {
              @cps.Block::BlockLit(lit) =>
                bound.append(lit.vparams + lit.bparams)
              _ => ()
            }
          }

          // (2) back up the parameters that the block mentions as const bindings
          let free_of_block = block.free()
          let values : Map[Int32, @cps.Expr] = Map([])
          for param in bound {
            if free_of_block.contains(param) {
              let tmp = fresh_sym("tmp_\{param.name().name}")
              stmts.push(Const(PatternVariable(name_def(tmp)), name_ref(param)))
              values.set(param.uid(), @cps.Expr::ValueVar(tmp))
            }
          }

          // (3) substitute the block, so that the backed up bindings are used
          let blocks : Map[Int32, @cps.Block] = Map([])
          let conts : Map[Int32, @cps.Cont] = Map([])
          let metaconts : Map[Int32, @cps.MetaCont] = Map([])
          let subst_block = @cps.substitute_block(
            block,
            @cps.Substitution::new(values, blocks, conts, metaconts),
          )
          let ctx2 : TransformerContext = {
            ..ctx,
            scope: [(id, subst_block)] + ctx.scope,
          }
          stmts.push(
            js_const(
              name_def(id),
              requiring_thunk(ctx2, c => to_js_block(id, subst_block, c)),
            ),
          )
          stmts.append((to_js_stmt(body, ctx).run)(k))
          stmts
        },
      }
    @cps.Stmt::If(cond, thn, els) =>
      pure([
        If(
          to_js_cps_expr(cond, ctx),
          to_js_stmt(thn, ctx).block(),
          to_js_stmt(els, ctx).block(),
        ),
      ])
    @cps.Stmt::LetExpr(id, binding, body) =>
      {
        run: fn(k) raise EffektError {
          [js_const(name_def(id), to_js_cps_expr(binding, ctx))] +
          (to_js_stmt(body, ctx).run)(k)
        },
      }

    // [[ let k(x, ks) = ...; if (...) jump k(42, ks2) else jump k(10, ks3) ]] =
    //    let x; if (...) { x = 42; ks = ks2 } else { x = 10; ks = ks3 } ...
    @cps.Stmt::LetCont(id, binding, body2) => {
      let direct_ok = match ctx.direct_style {
        Some(info) => !body2.free().contains(info.k)
        None => true
      }
      if can_be_direct(id, body2, ctx) && direct_ok {
        let params = binding.results
        let ks = binding.ks
        let cont_body = binding.body
        {
          run: fn(k) raise EffektError {
            let out : Array[Stmt] = []
            for p in params {
              out.push(js_let(name_def(p), undefined()))
            }
            out.append(
              to_js_stmt(body2, ctx.mark_direct_style(id, params)).stmts(),
            )
            out.append(
              (to_js_stmt(maintain_direct_style(ks, cont_body, ctx), ctx).run)(
                k,
              ),
            )
            out
          },
        }
      } else {
        // `js.Const(nameDef(id), toJS(binding)) :: requiringThunk { toJS(body) }`
        // where `body` is the *rest* of the program, not the continuation body.
        let lam = @cps.Cont::ContLam(binding)
        let ks2 = binding.ks
        {
          run: fn(k) raise EffektError {
            [js_const(name_def(id), to_js_cont(lam, ctx.nonrecursive(ks2)))] +
            (requiring_thunk(ctx, c => to_js_stmt(body2, c)).run)(k)
          },
        }
      }
    }
    @cps.Stmt::ImpureApp(id, callee, vargs, bargs, body) =>
      if bargs.length() == 0 {
        {
          run: fn(k) raise EffektError {
            [js_const(name_def(id), inline_extern(callee, vargs, ctx))] +
            (to_js_stmt(body, ctx).run)(k)
          },
        }
      } else {
        {
          run: fn(k) raise EffektError {
            [
              js_const(
                name_def(id),
                call(
                  name_ref(callee),
                  vargs.map(v => to_js_cps_expr(v, ctx)) +
                  bargs.map(b => argument_to_js(b, ctx)),
                ),
              ),
            ] +
            (to_js_stmt(body, ctx).run)(k)
          },
        }
      }
    @cps.Stmt::Match(scrutinee, clauses, default) => {
      let no_default = match default {
        None => true
        Some(_) => false
      }
      if clauses.length() == 0 && no_default {
        pure([Return(effekt_call("unreachable", []))])
      } else if clauses.length() == 1 && no_default {
        let scrutinee_js = to_js_cps_expr(scrutinee, ctx)
        let (_tag, stmts) = to_js_clause(scrutinee_js, clauses[0], ctx)
        stmts
      } else {
        // (function () { switch (sc.tag) { case 0: return f17.apply(null, sc.data) } })
        let scrutinee_js = to_js_cps_expr(scrutinee, ctx)
        let branches : Array[SwitchBranch] = []
        for clause in clauses {
          let (tag, binding) = to_js_clause(scrutinee_js, clause, ctx)
          let stmts = binding.stmts()
          let terminated = if stmts.length() == 0 {
            false
          } else {
            match stmts[stmts.length() - 1] {
              Return(_) | Break | Continue(_) => true
              _ => false
            }
          }
          branches.push(
            SwitchBranch::new(
              tag,
              if terminated {
                stmts
              } else {
                stmts + [Break]
              },
            ),
          )
        }
        let default_stmts = match default {
          Some(body) => Some(to_js_stmt(body, ctx).stmts())
          None => None
        }
        pure([
          Switch(
            Member(scrutinee_js, JSName::new("__tag")),
            branches,
            default_stmts,
          ),
        ])
      }
    }
    @cps.Stmt::Jump(k, vargs, ks) =>
      match ctx.direct_style {
        Some(info) if info.k.uid() == k.uid() => {
          let assigns : Array[Stmt] = []
          for i = 0; i < min2(info.vparams.length(), vargs.length()); i = i + 1 {
            assigns.push(
              Assign(name_ref(info.vparams[i]), to_js_cps_expr(vargs[i], ctx)),
            )
          }
          pure(assigns)
        }
        _ =>
          pure([
            Return(
              maybe_thunking_expr(
                ctx,
                call(
                  name_ref(k),
                  vargs.map(v => to_js_cps_expr(v, ctx)) +
                  [to_js_metacont(ks, ctx)],
                ),
              ),
            ),
          ])
      }
    @cps.Stmt::App(callee, vargs, bargs, ks, k) =>
      match recursive_info_of(callee, ctx) {
        Some(info) =>
          {
            run: fn(k2) raise EffektError {
              let stmts : Array[Stmt] = []
              stmts.push(raw_stmt("/* prepare call */"))
              info.used.jumped.val = true

              // We need to create temporaries for all free variables that appear
              // in arguments
              let mut free_in_args = @cps.Variables::empty()
              for v in vargs {
                free_in_args = free_in_args.union(v.free())
              }
              for b in bargs {
                free_in_args = free_in_args.union(b.free())
              }

              // Only compute the free variables of the continuation if it is not
              // a continuation variable
              let (is_tail_call, free_in_k) = match k {
                @cps.Cont::ContVar(kid) =>
                  (
                    kid.uid() == info.k.uid() && ks.id.uid() == info.ks.uid(),
                    @cps.Variables::empty(),
                  )
                _ => (false, k.free())
              }
              let all_free_vars = free_in_args.union(free_in_k)
              let needs_ks_tmp = all_free_vars.contains(info.ks)

              // Create temporaries for the parameters that are used in the
              // arguments or in the continuation
              let values : Map[Int32, @cps.Expr] = Map([])
              for param in info.vparams + info.bparams {
                if all_free_vars.contains(param) {
                  let tmp = fresh_sym("tmp_\{param.name().name}")
                  stmts.push(
                    Const(PatternVariable(name_def(tmp)), name_ref(param)),
                  )
                  values.set(param.uid(), @cps.Expr::ValueVar(tmp))
                }
              }

              let tmp_ks = if needs_ks_tmp {
                let tmp = fresh_sym("tmp_ks")
                stmts.push(
                  Const(PatternVariable(name_def(tmp)), name_ref(info.ks)),
                )
                Some(tmp)
              } else {
                None
              }

              // For non-tail calls we need a continuation temporary if this is
              // not a simple variable renaming
              let tmp_k = if !is_tail_call {
                match k {
                  @cps.Cont::ContVar(kid) if kid.uid() != info.k.uid() => None
                  _ => {
                    let tmp = fresh_sym("tmp_k")
                    stmts.push(
                      Const(PatternVariable(name_def(tmp)), name_ref(info.k)),
                    )
                    Some(tmp)
                  }
                }
                // For tail calls, only create a temporary if `k1` appears in the
                // arguments
              } else if free_in_args.contains(info.k) {
                let tmp = fresh_sym("tmp_k")
                stmts.push(
                  Const(PatternVariable(name_def(tmp)), name_ref(info.k)),
                )
                Some(tmp)
              } else {
                None
              }

              // Prepare the substitution
              let conts : Map[Int32, @cps.Cont] = Map([])
              match tmp_k {
                Some(t) => conts.set(info.k.uid(), @cps.Cont::ContVar(t))
                None => ()
              }
              let metaconts : Map[Int32, @cps.MetaCont] = Map([])
              match tmp_ks {
                Some(t) => metaconts.set(info.ks.uid(), @cps.MetaCont::new(t))
                None => ()
              }
              let blocks : Map[Int32, @cps.Block] = Map([])
              let subst = @cps.Substitution::new(
                values, blocks, conts, metaconts,
              )

              // Update the continuation if this is not a tail call
              if !is_tail_call {
                match k {
                  @cps.Cont::ContVar(kid) if kid.uid() != info.k.uid() =>
                    stmts.push(Assign(name_ref(info.k), name_ref(kid)))
                  _ =>
                    stmts.push(
                      Assign(
                        name_ref(info.k),
                        to_js_cont(@cps.substitute_cont(k, subst), ctx),
                      ),
                    )
                }
              }

              // Assign the substituted arguments
              for i = 0
                  i < min2(info.vparams.length(), vargs.length())
                  i = i + 1 {
                stmts.push(
                  Assign(
                    name_ref(info.vparams[i]),
                    to_js_cps_expr(@cps.substitute_expr(vargs[i], subst), ctx),
                  ),
                )
              }
              for i = 0
                  i < min2(info.bparams.length(), bargs.length())
                  i = i + 1 {
                stmts.push(
                  Assign(
                    name_ref(info.bparams[i]),
                    argument_to_js(@cps.substitute_block(bargs[i], subst), ctx),
                  ),
                )
              }

              // Restore the metacontinuation if needed
              if needs_ks_tmp {
                match tmp_ks {
                  Some(t) => stmts.push(Assign(name_ref(info.ks), name_ref(t)))
                  None => ()
                }
              }

              let jump = Continue(Some(unique_name(info.label)))
              stmts.append(k2([jump]))
              stmts
            },
          }
        None =>
          pure([
            Return(
              call(
                to_js_block_expr(callee, ctx),
                vargs.map(v => to_js_cps_expr(v, ctx)) +
                bargs.map(b => argument_to_js(b, ctx)) +
                [
                  to_js_metacont(ks, ctx),
                  requiring_thunk(ctx, c => to_js_cont(k, c)),
                ],
              ),
            ),
          ])
      }
    @cps.Stmt::Invoke(callee, method, vargs, bargs, ks, k) =>
      pure([
        Return(
          method_call(
            to_js_block_expr(callee, ctx),
            member_name_ref(method),
            vargs.map(v => to_js_cps_expr(v, ctx)) +
            bargs.map(b => argument_to_js(b, ctx)) +
            [to_js_metacont(ks, ctx), to_js_cont(k, ctx)],
          ),
        ),
      ])

    // const r = REGION(ks); body
    @cps.Stmt::Region(id, ks, body) =>
      {
        run: fn(k) raise EffektError {
          [
            Const(
              PatternVariable(name_def(id)),
              call(region_fn(), [to_js_metacont(ks, ctx)]),
            ),
          ] +
          (to_js_stmt(body, ctx).run)(k)
        },
      }

    // const x = r.fresh(init); body
    @cps.Stmt::Alloc(id, init, region, body) =>
      {
        run: fn(k) raise EffektError {
          [
            Const(
              PatternVariable(name_def(id)),
              method_call(name_ref(region), JSName::new("fresh"), [
                to_js_cps_expr(init, ctx),
              ]),
            ),
          ] +
          (to_js_stmt(body, ctx).run)(k)
        },
      }

    // const x = VAR(1, ks); body
    @cps.Stmt::Var(id, init, ks, body) =>
      {
        run: fn(k) raise EffektError {
          [
            Const(
              PatternVariable(name_def(id)),
              call(var_fn(), [
                to_js_cps_expr(init, ctx),
                to_js_metacont(ks, ctx),
              ]),
            ),
          ] +
          (to_js_stmt(body, ctx).run)(k)
        },
      }
    @cps.Stmt::Dealloc(_ref, body) => to_js_stmt(body, ctx)

    // const id = ref.value; body
    @cps.Stmt::Get(ref, id, body) =>
      {
        run: fn(k) raise EffektError {
          [
            Const(
              PatternVariable(name_def(id)),
              Member(name_ref(ref), JSName::new("value")),
            ),
          ] +
          (to_js_stmt(body, ctx).run)(k)
        },
      }

    // ref.set(value); body
    @cps.Stmt::Put(ref, value, body) =>
      {
        run: fn(k) raise EffektError {
          [
            ExprStmt(
              method_call(name_ref(ref), JSName::new("set"), [
                to_js_cps_expr(value, ctx),
              ]),
            ),
          ] +
          (to_js_stmt(body, ctx).run)(k)
        },
      }
    @cps.Stmt::Reset(prog, ks, k) =>
      pure([
        Return(
          call(reset_fn(), [
            requiring_thunk(ctx.nonrecursive(prog.ks), c => {
              to_js_block_expr(@cps.Block::BlockLit(prog), c)
            }),
            to_js_metacont(ks, ctx),
            to_js_cont(k, ctx),
          ]),
        ),
      ])
    @cps.Stmt::Shift(prompt, body, ks, k) =>
      pure([
        Return(
          call(shift_fn(), [
            name_ref(prompt),
            requiring_thunk(ctx.nonrecursive(body.ks), c => {
              to_js_block_expr(@cps.Block::BlockLit(body), c)
            }),
            to_js_metacont(ks, ctx),
            to_js_cont(k, ctx),
          ]),
        ),
      ])
    @cps.Stmt::Resume(r, b, ks2, k2) =>
      pure([
        Return(
          call(resume_fn(), [
            name_ref(r),
            to_js_block_expr(@cps.Block::BlockLit(b), ctx.nonrecursive(b.ks)),
            to_js_metacont(ks2, ctx),
            requiring_thunk(ctx, c => to_js_cont(k2, c)),
          ]),
        ),
      ])
    @cps.Stmt::Hole(span) =>
      pure([
        Return(effekt_call("hole", [js_string(span.position().to_string())])),
      ])
  }
}
