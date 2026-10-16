// Tests for the source-to-core transformer.
//
// Since the parser and the namer are not stable yet, the source trees are built
// programmatically and the annotations the transformer reads from the source
// `Context` (resolved symbols, inferred types and captures) are filled in by
// hand, exactly like the namer and the typer would.

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

///|
fn missing() -> @util.Span {
  @util.Span::missing()
}

///|
fn tctx() -> @source.Context {
  @source.Context::new(@source.Config::default())
}

///|
fn id_def(name : String) -> @source.IdDef {
  @source.IdDef::new(name, missing())
}

///|
fn id_ref(name : String) -> @source.IdRef {
  @source.IdRef::new(name, missing())
}

///|
fn var_term(id : @source.IdRef) -> @source.Term {
  @source.mk_term(missing(), @source.Var(id))
}

///|
fn lit_term(v : @source.LiteralValue, t : @symbols.ValueType) -> @source.Term {
  @source.mk_term(missing(), @source.Literal(v, t))
}

///|
fn call_term(
  fun : @source.IdRef,
  vargs : Array[@source.Term],
  bargs : Array[@source.Term],
) -> @source.Term {
  @source.mk_term(
    missing(),
    @source.Call(
      @source.IdTarget(fun),
      [],
      vargs.map(t => @source.ValueArg::unnamed(t)),
      bargs,
    ),
  )
}

///|
fn ret_stmt(t : @source.Term) -> @source.Stmt {
  @source.mk_stmt(missing(), @source.Return(t))
}

///|
fn expr_stmt(t : @source.Term, rest : @source.Stmt) -> @source.Stmt {
  @source.mk_stmt(missing(), @source.ExprStmt(t, rest))
}

///|
fn def_stmt(d : @source.Def, rest : @source.Stmt) -> @source.Stmt {
  @source.mk_stmt(missing(), @source.DefStmt(d, rest))
}

///|
fn value_param(name : String, tpe : @symbols.ValueType) -> @source.ValueParam {
  @source.ValueParam::{ id: id_def(name), tpe: None, is_implicit: false, }
}

///|
fn value_param_sym(name : String, tpe : @symbols.ValueType) -> @symbols.Sym {
  @symbols.Sym::value_param(@symbols.Name::local(name), Some(tpe), missing())
}

///|
fn block_param_sym(
  name : String,
  tpe : @symbols.BlockType,
  capture : @symbols.Sym,
) -> @symbols.Sym {
  @symbols.Sym::block_param(
    @symbols.Name::local(name),
    Some(tpe),
    capture,
    false,
    missing(),
  )
}

///|
fn user_function_sym(name : String) -> @symbols.Sym {
  @symbols.Sym::UserFunction({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local(name),
      decl: missing(),
    },
    tparams: [],
    vparams: [],
    bparams: [],
    annotated_captures: None,
    annotated_result: Some(@symbols.t_unit()),
    annotated_effects: Some(@symbols.Effects::empty()),
  })
}

///|
fn extern_function_sym(
  name : String,
  result : @symbols.ValueType,
  capture : Array[@symbols.Sym],
) -> @symbols.Sym {
  @symbols.Sym::ExternFunction({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local(name),
      decl: missing(),
    },
    tparams: [],
    vparams: [],
    bparams: [],
    result,
    effects: @symbols.Effects::empty(),
    capture,
  })
}

///|
fn fun_def(
  name : String,
  params : Array[@source.ValueParam],
  body : @source.Stmt,
) -> @source.Def {
  @source.mk_def(
    missing(),
    @source.Info::empty(),
    @source.FunDef(id_def(name), [], params, [], None, None, body),
  )
}

///|
fn module_with(defs : Array[@source.Def]) -> @source.ModuleDecl {
  @source.ModuleDecl::{
    uid: @util.fresh_uid(),
    span: missing(),
    path: "test",
    includes: [],
    defs,
    doc: None,
  }
}

///|
/// The body of the `i`th toplevel block definition.
fn body_of(module : @core.ModuleDecl, i : Int32) -> @core.Stmt {
  match module.definitions[i] {
    @core.ToplevelDef(_, @core.BlockLit(lit)) => lit.body
    _ => abort("expected a toplevel block definition")
  }
}

///|
/// Skips the leading `Def`s the pattern matching compiler emits for joinpoints.
fn skip_defs(s : @core.Stmt) -> @core.Stmt {
  match s {
    @core.Def(_, _, rest) => skip_defs(rest)
    _ => s
  }
}

///|
fn only_toplevel_def(module : @core.ModuleDecl) -> @core.Toplevel {
  if module.definitions.length() != 1 {
    abort(
      "expected exactly one toplevel definition, got \{module.definitions.length()}",
    )
  }
  module.definitions[0]
}

// ---------------------------------------------------------------------------
// A toplevel function with a value parameter
// ---------------------------------------------------------------------------

///|
test "toplevel def with a value parameter becomes a BlockLit" {
  let ctx = tctx()
  let f_sym = user_function_sym("id")
  let x_sym = value_param_sym("x", @symbols.t_int())
  let x_param = value_param("x", @symbols.t_int())
  ctx.assign_symbol(x_param.id.uid, x_sym)
  let x_use = id_ref("x")
  ctx.assign_symbol(x_use.uid, x_sym)
  let body = ret_stmt(var_term(x_use))
  let d = fun_def("id", [x_param], body)
  ctx.assign_symbol(d.uid, f_sym)

  let core = @core.transform(module_with([d]), "test", ctx)
  match only_toplevel_def(core) {
    @core.ToplevelDef(id, @core.BlockLit(lit)) => {
      assert_eq(id.uid(), f_sym.uid())
      assert_eq(lit.vparams.length(), 1)
      assert_eq(lit.vparams[0].id.uid(), x_sym.uid())
      assert_eq(lit.cparams.length(), 0)
      assert_true(lit.body is @core.Return(_))
    }
    _ => abort("expected ToplevelDef(id, BlockLit(...))")
  }
}

// ---------------------------------------------------------------------------
// Pure expressions stay pure
// ---------------------------------------------------------------------------

///|
test "1 + 2 stays a pure application without a statement wrapper" {
  let ctx = tctx()
  let add_sym = extern_function_sym("infixAdd", @symbols.t_int(), [])
  let one = lit_term(@source.LInt(1), @symbols.t_int())
  let two = lit_term(@source.LInt(2), @symbols.t_int())
  let add_ref = id_ref("infixAdd")
  ctx.assign_symbol(add_ref.uid, add_sym)
  let call = @source.mk_term(
    missing(),
    @source.Call(
      @source.IdTarget(add_ref),
      [],
      [@source.ValueArg::unnamed(one), @source.ValueArg::unnamed(two)],
      [],
    ),
  )
  let d = fun_def("onePlusTwo", [], ret_stmt(call))
  ctx.assign_symbol(d.uid, user_function_sym("onePlusTwo"))

  let core = @core.transform(module_with([d]), "test", ctx)
  match body_of(core, 0) {
    // a pure call is returned directly, without wrapping it in a Val
    @core.Return(@core.PureApp(callee, targs, vargs)) => {
      assert_eq(callee.id.uid(), add_sym.uid())
      assert_eq(targs.length(), 0)
      assert_eq(vargs.length(), 2)
      assert_true(vargs[0] is @core.Literal(@source.LInt(1), _))
      assert_true(vargs[1] is @core.Literal(@source.LInt(2), _))
    }
    other =>
      abort("expected Return(PureApp(...)), got \{@core.show_core_stmt(other)}")
  }
}

// ---------------------------------------------------------------------------
// Sequencing: val x = f(); g(x)
// ---------------------------------------------------------------------------

///|
test "val x = f(); g(x) nests Let/Val in the right order" {
  let ctx = tctx()
  let f_sym = user_function_sym("f")
  let g_sym = user_function_sym("g")
  let x_sym = value_param_sym("x", @symbols.t_unit())

  // val x = f()
  let f_ref = id_ref("f")
  ctx.assign_symbol(f_ref.uid, f_sym)
  let f_call = @source.mk_term(
    missing(),
    @source.Call(@source.IdTarget(f_ref), [], [], []),
  )
  let val_def = @source.mk_def(
    missing(),
    @source.Info::empty(),
    @source.ValDef(id_def("x"), None, ret_stmt(f_call)),
  )
  ctx.assign_symbol(val_def.uid, x_sym)

  // g(x)
  let g_ref = id_ref("g")
  ctx.assign_symbol(g_ref.uid, g_sym)
  let x_ref = id_ref("x")
  ctx.assign_symbol(x_ref.uid, x_sym)
  let g_call = @source.mk_term(
    missing(),
    @source.Call(
      @source.IdTarget(g_ref),
      [],
      [@source.ValueArg::unnamed(var_term(x_ref))],
      [],
    ),
  )

  let unit = lit_term(@source.LUnit, @symbols.t_unit())
  let body = def_stmt(val_def, expr_stmt(g_call, ret_stmt(unit)))
  let d = fun_def("main", [], body)
  ctx.assign_symbol(d.uid, user_function_sym("main"))

  let core = @core.transform(module_with([d]), "test", ctx)
  match body_of(core, 0) {
    @core.Val(v, @core.App(callee_f, _, _, _), rest) => {
      assert_eq(v.uid(), x_sym.uid())
      assert_true(callee_f is @core.BlockVar(_))
      match callee_f {
        @core.BlockVar(bv) => assert_eq(bv.id.uid(), f_sym.uid())
        _ => abort("unreachable")
      }
      // g(x) is bound to a temporary and the result discarded
      match rest {
        @core.Val(_, @core.App(callee_g, _, vargs, _), tail) => {
          match callee_g {
            @core.BlockVar(bv) => {
              assert_eq(bv.id.uid(), g_sym.uid())
              assert_eq(vargs.length(), 1)
              assert_true(
                vargs[0] is @core.ValueVar(id, _) && id.uid() == x_sym.uid(),
              )
            }
            _ => abort("expected a block variable")
          }
          assert_true(tail is @core.Return(_))
        }
        other =>
          abort("expected a nested Val, got \{@core.show_core_stmt(other)}")
      }
    }
    other =>
      abort(
        "expected Val(x, App(f, ...), ...), got \{@core.show_core_stmt(other)}",
      )
  }
}

// ---------------------------------------------------------------------------
// if / else
// ---------------------------------------------------------------------------

///|
test "if/else becomes Stmt.If" {
  let ctx = tctx()
  let c_sym = value_param_sym("c", @symbols.t_bool())
  let c_ref = id_ref("c")
  ctx.assign_symbol(c_ref.uid, c_sym)
  let bool_guard = @source.mk_guard(
    missing(),
    @source.BooleanGuard(var_term(c_ref)),
  )
  let if_term = @source.mk_term(
    missing(),
    @source.If(
      [bool_guard],
      ret_stmt(lit_term(@source.LInt(1), @symbols.t_int())),
      ret_stmt(lit_term(@source.LInt(2), @symbols.t_int())),
    ),
  )
  let d = fun_def(
    "choose",
    [value_param("c", @symbols.t_bool())],
    ret_stmt(if_term),
  )
  ctx.assign_symbol(d.uid, user_function_sym("choose"))

  let core = @core.transform(module_with([d]), "test", ctx)
  match body_of(core, 0) {
    @core.If(cond, thn, els) => {
      assert_true(cond is @core.ValueVar(id, _) && id.uid() == c_sym.uid())
      assert_true(thn is @core.Return(@core.Literal(@source.LInt(1), _)))
      assert_true(els is @core.Return(@core.Literal(@source.LInt(2), _)))
    }
    other => abort("expected Stmt.If, got \{@core.show_core_stmt(other)}")
  }
}

// ---------------------------------------------------------------------------
// match on a two-constructor data type
// ---------------------------------------------------------------------------

///|
test "match on a two-constructor data type produces tags 0 and 1" {
  let ctx = tctx()
  // type Bool2 { TT(); FF() }
  let data_sym = @symbols.Sym::DataType({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local("Bool2"),
      decl: missing(),
    },
    tparams: [],
    constructors: [],
  })
  let tt_sym = @symbols.Sym::Constructor({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local("TT"),
      decl: missing(),
    },
    tparams: [],
    fields: [],
    tpe: data_sym,
  })
  let ff_sym = @symbols.Sym::Constructor({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local("FF"),
      decl: missing(),
    },
    tparams: [],
    fields: [],
    tpe: data_sym,
  })
  match data_sym {
    @symbols.Sym::DataType(d) => d.constructors = [tt_sym, ff_sym]
    _ => abort("unreachable")
  }

  let scrutinee_sym = value_param_sym("b", @symbols.ValueTypeApp(data_sym, []))
  let b_ref = id_ref("b")
  ctx.assign_symbol(b_ref.uid, scrutinee_sym)

  let tt_ref = id_ref("TT")
  ctx.assign_symbol(tt_ref.uid, tt_sym)
  let ff_ref = id_ref("FF")
  ctx.assign_symbol(ff_ref.uid, ff_sym)

  let clause_tt = @source.MatchClause::{
    uid: @util.fresh_uid(),
    span: missing(),
    pattern: @source.mk_pattern(missing(), @source.TagPattern(tt_ref, [])),
    guards: [],
    body: ret_stmt(lit_term(@source.LInt(1), @symbols.t_int())),
  }
  let clause_ff = @source.MatchClause::{
    uid: @util.fresh_uid(),
    span: missing(),
    pattern: @source.mk_pattern(missing(), @source.TagPattern(ff_ref, [])),
    guards: [],
    body: ret_stmt(lit_term(@source.LInt(2), @symbols.t_int())),
  }
  let match_term = @source.mk_term(
    missing(),
    @source.Match([var_term(b_ref)], [clause_tt, clause_ff], None),
  )
  ctx.assign_value_type(match_term.uid, @symbols.t_int())

  let d = fun_def(
    "which",
    [value_param("b", @symbols.ValueTypeApp(data_sym, []))],
    ret_stmt(match_term),
  )
  ctx.assign_symbol(d.uid, user_function_sym("which"))

  // the data declaration, so that the tags can be computed from the module
  let data_def = @source.mk_def(
    missing(),
    @source.Info::empty(),
    @source.DataDef(id_def("Bool2"), [], [
      @source.Constructor::{
        uid: @util.fresh_uid(),
        span: missing(),
        id: id_def("TT"),
        tparams: [],
        params: [],
        doc: None,
      },
      @source.Constructor::{
        uid: @util.fresh_uid(),
        span: missing(),
        id: id_def("FF"),
        tparams: [],
        params: [],
        doc: None,
      },
    ]),
  )
  ctx.assign_symbol(data_def.uid, data_sym)

  let core = @core.transform(module_with([data_def, d]), "test", ctx)
  // the joinpoints of the match compiler are emitted as leading Defs
  match skip_defs(body_of(core, 0)) {
    @core.Match(scrutinee, tpe, clauses, default) => {
      assert_true(
        scrutinee is @core.ValueVar(id, _) && id.uid() == scrutinee_sym.uid(),
      )
      assert_eq(
        @core.show_core_value_type(tpe),
        @core.show_core_value_type(@symbols.t_int()),
      )
      assert_eq(clauses.length(), 2)
      assert_eq(clauses[0].tag.uid(), tt_sym.uid())
      assert_eq(clauses[1].tag.uid(), ff_sym.uid())
      assert_true(default is None)
      // the tags the JS backend relies on are the indices of the constructors
      // in their data declaration
      assert_eq(core.declarations.length(), 1)
      let dctx = @core.DeclarationContext::new(core.declarations, core.externs)
      assert_eq(dctx.get_constructor_tag(clauses[0].tag), 0)
      assert_eq(dctx.get_constructor_tag(clauses[1].tag), 1)
    }
    other => abort("expected Stmt.Match, got \{@core.show_core_stmt(other)}")
  }
}

// ---------------------------------------------------------------------------
// try / handle
// ---------------------------------------------------------------------------

///|
test "try/handle becomes Reset/Shift" {
  let ctx = tctx()
  // interface Op { def op(): Int }
  let op_iface = @symbols.Sym::Interface({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local("Op"),
      decl: missing(),
    },
    tparams: [],
    operations: [],
  })
  let op_sym = @symbols.Sym::Operation({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local("op"),
      decl: missing(),
    },
    tparams: [],
    vparams: [],
    bparams: [],
    result_type: @symbols.t_int(),
    effects: @symbols.Effects::empty(),
    interface: op_iface,
  })
  match op_iface {
    @symbols.Sym::Interface(i) => i.operations = [op_sym]
    _ => abort("unreachable")
  }

  // the capability bound by the handler
  let cap_sym = block_param_sym(
    "cap",
    @symbols.InterfaceType(op_iface, []),
    @symbols.Sym::capture_param(@symbols.Name::local("cap")),
  )
  let cap_id = id_def("cap")
  ctx.assign_symbol(cap_id.uid, cap_sym)

  // the continuation: (Int) => Int
  let resume_sym = block_param_sym(
    "resume",
    @symbols.FunctionType(
      [],
      [],
      [@symbols.t_int()],
      [],
      @symbols.t_int(),
      @symbols.Effects::empty(),
    ),
    @symbols.Sym::capture_param(@symbols.Name::local("resume")),
  )
  let resume_id = id_def("resume")
  ctx.assign_symbol(resume_id.uid, resume_sym)

  let op_ref = id_ref("op")
  ctx.assign_symbol(op_ref.uid, op_sym)
  let op_clause = @source.OpClause::{
    uid: @util.fresh_uid(),
    span: missing(),
    id: op_ref,
    tparams: [],
    vparams: [],
    bparams: [],
    ret: None,
    body: ret_stmt(lit_term(@source.LInt(1), @symbols.t_int())),
    resume: resume_id,
  }
  let implementation = @source.Implementation::{
    uid: @util.fresh_uid(),
    span: missing(),
    interface: @source.mk_type(missing(), @source.TypeRef(id_ref("Op"), [])),
    clauses: [op_clause],
  }
  ctx.assign_block_type(
    implementation.uid,
    @symbols.InterfaceType(op_iface, []),
  )

  let cap_param = @source.BlockParam::{
    id: cap_id,
    tpe: None,
    is_implicit: false,
  }
  let handler = @source.Handler::{
    uid: @util.fresh_uid(),
    span: missing(),
    capability: Some(cap_param),
    implementation,
  }

  // the body: cap.op()  (capability passing turned `do op()` into a method call)
  let cap_ref = id_ref("cap")
  ctx.assign_symbol(cap_ref.uid, cap_sym)
  let method_call = @source.mk_term(
    missing(),
    @source.MethodCall(var_term(cap_ref), op_ref, [], [], []),
  )
  ctx.assign_block_type(method_call.uid, @symbols.InterfaceType(op_iface, []))
  let receiver = match method_call.kind {
    @source.MethodCall(r, _, _, _, _) => r
    _ => abort("unreachable")
  }
  ctx.assign_block_type(receiver.uid, @symbols.InterfaceType(op_iface, []))
  let prog = expr_stmt(
    method_call,
    ret_stmt(lit_term(@source.LUnit, @symbols.t_unit())),
  )
  ctx.assign_value_type(prog.uid, @symbols.t_int())

  let try_term = @source.mk_term(missing(), @source.TryHandle(prog, [handler]))
  let d = fun_def("run", [], ret_stmt(try_term))
  ctx.assign_symbol(d.uid, user_function_sym("run"))

  let core = @core.transform(module_with([d]), "test", ctx)
  match body_of(core, 0) {
    @core.Reset(lit) => {
      assert_eq(lit.cparams.length(), 1)
      assert_eq(lit.bparams.length(), 1)
      // the prompt is bound by the reset's block parameter, whose capture is
      // the reset's capture parameter
      assert_eq(lit.cparams[0].uid(), lit.bparams[0].capt.to_array()[0].uid())
      match lit.body {
        @core.Def(id, @core.New(implementation), _) => {
          assert_eq(id.uid(), cap_sym.uid())
          assert_eq(implementation.operations.length(), 1)
          assert_eq(implementation.operations[0].name.uid(), op_sym.uid())
          // the operation body is wrapped in a Shift on the prompt
          match implementation.operations[0].body {
            @core.Shift(prompt, k, shared) => {
              assert_eq(prompt.id.uid(), lit.bparams[0].id.uid())
              // the resumption is eta-expanded into a block definition that
              // resumes on the captured continuation `k`
              match shared {
                @core.Def(resume, @core.BlockLit(resume_lit), _) => {
                  assert_eq(resume.uid(), resume_sym.uid())
                  assert_eq(resume_lit.vparams.length(), 1)
                  match resume_lit.body {
                    @core.Resume(k_var, @core.Return(@core.ValueVar(arg, _))) => {
                      assert_eq(k_var.id.uid(), k.id.uid())
                      assert_eq(arg.uid(), resume_lit.vparams[0].id.uid())
                    }
                    other =>
                      abort(
                        "expected Resume(k, Return(a)), got \{@core.show_core_stmt(other)}",
                      )
                  }
                }
                other =>
                  abort(
                    "expected Def(resume, BlockLit(...)), got \{@core.show_core_stmt(other)}",
                  )
              }
            }
            other =>
              abort("expected Stmt.Shift, got \{@core.show_core_stmt(other)}")
          }
        }
        other =>
          abort(
            "expected Def(cap, New(...)), got \{@core.show_core_stmt(other)}",
          )
      }
    }
    other => abort("expected Stmt.Reset, got \{@core.show_core_stmt(other)}")
  }
}

// ---------------------------------------------------------------------------
// resume: unidirectional (value resume) and bidirectional (block resume)
// ---------------------------------------------------------------------------

///|
/// The pieces of a `try { ... } with Op { def op(...) = ... }` fixture.
pub(all) struct HandlerFixture {
  term : @source.Term
  op_sym : @symbols.Sym
  cap_sym : @symbols.Sym
  implementation : @source.Implementation
}

///|
/// Builds `try { cap.op(...) } with Op { def op(<vparams>) = <body> }`.
///
/// `resume_type` is the block type the typer annotates on the `resume` binder
/// (see `Typer.check_op_clause`): `(T) => Answer` for a uni-directional resume
/// and `({...} => T) => Answer` for a bi-directional one.
fn handler_fixture(
  ctx : @source.Context,
  resume_id : @source.IdDef,
  resume_sym : @symbols.Sym,
  resume_type : @symbols.BlockType,
  vparams : Array[@source.ValueParam],
  clause_body : @source.Stmt,
) -> HandlerFixture {
  // interface Op { def op(...): Int }
  let op_iface = @symbols.Sym::Interface({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local("Op"),
      decl: missing(),
    },
    tparams: [],
    operations: [],
  })
  let op_sym = @symbols.Sym::Operation({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local("op"),
      decl: missing(),
    },
    tparams: [],
    vparams: [],
    bparams: [],
    result_type: @symbols.t_int(),
    effects: @symbols.Effects::empty(),
    interface: op_iface,
  })
  match op_iface {
    @symbols.Sym::Interface(i) => i.operations = [op_sym]
    _ => abort("unreachable")
  }

  // the capability bound by the handler
  let cap_sym = block_param_sym(
    "cap",
    @symbols.InterfaceType(op_iface, []),
    @symbols.Sym::capture_param(@symbols.Name::local("cap")),
  )
  let cap_id = id_def("cap")
  ctx.assign_symbol(cap_id.uid, cap_sym)

  ctx.assign_symbol(resume_id.uid, resume_sym)
  ctx.assign_block_type(resume_sym.uid(), resume_type)

  let op_ref = id_ref("op")
  ctx.assign_symbol(op_ref.uid, op_sym)
  let op_clause = @source.OpClause::{
    uid: @util.fresh_uid(),
    span: missing(),
    id: op_ref,
    tparams: [],
    vparams,
    bparams: [],
    ret: None,
    body: clause_body,
    resume: resume_id,
  }
  let implementation = @source.Implementation::{
    uid: @util.fresh_uid(),
    span: missing(),
    interface: @source.mk_type(missing(), @source.TypeRef(id_ref("Op"), [])),
    clauses: [op_clause],
  }
  ctx.assign_block_type(
    implementation.uid,
    @symbols.InterfaceType(op_iface, []),
  )

  let cap_param = @source.BlockParam::{
    id: cap_id,
    tpe: None,
    is_implicit: false,
  }
  let handler = @source.Handler::{
    uid: @util.fresh_uid(),
    span: missing(),
    capability: Some(cap_param),
    implementation,
  }

  // the body of the `try`: `cap.op()` (capability passing turned `do op()`
  // into a method call)
  let cap_ref = id_ref("cap")
  ctx.assign_symbol(cap_ref.uid, cap_sym)
  let method_call = @source.mk_term(
    missing(),
    @source.MethodCall(var_term(cap_ref), op_ref, [], [], []),
  )
  ctx.assign_block_type(method_call.uid, @symbols.InterfaceType(op_iface, []))
  let receiver = match method_call.kind {
    @source.MethodCall(r, _, _, _, _) => r
    _ => abort("unreachable")
  }
  ctx.assign_block_type(receiver.uid, @symbols.InterfaceType(op_iface, []))
  let prog = expr_stmt(
    method_call,
    ret_stmt(lit_term(@source.LInt(42), @symbols.t_int())),
  )
  ctx.assign_value_type(prog.uid, @symbols.t_int())

  {
    term: @source.mk_term(missing(), @source.TryHandle(prog, [handler])),
    op_sym,
    cap_sym,
    implementation,
  }
}

///|
/// The `Implementation` of the single handler of a fixture's `Reset`.
fn implementation_of(core : @core.ModuleDecl) -> @core.Implementation {
  match skip_defs(body_of(core, 0)) {
    @core.Reset(lit) =>
      match lit.body {
        @core.Def(_, @core.New(implementation), _) => implementation
        other =>
          abort(
            "expected Def(cap, New(...)), got \{@core.show_core_stmt(other)}",
          )
      }
    other => abort("expected Stmt.Reset, got \{@core.show_core_stmt(other)}")
  }
}

///|
test "unidirectional resume of an operation with a value parameter" {
  let ctx = tctx()
  // def op(x: Int) = resume(x)
  let x_sym = value_param_sym("x", @symbols.t_int())
  let x_param = @source.ValueParam::{
    id: id_def("x"),
    tpe: None,
    is_implicit: false,
  }
  ctx.assign_symbol(x_param.id.uid, x_sym)
  let resume_sym = @symbols.Sym::resume_param()
  let resume_ref = id_ref("resume")
  ctx.assign_symbol(resume_ref.uid, resume_sym)
  let x_use = id_ref("x")
  ctx.assign_symbol(x_use.uid, x_sym)
  let clause_body = ret_stmt(call_term(resume_ref, [var_term(x_use)], []))
  // the typer annotates the resumption as `(Int) => Int`
  let fx = handler_fixture(
    ctx,
    id_def("resume"),
    resume_sym,
    @symbols.FunctionType(
      [],
      [],
      [@symbols.t_int()],
      [],
      @symbols.t_int(),
      @symbols.Effects::empty(),
    ),
    [x_param],
    clause_body,
  )
  let d = fun_def("run", [], ret_stmt(fx.term))
  ctx.assign_symbol(d.uid, user_function_sym("run"))

  let core = @core.transform(module_with([d]), "test", ctx)
  let implementation = implementation_of(core)
  assert_eq(implementation.operations[0].name.uid(), fx.op_sym.uid())
  match implementation.operations[0].body {
    @core.Shift(prompt, k, shared) => {
      assert_eq(implementation.operations[0].cparams.length(), 0)
      assert_eq(implementation.operations[0].bparams.length(), 0)
      // the prompt and the continuation are distinct binders
      assert_true(prompt.id.uid() != k.id.uid())
      // [[ def resume(a) = resume(k) { return a } ]]
      match shared {
        @core.Def(resume, @core.BlockLit(resume_lit), body) => {
          assert_eq(resume.uid(), resume_sym.uid())
          assert_eq(resume_lit.vparams.length(), 1)
          assert_eq(resume_lit.bparams.length(), 0)
          match resume_lit.body {
            @core.Resume(k_var, @core.Return(@core.ValueVar(arg, _))) => {
              assert_eq(k_var.id.uid(), k.id.uid())
              assert_eq(arg.uid(), resume_lit.vparams[0].id.uid())
            }
            other =>
              abort(
                "expected Resume(k, Return(a)), got \{@core.show_core_stmt(other)}",
              )
          }
          // the clause body calls resume(x)
          match body {
            @core.App(callee, _, vargs, _) => {
              assert_eq(vargs.length(), 1)
              assert_true(
                vargs[0] is @core.ValueVar(id, _) && id.uid() == x_sym.uid(),
              )
              match callee {
                @core.BlockVar(bv) => assert_eq(bv.id.uid(), resume_sym.uid())
                _ => abort("expected a block variable")
              }
            }
            other =>
              abort(
                "expected App(resume, [x]), got \{@core.show_core_stmt(other)}",
              )
          }
        }
        other =>
          abort(
            "expected Def(resume, BlockLit(...)), got \{@core.show_core_stmt(other)}",
          )
      }
    }
    other => abort("expected Stmt.Shift, got \{@core.show_core_stmt(other)}")
  }
}

///|
test "bidirectional resume of an operation" {
  let ctx = tctx()
  // the continuation takes a block: `({Int} => Int) => Int`
  let k_capt = @symbols.Sym::capture_param(@symbols.Name::local("k"))
  let inner_param = @symbols.FunctionType(
    [],
    [],
    [@symbols.t_int()],
    [],
    @symbols.t_int(),
    @symbols.Effects::empty(),
  )
  let inner = @symbols.FunctionType(
    [],
    [@symbols.CaptureSetOf([k_capt])],
    [],
    [inner_param],
    @symbols.t_int(),
    @symbols.Effects::empty(),
  )
  let resume_capt = @symbols.Sym::capture_param(
    @symbols.Name::local("resumeBlock"),
  )
  let resume_type = @symbols.FunctionType(
    [],
    [@symbols.CaptureSetOf([resume_capt])],
    [],
    [inner],
    @symbols.t_int(),
    @symbols.Effects::empty(),
  )

  // def op() = resume { k => k(1) }
  let resume_sym = @symbols.Sym::resume_param()
  let resume_ref = id_ref("resume")
  ctx.assign_symbol(resume_ref.uid, resume_sym)
  let k_sym = value_param_sym("k", @symbols.t_int())
  let k_ref = id_ref("k")
  ctx.assign_symbol(k_ref.uid, k_sym)
  let k_param = @source.ValueParam::{
    id: id_def("k"),
    tpe: None,
    is_implicit: false,
  }
  ctx.assign_symbol(k_param.id.uid, k_sym)
  let block_arg = @source.mk_term(
    missing(),
    @source.BlockLiteral([], [k_param], [], ret_stmt(var_term(k_ref))),
  )
  let clause_body = ret_stmt(call_term(resume_ref, [], [block_arg]))

  let fx = handler_fixture(
    ctx,
    id_def("resume"),
    resume_sym,
    resume_type,
    [],
    clause_body,
  )
  let d = fun_def("run", [], ret_stmt(fx.term))
  ctx.assign_symbol(d.uid, user_function_sym("run"))

  let core = @core.transform(module_with([d]), "test", ctx)
  let implementation = implementation_of(core)
  let op = implementation.operations[0]
  // one capture parameter and one block parameter, both coming from the type
  // of the continuation
  assert_eq(op.cparams.length(), 1)
  assert_eq(op.cparams[0].uid(), k_capt.uid())
  assert_eq(op.bparams.length(), 1)

  match op.body {
    @core.Shift(_, k, shared) =>
      match shared {
        @core.Def(resume, @core.BlockLit(resume_lit), _) => {
          assert_eq(resume.uid(), resume_sym.uid())
          // [[ def resume {h} = resume(k) { h {g} } ]]
          assert_eq(resume_lit.cparams.length(), 1)
          assert_eq(resume_lit.vparams.length(), 0)
          assert_eq(resume_lit.bparams.length(), 1)
          assert_eq(
            resume_lit.cparams[0].uid(),
            resume_lit.bparams[0].capt.to_array()[0].uid(),
          )
          match resume_lit.body {
            // the argument `h` is applied to the capabilities `g` bound by the
            // operation
            @core.Resume(k_var, @core.App(callee, _, _, bargs)) => {
              assert_eq(k_var.id.uid(), k.id.uid())
              assert_eq(bargs.length(), 1)
              match (callee, bargs[0]) {
                (@core.BlockVar(h), @core.BlockVar(g)) => {
                  assert_eq(h.id.uid(), resume_lit.bparams[0].id.uid())
                  assert_eq(g.id.uid(), op.bparams[0].id.uid())
                }
                _ => abort("expected block variables")
              }
            }
            other =>
              abort(
                "expected Resume(k, App(h, [g])), got \{@core.show_core_stmt(other)}",
              )
          }
        }
        other =>
          abort(
            "expected Def(resume, BlockLit(...)), got \{@core.show_core_stmt(other)}",
          )
      }
    other => abort("expected Stmt.Shift, got \{@core.show_core_stmt(other)}")
  }
}

// ---------------------------------------------------------------------------
// var: Stmt.Var / Stmt.Get / Stmt.Put
// ---------------------------------------------------------------------------

///|
test "var and assignment become Var/Get/Put" {
  let ctx = tctx()
  let add_sym = extern_function_sym("infixAdd", @symbols.t_int(), [])
  let add_ref = id_ref("infixAdd")
  ctx.assign_symbol(add_ref.uid, add_sym)

  let var_capture = @symbols.Sym::capture_param(@symbols.Name::local("x"))
  let var_sym = @symbols.Sym::VarBinder({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local("x"),
      decl: missing(),
    },
    tpe: Some(@symbols.t_int()),
    capture: var_capture,
  })

  // var x = 1
  let var_def = @source.mk_def(
    missing(),
    @source.Info::empty(),
    @source.VarDef(
      id_def("x"),
      None,
      ret_stmt(lit_term(@source.LInt(1), @symbols.t_int())),
    ),
  )
  ctx.assign_symbol(var_def.uid, var_sym)

  // x = x + 1
  let x_write = id_ref("x")
  ctx.assign_symbol(x_write.uid, var_sym)
  let x_read = id_ref("x")
  ctx.assign_symbol(x_read.uid, var_sym)
  let add_call = @source.mk_term(
    missing(),
    @source.Call(
      @source.IdTarget(add_ref),
      [],
      [
        @source.ValueArg::unnamed(var_term(x_read)),
        @source.ValueArg::unnamed(lit_term(@source.LInt(1), @symbols.t_int())),
      ],
      [],
    ),
  )
  let assign = @source.mk_term(missing(), @source.Assign(x_write, add_call))

  // the tail reads x again
  let x_tail = id_ref("x")
  ctx.assign_symbol(x_tail.uid, var_sym)

  let body = def_stmt(var_def, expr_stmt(assign, ret_stmt(var_term(x_tail))))
  let d = fun_def("main", [], body)
  ctx.assign_symbol(d.uid, user_function_sym("main"))

  let core = @core.transform(module_with([d]), "test", ctx)
  // the initializer is bound to a temporary first: `let v = 1; var x = v; ...`
  match body_of(core, 0) {
    @core.Let(_, @core.Literal(@source.LInt(1), _), rest) =>
      match rest {
        @core.Var(id, init, capture, body) => {
          assert_eq(id.uid(), var_sym.uid())
          assert_eq(capture.uid(), var_capture.uid())
          assert_true(init is @core.ValueVar(_, _))
          // reading `x` for the right-hand side emits a Get ...
          match body {
            @core.Get(s1, _, ref1, capt1, rest1) => {
              assert_eq(ref1.uid(), var_sym.uid())
              assert_eq(capt1.to_array()[0].uid(), var_capture.uid())
              // ... then the assignment emits a Put
              match rest1 {
                @core.Put(ref2, capt2, value, rest2) => {
                  assert_eq(ref2.uid(), var_sym.uid())
                  assert_eq(capt2.to_array()[0].uid(), var_capture.uid())
                  match value {
                    @core.PureApp(callee, _, vargs) => {
                      assert_eq(callee.id.uid(), add_sym.uid())
                      assert_eq(vargs.length(), 2)
                      assert_true(
                        vargs[0] is @core.ValueVar(id, _) &&
                        id.uid() == s1.uid(),
                      )
                    }
                    other =>
                      abort(
                        "expected PureApp(infixAdd, ...), got \{@core.show_core_expr(other)}",
                      )
                  }
                  // the tail reads `x` again
                  match rest2 {
                    @core.Get(
                      s2,
                      _,
                      ref3,
                      _,
                      @core.Return(@core.ValueVar(result, _))
                    ) => {
                      assert_eq(ref3.uid(), var_sym.uid())
                      assert_eq(result.uid(), s2.uid())
                    }
                    other =>
                      abort(
                        "expected Get(..., Return(...)), got \{@core.show_core_stmt(other)}",
                      )
                  }
                }
                other =>
                  abort("expected Stmt.Put, got \{@core.show_core_stmt(other)}")
              }
            }
            other =>
              abort("expected Stmt.Get, got \{@core.show_core_stmt(other)}")
          }
        }
        other => abort("expected Stmt.Var, got \{@core.show_core_stmt(other)}")
      }
    other => abort("expected Stmt.Let, got \{@core.show_core_stmt(other)}")
  }
}

// ---------------------------------------------------------------------------
// regions: Stmt.Region / Stmt.Alloc
// ---------------------------------------------------------------------------

///|
test "regions become Region and Alloc" {
  let ctx = tctx()
  let region_sym = @symbols.Sym::lexical_region(
    @symbols.Name::local("r"),
    missing(),
  )
  let region_id = id_def("r")
  ctx.assign_symbol(region_id.uid, region_sym)

  // region r { () }
  let region_term = @source.mk_term(
    missing(),
    @source.Region(
      region_id,
      ret_stmt(lit_term(@source.LUnit, @symbols.t_unit())),
    ),
  )

  // reg r2 = 1; region r { () }
  let r2_sym = @symbols.Sym::RegBinder({
    base: {
      uid: @util.fresh_uid(),
      name: @symbols.Name::local("r2"),
      decl: missing(),
    },
    tpe: Some(@symbols.t_int()),
    region: region_sym,
  })
  let reg_def = @source.mk_def(
    missing(),
    @source.Info::empty(),
    @source.RegDef(
      id_def("r2"),
      None,
      id_ref("r"),
      ret_stmt(lit_term(@source.LInt(1), @symbols.t_int())),
    ),
  )
  ctx.assign_symbol(reg_def.uid, r2_sym)

  let body = def_stmt(reg_def, ret_stmt(region_term))
  let d = fun_def("main", [], body)
  ctx.assign_symbol(d.uid, user_function_sym("main"))

  let core = @core.transform(module_with([d]), "test", ctx)
  match body_of(core, 0) {
    @core.Let(_, @core.Literal(@source.LInt(1), _), rest) =>
      match rest {
        @core.Alloc(id, init, region, body) => {
          assert_eq(id.uid(), r2_sym.uid())
          assert_true(init is @core.ValueVar(_, _))
          assert_eq(region.uid(), region_sym.uid())
          match body {
            @core.Region(lit) => {
              // the region is bound by a block parameter whose capture is the
              // block literal's capture parameter
              assert_eq(lit.cparams.length(), 1)
              assert_eq(lit.bparams.length(), 1)
              assert_eq(lit.bparams[0].id.uid(), region_sym.uid())
              assert_eq(
                lit.cparams[0].uid(),
                lit.bparams[0].capt.to_array()[0].uid(),
              )
              assert_true(
                lit.body is @core.Return(@core.Literal(@source.LUnit, _)),
              )
            }
            other =>
              abort("expected Stmt.Region, got \{@core.show_core_stmt(other)}")
          }
        }
        other =>
          abort("expected Stmt.Alloc, got \{@core.show_core_stmt(other)}")
      }
    other => abort("expected Stmt.Let, got \{@core.show_core_stmt(other)}")
  }
}
