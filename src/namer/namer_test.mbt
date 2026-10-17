// Tests for the namer.
//
// The trees are built programmatically with the smart constructors of
// `src/source/tree.mbt`, so these tests do not depend on the parser.

// ---------------------------------------------------------------------------
// Helpers for building trees
// ---------------------------------------------------------------------------

///|
fn sp() -> @util.Span {
  @util.Span::missing()
}

///|
fn fresh_context() -> @source.Context {
  @source.Context::new(@source.Config::default())
}

///|
fn id_def(name : String) -> @source.IdDef {
  @source.IdDef::new(name, sp())
}

///|
fn id_ref(name : String) -> @source.IdRef {
  @source.IdRef::new(name, sp())
}

///|
fn id_ref_qualified(path : Array[String], name : String) -> @source.IdRef {
  @source.IdRef::qualified(path, name, sp())
}

///|
fn vparam(id : @source.IdDef, tpe : @source.TypeTree?) -> @source.ValueParam {
  { id, tpe, is_implicit: false, }
}

///|
fn type_ref(name : String) -> @source.TypeTree {
  @source.mk_type(sp(), @source.TypeKind::TypeRef(id_ref(name), []))
}

///|
/// A type tree annotated with a pure effect set, i.e. `T / {}`.
fn pure(tpe : @source.TypeTree) -> @source.TypeTree {
  @source.mk_type(
    sp(),
    @source.TypeKind::Effectful(tpe, @source.EffectsTree::pure(sp())),
  )
}

///|
fn int_lit(n : Int32) -> @source.Term {
  @source.mk_term(
    sp(),
    @source.TermKind::Literal(@source.LiteralValue::LInt(n), @symbols.t_int()),
  )
}

///|
fn var_ref(name : String) -> @source.Term {
  @source.mk_term(sp(), @source.TermKind::Var(id_ref(name)))
}

///|
fn call(name : String, args : Array[@source.ValueArg]) -> @source.Term {
  @source.mk_term(
    sp(),
    @source.TermKind::Call(
      @source.CallTarget::IdTarget(id_ref(name)),
      [],
      args,
      [],
    ),
  )
}

///|
fn call_qualified(
  path : Array[String],
  name : String,
  args : Array[@source.ValueArg],
) -> @source.Term {
  @source.mk_term(
    sp(),
    @source.TermKind::Call(
      @source.CallTarget::IdTarget(id_ref_qualified(path, name)),
      [],
      args,
      [],
    ),
  )
}

///|
fn do_op(name : String, args : Array[@source.ValueArg]) -> @source.Term {
  @source.mk_term(sp(), @source.TermKind::Do(id_ref(name), [], args, []))
}

///|
fn arg(term : @source.Term) -> @source.ValueArg {
  @source.ValueArg::unnamed(term)
}

///|
fn returns(term : @source.Term) -> @source.Stmt {
  @source.mk_stmt(sp(), @source.StmtKind::Return(term))
}

///|
fn expr(term : @source.Term, rest : @source.Stmt) -> @source.Stmt {
  @source.mk_stmt(sp(), @source.StmtKind::ExprStmt(term, rest))
}

///|
fn fun_def(
  id : @source.IdDef,
  params : Array[@source.ValueParam],
  annot : @source.TypeTree?,
  body : @source.Stmt,
) -> @source.Def {
  @source.mk_def(
    sp(),
    @source.Info::empty(),
    @source.DefKind::FunDef(id, [], params, [], None, annot, body),
  )
}

///|
fn val_def(id : @source.IdDef, binding : @source.Stmt) -> @source.Def {
  @source.mk_def(
    sp(),
    @source.Info::empty(),
    @source.DefKind::ValDef(id, None, binding),
  )
}

///|
fn module_decl(
  path : String,
  includes : Array[@source.Include],
  defs : Array[@source.Def],
) -> @source.ModuleDecl {
  { uid: @util.fresh_uid(), span: sp(), path, includes, defs, doc: None, }
}

// ---------------------------------------------------------------------------
// Helpers for inspecting the result
// ---------------------------------------------------------------------------

///|
fn resolve_ok(
  module : @source.ModuleDecl,
  context : @source.Context,
) -> @namer.ResolvedModule? {
  resolve_with(module, context, Map([]))
}

///|
fn resolve_with(
  module : @source.ModuleDecl,
  context : @source.Context,
  deps : Map[String, @namer.ResolvedModule],
) -> @namer.ResolvedModule? {
  Some(@namer.resolve_module(module, context, deps)) catch {
    _ => None
  }
}

///|
fn messages(context : @source.Context) -> String {
  context.messages.map(m => m.render()).join("\n")
}

///|
fn same_symbol(context : @source.Context, a_uid : Int32, b_uid : Int32) -> Bool {
  match (context.symbol_of(a_uid), context.symbol_of(b_uid)) {
    (Some(a), Some(b)) => a.uid() == b.uid()
    _ => false
  }
}

///|
/// The kind of the symbol attached to a node, for readable assertions.
fn symbol_kind(context : @source.Context, uid : Int32) -> String {
  match context.symbol_of(uid) {
    Some(sym) =>
      match sym {
        @symbols.Sym::ValueParam(_) => "ValueParam"
        @symbols.Sym::ValBinder(_) => "ValBinder"
        @symbols.Sym::VarBinder(_) => "VarBinder"
        @symbols.Sym::BlockParam(_) => "BlockParam"
        @symbols.Sym::Hole(_) => "Hole"
        @symbols.Sym::UserFunction(_) => "UserFunction"
        @symbols.Sym::ResumeParam(_) => "ResumeParam"
        @symbols.Sym::DefBinder(_) => "DefBinder"
        @symbols.Sym::CallTarget(_) => "CallTarget"
        @symbols.Sym::Operation(_) => "Operation"
        @symbols.Sym::Constructor(_) => "Constructor"
        @symbols.Sym::Field(_) => "Field"
        @symbols.Sym::TypeParam(_) => "TypeParam"
        @symbols.Sym::TypeAlias(_) => "TypeAlias"
        @symbols.Sym::DataType(_) => "DataType"
        @symbols.Sym::Record(_) => "Record"
        @symbols.Sym::Interface(_) => "Interface"
        @symbols.Sym::CaptureParam(_) => "CaptureParam"
        _ => "other"
      }
    None => "none"
  }
}

///|
/// Is the symbol of `uid` a call target that contains `sym`?
fn call_target_contains(
  context : @source.Context,
  uid : Int32,
  sym : @symbols.Sym,
) -> Bool {
  match context.symbol_of(uid) {
    Some(@symbols.Sym::CallTarget(target)) =>
      target.symbols.any(group => group.any(s => s.uid() == sym.uid()))
    _ => false
  }
}

///|
fn is_user_function_named(
  context : @source.Context,
  uid : Int32,
  path : Array[String],
  name : String,
) -> Bool {
  match context.symbol_of(uid) {
    Some(@symbols.Sym::UserFunction(f)) =>
      f.base.name.name == name && f.base.name.path == path
    _ => false
  }
}

///|
/// Does the type recorded for the tree node `uid` equal `expected`?
fn resolved_type_is(
  context : @source.Context,
  uid : Int32,
  expected : @symbols.ValueType,
) -> Bool {
  match context.value_type_of(uid) {
    Some(actual) => @symbols.value_type_equal(actual, expected)
    None => false
  }
}

///|
fn is_call_target(context : @source.Context, uid : Int32) -> Bool {
  match context.symbol_of(uid) {
    Some(@symbols.Sym::CallTarget(_)) => true
    _ => false
  }
}

///|
/// The unit literal.
fn unit_lit() -> @source.Term {
  @source.mk_term(
    sp(),
    @source.TermKind::Literal(@source.LiteralValue::LUnit, @symbols.t_unit()),
  )
}

///|
/// Is `name` bound as a type in `bindings`?
fn has_type(bindings : @symbols.Bindings, name : String) -> Bool {
  match bindings.types.get(name) {
    Some(_) => true
    None => false
  }
}

///|
/// Is `name` bound as a term in `bindings`?
fn has_term(bindings : @symbols.Bindings, name : String) -> Bool {
  match bindings.terms.get(name) {
    Some(_) => true
    None => false
  }
}

///|
/// Does the call target of `uid` contain a field with the given name?
fn call_target_contains_field(
  context : @source.Context,
  uid : Int32,
  name : String,
) -> Bool {
  match context.symbol_of(uid) {
    Some(@symbols.Sym::CallTarget(target)) =>
      target.symbols.any(group => {
        group.any(sym => {
          match sym {
            @symbols.Sym::Field(field) => field.base.name.name == name
            _ => false
          }
        })
      })
    _ => false
  }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

///|
test "resolves a function definition and a forward call" {
  let context = fresh_context()
  let main_id = id_def("main")
  let foo_id = id_def("foo")
  let x_id = id_def("x")
  let int_tree = type_ref("Int")
  let main_annot = pure(int_tree)
  let the_call = call("foo", [arg(int_lit(1))])
  // main is declared *before* foo: the two passes over the toplevel have to
  // make the forward reference work.
  let main = fun_def(
    main_id,
    [],
    Some(main_annot),
    expr(the_call, returns(int_lit(0))),
  )
  let x_use = var_ref("x")
  let foo = fun_def(
    foo_id,
    [vparam(x_id, Some(type_ref("Int")))],
    Some(pure(type_ref("Int"))),
    returns(x_use),
  )
  let module = module_decl("test", [], [main, foo])
  match resolve_ok(module, context) {
    Some(_) => {
      assert_true(is_user_function_named(context, foo_id.uid, ["test"], "foo"))
      assert_eq(symbol_kind(context, x_id.uid), "ValueParam")
      // the use of `x` resolves to the parameter
      assert_true(same_symbol(context, x_use.uid, x_id.uid))
      // a call goes through a call target that contains the function
      assert_true(is_call_target(context, the_call.uid))
      match context.symbol_of(foo_id.uid) {
        Some(foo_sym) =>
          assert_true(call_target_contains(context, the_call.uid, foo_sym))
        None => assert_true(false)
      }
      // the return annotation was resolved (as upstream, on the inner value
      // type tree of the `Effectful` annotation)
      assert_true(resolved_type_is(context, int_tree.uid, @symbols.t_int()))
    }
    None => {
      println(messages(context))
      assert_true(false)
    }
  }
}

///|
test "a local val shadows a toplevel val" {
  let context = fresh_context()
  let toplevel_id = id_def("x")
  let local_id = id_def("x")
  let use = var_ref("x")
  let body = @source.mk_stmt(
    sp(),
    @source.StmtKind::DefStmt(
      val_def(local_id, returns(int_lit(2))),
      returns(use),
    ),
  )
  let main = fun_def(id_def("main"), [], None, body)
  let module = module_decl("test", [], [
    val_def(toplevel_id, returns(int_lit(1))),
    main,
  ])
  match resolve_ok(module, context) {
    Some(_) => {
      assert_eq(symbol_kind(context, toplevel_id.uid), "ValBinder")
      assert_eq(symbol_kind(context, local_id.uid), "ValBinder")
      // the two binders are different symbols ...
      assert_true(!same_symbol(context, toplevel_id.uid, local_id.uid))
      // ... and the use refers to the local one
      assert_true(same_symbol(context, use.uid, local_id.uid))
      assert_true(!same_symbol(context, use.uid, toplevel_id.uid))
    }
    None => {
      println(messages(context))
      assert_true(false)
    }
  }
}

///|
test "resolves type and data declarations and type references" {
  let context = fresh_context()
  let num_id = id_def("Num")
  let list_id = id_def("List")
  let head_id = id_def("head")
  let tail_id = id_def("tail")
  let cons_id = id_def("Cons")
  let param_tpe = type_ref("Num")
  let n_id = id_def("n")
  let use = var_ref("n")
  let type_def = @source.mk_def(
    sp(),
    @source.Info::empty(),
    @source.DefKind::TypeDef(num_id, [], type_ref("Int")),
  )
  let data_def = @source.mk_def(
    sp(),
    @source.Info::empty(),
    @source.DefKind::DataDef(list_id, [], [
      @source.Constructor::{
        uid: @util.fresh_uid(),
        span: sp(),
        id: id_def("Nil"),
        tparams: [],
        params: [],
        doc: None,
      },
      @source.Constructor::{
        uid: @util.fresh_uid(),
        span: sp(),
        id: cons_id,
        tparams: [],
        params: [
          vparam(head_id, Some(type_ref("Int"))),
          vparam(tail_id, Some(type_ref("List"))),
        ],
        doc: None,
      },
    ]),
  )
  let fun = fun_def(
    id_def("f"),
    [vparam(n_id, Some(param_tpe))],
    Some(pure(type_ref("Num"))),
    returns(use),
  )
  let module = module_decl("test", [], [type_def, data_def, fun])
  match resolve_ok(module, context) {
    Some(_) => {
      assert_eq(symbol_kind(context, num_id.uid), "TypeAlias")
      assert_eq(symbol_kind(context, list_id.uid), "DataType")
      // the type reference `Num` resolves to the alias and is dealiased to Int
      assert_true(same_symbol(context, param_tpe.uid, num_id.uid))
      assert_true(resolved_type_is(context, param_tpe.uid, @symbols.t_int()))
      // the constructor is defined in the namespace of the data type
      assert_eq(symbol_kind(context, cons_id.uid), "Constructor")
      // the fields of `Cons` are resolved to Field symbols ...
      match context.symbol_of(list_id.uid) {
        Some(@symbols.Sym::DataType(data)) => {
          assert_eq(data.constructors.length(), 2)
          match data.constructors[1] {
            @symbols.Sym::Constructor(ctor) => {
              assert_eq(ctor.fields.length(), 2)
              match ctor.fields[0] {
                @symbols.Sym::Field(field) =>
                  match field.param {
                    @symbols.Sym::ValueParam(param) =>
                      assert_true(
                        match param.tpe {
                          Some(t) =>
                            @symbols.value_type_equal(t, @symbols.t_int())
                          None => false
                        },
                      )
                    _ => assert_true(false)
                  }
                _ => assert_true(false)
              }
            }
            _ => assert_true(false)
          }
        }
        _ => assert_true(false)
      }
      // ... and the parameter id of the constructor field is a value param
      assert_eq(symbol_kind(context, head_id.uid), "ValueParam")
    }
    None => {
      println(messages(context))
      assert_true(false)
    }
  }
}

///|
test "resolves an effect declaration, its operations and a handler with resume" {
  let context = fresh_context()
  let exc_id = id_def("Exc")
  let op_id = id_def("raise")
  let msg_id = id_def("msg")
  let exc_ref = type_ref("Exc")
  let operation = @source.Operation::{
    uid: @util.fresh_uid(),
    span: sp(),
    id: op_id,
    tparams: [],
    vparams: [vparam(msg_id, Some(type_ref("String")))],
    bparams: [],
    ret: pure(type_ref("Int")),
    doc: None,
  }
  let effect_def = @source.mk_def(
    sp(),
    @source.Info::empty(),
    @source.DefKind::InterfaceDef(exc_id, [], [operation]),
  )
  // try { do raise("boom") } with Exc { def raise(msg) = resume(1) }
  let do_call = do_op("raise", [arg(int_lit(0))])
  let resume_id = id_def("resume")
  let resume_call = call("resume", [arg(int_lit(1))])
  let clause = @source.OpClause::{
    uid: @util.fresh_uid(),
    span: sp(),
    id: id_ref("raise"),
    tparams: [],
    vparams: [vparam(id_def("msg"), None)],
    bparams: [],
    ret: None,
    body: returns(resume_call),
    resume: resume_id,
  }
  let handler = @source.Handler::{
    uid: @util.fresh_uid(),
    span: sp(),
    capability: None,
    implementation: @source.Implementation::{
      uid: @util.fresh_uid(),
      span: sp(),
      interface: exc_ref,
      clauses: [clause],
    },
  }
  let try_handle = @source.mk_term(
    sp(),
    @source.TermKind::TryHandle(expr(do_call, returns(int_lit(0))), [handler]),
  )
  let main = fun_def(id_def("main"), [], None, returns(try_handle))
  let module = module_decl("test", [], [effect_def, main])
  match resolve_ok(module, context) {
    Some(_) => {
      assert_eq(symbol_kind(context, exc_id.uid), "Interface")
      assert_eq(symbol_kind(context, op_id.uid), "Operation")
      // the operation is attached to the operation *tree* as well
      assert_true(same_symbol(context, operation.uid, op_id.uid))
      match context.symbol_of(op_id.uid) {
        Some(@symbols.Sym::Operation(op)) => {
          // the operation knows its interface ...
          assert_true(same_symbol(context, exc_id.uid, exc_id.uid))
          match context.symbol_of(exc_id.uid) {
            Some(exc_sym) => assert_true(op.interface.uid() == exc_sym.uid())
            None => assert_true(false)
          }
          // ... and `do raise(...)` resolves to a call target containing it
          assert_true(
            call_target_contains(
              context,
              do_call.uid,
              @symbols.Sym::Operation(op),
            ),
          )
        }
        _ => assert_true(false)
      }
      // the clause resolves the operation ...
      assert_true(same_symbol(context, clause.id.uid, op_id.uid))
      // ... and `resume` is bound as a resume parameter
      assert_eq(symbol_kind(context, resume_id.uid), "ResumeParam")
      match context.symbol_of(resume_id.uid) {
        Some(resume_sym) =>
          assert_true(
            call_target_contains(context, resume_call.uid, resume_sym),
          )
        None => assert_true(false)
      }
      // the handled interface is recorded on the implementation
      assert_true(same_symbol(context, handler.implementation.uid, exc_id.uid))
    }
    None => {
      println(messages(context))
      assert_true(false)
    }
  }
}

///|
test "resolves dotted references into a namespace" {
  let context = fresh_context()
  let bar_id = id_def("bar")
  let namespace_def = @source.mk_def(
    sp(),
    @source.Info::empty(),
    @source.DefKind::NamespaceDef(id_def("foo"), [
      fun_def(bar_id, [], Some(pure(type_ref("Int"))), returns(int_lit(1))),
    ]),
  )
  // call it as `foo::bar()` and as `test::foo::bar()` (the module self-import)
  let dotted = call_qualified(["foo"], "bar", [])
  let fully_dotted = call_qualified(["test", "foo"], "bar", [])
  let main = fun_def(
    id_def("main"),
    [],
    None,
    expr(dotted, expr(fully_dotted, returns(int_lit(0)))),
  )
  let module = module_decl("test", [], [namespace_def, main])
  match resolve_ok(module, context) {
    Some(_) => {
      assert_true(
        is_user_function_named(context, bar_id.uid, ["test", "foo"], "bar"),
      )
      match context.symbol_of(bar_id.uid) {
        Some(bar_sym) => {
          assert_true(call_target_contains(context, dotted.uid, bar_sym))
          assert_true(call_target_contains(context, fully_dotted.uid, bar_sym))
        }
        None => assert_true(false)
      }
    }
    None => {
      println(messages(context))
      assert_true(false)
    }
  }
}

///|
test "imports an included module's exports" {
  // module `lib`: def inc(x: Int): Int = x
  let lib_context = fresh_context()
  let inc_id = id_def("inc")
  let lib_module = module_decl("lib", [], [
    fun_def(
      inc_id,
      [vparam(id_def("x"), Some(type_ref("Int")))],
      Some(pure(type_ref("Int"))),
      returns(var_ref("x")),
    ),
  ])
  match resolve_ok(lib_module, lib_context) {
    None => {
      println(messages(lib_context))
      assert_true(false)
    }
    Some(lib) => {
      // module `app`: include "lib"; call `inc(1)` (opened) and `lib::inc(1)`
      let context = fresh_context()
      let opened = call("inc", [arg(int_lit(1))])
      let qualified = call_qualified(["lib"], "inc", [arg(int_lit(1))])
      let main = fun_def(
        id_def("main"),
        [],
        None,
        expr(opened, expr(qualified, returns(int_lit(0)))),
      )
      let module = module_decl(
        "app",
        [@source.Include::{ path: "lib", span: sp(), }],
        [main],
      )
      let deps : Map[String, @namer.ResolvedModule] = { "lib": lib }
      match resolve_with(module, context, deps) {
        Some(resolved) => {
          assert_eq(resolved.module.includes.length(), 1)
          // the symbol lives in the *dependency's* context
          match lib_context.symbol_of(inc_id.uid) {
            Some(inc_sym) => {
              assert_true(call_target_contains(context, opened.uid, inc_sym))
              assert_true(call_target_contains(context, qualified.uid, inc_sym))
            }
            None => assert_true(false)
          }
          // the module does not re-export what it imports
          match resolved.module.exports.terms.get("inc") {
            Some(_) => assert_true(false)
            None => assert_true(true)
          }
        }
        None => {
          println(messages(context))
          assert_true(false)
        }
      }
    }
  }
}

///|
test "a local definition shadows an imported name" {
  // module `lib` exports `answer`
  let lib_context = fresh_context()
  let lib_answer_id = id_def("answer")
  let lib_module = module_decl("lib", [], [
    val_def(lib_answer_id, returns(int_lit(1))),
  ])
  match resolve_ok(lib_module, lib_context) {
    None => {
      println(messages(lib_context))
      assert_true(false)
    }
    Some(lib) => {
      // module `app` defines its own `answer` and uses it
      let context = fresh_context()
      let local_answer_id = id_def("answer")
      let use = var_ref("answer")
      let module = module_decl(
        "app",
        [@source.Include::{ path: "lib", span: sp(), }],
        [
          val_def(local_answer_id, returns(int_lit(2))),
          fun_def(id_def("main"), [], None, returns(use)),
        ],
      )
      let deps : Map[String, @namer.ResolvedModule] = { "lib": lib }
      match resolve_with(module, context, deps) {
        Some(_) => {
          // the definition shadows the imported name instead of being ambiguous
          assert_true(!context.has_errors())
          assert_true(same_symbol(context, use.uid, local_answer_id.uid))
          match lib_context.symbol_of(lib_answer_id.uid) {
            Some(imported) =>
              assert_true(!same_symbol(context, use.uid, imported.uid()))
            None => assert_true(false)
          }
        }
        None => {
          println(messages(context))
          assert_true(false)
        }
      }
    }
  }
}

///|
test "resolves a record, its constructor and field selectors" {
  let context = fresh_context()
  let point_id = id_def("Point")
  let x_id = id_def("x")
  let record_def = @source.mk_def(
    sp(),
    @source.Info::empty(),
    @source.DefKind::RecordDef(point_id, [], [
      vparam(x_id, Some(type_ref("Int"))),
    ]),
  )
  // p.x
  let select = @source.mk_term(
    sp(),
    @source.TermKind::Select(var_ref("p"), id_ref("x")),
  )
  let fun = fun_def(
    id_def("getX"),
    [vparam(id_def("p"), Some(type_ref("Point")))],
    Some(pure(type_ref("Int"))),
    returns(select),
  )
  let module = module_decl("test", [], [record_def, fun])
  match resolve_ok(module, context) {
    Some(_) => {
      assert_eq(symbol_kind(context, point_id.uid), "Record")
      // the field accessor resolves through a call target containing the Field
      assert_true(is_call_target(context, select.uid))
      assert_true(call_target_contains_field(context, select.uid, "x"))
    }
    None => {
      println(messages(context))
      assert_true(false)
    }
  }
}

///|
test "resolves a def (block) definition and a call to it" {
  let context = fresh_context()
  let bar_id = id_def("bar")
  let block_body = @source.mk_term(
    sp(),
    @source.TermKind::BlockLiteral([], [], [], returns(int_lit(1))),
  )
  let bar = @source.mk_def(
    sp(),
    @source.Info::empty(),
    @source.DefKind::DefDef(bar_id, None, None, block_body),
  )
  let the_call = call("bar", [])
  let main = fun_def(
    id_def("main"),
    [],
    None,
    expr(the_call, returns(int_lit(0))),
  )
  let module = module_decl("test", [], [bar, main])
  match resolve_ok(module, context) {
    Some(_) => {
      assert_eq(symbol_kind(context, bar_id.uid), "DefBinder")
      match context.symbol_of(bar_id.uid) {
        Some(bar_sym) =>
          assert_true(call_target_contains(context, the_call.uid, bar_sym))
        None => assert_true(false)
      }
    }
    None => {
      println(messages(context))
      assert_true(false)
    }
  }
}

///|
test "resolves a hole and numbers it after the enclosing definition" {
  let context = fresh_context()
  let hole_id = id_def("h")
  let hole = @source.mk_term(
    sp(),
    @source.TermKind::Hole(
      hole_id,
      @util.Template::new(["???"], [returns(int_lit(0))]),
    ),
  )
  let main = fun_def(id_def("main"), [], None, returns(hole))
  let module = module_decl("test", [], [main])
  match resolve_ok(module, context) {
    Some(resolved) => {
      assert_eq(symbol_kind(context, hole_id.uid), "Hole")
      match context.symbol_of(hole_id.uid) {
        // the hole is named after the enclosing definition plus a counter
        Some(hole_sym) => assert_eq(hole_sym.name().name, "main0")
        None => assert_true(false)
      }
      assert_eq(resolved.holes.length(), 1)
    }
    None => {
      println(messages(context))
      assert_true(false)
    }
  }
}

///|
test "a missing include is reported and skipped" {
  let context = fresh_context()
  let module = module_decl(
    "app",
    [@source.Include::{ path: "missing", span: sp(), }],
    [fun_def(id_def("main"), [], None, returns(int_lit(0)))],
  )
  match resolve_ok(module, context) {
    Some(resolved) => {
      assert_eq(resolved.module.includes.length(), 0)
      assert_true(context.has_errors())
    }
    None => assert_true(false)
  }
}

///|
test "the `resolve` entry point publishes the module in the context" {
  let context = fresh_context()
  let main_id = id_def("main")
  let module = module_decl("test", [], [
    fun_def(main_id, [], None, returns(int_lit(0))),
  ])
  @namer.resolve(module, context) catch {
    _ => {
      println(messages(context))
      assert_true(false)
    }
  }
  match context.resolved_module() {
    Some(resolved) => {
      assert_eq(resolved.path, "test")
      // the exports of the module are the toplevel definitions
      match resolved.exports.terms.get("main") {
        Some(syms) => assert_eq(syms.length(), 1)
        None => assert_true(false)
      }
    }
    None => assert_true(false)
  }
  assert_true(!context.has_errors())
}

///|
test "reports unresolved names instead of silently accepting them" {
  let context = fresh_context()
  let module = module_decl("test", [], [
    fun_def(id_def("main"), [], None, returns(var_ref("doesNotExist"))),
  ])
  assert_true(resolve_ok(module, context) is None)
  assert_true(context.has_errors())
}

///|
/// The driver resolves a whole dependency closure with *one* context, in
/// topological order, and passes each resolved module to its importers. This
/// test mirrors that: `lib` is resolved first, then `app` imports it — twice,
/// like the driver's implicit prelude include — and has to see both the terms
/// *and* the types of `lib`.
test "an importer resolved after its dependency sees its terms and types" {
  let context = fresh_context()
  // module `lib`:
  //   interface Box[E] { def put(e: E): Unit }
  //   record Pair()
  //   def make(): Int = 1
  let box_id = id_def("Box")
  let e_id = id_def("E")
  let put_id = id_def("put")
  let put_op = @source.Operation::{
    uid: @util.fresh_uid(),
    span: sp(),
    id: put_id,
    tparams: [],
    vparams: [
      vparam(
        id_def("e"),
        Some(@source.mk_type(sp(), @source.TypeKind::TypeRef(id_ref("E"), []))),
      ),
    ],
    bparams: [],
    ret: pure(type_ref("Unit")),
    doc: None,
  }
  let pair_id = id_def("Pair")
  let make_id = id_def("make")
  let lib_module = module_decl("lib", [], [
    @source.mk_def(
      sp(),
      @source.Info::empty(),
      @source.DefKind::InterfaceDef(box_id, [e_id], [put_op]),
    ),
    @source.mk_def(
      sp(),
      @source.Info::empty(),
      @source.DefKind::RecordDef(pair_id, [], []),
    ),
    fun_def(make_id, [], Some(pure(type_ref("Int"))), returns(int_lit(1))),
  ])
  match resolve_ok(lib_module, context) {
    None => {
      println(messages(context))
      assert_true(false)
    }
    Some(lib) => {
      // the dependency itself exports its interface and its function
      assert_true(has_type(lib.module.exports, "Box"))
      assert_true(has_type(lib.module.exports, "Pair"))
      assert_true(has_term(lib.module.exports, "make"))
      let box_uid = match context.symbol_of(box_id.uid) {
        Some(sym) => sym.uid()
        None => -1
      }
      let put_uid = match context.symbol_of(put_id.uid) {
        Some(sym) => sym.uid()
        None => -1
      }
      // module `app`: includes "lib" twice; uses `Box[Int]` as the handled
      // interface (a type), calls `put` (an operation) and `make` (a term)
      let box_int = @source.mk_type(
        sp(),
        @source.TypeKind::TypeRef(id_ref("Box"), [type_ref("Int")]),
      )
      let do_put = do_op("put", [arg(int_lit(1))])
      let handler = @source.Handler::{
        uid: @util.fresh_uid(),
        span: sp(),
        capability: None,
        implementation: @source.Implementation::{
          uid: @util.fresh_uid(),
          span: sp(),
          interface: box_int,
          clauses: [
            @source.OpClause::{
              uid: @util.fresh_uid(),
              span: sp(),
              id: id_ref("put"),
              tparams: [],
              vparams: [vparam(id_def("e"), None)],
              bparams: [],
              ret: None,
              body: returns(unit_lit()),
              resume: id_def("resume"),
            },
          ],
        },
      }
      let try_handle = @source.mk_term(
        sp(),
        @source.TermKind::TryHandle(expr(do_put, returns(unit_lit())), [handler]),
      )
      let make_call = call("make", [])
      let app_module = module_decl(
        "app",
        [
          @source.Include::{ path: "lib", span: sp(), },
          @source.Include::{ path: "lib", span: sp(), },
        ],
        [
          fun_def(
            id_def("main"),
            [],
            None,
            expr(make_call, returns(try_handle)),
          ),
        ],
      )
      let deps : Map[String, @namer.ResolvedModule] = { "lib": lib }
      match resolve_with(app_module, context, deps) {
        Some(app) => {
          // including a module twice imports it once
          assert_eq(app.module.includes.length(), 1)
          assert_true(!context.has_errors())
          // the *type* `Box[Int]` of the dependency resolves to the same symbol
          match context.symbol_of(box_int.uid) {
            Some(sym) => assert_eq(sym.uid(), box_uid)
            None => assert_true(false)
          }
          // the operation `put` of the dependency resolves
          match context.symbol_of(put_id.uid) {
            Some(put_sym) => {
              assert_eq(put_sym.uid(), put_uid)
              assert_true(call_target_contains(context, do_put.uid, put_sym))
            }
            None => assert_true(false)
          }
          // the *term* `make` of the dependency resolves
          match context.symbol_of(make_id.uid) {
            Some(make_sym) =>
              assert_true(
                call_target_contains(context, make_call.uid, make_sym),
              )
            None => assert_true(false)
          }
          // resolving the importer did not corrupt the dependency's exports
          assert_true(has_type(lib.module.exports, "Box"))
          assert_true(has_type(lib.module.exports, "Pair"))
          assert_true(has_term(lib.module.exports, "make"))
        }
        None => {
          println(messages(context))
          assert_true(false)
        }
      }
    }
  }
}
