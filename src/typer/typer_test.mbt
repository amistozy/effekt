// Tests for the type checker.
//
// NOTE: `src/namer` is being written concurrently, so these tests do the name
// resolution by hand: they build syntax trees with the `@source` smart
// constructors, create the symbols the Namer would create and register them in
// the `Context` with `assign_symbol`. Everything else (unbox inference and
// type checking) runs for real.

///|
fn test_span() -> @util.Span {
  @util.Span::missing()
}

///|
fn test_ctx() -> @source.Context {
  @source.Context::new(@source.Config::default())
}

///|
fn base(name : String) -> @symbols.SymBase {
  {
    uid: @util.fresh_uid(),
    name: @symbols.Name::local(name),
    decl: @util.Span::missing(),
  }
}

///|
fn int_tree() -> @source.TypeTree {
  @source.mk_type(
    test_span(),
    @source.TypeKind::ValueTypeTree(@symbols.t_int()),
  )
}

///|
fn unit_tree() -> @source.TypeTree {
  @source.mk_type(
    test_span(),
    @source.TypeKind::ValueTypeTree(@symbols.t_unit()),
  )
}

///|
fn value_param(
  id : @source.IdDef,
  tpe : @source.TypeTree?,
) -> @source.ValueParam {
  { id, tpe, is_implicit: false, }
}

///|
fn empty_captures() -> @source.CaptureSetTree {
  { span: test_span(), captures: [], }
}

///|
fn extern_body() -> Array[@source.ExternBody] {
  [
    @source.ExternBody::StringExternBody(
      @source.FeatureFlag::Default,
      @util.Template::empty(),
    ),
  ]
}

///|
fn id_ref(
  ctx : @source.Context,
  name : String,
  sym : @symbols.Sym,
) -> @source.IdRef {
  let id = @source.IdRef::new(name, test_span())
  ctx.assign_symbol(id.uid, sym)
  id
}

///|
fn id_def(
  ctx : @source.Context,
  name : String,
  sym : @symbols.Sym,
) -> @source.IdDef {
  let id = @source.IdDef::new(name, test_span())
  ctx.assign_symbol(id.uid, sym)
  id
}

///|
fn var_of(
  ctx : @source.Context,
  name : String,
  sym : @symbols.Sym,
) -> @source.Term {
  @source.mk_term(test_span(), @source.TermKind::Var(id_ref(ctx, name, sym)))
}

///|
fn int_lit(n : Int32) -> @source.Term {
  @source.mk_term(
    test_span(),
    @source.TermKind::Literal(@source.LiteralValue::LInt(n), @symbols.t_int()),
  )
}

///|
fn module_of(defs : Array[@source.Def]) -> @source.ModuleDecl {
  {
    uid: @util.fresh_uid(),
    span: test_span(),
    path: "test",
    includes: [],
    defs,
    doc: None,
  }
}

///|
/// Runs the type checker and reports the collected diagnostics when it fails.
fn run_typecheck(
  module : @source.ModuleDecl,
  ctx : @source.Context,
) -> Unit raise {
  let mut failure = ""
  @typer.typecheck(module, ctx) catch {
    @util.EffektError::Fatal(m) => failure = m
    @util.EffektError::Internal(m) => failure = m
  }
  if failure != "" {
    let rendered : Array[String] = []
    for m in ctx.messages() {
      rendered.push(m.render())
    }
    let message =
      $|\{failure}
      $|\{rendered.join("\n")}
    fail(message)
  }
  let errors : Array[String] = []
  for m in ctx.messages() {
    if m.severity == @util.Severity::Error {
      errors.push(m.render())
    }
  }
  if errors.length() > 0 {
    let message =
      $|type checking reported errors:
      $|\{errors.join("\n")}
    fail(message)
  }
}

///|
fn extern_add_def(ctx : @source.Context) -> (@source.Def, @symbols.Sym) {
  let a_sym = @symbols.Sym::value_param(
    @symbols.Name::local("a"),
    Some(@symbols.t_int()),
    test_span(),
  )
  let b_sym = @symbols.Sym::value_param(
    @symbols.Name::local("b"),
    Some(@symbols.t_int()),
    test_span(),
  )
  let add_id = @source.IdDef::new("add", test_span())
  let add_sym : @symbols.Sym = @symbols.ExternFunction({
    base: base("add"),
    tparams: [],
    vparams: [a_sym, b_sym],
    bparams: [],
    result: @symbols.t_int(),
    effects: @symbols.Effects::empty(),
    capture: [],
  })
  ctx.assign_symbol(add_id.uid, add_sym)
  let d = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::ExternDef(
      add_id,
      [],
      [
        value_param(@source.IdDef::new("a", test_span()), Some(int_tree())),
        value_param(@source.IdDef::new("b", test_span()), Some(int_tree())),
      ],
      [],
      empty_captures(),
      int_tree(),
      extern_body(),
    ),
  )
  (d, add_sym)
}

///|
test "1 + 2 : Int" {
  let ctx = test_ctx()
  let (add_def, add_sym) = extern_add_def(ctx)
  // val x = add(1, 2)
  let x_sym : @symbols.Sym = @symbols.ValBinder({ base: base("x"), tpe: None, })
  let x_id = id_def(ctx, "x", x_sym)
  let call = @source.mk_term(
    test_span(),
    @source.TermKind::Call(
      @source.CallTarget::IdTarget(id_ref(ctx, "add", add_sym)),
      [],
      [
        @source.ValueArg::unnamed(int_lit(1)),
        @source.ValueArg::unnamed(int_lit(2)),
      ],
      [],
    ),
  )
  let x_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::ValDef(
      x_id,
      None,
      @source.mk_stmt(test_span(), @source.StmtKind::Return(call)),
    ),
  )
  let module = module_of([add_def, x_def])
  run_typecheck(module, ctx)
  match ctx.value_type_of(x_def.uid) {
    Some(t) => assert_true(@typer.value_type_eq(t, @symbols.t_int()))
    None => fail("no type inferred for x")
  }
  // the call itself is annotated with its type
  match ctx.value_type_of(call.uid) {
    Some(t) => assert_true(@typer.value_type_eq(t, @symbols.t_int()))
    None => fail("no type inferred for the call")
  }
}

///|
test "lambda has an inferred function type" {
  let ctx = test_ctx()
  // def apply(f: (Int) => Int): Int
  let fun_type = @symbols.BlockType::FunctionType(
    [],
    [],
    [@symbols.t_int()],
    [],
    @symbols.t_int(),
    @symbols.Effects::empty(),
  )
  let f_capture = @symbols.Sym::capture_param(@symbols.Name::local("f"))
  let f_sym = @symbols.Sym::block_param(
    @symbols.Name::local("f"),
    Some(fun_type),
    f_capture,
    false,
    test_span(),
  )
  let apply_id = @source.IdDef::new("apply", test_span())
  let apply_sym : @symbols.Sym = @symbols.ExternFunction({
    base: base("apply"),
    tparams: [],
    vparams: [],
    bparams: [f_sym],
    result: @symbols.t_int(),
    effects: @symbols.Effects::empty(),
    // one capture per block parameter
    capture: [],
  })
  ctx.assign_symbol(apply_id.uid, apply_sym)
  let apply_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::ExternDef(
      apply_id,
      [],
      [],
      [
        {
          id: @source.IdDef::new("f", test_span()),
          tpe: Some(
            @source.mk_type(
              test_span(),
              @source.TypeKind::BlockTypeTree(fun_type),
            ),
          ),
          is_implicit: false,
        },
      ],
      empty_captures(),
      int_tree(),
      extern_body(),
    ),
  )
  // { (x: Int) => x }
  let x_sym = @symbols.Sym::value_param(
    @symbols.Name::local("x"),
    Some(@symbols.t_int()),
    test_span(),
  )
  let lambda = @source.mk_term(
    test_span(),
    @source.TermKind::BlockLiteral(
      [],
      [value_param(id_def(ctx, "x", x_sym), Some(int_tree()))],
      [],
      @source.mk_stmt(
        test_span(),
        @source.StmtKind::Return(var_of(ctx, "x", x_sym)),
      ),
    ),
  )
  let call = @source.mk_term(
    test_span(),
    @source.TermKind::Call(
      @source.CallTarget::IdTarget(id_ref(ctx, "apply", apply_sym)),
      [],
      [],
      [lambda],
    ),
  )
  let y_sym : @symbols.Sym = @symbols.ValBinder({ base: base("y"), tpe: None, })
  let y_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::ValDef(
      id_def(ctx, "y", y_sym),
      None,
      @source.mk_stmt(test_span(), @source.StmtKind::Return(call)),
    ),
  )
  run_typecheck(module_of([apply_def, y_def]), ctx)
  assert_false(ctx.has_errors())
  match ctx.block_type_of(lambda.uid) {
    Some(@symbols.BlockType::FunctionType(_, _, vps, bps, ret, effs)) => {
      assert_eq(vps.length(), 1)
      assert_true(@typer.value_type_eq(vps[0], @symbols.t_int()))
      assert_eq(bps.length(), 0)
      assert_true(@typer.value_type_eq(ret, @symbols.t_int()))
      assert_true(effs.is_empty())
    }
    Some(_) => fail("lambda was not given a function type")
    None => fail("no block type inferred for the lambda")
  }
}

///|
test "pure function has empty effect" {
  let ctx = test_ctx()
  // def f(x: Int): Int = x
  let x_sym = @symbols.Sym::value_param(
    @symbols.Name::local("x"),
    Some(@symbols.t_int()),
    test_span(),
  )
  let f_sym : @symbols.Sym = @symbols.UserFunction({
    base: base("f"),
    tparams: [],
    vparams: [x_sym],
    bparams: [],
    annotated_captures: None,
    annotated_result: Some(@symbols.t_int()),
    annotated_effects: Some(@symbols.Effects::empty()),
  })
  let f_id = id_def(ctx, "f", f_sym)
  let f_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::FunDef(
      f_id,
      [],
      [value_param(id_def(ctx, "x", x_sym), Some(int_tree()))],
      [],
      None,
      Some(int_tree()),
      @source.mk_stmt(
        test_span(),
        @source.StmtKind::Return(var_of(ctx, "x", x_sym)),
      ),
    ),
  )
  run_typecheck(module_of([f_def]), ctx)
  assert_false(ctx.has_errors())
  match ctx.effects_of(f_def.uid) {
    Some(effs) => assert_true(effs.is_empty())
    None => fail("no effects inferred for f")
  }
}

///|
test "declared effects flow through calls" {
  let ctx = test_ctx()
  // interface Exc { def raise(msg: String): Unit }
  let exc_sym : @symbols.Sym = @symbols.Interface({
    base: base("Exc"),
    tparams: [],
    operations: [],
  })
  let msg_sym = @symbols.Sym::value_param(
    @symbols.Name::local("msg"),
    Some(@symbols.t_string()),
    test_span(),
  )
  let raise_sym : @symbols.Sym = @symbols.Operation({
    base: base("raise"),
    tparams: [],
    vparams: [msg_sym],
    bparams: [],
    result_type: @symbols.t_unit(),
    effects: @symbols.Effects::empty(),
    interface: exc_sym,
  })
  match exc_sym {
    @symbols.Sym::Interface(i) => i.operations = [raise_sym]
    _ => ()
  }
  let exc = @symbols.BlockType::InterfaceType(exc_sym, [])
  // def f(): Unit / {Exc} = raise("boom")
  let f_sym : @symbols.Sym = @symbols.UserFunction({
    base: base("f"),
    tparams: [],
    vparams: [],
    bparams: [],
    annotated_captures: None,
    annotated_result: Some(@symbols.t_unit()),
    annotated_effects: Some(@symbols.Effects::new([exc])),
  })
  let f_id = id_def(ctx, "f", f_sym)
  let f_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::FunDef(
      f_id,
      [],
      [],
      [],
      None,
      Some(unit_tree()),
      @source.mk_stmt(
        test_span(),
        @source.StmtKind::Return(
          @source.mk_term(
            test_span(),
            @source.TermKind::Do(
              id_ref(ctx, "raise", raise_sym),
              [],
              [
                @source.ValueArg::unnamed(
                  @source.mk_term(
                    test_span(),
                    @source.TermKind::Literal(
                      @source.LiteralValue::LString("boom"),
                      @symbols.t_string(),
                    ),
                  ),
                ),
              ],
              [],
            ),
          ),
        ),
      ),
    ),
  )
  // def g(x: Int): Int / {Exc} = { f(); x }
  let x_sym = @symbols.Sym::value_param(
    @symbols.Name::local("x"),
    Some(@symbols.t_int()),
    test_span(),
  )
  let g_sym : @symbols.Sym = @symbols.UserFunction({
    base: base("g"),
    tparams: [],
    vparams: [x_sym],
    bparams: [],
    annotated_captures: None,
    annotated_result: Some(@symbols.t_int()),
    annotated_effects: Some(@symbols.Effects::new([exc])),
  })
  let g_id = id_def(ctx, "g", g_sym)
  let f_call = @source.mk_term(
    test_span(),
    @source.TermKind::Call(
      @source.CallTarget::IdTarget(id_ref(ctx, "f", f_sym)),
      [],
      [],
      [],
    ),
  )
  let body = @source.mk_stmt(
    test_span(),
    @source.StmtKind::ExprStmt(
      f_call,
      @source.mk_stmt(
        test_span(),
        @source.StmtKind::Return(var_of(ctx, "x", x_sym)),
      ),
    ),
  )
  let g_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::FunDef(
      g_id,
      [],
      [value_param(id_def(ctx, "x", x_sym), Some(int_tree()))],
      [],
      None,
      Some(int_tree()),
      body,
    ),
  )
  run_typecheck(module_of([f_def, g_def]), ctx)
  assert_false(ctx.has_errors())
  match ctx.effects_of(g_def.uid) {
    Some(effs) => {
      assert_eq(effs.distinct().size(), 1)
      assert_true(@symbols.interface_type_equal(effs.to_list()[0], exc))
    }
    None => fail("no effects inferred for g")
  }
  // the capability for Exc is passed to the call of f
  assert_eq(ctx.capability_arguments_of(f_call.uid).length(), 1)
}

///|
test "effect polymorphism" {
  let ctx = test_ctx()
  // def h[A]() { k: () => A }: A = k()
  let a_sym = @symbols.Sym::type_param(@symbols.Name::local("A"), test_span())
  let k_capture = @symbols.Sym::capture_param(@symbols.Name::local("k"))
  let k_type = @symbols.BlockType::FunctionType(
    [],
    [],
    [],
    [],
    @symbols.ValueType::ValueTypeRef(a_sym),
    @symbols.Effects::empty(),
  )
  let k_sym = @symbols.Sym::block_param(
    @symbols.Name::local("k"),
    Some(k_type),
    k_capture,
    false,
    test_span(),
  )
  let h_sym : @symbols.Sym = @symbols.UserFunction({
    base: base("h"),
    tparams: [a_sym],
    vparams: [],
    bparams: [k_sym],
    annotated_captures: None,
    annotated_result: Some(@symbols.ValueType::ValueTypeRef(a_sym)),
    annotated_effects: Some(@symbols.Effects::empty()),
  })
  let h_id = id_def(ctx, "h", h_sym)
  let k_call = @source.mk_term(
    test_span(),
    @source.TermKind::Call(
      @source.CallTarget::IdTarget(id_ref(ctx, "k", k_sym)),
      [],
      [],
      [],
    ),
  )
  let h_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::FunDef(
      h_id,
      [@source.IdDef::new("A", test_span())],
      [],
      [
        {
          id: @source.IdDef::new("k", test_span()),
          tpe: Some(
            @source.mk_type(
              test_span(),
              @source.TypeKind::BlockTypeTree(k_type),
            ),
          ),
          is_implicit: false,
        },
      ],
      None,
      Some(
        @source.mk_type(
          test_span(),
          @source.TypeKind::ValueTypeTree(
            @symbols.ValueType::ValueTypeRef(a_sym),
          ),
        ),
      ),
      @source.mk_stmt(test_span(), @source.StmtKind::Return(k_call)),
    ),
  )
  run_typecheck(module_of([h_def]), ctx)
  assert_false(ctx.has_errors())
  match ctx.block_type_of(h_def.uid) {
    Some(@symbols.BlockType::FunctionType(_, _, vps, bps, ret, effs)) => {
      assert_eq(vps.length(), 0)
      assert_eq(bps.length(), 1)
      assert_true(
        @typer.value_type_eq(ret, @symbols.ValueType::ValueTypeRef(a_sym)),
      )
      assert_true(effs.is_empty())
    }
    Some(_) => fail("h was not given a function type")
    None => fail("no block type inferred for h")
  }
}

///|
test "effect operation call gets a capability" {
  let ctx = test_ctx()
  // interface Exc { def raise(msg: String): Unit }
  let exc_sym : @symbols.Sym = @symbols.Interface({
    base: base("Exc"),
    tparams: [],
    operations: [],
  })
  let msg_sym = @symbols.Sym::value_param(
    @symbols.Name::local("msg"),
    Some(@symbols.t_string()),
    test_span(),
  )
  let raise_sym : @symbols.Sym = @symbols.Operation({
    base: base("raise"),
    tparams: [],
    vparams: [msg_sym],
    bparams: [],
    result_type: @symbols.t_unit(),
    effects: @symbols.Effects::empty(),
    interface: exc_sym,
  })
  match exc_sym {
    @symbols.Sym::Interface(i) => i.operations = [raise_sym]
    _ => ()
  }
  let exc = @symbols.BlockType::InterfaceType(exc_sym, [])
  // def f(): Unit / {Exc} = raise("boom")
  let f_sym : @symbols.Sym = @symbols.UserFunction({
    base: base("f"),
    tparams: [],
    vparams: [],
    bparams: [],
    annotated_captures: None,
    annotated_result: Some(@symbols.t_unit()),
    annotated_effects: Some(@symbols.Effects::new([exc])),
  })
  let f_id = id_def(ctx, "f", f_sym)
  let do_node = @source.mk_term(
    test_span(),
    @source.TermKind::Do(
      id_ref(ctx, "raise", raise_sym),
      [],
      [
        @source.ValueArg::unnamed(
          @source.mk_term(
            test_span(),
            @source.TermKind::Literal(
              @source.LiteralValue::LString("boom"),
              @symbols.t_string(),
            ),
          ),
        ),
      ],
      [],
    ),
  )
  let f_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::FunDef(
      f_id,
      [],
      [],
      [],
      None,
      Some(unit_tree()),
      @source.mk_stmt(test_span(), @source.StmtKind::Return(do_node)),
    ),
  )
  run_typecheck(module_of([f_def]), ctx)
  assert_false(ctx.has_errors())
  // the type arguments and the capability receiver are recorded for
  // ExplicitCapabilities
  assert_true(ctx.capability_receiver_of(do_node.uid) is Some(_))
  match ctx.capability_receiver_of(do_node.uid) {
    Some(cap) =>
      match @typer.capability_type(cap) {
        Some(t) => assert_true(@symbols.interface_type_equal(t, exc))
        None => fail("capability has no type")
      }
    None => fail("no capability receiver")
  }
}

///|
/// Runs the type checker, returning the rendered error messages (the checker is
/// expected to report errors).
fn run_typecheck_expecting_errors(
  module : @source.ModuleDecl,
  ctx : @source.Context,
) -> String {
  @typer.typecheck(module, ctx) catch {
    @util.EffektError::Fatal(_) => ()
    @util.EffektError::Internal(_) => ()
  }
  let rendered : Array[String] = []
  for m in ctx.messages() {
    rendered.push(m.render())
  }
  rendered.join("\n")
}

///|
test "non-exhaustive match is reported" {
  let ctx = test_ctx()
  // data Option { None; Some(Int) }
  let option_sym : @symbols.Sym = @symbols.DataType({
    base: base("Option"),
    tparams: [],
    constructors: [],
  })
  let none_sym : @symbols.Sym = @symbols.Constructor({
    base: base("None"),
    tparams: [],
    fields: [],
    tpe: option_sym,
  })
  let some_field = @symbols.Sym::value_param(
    @symbols.Name::local("value"),
    Some(@symbols.t_int()),
    test_span(),
  )
  let some_sym : @symbols.Sym = @symbols.Constructor({
    base: base("Some"),
    tparams: [],
    fields: [
      @symbols.Sym::Field({
        base: base("value"),
        param: some_field,
        constructor: some_sym_placeholder(),
      }),
    ],
    tpe: option_sym,
  })
  match option_sym {
    @symbols.Sym::DataType(d) => d.constructors = [none_sym, some_sym]
    _ => ()
  }
  let option_type = @symbols.ValueType::ValueTypeApp(option_sym, [])
  // extern def mk(): Option
  let mk_sym : @symbols.Sym = @symbols.ExternFunction({
    base: base("mk"),
    tparams: [],
    vparams: [],
    bparams: [],
    result: option_type,
    effects: @symbols.Effects::empty(),
    capture: [],
  })
  let mk_id = id_def(ctx, "mk", mk_sym)
  let mk_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::ExternDef(
      mk_id,
      [],
      [],
      [],
      empty_captures(),
      @source.mk_type(test_span(), @source.TypeKind::ValueTypeTree(option_type)),
      extern_body(),
    ),
  )
  // def f(): Int = match mk() { case None => 0 }
  let none_pattern = @source.mk_pattern(
    test_span(),
    @source.PatternKind::TagPattern(id_ref(ctx, "None", none_sym), []),
  )
  let match_term = @source.mk_term(
    test_span(),
    @source.TermKind::Match(
      [
        @source.mk_term(
          test_span(),
          @source.TermKind::Call(
            @source.CallTarget::IdTarget(id_ref(ctx, "mk", mk_sym)),
            [],
            [],
            [],
          ),
        ),
      ],
      [
        {
          uid: @util.fresh_uid(),
          span: test_span(),
          pattern: none_pattern,
          guards: [],
          body: @source.mk_stmt(
            test_span(),
            @source.StmtKind::Return(int_lit(0)),
          ),
        },
      ],
      None,
    ),
  )
  let f_sym : @symbols.Sym = @symbols.UserFunction({
    base: base("f"),
    tparams: [],
    vparams: [],
    bparams: [],
    annotated_captures: None,
    annotated_result: Some(@symbols.t_int()),
    annotated_effects: Some(@symbols.Effects::empty()),
  })
  let f_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::FunDef(
      id_def(ctx, "f", f_sym),
      [],
      [],
      [],
      None,
      Some(int_tree()),
      @source.mk_stmt(test_span(), @source.StmtKind::Return(match_term)),
    ),
  )
  let diagnostics = run_typecheck_expecting_errors(
    module_of([mk_def, f_def]),
    ctx,
  )
  assert_true(diagnostics.contains("Non-exhaustive"))
}

///|
/// A placeholder constructor symbol, used before the real one exists.
fn some_sym_placeholder() -> @symbols.Sym {
  @symbols.Constructor({
    base: base("Some"),
    tparams: [],
    fields: [],
    tpe: @symbols.Sym::wildcard(),
  })
}

///|
test "unbox inference wraps values in blocks" {
  let ctx = test_ctx()
  // def f = 1     (should become `def f = unbox 1`)
  let f_sym : @symbols.Sym = @symbols.DefBinder({
    base: base("f"),
    caps: None,
    tpe: None,
  })
  let binding = int_lit(1)
  let def_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::DefDef(id_def(ctx, "f", f_sym), None, None, binding),
  )
  let rewritten = @typer.unbox_inference(module_of([def_def]), ctx)
  match rewritten.defs[0].kind {
    @source.DefKind::DefDef(_, _, _, new_binding) =>
      match new_binding.kind {
        @source.TermKind::Unbox(_) => ()
        _ => fail("expected the binding to be wrapped in an unbox")
      }
    _ => fail("expected a DefDef")
  }
}

// ---------------------------------------------------------------------------
// Regressions for the `show` / `println` failures in the standard library
// ---------------------------------------------------------------------------

///|
/// `extern def name[R...](params...): result` together with its symbol.
fn extern_fn(
  ctx : @source.Context,
  name : String,
  tparams : Array[@symbols.Sym],
  params : Array[(String, @symbols.ValueType)],
  result : @symbols.ValueType,
) -> (@source.Def, @symbols.Sym) {
  let vparams : Array[@symbols.Sym] = params.map(p => {
    let (n, t) = p
    @symbols.Sym::value_param(@symbols.Name::local(n), Some(t), test_span())
  })
  let id = @source.IdDef::new(name, test_span())
  let sym : @symbols.Sym = @symbols.ExternFunction({
    base: base(name),
    tparams,
    vparams,
    bparams: [],
    result,
    effects: @symbols.Effects::empty(),
    capture: [],
  })
  ctx.assign_symbol(id.uid, sym)
  let tree_params : Array[@source.ValueParam] = []
  for i = 0; i < vparams.length(); i = i + 1 {
    let t = params[i].1
    tree_params.push(
      value_param(
        @source.IdDef::new(params[i].0, test_span()),
        Some(@source.mk_type(test_span(), @source.TypeKind::ValueTypeTree(t))),
      ),
    )
  }
  let d = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::ExternDef(
      id,
      tparams.map(t => @source.IdDef::new(t.name().name, test_span())),
      tree_params,
      [],
      empty_captures(),
      @source.mk_type(test_span(), @source.TypeKind::ValueTypeTree(result)),
      extern_body(),
    ),
  )
  (d, sym)
}

///|
/// `def name[R...](params...): result = body` together with its symbol.
fn user_fn(
  ctx : @source.Context,
  name : String,
  tparams : Array[@symbols.Sym],
  params : Array[(String, @symbols.Sym, @symbols.ValueType)],
  result : @symbols.ValueType,
  body : @source.Stmt,
) -> (@source.Def, @symbols.Sym) {
  let id = @source.IdDef::new(name, test_span())
  let sym : @symbols.Sym = @symbols.UserFunction({
    base: base(name),
    tparams,
    vparams: params.map(p => p.1),
    bparams: [],
    annotated_captures: None,
    annotated_result: Some(result),
    annotated_effects: Some(@symbols.Effects::empty()),
  })
  ctx.assign_symbol(id.uid, sym)
  let tree_params : Array[@source.ValueParam] = []
  for p in params {
    let (n, _, t) = p
    tree_params.push(
      value_param(
        @source.IdDef::new(n, test_span()),
        Some(@source.mk_type(test_span(), @source.TypeKind::ValueTypeTree(t))),
      ),
    )
  }
  let d = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::FunDef(
      id,
      tparams.map(t => @source.IdDef::new(t.name().name, test_span())),
      tree_params,
      [],
      None,
      Some(
        @source.mk_type(test_span(), @source.TypeKind::ValueTypeTree(result)),
      ),
      body,
    ),
  )
  (d, sym)
}

///|
fn return_of(t : @source.Term) -> @source.Stmt {
  @source.mk_stmt(test_span(), @source.StmtKind::Return(t))
}

///|
/// Runs the *full* transformation the driver uses: unbox inference followed by
/// type checking of the rewritten tree.
fn run_frontend(
  module : @source.ModuleDecl,
  ctx : @source.Context,
) -> @source.ModuleDecl raise {
  let mut failure = ""
  let mut rewritten : @source.ModuleDecl? = None
  try {
    let tree2 = @typer.unbox_inference(module, ctx)
    rewritten = Some(tree2)
    @typer.typecheck(tree2, ctx)
  } catch {
    @util.EffektError::Fatal(m) => failure = m
    @util.EffektError::Internal(m) => failure = m
  }
  if failure != "" || ctx.has_errors() {
    let rendered : Array[String] = []
    for m in ctx.messages() {
      rendered.push(m.render())
    }
    let message =
      $|\{failure}
      $|\{rendered.join("\n")}
    fail(message)
  }
  match rewritten {
    Some(t) => t
    None => fail("unbox inference did not return a tree")
  }
}

///|
test "method call on a value is desugared to a call" {
  let ctx = test_ctx()
  let r = @symbols.Sym::type_param(@symbols.Name::local("R"), test_span())
  // extern def show[R](value: R) at {}: String
  let (show_def, show_sym) = extern_fn(
    ctx,
    "show",
    [r],
    [("value", @symbols.ValueType::ValueTypeRef(r))],
    @symbols.t_string(),
  )
  // def f(x: Int): String = x.show
  let x_sym = @symbols.Sym::value_param(
    @symbols.Name::local("x"),
    Some(@symbols.t_int()),
    test_span(),
  )
  let method_call = @source.mk_term(
    test_span(),
    @source.TermKind::MethodCall(
      var_of(ctx, "x", x_sym),
      id_ref(ctx, "show", show_sym),
      [],
      [],
      [],
    ),
  )
  let (f_def, _) = user_fn(
    ctx,
    "f",
    [],
    [("x", x_sym, @symbols.t_int())],
    @symbols.t_string(),
    return_of(method_call),
  )
  let rewritten = run_frontend(module_of([show_def, f_def]), ctx)
  // the rewritten definition must contain a plain call to `show`
  match rewritten.defs[1].kind {
    @source.DefKind::FunDef(_, _, _, _, _, _, body) =>
      match body.kind {
        @source.StmtKind::Return(e) =>
          match e.kind {
            @source.TermKind::Call(
              @source.CallTarget::IdTarget(id),
              _,
              vargs,
              bargs
            ) => {
              assert_eq(id.name, "show")
              assert_eq(vargs.length(), 1)
              assert_eq(bargs.length(), 0)
            }
            _ => fail("expected the method call to become a function call")
          }
        _ => fail("expected a return statement")
      }
    _ => fail("expected the rewritten function")
  }
}

///|
test "overload resolution retries and picks the second candidate" {
  let ctx = test_ctx()
  // def show(value: Bool): String = "bool"      (fails for an Int argument)
  // def show(value: Int): String = "int"        (succeeds)
  let b_sym = @symbols.Sym::value_param(
    @symbols.Name::local("value"),
    Some(@symbols.t_bool()),
    test_span(),
  )
  let (bool_def, bool_show) = user_fn(
    ctx,
    "show",
    [],
    [("value", b_sym, @symbols.t_bool())],
    @symbols.t_string(),
    return_of(
      @source.mk_term(
        test_span(),
        @source.TermKind::Literal(
          @source.LiteralValue::LString("bool"),
          @symbols.t_string(),
        ),
      ),
    ),
  )
  let i_sym = @symbols.Sym::value_param(
    @symbols.Name::local("value"),
    Some(@symbols.t_int()),
    test_span(),
  )
  let (int_def, int_show) = user_fn(
    ctx,
    "show",
    [],
    [("value", i_sym, @symbols.t_int())],
    @symbols.t_string(),
    return_of(
      @source.mk_term(
        test_span(),
        @source.TermKind::Literal(
          @source.LiteralValue::LString("int"),
          @symbols.t_string(),
        ),
      ),
    ),
  )
  // val y = wrap(show(1)) where wrap: String => String
  let (wrap_def, wrap_sym) = extern_fn(
    ctx,
    "wrap",
    [],
    [("x", @symbols.t_string())],
    @symbols.t_string(),
  )
  let show_ref = @source.IdRef::new("show", test_span())
  ctx.assign_symbol(
    show_ref.uid,
    @symbols.Sym::call_target([[bool_show, int_show]]),
  )
  let inner = @source.mk_term(
    test_span(),
    @source.TermKind::Call(
      @source.CallTarget::IdTarget(show_ref),
      [],
      [@source.ValueArg::unnamed(int_lit(1))],
      [],
    ),
  )
  let wrap_ref = @source.IdRef::new("wrap", test_span())
  ctx.assign_symbol(wrap_ref.uid, wrap_sym)
  let outer = @source.mk_term(
    test_span(),
    @source.TermKind::Call(
      @source.CallTarget::IdTarget(wrap_ref),
      [],
      [@source.ValueArg::unnamed(inner)],
      [],
    ),
  )
  let y_sym : @symbols.Sym = @symbols.ValBinder({ base: base("y"), tpe: None, })
  let y_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::ValDef(id_def(ctx, "y", y_sym), None, return_of(outer)),
  )
  run_typecheck(module_of([bool_def, int_def, wrap_def, y_def]), ctx)
  // the failing candidate is skipped and the successful one is annotated
  match ctx.symbol_of(show_ref.uid) {
    Some(s) => assert_true(@symbols.sym_eq(s, int_show))
    None => fail("no symbol for the call")
  }
  // ... and the enclosing call still type checks (its verdict is not poisoned
  // by the failing candidate of the nested overload resolution)
  match ctx.value_type_of(outer.uid) {
    Some(t) => assert_true(@typer.value_type_eq(t, @symbols.t_string()))
    None => fail("no type for the outer call")
  }
}

///|
test "generic extern is instantiated with an inferred type argument" {
  let ctx = test_ctx()
  // extern def id[R](x: R) at {}: R
  let r = @symbols.Sym::type_param(@symbols.Name::local("R"), test_span())
  let (id_extern, id_sym) = extern_fn(
    ctx,
    "id",
    [r],
    [("x", @symbols.ValueType::ValueTypeRef(r))],
    @symbols.ValueType::ValueTypeRef(r),
  )
  // val v = id(42)
  let call = @source.mk_term(
    test_span(),
    @source.TermKind::Call(
      @source.CallTarget::IdTarget(id_ref(ctx, "id", id_sym)),
      [],
      [@source.ValueArg::unnamed(int_lit(42))],
      [],
    ),
  )
  let v_sym : @symbols.Sym = @symbols.ValBinder({ base: base("v"), tpe: None, })
  let v_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::ValDef(id_def(ctx, "v", v_sym), None, return_of(call)),
  )
  run_typecheck(module_of([id_extern, v_def]), ctx)
  match ctx.value_type_of(call.uid) {
    Some(t) => assert_true(@typer.value_type_eq(t, @symbols.t_int()))
    None => fail("no type inferred for the call")
  }
  // the inferred type argument is recorded for ExplicitCapabilities
  let targs = ctx.type_arguments_of(call.uid)
  assert_eq(targs.length(), 1)
  assert_true(@typer.value_type_eq(targs[0], @symbols.t_int()))
}

///|
test "a rigid type parameter is passed to a generic function" {
  let ctx = test_ctx()
  // extern def show[R](value: R) at {}: String
  let r = @symbols.Sym::type_param(@symbols.Name::local("R"), test_span())
  let (show_def, show_sym) = extern_fn(
    ctx,
    "show",
    [r],
    [("value", @symbols.ValueType::ValueTypeRef(r))],
    @symbols.t_string(),
  )
  // def describe[A](x: A): String = show(x)
  // (the argument has the *rigid* type A, the parameter of `show` a fresh
  //  unification variable -- this used to be rejected)
  let a = @symbols.Sym::type_param(@symbols.Name::local("A"), test_span())
  let x_sym = @symbols.Sym::value_param(
    @symbols.Name::local("x"),
    Some(@symbols.ValueType::ValueTypeRef(a)),
    test_span(),
  )
  let call = @source.mk_term(
    test_span(),
    @source.TermKind::Call(
      @source.CallTarget::IdTarget(id_ref(ctx, "show", show_sym)),
      [],
      [@source.ValueArg::unnamed(var_of(ctx, "x", x_sym))],
      [],
    ),
  )
  let (describe_def, _) = user_fn(
    ctx,
    "describe",
    [a],
    [("x", x_sym, @symbols.ValueType::ValueTypeRef(a))],
    @symbols.t_string(),
    return_of(call),
  )
  run_typecheck(module_of([show_def, describe_def]), ctx)
  match ctx.value_type_of(call.uid) {
    Some(t) => assert_true(@typer.value_type_eq(t, @symbols.t_string()))
    None => fail("no type inferred for the show call")
  }
}

// ---------------------------------------------------------------------------
// Regressions for the driver-level bugs (method calls, Nothing)
// ---------------------------------------------------------------------------

///|
/// Mimics the driver's pipeline *as it is currently wired*: the result of
/// `unbox_inference` is dropped and the original tree is type checked. The
/// type checker has to cope with that (it unboxes again and writes the
/// rewritten definitions back into the module), otherwise uniform function
/// call syntax (`x.f`) never reaches the type checker in desugared form.
fn run_typecheck_dropping_unbox(
  module : @source.ModuleDecl,
  ctx : @source.Context,
) -> Unit raise {
  let mut failure = ""
  try {
    let _ = @typer.unbox_inference(module, ctx)
    @typer.typecheck(module, ctx)
  } catch {
    @util.EffektError::Fatal(m) => failure = m
    @util.EffektError::Internal(m) => failure = m
  }
  if failure != "" || ctx.has_errors() {
    let rendered : Array[String] = []
    for m in ctx.messages() {
      rendered.push(m.render())
    }
    let message =
      $|\{failure}
      $|\{rendered.join("\n")}
    fail(message)
  }
}

///|
test "method call is desugared even when the driver drops the unboxed tree" {
  let ctx = test_ctx()
  let r = @symbols.Sym::type_param(@symbols.Name::local("R"), test_span())
  // extern def show[R](value: R) at {}: String
  let (show_def, show_sym) = extern_fn(
    ctx,
    "show",
    [r],
    [("value", @symbols.ValueType::ValueTypeRef(r))],
    @symbols.t_string(),
  )
  // extern def println(value: String): Unit
  let (println_def, println_sym) = extern_fn(
    ctx,
    "println",
    [],
    [("value", @symbols.t_string())],
    @symbols.t_unit(),
  )
  // def main() = println(1.show)
  let method_call = @source.mk_term(
    test_span(),
    @source.TermKind::MethodCall(
      int_lit(1),
      id_ref(ctx, "show", show_sym),
      [],
      [],
      [],
    ),
  )
  let (main_def, _) = user_fn(
    ctx,
    "main",
    [],
    [],
    @symbols.t_unit(),
    return_of(
      @source.mk_term(
        test_span(),
        @source.TermKind::Call(
          @source.CallTarget::IdTarget(id_ref(ctx, "println", println_sym)),
          [],
          [@source.ValueArg::unnamed(method_call)],
          [],
        ),
      ),
    ),
  )
  let module = module_of([show_def, println_def, main_def])
  run_typecheck_dropping_unbox(module, ctx)
  // the call is annotated with its type (the uid is preserved by the rewrite)
  match ctx.value_type_of(method_call.uid) {
    Some(t) => assert_true(@typer.value_type_eq(t, @symbols.t_string()))
    None => fail("no type inferred for the desugared method call")
  }
  // ... and the module the driver holds now contains the desugared call
  match module.defs[2].kind {
    @source.DefKind::FunDef(_, _, _, _, _, _, body) =>
      match body.kind {
        @source.StmtKind::Return(e) =>
          match e.kind {
            @source.TermKind::Call(_, _, vargs, _) =>
              match vargs[0].value.kind {
                @source.TermKind::Call(
                  @source.CallTarget::IdTarget(id),
                  _,
                  _,
                  _
                ) => assert_eq(id.name, "show")
                _ => fail("expected the argument to be a call to show")
              }
            _ => fail("expected a call")
          }
        _ => fail("expected a return statement")
      }
    _ => fail("expected a function definition")
  }
}

///|
test "Nothing coerces to the expected type" {
  let ctx = test_ctx()
  // interface E { def raise(m: String): Nothing }
  let e_sym : @symbols.Sym = @symbols.Interface({
    base: base("E"),
    tparams: [],
    operations: [],
  })
  let m_sym = @symbols.Sym::value_param(
    @symbols.Name::local("m"),
    Some(@symbols.t_string()),
    test_span(),
  )
  let raise_sym : @symbols.Sym = @symbols.Operation({
    base: base("raise"),
    tparams: [],
    vparams: [m_sym],
    bparams: [],
    result_type: @symbols.t_bottom(),
    effects: @symbols.Effects::empty(),
    interface: e_sym,
  })
  match e_sym {
    @symbols.Sym::Interface(i) => i.operations = [raise_sym]
    _ => ()
  }
  let e = @symbols.BlockType::InterfaceType(e_sym, [])
  // def f(y: Int): Int / E = if (y == 0) do raise("boom") else y
  // (the `then` branch has type Nothing and has to coerce to Int)
  let y_sym = @symbols.Sym::value_param(
    @symbols.Name::local("y"),
    Some(@symbols.t_int()),
    test_span(),
  )
  let do_raise = @source.mk_term(
    test_span(),
    @source.TermKind::Do(
      id_ref(ctx, "raise", raise_sym),
      [],
      [
        @source.ValueArg::unnamed(
          @source.mk_term(
            test_span(),
            @source.TermKind::Literal(
              @source.LiteralValue::LString("boom"),
              @symbols.t_string(),
            ),
          ),
        ),
      ],
      [],
    ),
  )
  let condition = @source.mk_guard(
    test_span(),
    @source.GuardKind::BooleanGuard(
      @source.mk_term(
        test_span(),
        @source.TermKind::Literal(
          @source.LiteralValue::LBool(true),
          @symbols.t_bool(),
        ),
      ),
    ),
  )
  let if_term = @source.mk_term(
    test_span(),
    @source.TermKind::If(
      [condition],
      return_of(do_raise),
      return_of(var_of(ctx, "y", y_sym)),
    ),
  )
  // ... with the effect declared, so that the capability for E is in scope
  let f_id = @source.IdDef::new("f", test_span())
  let f_sym : @symbols.Sym = @symbols.UserFunction({
    base: base("f"),
    tparams: [],
    vparams: [y_sym],
    bparams: [],
    annotated_captures: None,
    annotated_result: Some(@symbols.t_int()),
    annotated_effects: Some(@symbols.Effects::new([e])),
  })
  ctx.assign_symbol(f_id.uid, f_sym)
  let f_def = @source.mk_def(
    test_span(),
    @source.Info::empty(),
    @source.DefKind::FunDef(
      f_id,
      [],
      [value_param(@source.IdDef::new("y", test_span()), Some(int_tree()))],
      [],
      None,
      Some(int_tree()),
      return_of(if_term),
    ),
  )
  run_typecheck(module_of([f_def]), ctx)
  match ctx.value_type_of(if_term.uid) {
    Some(t) => assert_true(@typer.value_type_eq(t, @symbols.t_int()))
    None => fail("no type inferred for the if")
  }
  match ctx.effects_of(f_def.uid) {
    Some(effs) => {
      assert_eq(effs.distinct().size(), 1)
      assert_true(@symbols.interface_type_equal(effs.to_list()[0], e))
    }
    None => fail("no effects inferred for f")
  }
}
