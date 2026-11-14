// Whitebox tests for `type.mbt`: upstream `Type.inferType` / `Type.inferCapt`.
// The trees are built by hand, so a test pins the annotation each node is read
// from *and* the deviations listed at the top of `type.mbt`.
//
// A whitebox test file does not inherit the `using` declarations of
// `prelude.mbt`, so the `@symbols` types are spelled out. The core types
// (`FunctionType`, `ResumeType`, ...) are this package's own constructors.

///|
fn wb_value(name : String) -> @symbols.Sym {
  @symbols.Sym::value_param(
    @symbols.Name::local(name),
    Some(@symbols.t_int()),
    @util.Span::missing(),
  )
}

///|
fn wb_block(
  name : String,
  tpe : BlockType,
  capt : @symbols.Captures,
) -> BlockVar {
  BlockVar::new(@symbols.Sym::tmp_block(name), tpe, capt)
}

///|
/// A singleton capture set, the shape capture parameters have in this port.
fn wb_captures(cap : @symbols.Sym) -> @symbols.Captures {
  @symbols.Captures::CaptureSetOf([cap])
}

///|
/// `(Int) ~> Bool`, the resumption type of a shift continuation that takes an
/// `Int` and answers with a `Bool`.
fn wb_continuation() -> BlockType {
  ResumeType([t_int()], [t_bool()])
}

///|
fn show_types(tpes : Array[ValueType]) -> String {
  tpes.map(t => "\{t}").join(", ")
}

///|
/// Whether running `f` raises, i.e. whether the inference fails.
fn wb_raises(f : () -> Unit raise EffektError) -> Bool {
  let mut raised = false
  f() catch {
    _ => raised = true
  }
  raised
}

///|
test "infer_type: a return takes the annotated type" {
  let x = wb_value("x")
  let stmt = Return([Expr::ValueVar(x, t_int())])
  assert_eq(show_types(stmt.infer_type()), "Int")
}

///|
test "infer_type: a block literal records its parameters and its body's type" {
  let x = wb_value("x")
  let cap = @symbols.Sym::capture_param(@symbols.Name::local("cap"))
  let lit = BlockLit::new(
    [],
    [cap],
    [ValueParam(x, t_int())],
    [],
    Return([Expr::ValueVar(x, t_int())]),
  )
  // The capture parameter becomes a singleton capture set, as everywhere in the
  // port's type language.
  assert_true(
    Block::BlockLit(lit).infer_type() ==
    FunctionType([], [wb_captures(cap)], [t_int()], [], [t_int()]),
  )
}

///|
test "infer_type: a block literal records all of its results" {
  // Unlike the source language, a core function type has a *list* of results:
  // the prompt/shift encoding turns a multi-value `return` into one.
  let lit = BlockLit::new(
    [],
    [],
    [],
    [],
    Return([
      Expr::ValueVar(wb_value("x"), t_int()),
      Expr::ValueVar(wb_value("y"), t_int()),
    ]),
  )
  assert_true(
    Block::BlockLit(lit).infer_type() ==
    FunctionType([], [], [], [], [t_int(), t_int()]),
  )
}

///|
test "infer_type: a pure application of a multi-result function has no type" {
  // Upstream's `single` aborts: a `PureApp` yields exactly one value.
  let f = wb_block(
    "f",
    FunctionType([], [], [], [], [t_int(), t_int()]),
    @symbols.Captures::empty(),
  )
  assert_true(
    wb_raises(() => {
      let _ = PureApp(f, [], []).infer_type()
    }),
  )
}

///|
test "infer_type: an application instantiates the type arguments" {
  let t = @symbols.Sym::type_param(
    @symbols.Name::local("t"),
    @util.Span::missing(),
  )
  let f = wb_block(
    "f",
    FunctionType([t], [], [ValueVar(t)], [], [ValueVar(t)]),
    @symbols.Captures::empty(),
  )
  let stmt = App(
    Block::BlockVar(f),
    [t_int()],
    [Expr::ValueVar(wb_value("x"), t_int())],
    [],
  )
  assert_eq(show_types(stmt.infer_type()), "Int")
}

///|
test "infer_type: a match is typed by its annotation" {
  let stmt = Match(
    Expr::ValueVar(wb_value("scrutinee"), t_int()),
    [t_bool()],
    [],
    None,
  )
  assert_eq(show_types(stmt.infer_type()), "Bool")
}

///|
test "infer_type: shift and resume read the resumption type" {
  let prompt = wb_block("p", PromptType([t_int()]), @symbols.Captures::empty())
  let k_cap = @symbols.Sym::capture_param(@symbols.Name::local("k"))
  let k = BlockParam(
    @symbols.Sym::tmp_block("k"),
    wb_continuation(),
    wb_captures(k_cap),
  )
  let k_var = wb_block("k", wb_continuation(), wb_captures(k_cap))
  // `shift p { k: (Int) ~> Bool => ... }` answers with what `k` takes, while
  // `resume k` answers with what `k` returns.
  let shifted = Shift(
    prompt,
    k,
    Return([Expr::ValueVar(wb_value("x"), t_bool())]),
  )
  assert_eq(show_types(shifted.infer_type()), "Int")
  let resumed = Resume(k_var, Return([Expr::ValueVar(wb_value("x"), t_int())]))
  assert_eq(show_types(resumed.infer_type()), "Bool")
}

///|
test "infer_type: unbox reads the boxed type and its captures" {
  let fn_tpe = wb_continuation()
  let cap = @symbols.Sym::capture_param(@symbols.Name::local("cap"))
  let boxed = ValueBoxed(fn_tpe, wb_captures(cap))
  let block = Block::Unbox(Expr::ValueVar(wb_value("f"), boxed))
  assert_true(block.infer_type() == fn_tpe)
  assert_eq("\{block.infer_capt()}", "{cap}")
}

///|
test "infer_type: an unannotated callee yields the unknown type" {
  // The pattern-match compiler's join points are block variables without an
  // annotated type (`unknown_block_type()`), so their calls have no type.
  let f = wb_block("f", unknown_block_type(), @symbols.Captures::empty())
  let tpes = App(Block::BlockVar(f), [], [], []).infer_type()
  assert_eq(tpes.length(), 1)
  assert_true(is_unknown_value_type(tpes[0]))
}

///|
test "infer_capt: shift drops the continuation and adds the prompt" {
  let prompt_id = @symbols.Sym::tmp_block("p")
  let prompt = BlockVar::new(
    prompt_id,
    PromptType([t_int()]),
    @symbols.Captures::empty(),
  )
  let k_cap = @symbols.Sym::capture_param(@symbols.Name::local("k"))
  let k = BlockParam(
    @symbols.Sym::tmp_block("k"),
    wb_continuation(),
    wb_captures(k_cap),
  )
  let k_var = BlockVar::new(
    @symbols.Sym::tmp_block("k"),
    wb_continuation(),
    wb_captures(k_cap),
  )
  // The body applies the continuation and therefore captures `k`; the shift
  // itself captures the prompt instead.
  let body = App(Block::BlockVar(k_var), [], [], [])
  assert_true(Shift(prompt, k, body).infer_capt() == wb_captures(prompt_id))
}

///|
test "infer_capt: alloc adds its region and var subtracts its capture" {
  let region = @symbols.Sym::capture_param(@symbols.Name::local("r"))
  let allocated = Alloc(
    @symbols.Sym::tmp_value("x"),
    Expr::ValueVar(wb_value("init"), t_int()),
    region,
    Return([Expr::ValueVar(wb_value("x"), t_int())]),
  )
  assert_eq("\{allocated.infer_capt()}", "{r}")
  let capture = @symbols.Sym::capture_param(@symbols.Name::local("s"))
  let state = wb_block(
    "s",
    InterfaceType(@symbols.state_effect_sym(), [t_int()]),
    wb_captures(capture),
  )
  let state_stmt = Var(
    @symbols.Sym::tmp_value("ref"),
    Expr::ValueVar(wb_value("init"), t_int()),
    capture,
    App(Block::BlockVar(state), [], [], []),
  )
  assert_eq("\{state_stmt.infer_capt()}", "{}")
}
