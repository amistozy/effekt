// Whitebox tests for `type.mbt`: upstream `Type.inferType` / `Type.inferCapt`.
// The trees are built by hand, so a test pins the annotation each node is read
// from *and* the deviations listed at the top of `type.mbt`.
//
// A whitebox test file does not inherit the `using` declarations of
// `prelude.mbt`, so the symbol types are spelled out.

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
  tpe : @symbols.BlockType,
  capt : @symbols.Captures,
) -> BlockVar {
  BlockVar::new(@symbols.Sym::tmp_block(name), tpe, capt)
}

///|
/// `(Int) => Bool`, the function type of a unidirectional handler continuation.
fn wb_continuation() -> @symbols.BlockType {
  @symbols.BlockType::FunctionType(
    [],
    [],
    [@symbols.t_int()],
    [],
    @symbols.t_bool(),
    @symbols.Effects::empty(),
  )
}

///|
fn show_types(tpes : Array[@symbols.ValueType]) -> String {
  tpes.map(t => "\{t}").join(", ")
}

///|
/// Whether running `f` raises, i.e. whether the inference fails.
fn raises(f : () -> Unit raise EffektError) -> Bool {
  let mut raised = false
  f() catch {
    _ => raised = true
  }
  raised
}

///|
test "infer_type: a return takes the annotated type" {
  let x = wb_value("x")
  let stmt = Return([ValueVar(x, @symbols.t_int())])
  assert_eq(show_types(stmt.infer_type()), "Int")
}

///|
test "infer_type: a block literal records its parameters and its body's type" {
  let x = wb_value("x")
  let cap = @symbols.Sym::capture_param(@symbols.Name::local("cap"))
  let lit = BlockLit::new(
    [],
    [cap],
    [ValueParam(x, @symbols.t_int())],
    [],
    Return([ValueVar(x, @symbols.t_int())]),
  )
  // The capture parameter becomes a singleton capture set, as everywhere in the
  // port's type language.
  assert_true(
    Block::BlockLit(lit).infer_type() ==
    @symbols.BlockType::FunctionType(
      [],
      [@symbols.Captures::CaptureSetOf([cap])],
      [@symbols.t_int()],
      [],
      @symbols.t_int(),
      @symbols.Effects::empty(),
    ),
  )
}

///|
test "infer_type: a block literal with several results has no type" {
  let lit = BlockLit::new(
    [],
    [],
    [],
    [],
    Return([
      ValueVar(wb_value("x"), @symbols.t_int()),
      ValueVar(wb_value("y"), @symbols.t_int()),
    ]),
  )
  assert_true(
    raises(() => {
      let _ = Block::BlockLit(lit).infer_type()
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
    @symbols.BlockType::FunctionType(
      [t],
      [],
      [@symbols.ValueType::ValueTypeRef(t)],
      [],
      @symbols.ValueType::ValueTypeRef(t),
      @symbols.Effects::empty(),
    ),
    @symbols.Captures::empty(),
  )
  let stmt = App(
    Block::BlockVar(f),
    [@symbols.t_int()],
    [ValueVar(wb_value("x"), @symbols.t_int())],
    [],
  )
  assert_eq(show_types(stmt.infer_type()), "Int")
}

///|
test "infer_type: a match is typed by its annotation" {
  let stmt = Match(
    ValueVar(wb_value("scrutinee"), @symbols.t_int()),
    @symbols.t_bool(),
    [],
    None,
  )
  assert_eq(show_types(stmt.infer_type()), "Bool")
}

///|
test "infer_type: shift and resume read the resumption type" {
  let prompt = wb_block(
    "p",
    @symbols.BlockType::InterfaceType(
      @symbols.Sym::id(@symbols.Name::local("Prompt")),
      [],
    ),
    @symbols.Captures::empty(),
  )
  let k = BlockParam(
    @symbols.Sym::tmp_block("k"),
    wb_continuation(),
    @symbols.Captures::empty(),
  )
  let k_var = wb_block("k", wb_continuation(), @symbols.Captures::empty())
  // `shift p { k => ... }` answers with what `k` takes, and `resume k` with
  // what `k` returns: upstream reads the resumption type, the port the
  // continuation's function type.
  let shifted = Shift(
    prompt,
    k,
    Return([ValueVar(wb_value("x"), @symbols.t_int())]),
  )
  assert_eq(show_types(shifted.infer_type()), "Int")
  let resumed = Resume(
    k_var,
    Return([ValueVar(wb_value("x"), @symbols.t_bool())]),
  )
  assert_eq(show_types(resumed.infer_type()), "Bool")
}

///|
test "infer_type: unbox reads the boxed type and its captures" {
  let fn_tpe = wb_continuation()
  let cap = @symbols.Sym::capture_param(@symbols.Name::local("cap"))
  let boxed = @symbols.ValueType::BoxedType(
    fn_tpe,
    @symbols.Captures::CaptureSetOf([cap]),
  )
  let block = Block::Unbox(ValueVar(wb_value("f"), boxed))
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
    @symbols.BlockType::InterfaceType(
      @symbols.Sym::id(@symbols.Name::local("Prompt")),
      [],
    ),
    @symbols.Captures::empty(),
  )
  let k_cap = @symbols.Sym::capture_param(@symbols.Name::local("k"))
  let k = BlockParam(
    @symbols.Sym::tmp_block("k"),
    wb_continuation(),
    @symbols.Captures::CaptureSetOf([k_cap]),
  )
  let k_var = BlockVar::new(
    @symbols.Sym::tmp_block("k"),
    wb_continuation(),
    @symbols.Captures::CaptureSetOf([k_cap]),
  )
  // The body applies the continuation and therefore captures `k`; the shift
  // itself captures the prompt instead.
  let body = App(Block::BlockVar(k_var), [], [], [])
  assert_true(
    Shift(prompt, k, body).infer_capt() ==
    @symbols.Captures::CaptureSetOf([prompt_id]),
  )
}

///|
test "infer_capt: alloc adds its region and var subtracts its capture" {
  let region = @symbols.Sym::capture_param(@symbols.Name::local("r"))
  let allocated = Alloc(
    @symbols.Sym::tmp_value("x"),
    ValueVar(wb_value("init"), @symbols.t_int()),
    region,
    Return([ValueVar(wb_value("x"), @symbols.t_int())]),
  )
  assert_eq("\{allocated.infer_capt()}", "{r}")
  let capture = @symbols.Sym::capture_param(@symbols.Name::local("s"))
  let state = wb_block(
    "s",
    @symbols.BlockType::InterfaceType(
      @symbols.Sym::id(@symbols.Name::local("State")),
      [@symbols.t_int()],
    ),
    @symbols.Captures::CaptureSetOf([capture]),
  )
  let state_stmt = Var(
    @symbols.Sym::tmp_value("ref"),
    ValueVar(wb_value("init"), @symbols.t_int()),
    capture,
    App(Block::BlockVar(state), [], [], []),
  )
  assert_eq("\{state_stmt.infer_capt()}", "{}")
}
