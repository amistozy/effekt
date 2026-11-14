// Blackbox tests for the static argument transformation. The expectations are
// the printed definitions, so a test pins both the decision (which parameters
// are static) and the shape of the wrapper and the worker.

///|
fn fn_bvar(f : @symbols.Sym, tpe : @core.BlockType) -> @core.BlockVar {
  @core.BlockVar::new(f, tpe, @symbols.Captures::empty())
}

///|
/// `(Int) => Int`, the type of a recursive function over one static `Int`.
fn unary_fun() -> @core.BlockType {
  @core.FunctionType([], [], [@core.t_int()], [], [@core.t_int()])
}

///|
fn run(definitions : Array[@core.Toplevel]) -> String raise @util.EffektError {
  let module = @core.ModuleDecl("test", [], [], [], definitions, [])
  @core.show_core_toplevels(@core.static_arguments(module).definitions)
}

///|
test "static arguments: an unchanged argument becomes a worker parameter" {
  let f = bsym("f")
  let x = xsym("x")
  // def f(x: Int) = { f(x) }
  let definition = @core.ToplevelDef(
    f,
    @core.BlockLit(
      @core.BlockLit::new(
        [],
        [],
        [@core.ValueParam(x, @core.t_int())],
        [],
        @core.App(@core.BlockVar(fn_bvar(f, unary_fun())), [], [int_var(x)], []),
      ),
    ),
  )
  let expected =
    #|def f(x: Int) = {
    #|  def f_worker ()= {
    #|    f_worker()
    #|  }
    #|  f_worker()
    #|}
  assert_eq(run([definition]), expected)
}

///|
test "static arguments: an unread parameter is vacuously static" {
  let f = bsym("f")
  let x = xsym("x")
  // def f(x: Int) = { f(1) }
  let definition = @core.ToplevelDef(
    f,
    @core.BlockLit(
      @core.BlockLit::new(
        [],
        [],
        [@core.ValueParam(x, @core.t_int())],
        [],
        @core.App(@core.BlockVar(fn_bvar(f, unary_fun())), [], [int_lit(1)], []),
      ),
    ),
  )
  let expected =
    #|def f(x: Int) = {
    #|  def f_worker ()= {
    #|    f_worker()
    #|  }
    #|  f_worker()
    #|}
  assert_eq(run([definition]), expected)
}

///|
test "static arguments: a type argument that is passed through is dropped" {
  let f = bsym("f")
  let x = xsym("x")
  let t = @symbols.Sym::type_param(
    @symbols.Name::local("t"),
    @util.Span::missing(),
  )
  let polymorphic = @core.FunctionType([t], [], [@core.t_int()], [], [
    @core.t_int(),
  ])
  // def f[t](x: Int) = { f[t](x) }
  let definition = @core.ToplevelDef(
    f,
    @core.BlockLit(
      @core.BlockLit::new(
        [t],
        [],
        [@core.ValueParam(x, @core.t_int())],
        [],
        @core.App(
          @core.BlockVar(fn_bvar(f, polymorphic)),
          [@core.ValueVar(t)],
          [int_var(x)],
          [],
        ),
      ),
    ),
  )
  let expected =
    #|def f['t](x: Int) = {
    #|  def f_worker ()= {
    #|    f_worker()
    #|  }
    #|  f_worker()
    #|}
  assert_eq(run([definition]), expected)
}

///|
test "static arguments: a changing argument keeps the definition" {
  let f = bsym("f")
  let x = xsym("x")
  let y = xsym("y")
  // def f(x: Int) = { val y = x; f(y) }
  let definition = @core.ToplevelDef(
    f,
    @core.BlockLit(
      @core.BlockLit::new(
        [],
        [],
        [@core.ValueParam(x, @core.t_int())],
        [],
        @core.Val(
          [y],
          @core.Return([int_var(x)]),
          @core.App(@core.BlockVar(fn_bvar(f, unary_fun())), [], [int_var(y)], []),
        ),
      ),
    ),
  )
  let expected =
    #|def f(x: Int) = {
    #|  val y = return x;
    #|  f(y)
    #|}
  assert_eq(run([definition]), expected)
}

///|
test "static arguments: mutual recursion is not detected" {
  let f = bsym("f")
  let g = bsym("g")
  let x = xsym("x")
  // def f(x: Int) = { g(x) }; def g(x: Int) = { f(x) }
  let definition_of = (id : @symbols.Sym, callee : @symbols.Sym) => {
    @core.ToplevelDef(
      id,
      @core.BlockLit(
        @core.BlockLit::new(
          [],
          [],
          [@core.ValueParam(x, @core.t_int())],
          [],
          @core.App(
            @core.BlockVar(fn_bvar(callee, unary_fun())),
            [],
            [int_var(x)],
            [],
          ),
        ),
      ),
    )
  }
  let expected =
    #|def f(x: Int) = {
    #|  g(x)
    #|}
    #|def g(x: Int) = {
    #|  f(x)
    #|}
  assert_eq(run([definition_of(f, g), definition_of(g, f)]), expected)
}
