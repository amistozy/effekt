// Blackbox tests for `bind_subexpressions`: every subexpression is named, and
// aliasing is removed. The expectations are the printed top level definition,
// so a test pins both the rewrite and the order of the emitted bindings.

///|
fn bvar(id : @symbols.Sym) -> @core.BlockVar {
  @core.BlockVar::new(
    id,
    @core.unknown_block_type(),
    @symbols.Captures::empty(),
  )
}

///|
fn int_lit(n : Int64) -> @core.Expr {
  @core.Literal(@source.LInt(n), @symbols.t_int())
}

///|
fn int_var(id : @symbols.Sym) -> @core.Expr {
  @core.ValueVar(id, @symbols.t_int())
}

///|
fn pure_app(f : @symbols.Sym, args : Array[@core.Expr]) -> @core.Expr {
  @core.PureApp(bvar(f), [], args)
}

///|
/// The top level definition `def main = { () => stmt }`, transformed by
/// `bind_subexpressions`.
fn transform_body(stmt : @core.Stmt) -> String raise @util.EffektError {
  let body = @core.BlockLit::new([], [], [], [], stmt)
  let module = @core.ModuleDecl(
    "test",
    [],
    [],
    [],
    [@core.ToplevelDef(bsym("main"), @core.BlockLit(body))],
    [],
  )
  let transformed = @core.bind_subexpressions(module)
  @core.show_core_toplevel(transformed.definitions[0])
}

///|
test "bind subexpressions: a return is kept" {
  let expected =
    #|def main() = {
    #|  return 42
    #|}
  assert_eq(transform_body(@core.Return([int_lit(42)])), expected)
}

///|
test "bind subexpressions: let aliasing is dropped" {
  // let x = y; return x  ==>  return y
  let x = xsym("x")
  let y = xsym("y")
  let stmt = @core.Let(x, int_var(y), @core.Return([int_var(x)]))
  let expected =
    #|def main() = {
    #|  return y
    #|}
  assert_eq(transform_body(stmt), expected)
}

///|
test "bind subexpressions: a pure application is bound to its own let" {
  // let x = f(1); return x  ==>  let tmp = f(1); return tmp
  let x = xsym("x")
  let f = bsym("f")
  let stmt = @core.Let(x, pure_app(f, [int_lit(1)]), @core.Return([int_var(x)]))
  let expected =
    #|def main() = {
    #|  let v_tmp = f(1)
    #|  return v_tmp
    #|}
  assert_eq(transform_body(stmt), expected)
}

///|
test "bind subexpressions: nested arguments are named inner first" {
  // let x = f(g(1)); return x  ==>  let tmp = g(1); let tmp = f(tmp); return tmp
  let x = xsym("x")
  let f = bsym("f")
  let g = bsym("g")
  let stmt = @core.Let(
    x,
    pure_app(f, [pure_app(g, [int_lit(1)])]),
    @core.Return([int_var(x)]),
  )
  let expected =
    #|def main() = {
    #|  let v_tmp = g(1)
    #|  let v_tmp = f(v_tmp)
    #|  return v_tmp
    #|}
  assert_eq(transform_body(stmt), expected)
}

///|
test "bind subexpressions: an impure application names its arguments" {
  // let !r = f(g(1)); return r  ==>  let tmp = g(1); let !r = f(tmp); return r
  let r = xsym("r")
  let f = bsym("f")
  let g = bsym("g")
  let stmt = @core.ImpureApp(
    r,
    bvar(f),
    [],
    [pure_app(g, [int_lit(1)])],
    [],
    @core.Return([int_var(r)]),
  )
  let expected =
    #|def main() = {
    #|  let v_tmp = g(1)
    #|  let ! r = f(v_tmp)
    #|  return r
    #|}
  assert_eq(transform_body(stmt), expected)
}

///|
test "bind subexpressions: a branch condition is named" {
  let f = bsym("f")
  let stmt = @core.If(
    pure_app(f, [int_lit(1)]),
    @core.Return([int_lit(1)]),
    @core.Return([int_lit(2)]),
  )
  let expected =
    #|def main() = {
    #|  let v_tmp = f(1)
    #|  if (v_tmp) {
    #|    return 1
    #|  } else {
    #|    return 2
    #|  }
    #|}
  assert_eq(transform_body(stmt), expected)
}

///|
test "bind subexpressions: a definition aliasing a block variable is dropped" {
  // def f = g; f()  ==>  g()
  let f = bsym("f")
  let g = bsym("g")
  let stmt = @core.Def(
    f,
    @core.BlockVar(bvar(g)),
    @core.App(@core.BlockVar(bvar(f)), [], [], []),
  )
  let expected =
    #|def main() = {
    #|  g()
    #|}
  assert_eq(transform_body(stmt), expected)
}

///|
test "bind subexpressions: a boxed block is bound to its own let" {
  // return box {} x  ==>  let tmp = box {} x; return tmp
  let x = bsym("x")
  let stmt = @core.Return([
    @core.Box(@core.BlockVar(bvar(x)), @symbols.Captures::empty()),
  ])
  let expected =
    #|def main() = {
    #|  let v_tmp = box {} x
    #|  return v_tmp
    #|}
  assert_eq(transform_body(stmt), expected)
}
