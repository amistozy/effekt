// Blackbox tests for the core trees: the pretty printer, free variables and
// substitution.

///|
fn xsym(name : String) -> @symbols.Sym {
  @symbols.Sym::value_param(
    @symbols.Name::local(name),
    Some(@symbols.t_int()),
    @util.Span::missing(),
  )
}

///|
fn bsym(name : String) -> @symbols.Sym {
  @symbols.Sym::block_param(
    @symbols.Name::local(name),
    None,
    @symbols.Sym::capture_param(@symbols.Name::local("cap")),
    false,
    @util.Span::missing(),
  )
}

///|
/// `def f(x: Int) = { return x }`
fn def_identity(f : @symbols.Sym, x : @symbols.Sym) -> @core.Toplevel {
  let lit = @core.BlockLit::new(
    [],
    [],
    [@core.ValueParam::new(x, @symbols.t_int())],
    [],
    @core.Return(@core.ValueVar(x, @symbols.t_int())),
  )
  @core.ToplevelDef(f, @core.BlockLit(lit))
}

///|
test "core pretty: toplevel definition" {
  let f = bsym("f")
  let x = xsym("x")
  let expected =
    #|def f(x: Int) = {
    #|  return x
    #|}
  assert_eq(@core.show_core_toplevel(def_identity(f, x)), expected)
}

///|
test "core pretty: module" {
  let m = @core.ModuleDecl::new(
    "test",
    [],
    [],
    [],
    [def_identity(bsym("f"), xsym("x"))],
    [],
  )
  let rendered = @core.show_core(m)
  let expected =
    #|def f(x: Int) = {
    #|  return x
    #|}
  assert_true(rendered.has_prefix("module test"))
  assert_true(rendered.contains(expected))
}

///|
test "core pretty: expressions" {
  let x = xsym("x")
  let tag = bsym("Leaf")
  let data = bsym("Tree")
  let e = @core.Make(data, tag, [@symbols.t_int()], [
    @core.ValueVar(x, @symbols.t_int()),
  ])
  assert_eq(@core.show_core_expr(e), "make Leaf[Int](x)")
  assert_eq(@core.show_core_stmt(@core.Return(e)), "return make Leaf[Int](x)")
}

///|
test "core: free variables" {
  let f = bsym("f")
  let x = xsym("x")
  let lit = @core.BlockLit::new(
    [],
    [],
    [@core.ValueParam::new(x, @symbols.t_int())],
    [],
    @core.Return(@core.ValueVar(x, @symbols.t_int())),
  )
  let s = @core.Def(
    f,
    @core.BlockLit(lit),
    @core.Return(@core.ValueVar(x, @symbols.t_int())),
  )
  let free = s.free()
  // x is bound inside the block, but free in the body of the definition
  assert_true(free.contains(x))
  // f is bound by the definition itself
  assert_true(!free.contains(f))
}

///|
test "core: substitution" {
  let x = xsym("x")
  let y = xsym("y")
  let values : Map[Int32, @core.Expr] = Map([])
  values.set(x.uid(), @core.ValueVar(y, @symbols.t_int()))
  let subst = @core.Substitution::new(Map([]), Map([]), values, Map([]))
  let e = @core.substitute_expr(@core.ValueVar(x, @symbols.t_int()), subst)
  assert_eq(@core.show_core_expr(e), "y")
}
