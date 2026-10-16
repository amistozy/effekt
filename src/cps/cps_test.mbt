// Blackbox tests for the CPS trees: free variables and substitution.

///|
fn vsym(hint : String) -> @symbols.Sym {
  @symbols.Sym::tmp_value(hint)
}

///|
fn bsym(hint : String) -> @symbols.Sym {
  @symbols.Sym::tmp_block(hint)
}

///|
fn some_value(a : @symbols.ValueType) -> @cps.Expr {
  @cps.Literal(@source.LInt(1), a)
}

///|
test "cps: free variables of a let expression" {
  let x = vsym("x")
  let k = bsym("k")
  let ks = bsym("ks")
  // let x = 1; jump k(x)[ks]
  let s = @cps.LetExpr(
    x,
    some_value(@symbols.t_int()),
    @cps.Jump(k, [@cps.ValueVar(x)], @cps.MetaCont::new(ks)),
  )
  let free = s.free()
  assert_true(free.contains(k))
  assert_true(free.contains(ks))
  // x is bound by the let, and the binding does not mention it
  assert_true(!free.contains(x))
}

///|
test "cps: free variables of a block literal exclude its parameters" {
  let x = vsym("x")
  let y = vsym("y")
  let ks = bsym("ks")
  let k = bsym("k")
  let lit = @cps.BlockLit::new(
    [x],
    [],
    ks,
    k,
    @cps.Jump(k, [@cps.ValueVar(x), @cps.ValueVar(y)], @cps.MetaCont::new(ks)),
  )
  let blk : @cps.Block = @cps.BlockLit(lit)
  let free = blk.free()
  assert_true(free.contains(y))
  assert_true(!free.contains(x))
  assert_true(!free.contains(ks))
  assert_true(!free.contains(k))
}

///|
test "cps: substitute as block var" {
  let r = bsym("r")
  let r2 = bsym("r2")
  let blocks : Map[Int32, @cps.Block] = Map([])
  blocks.set(r.uid(), @cps.BlockVar(r2))
  let subst = @cps.Substitution::new(Map([]), blocks, Map([]), Map([]))
  assert_true(@cps.substitute_as_block_var(r, subst).uid() == r2.uid())
  assert_true(
    @cps.substitute_as_block_var(bsym("other"), subst).uid() != r2.uid(),
  )
}
