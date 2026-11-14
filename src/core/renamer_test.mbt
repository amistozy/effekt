// Blackbox tests for the core renamer: binders are freshened, their references
// follow, free variables are left alone, and the previous scope is restored when
// the binder goes out of scope.

///|
test "renamer: freshens a binder and its references" {
  let x = xsym("x")
  let lit = @core.BlockLit::new(
    [],
    [],
    [@core.ValueParam(x, @core.t_int())],
    [],
    @core.Return([int_var(x)]),
  )
  let (renamed, renamings) = @core.rename_block_lit(lit)
  let x2 = renamed.vparams[0].id
  assert_true(x2.uid() != x.uid(), msg="the binder is fresh")
  assert_true(x2.name() == x.name(), msg="but keeps its name")
  // the reference in the body was renamed to the fresh binder
  match renamed.body {
    @core.Return([@core.ValueVar(id, _)]) =>
      assert_true(id.uid() == x2.uid(), msg="the reference follows the binder")
    _ => abort("expected a single returned variable")
  }
  // and the renaming is recorded
  match renamings.get(x2.uid()) {
    Some(original) =>
      assert_true(original.uid() == x.uid(), msg="the fresh symbol maps back")
    None => abort("expected the fresh symbol to be recorded")
  }
}

///|
test "renamer: leaves free variables untouched" {
  let x = xsym("x")
  let y = xsym("y")
  let lit = @core.BlockLit::new(
    [],
    [],
    [@core.ValueParam(x, @core.t_int())],
    [],
    @core.Return([int_var(y)]),
  )
  let (renamed, _) = @core.rename_block_lit(lit)
  match renamed.body {
    @core.Return([@core.ValueVar(id, _)]) =>
      assert_true(id.uid() == y.uid(), msg="y is free, so it is not renamed")
    _ => abort("expected a single returned variable")
  }
}

///|
test "renamer: an inner binder shadows, the outer one is restored" {
  let x = xsym("x")
  let outer = @core.ValueParam(x, @core.t_int())
  // { (x) => let x = 42; return x }
  let inner_let = @core.Let(x, int_lit(42), @core.Return([int_var(x)]))
  let lit = @core.BlockLit::new([], [], [outer], [], inner_let)
  let (renamed, _) = @core.rename_block_lit(lit)
  let x_param = renamed.vparams[0].id
  match renamed.body {
    @core.Let(binder, _, @core.Return([@core.ValueVar(reference, _)])) => {
      // the inner binder is a *different* fresh symbol than the parameter
      assert_true(
        binder.uid() != x_param.uid(),
        msg="the let shadows the parameter",
      )
      assert_true(
        reference.uid() == binder.uid(),
        msg="the return refers to the let",
      )
    }
    _ => abort("expected let .. return ..")
  }
}

///|
test "renamer: two siblings do not see each other's binders" {
  let x = xsym("x")
  let f = bsym("f")
  let g = bsym("g")
  // def f = { () => return 1 }; def g = { () => return 2 }; return x
  let f_lit = @core.BlockLit::new([], [], [], [], @core.Return([int_lit(1)]))
  let g_lit = @core.BlockLit::new([], [], [], [], @core.Return([int_lit(2)]))
  let lit = @core.BlockLit::new(
    [],
    [],
    [],
    [],
    @core.Def(
      f,
      @core.BlockLit(f_lit),
      @core.Def(g, @core.BlockLit(g_lit), @core.Return([int_var(x)])),
    ),
  )
  let (renamed, _) = @core.rename_block_lit(lit)
  match renamed.body {
    @core.Def(f2, _, @core.Def(g2, _, @core.Return([@core.ValueVar(id, _)]))) => {
      assert_true(f2.uid() != f.uid(), msg="f is freshened")
      assert_true(g2.uid() != g.uid(), msg="g is freshened")
      assert_true(f2.uid() != g2.uid(), msg="and they are distinct")
      assert_true(id.uid() == x.uid(), msg="x stays free")
    }
    _ => abort("expected two nested definitions")
  }
}

///|
test "renamer: the binder of a definition is visible in its own body" {
  let f = bsym("f")
  // def f = { () => return f() }  (recursive)
  let lit = @core.BlockLit::new([], [], [], [], @core.Return([pure_app(f, [])]))
  let recursing = @core.BlockLit::new(
    [],
    [],
    [],
    [],
    @core.Def(f, @core.BlockLit(lit), @core.Return([int_lit(0)])),
  )
  let (renamed, _) = @core.rename_block_lit(recursing)
  match renamed.body {
    @core.Def(f2, @core.BlockLit(inner), _) =>
      match inner.body {
        @core.Return([@core.PureApp(callee, _, _)]) =>
          assert_true(
            callee.id.uid() == f2.uid(),
            msg="the recursive call refers to the fresh definition",
          )
        _ => abort("expected a returned application")
      }
    _ => abort("expected a definition")
  }
}
