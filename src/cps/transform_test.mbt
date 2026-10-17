// Blackbox tests for `cps.transform` and `cps.contify`.

///|
fn tv(hint : String) -> @symbols.Sym {
  @symbols.Sym::tmp_value(hint)
}

///|
fn tb(hint : String) -> @symbols.Sym {
  @symbols.Sym::tmp_block(hint)
}

///|
fn int_expr(i : Int32) -> @core.Expr {
  @core.Expr::Literal(@source.LInt(i), @symbols.t_int())
}

///|
fn int_pure(i : Int32) -> @cps.Expr {
  @cps.Expr::Literal(@source.LInt(i), @symbols.t_int())
}

///|
fn core_module(
  definition : @core.Toplevel,
  main : @symbols.Sym,
) -> @core.ModuleDecl {
  @core.ModuleDecl::new("test", [], [], [], [definition], [main])
}

// ---------------------------------------------------------------------------
// transformer
// ---------------------------------------------------------------------------

///|
test "cps.transform: dealiases a let-bound variable" {
  let x = tv("x")
  let y = tv("y")
  let main = tb("main")
  // val x = y; return x
  let stmt = @core.Stmt::Let(
    x,
    @core.Expr::ValueVar(y, @symbols.t_int()),
    @core.Stmt::Return(@core.Expr::ValueVar(x, @symbols.t_int())),
  )
  let module = @cps.transform(core_module(@core.ToplevelVal(main, stmt), main))
  match module.definitions[0] {
    @cps.ToplevelVal(_id, _ks, _k, binding) =>
      match binding {
        @cps.Jump(_k2, vargs, _ks2) => {
          assert_true(vargs.length() == 1, msg="expected exactly one argument")
          match vargs[0] {
            @cps.ValueVar(id) =>
              // the dealiased `y`, not the let-bound `x`
              assert_true(id.uid() == y.uid(), msg="expected the dealiased `y`")
            _ => assert_true(false, msg="expected a value variable")
          }
        }
        _ => assert_true(false, msg="expected a jump")
      }
    _ => assert_true(false, msg="expected a toplevel val")
  }
}

///|
test "cps.transform: inlines a value binding (static continuation)" {
  let x = tv("x")
  let main = tb("main")
  // val x = 42; return x
  let stmt = @core.Stmt::Val(
    x,
    @core.Stmt::Return(int_expr(42)),
    @core.Stmt::Return(@core.Expr::ValueVar(x, @symbols.t_int())),
  )
  let module = @cps.transform(core_module(@core.ToplevelVal(main, stmt), main))
  match module.definitions[0] {
    @cps.ToplevelVal(_id, _ks, _k, binding) =>
      match binding {
        @cps.Jump(_k2, vargs, _ks2) => {
          assert_true(vargs.length() == 1, msg="expected exactly one argument")
          match vargs[0] {
            @cps.Literal(@source.LInt(42), _) =>
              assert_true(true, msg="the value is inlined")
            _ => assert_true(false, msg="expected the literal 42")
          }
        }
        _ => assert_true(false, msg="expected a jump")
      }
    _ => assert_true(false, msg="expected a toplevel val")
  }
}

///|
test "cps.transform: an application passes metacont and continuation" {
  let f = tb("f")
  let main = tb("main")
  // def f = { () => return 1 }; f()
  let definition = @core.Block::BlockLit(
    @core.BlockLit::new([], [], [], [], @core.Stmt::Return(int_expr(1))),
  )
  let stmt = @core.Stmt::Def(
    f,
    definition,
    @core.Stmt::App(
      @core.Block::BlockVar(
        @core.BlockVar::new(
          f,
          @core.unknown_block_type(),
          @symbols.Captures::empty(),
        ),
      ),
      [],
      [],
      [],
    ),
  )
  let module = @cps.transform(core_module(@core.ToplevelVal(main, stmt), main))
  match module.definitions[0] {
    @cps.ToplevelVal(_id, ks, k, binding) =>
      match binding {
        @cps.LetDef(id, _block, body) => {
          assert_true(id.uid() == f.uid(), msg="expected the definition of `f`")
          match body {
            @cps.App(callee, vargs, bargs, meta, cont) => {
              assert_true(vargs.length() == 0 && bargs.length() == 0)
              assert_true(
                callee is @cps.BlockVar(_),
                msg="expected a block variable",
              )
              assert_true(
                meta.id.uid() == ks.uid(),
                msg="the metacontinuation is the enclosing one",
              )
              match cont {
                @cps.ContVar(k2) =>
                  assert_true(
                    k2.uid() == k.uid(),
                    msg="the continuation is the enclosing one",
                  )
                _ => assert_true(false, msg="expected a continuation variable")
              }
            }
            _ => assert_true(false, msg="expected an application")
          }
        }
        _ => assert_true(false, msg="expected a let definition")
      }
    _ => assert_true(false, msg="expected a toplevel val")
  }
}

// ---------------------------------------------------------------------------
// contify
// ---------------------------------------------------------------------------

///|
test "cps.contify: a block that always returns to the same continuation becomes a continuation" {
  let f = tb("f")
  let ks = tb("ks")
  let k = tb("k")
  let k2 = tb("k2")
  let main = tb("main")
  // let f (ks) (k) = jump k(1)[ks]
  // f() returning to k2
  let lit = @cps.BlockLit::new(
    [],
    [],
    ks,
    k,
    @cps.Jump(k, [int_pure(1)], @cps.MetaCont::new(ks)),
  )
  let rest = @cps.App(
    @cps.Block::BlockVar(f),
    [],
    [],
    @cps.MetaCont::new(ks),
    @cps.ContVar(k2),
  )
  let module = @cps.ModuleDecl::new(
    "test",
    [],
    [],
    [],
    [
      @cps.ToplevelVal(
        main,
        ks,
        k,
        @cps.LetDef(f, @cps.Block::BlockLit(lit), rest),
      ),
    ],
    [main],
  )
  let rewritten = @cps.contify(module)
  match rewritten.definitions[0] {
    @cps.ToplevelVal(_id, _ks, _k, binding) =>
      match binding {
        @cps.LetCont(id, lam, body) => {
          assert_true(
            id.uid() == f.uid(),
            msg="the definition becomes a continuation",
          )
          // the continuation now returns to `k2`
          match lam.body {
            @cps.Jump(k3, _vargs, _ks3) =>
              assert_true(
                k3.uid() == k2.uid(),
                msg="the continuation of the block is substituted",
              )
            _ => assert_true(false, msg="expected a jump")
          }
          // and the call site is contified into a jump
          match body {
            @cps.Jump(callee, vargs, _ks4) => {
              assert_true(
                callee.uid() == f.uid(),
                msg="the call becomes a jump to the continuation",
              )
              assert_true(vargs.length() == 0)
            }
            _ => assert_true(false, msg="expected a jump")
          }
        }
        _ => assert_true(false, msg="expected a let continuation")
      }
    _ => assert_true(false, msg="expected a toplevel val")
  }
}

///|
test "cps.contify: a block used as a value is not contified" {
  let f = tb("f")
  let ks = tb("ks")
  let k = tb("k")
  let k2 = tb("k2")
  let main = tb("main")
  let lit = @cps.BlockLit::new(
    [],
    [],
    ks,
    k,
    @cps.Jump(k, [int_pure(1)], @cps.MetaCont::new(ks)),
  )
  // f is passed as a block argument: it escapes
  let rest = @cps.App(
    @cps.Block::BlockVar(k2),
    [],
    [@cps.Block::BlockVar(f)],
    @cps.MetaCont::new(ks),
    @cps.ContVar(k2),
  )
  let module = @cps.ModuleDecl::new(
    "test",
    [],
    [],
    [],
    [
      @cps.ToplevelVal(
        main,
        ks,
        k,
        @cps.LetDef(f, @cps.Block::BlockLit(lit), rest),
      ),
    ],
    [main],
  )
  let rewritten = @cps.contify(module)
  match rewritten.definitions[0] {
    @cps.ToplevelVal(_id, _ks, _k, binding) =>
      match binding {
        @cps.LetDef(id, _block, _body) =>
          assert_true(
            id.uid() == f.uid(),
            msg="the definition is left alone since the block escapes",
          )
        _ => assert_true(false, msg="expected a let definition")
      }
    _ => assert_true(false, msg="expected a toplevel val")
  }
}
