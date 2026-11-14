// Blackbox tests for the normalizer. The expectations are the printed
// definitions, so a test pins the inlining decision *and* the shape of the
// result (upstream prints definitions separated by a single line break).

///|
fn inlined(body : @core.Stmt) -> @core.BlockLit {
  @core.BlockLit::new([], [], [], [], body)
}

///|
fn identity_block(x : @symbols.Sym) -> @core.Block {
  @core.BlockLit(
    @core.BlockLit::new(
      [],
      [],
      [@core.ValueParam(x, @core.t_int())],
      [],
      @core.Return([int_var(x)]),
    ),
  )
}

///|
fn normalize_module(
  m : @core.ModuleDecl,
  main : @symbols.Sym,
  policy : @core.InliningPolicy,
) -> String raise @util.EffektError {
  @core.show_core_toplevels(@core.normalize(m, [main], policy).definitions)
}

///|
/// `def f = { (x) => return x }; def main = { () => body }`, where the body is
/// built from the symbol of `f`.
fn apply_to_identity(
  policy : @core.InliningPolicy,
  body : (@symbols.Sym) -> @core.Stmt,
) -> String raise @util.EffektError {
  let f = bsym("f")
  let main = bsym("main")
  let module = @core.ModuleDecl(
    "test",
    [],
    [],
    [],
    [
      @core.ToplevelDef(f, identity_block(xsym("x"))),
      @core.ToplevelDef(main, @core.BlockLit(inlined(body(f)))),
    ],
    [],
  )
  normalize_module(module, main, policy)
}

///|
test "normalize: a used-once callee is inlined" {
  let expected =
    #|def f(x: Int) = {
    #|  return x
    #|}
    #|def main() = {
    #|  return 42
    #|}
  assert_eq(
    apply_to_identity(@core.InliningPolicy::Unique(50), f => {
      @core.App(@core.BlockVar(bvar(f)), [], [int_lit(42)], [])
    }),
    expected,
  )
}

///|
test "normalize: a used-once callee is inlined even over the budget" {
  // `Unique` inlines a callee that is used exactly once regardless of its size
  let expected =
    #|def f(x: Int) = {
    #|  return x
    #|}
    #|def main() = {
    #|  return 42
    #|}
  assert_eq(
    apply_to_identity(@core.InliningPolicy::Unique(0), f => {
      @core.App(@core.BlockVar(bvar(f)), [], [int_lit(42)], [])
    }),
    expected,
  )
}

///|
test "normalize: a recursive callee is kept" {
  let f = bsym("f")
  let main = bsym("main")
  // def f = { () => f() }; def main = { () => f() }
  let module = @core.ModuleDecl(
    "test",
    [],
    [],
    [],
    [
      @core.ToplevelDef(
        f,
        @core.BlockLit(inlined(@core.App(@core.BlockVar(bvar(f)), [], [], []))),
      ),
      @core.ToplevelDef(
        main,
        @core.BlockLit(inlined(@core.App(@core.BlockVar(bvar(f)), [], [], []))),
      ),
    ],
    [],
  )
  let expected =
    #|def f() = {
    #|  f()
    #|}
    #|def main() = {
    #|  f()
    #|}
  assert_eq(
    normalize_module(module, main, @core.InliningPolicy::Unique(50)),
    expected,
  )
}

///|
test "normalize: a callee used twice is kept by an empty budget" {
  let expected =
    #|def f(x: Int) = {
    #|  return x
    #|}
    #|def main() = {
    #|  val a = f(1);
    #|  f(2)
    #|}
  assert_eq(
    apply_to_identity(@core.InliningPolicy::Default(0, Some(0), 0), f => {
      @core.Val(
        [xsym("a")],
        @core.App(@core.BlockVar(bvar(f)), [], [int_lit(1)], []),
        @core.App(@core.BlockVar(bvar(f)), [], [int_lit(2)], []),
      )
    }),
    expected,
  )
}

///|
test "normalize: if on a known condition is folded" {
  let main = bsym("main")
  let module = @core.ModuleDecl(
    "test",
    [],
    [],
    [],
    [
      @core.ToplevelDef(
        main,
        @core.BlockLit(
          inlined(
            @core.If(
              @core.Literal(@source.LBool(true), @core.t_bool()),
              @core.Return([int_lit(1)]),
              @core.Return([int_lit(2)]),
            ),
          ),
        ),
      ),
    ],
    [],
  )
  let expected =
    #|def main() = {
    #|  return 1
    #|}
  assert_eq(
    normalize_module(module, main, @core.InliningPolicy::Unique(50)),
    expected,
  )
}

///|
test "normalize: val of a returned value is bound as a let" {
  let main = bsym("main")
  let x = xsym("x")
  // val x = return 42; return x
  let module = @core.ModuleDecl(
    "test",
    [],
    [],
    [],
    [
      @core.ToplevelDef(
        main,
        @core.BlockLit(
          inlined(
            @core.Val(
              [x],
              @core.Return([int_lit(42)]),
              @core.Return([int_var(x)]),
            ),
          ),
        ),
      ),
    ],
    [],
  )
  let expected =
    #|def main() = {
    #|  let x = 42
    #|  return x
    #|}
  assert_eq(
    normalize_module(module, main, @core.InliningPolicy::Unique(50)),
    expected,
  )
}

///|
test "normalize: val whose result is returned directly is dropped" {
  let main = bsym("main")
  let x = xsym("x")
  // val x = f(1); return x   ==>   f(1)
  let module = @core.ModuleDecl(
    "test",
    [],
    [],
    [],
    [
      @core.ToplevelDef(
        main,
        @core.BlockLit(
          inlined(
            @core.Val(
              [x],
              @core.App(@core.BlockVar(bvar(bsym("f"))), [], [int_lit(1)], []),
              @core.Return([int_var(x)]),
            ),
          ),
        ),
      ),
    ],
    [],
  )
  let expected =
    #|def main() = {
    #|  f(1)
    #|}
  assert_eq(
    normalize_module(module, main, @core.InliningPolicy::Unique(50)),
    expected,
  )
}

///|
test "normalize: a local unused definition is dropped" {
  let main = bsym("main")
  let unused = bsym("unused")
  // def main = { () => def unused = { (x) => return x }; return 0 }
  let module = @core.ModuleDecl(
    "test",
    [],
    [],
    [],
    [
      @core.ToplevelDef(
        main,
        @core.BlockLit(
          inlined(
            @core.Def(
              unused,
              identity_block(xsym("x")),
              @core.Return([int_lit(0)]),
            ),
          ),
        ),
      ),
    ],
    [],
  )
  let expected =
    #|def main() = {
    #|  return 0
    #|}
  assert_eq(
    normalize_module(module, main, @core.InliningPolicy::Unique(50)),
    expected,
  )
}
