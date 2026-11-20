// Blackbox tests for the pass that drops unique value bindings. The
// expectations are the printed definitions, like the normalizer's tests.

///|
/// `def main() = { <body> }`, returning the module and the `main` symbol (the
/// entry point of `drop_bindings`).
fn main_module(body : @core.Stmt) -> (@core.ModuleDecl, @symbols.Sym) {
  let main = bsym("main")
  let m = @core.ModuleDecl(
    "test",
    [],
    [],
    [],
    [
      @core.ToplevelDef(
        main,
        @core.BlockLit(@core.BlockLit::BlockLit([], [], [], [], body)),
      ),
    ],
    [],
  )
  (m, main)
}

///|
fn dropped(
  m : @core.ModuleDecl,
  main : @symbols.Sym,
) -> String raise @util.EffektError {
  @core.show_core_toplevels(@core.drop_bindings(m, [main]).definitions)
}

///|
/// A block literal whose body is `body`.
fn lit(body : @core.Stmt) -> @core.Block {
  @core.BlockLit(@core.BlockLit::BlockLit([], [], [], [], body))
}

///|
test "drop-bindings: a binding that is used once is inlined" {
  let x = xsym("x")
  let (m, main) = main_module(
    @core.Let(x, int_lit(42), @core.Return([int_var(x)])),
  )
  let expected =
    #|def main() = {
    #|  return 42
    #|}
  assert_eq(dropped(m, main), expected)
}

///|
test "drop-bindings: a binding that is used twice stays" {
  let x = xsym("x")
  let (m, main) = main_module(
    @core.Let(x, int_lit(42), @core.Return([int_var(x), int_var(x)])),
  )
  let expected =
    #|def main() = {
    #|  let x = 42
    #|  return x,x
    #|}
  assert_eq(dropped(m, main), expected)
}

///|
/// A reference inside a block that is called is one reference per call, so the
/// binding may not move into the block (upstream's `usedInCalledBlock`).
test "drop-bindings: a binding used inside a called block stays" {
  let n = xsym("n")
  let go = bsym("go")
  let (m, main) = main_module(
    @core.Let(
      n,
      int_lit(1),
      @core.Def(
        go,
        lit(@core.Return([int_var(n)])),
        @core.App(@core.BlockVar(bvar(go)), [], [], []),
      ),
    ),
  )
  let expected =
    #|def main() = {
    #|  let n = 1
    #|  def go() = {
    #|    return n
    #|  }
    #|  go()
    #|}
  assert_eq(dropped(m, main), expected)
}

///|
/// An immediately applied block literal runs in place, so a reference inside it
/// is in the scope of the enclosing block and the binding can move in.
test "drop-bindings: an applied block literal is in place" {
  let n = xsym("n")
  let (m, main) = main_module(
    @core.Let(
      n,
      int_lit(1),
      @core.App(lit(@core.Return([int_var(n)])), [], [], []),
    ),
  )
  let expected =
    #|def main() = {
    #|  { () => return 1
    #|  }()
    #|}
  assert_eq(dropped(m, main), expected)
}
