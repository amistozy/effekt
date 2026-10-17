// Blackbox tests for the JavaScript backend trees and pretty printer.
//
// The trees are hand-built (no parser, no CPS transformer) so that the exact
// printed output of the `PrettyPrinter` port is pinned down.
//
// Note: the output follows kiama's `hsep(docs, comma)`, which does not insert a
// space after the comma (`(ks,k)`), and every `const`/`let`/`return` is
// terminated by `;`, exactly like `generator/js/PrettyPrinter.scala`.

///|
fn jname(s : String) -> @symbols.JSName {
  @symbols.JSName::new(s)
}

///|
fn variable(s : String) -> @js.Expr {
  @js.Variable(jname(s))
}

///|
fn run_toplevel(name : String) -> @js.Expr {
  @js.call(variable("RUN_TOPLEVEL"), [variable(name)])
}

///|
/// `const main = (ks, k) => { return RUN_TOPLEVEL(main_1); }`
fn main_binding() -> @js.Stmt {
  @js.Const(
    @js.PatternVariable(jname("main")),
    @js.Lambda(
      [jname("ks"), jname("k")],
      @js.Block([@js.Return(run_toplevel("main_1"))]),
    ),
  )
}

///|
test "js pretty: module skeleton (virtual)" {
  let m = @js.Module::new(jname("mymod"), [], [], [main_binding()])
  let expected =
    #|const $effekt = {};
    #|const mymod = {};
    #|const main = (ks,k) => {
    #|  return RUN_TOPLEVEL(main_1);
    #|};
    #|module.exports = {};
  assert_eq(@js.show_stmts(m.virtual()), expected)
}

///|
test "js pretty: module skeleton (commonjs)" {
  let m = @js.Module::new(jname("mymod"), [], [], [main_binding()])
  let stmts = m.commonjs()
  assert_eq(stmts.length(), 3)
  let rendered = @js.show_stmts(stmts)
  assert_true(rendered.contains("const $effekt = {};\n"))
  let main_decl =
    #|const main = (ks,k) => {
    #|  return RUN_TOPLEVEL(main_1);
    #|};
  assert_true(rendered.contains(main_decl))
  assert_true(
    rendered.contains(
      "(typeof module != \"undefined\" && module !== null ? module : {}).exports = mymod = {};",
    ),
  )
}

///|
test "js pretty: import statements" {
  let m = @js.Module::new(
    jname("mymod"),
    [
      @js.ImportAll(jname("dep"), "dep.js"),
      @js.ImportSelective([jname("x"), jname("y")], "other.js"),
    ],
    [],
    [],
  )
  let expected =
    #|const $effekt = {};
    #|const dep = load("dep.js");
    #|const {x,y} = load("other.js");
    #|const mymod = {};
    #|module.exports = {};
  assert_eq(@js.show_stmts(m.virtual()), expected)
}

///|
test "js pretty: switch/case" {
  let stmt = @js.Switch(
    variable("sc"),
    [
      @js.SwitchBranch::new(@js.raw_expr("0"), [
        @js.Return(@js.js_string("zero")),
      ]),
      @js.SwitchBranch::new(@js.raw_expr("1"), [
        @js.Return(@js.js_string("one")),
      ]),
    ],
    Some([@js.Return(@js.js_string("other"))]),
  )
  let expected =
    #|switch (sc) {
    #|  case 0: return "zero";
    #|  case 1: return "one";
    #|  default: return "other";
    #|}
  assert_eq(@js.show_stmt(stmt), expected)
}

///|
test "js pretty: while loop with label" {
  let body = @js.Assign(variable("i"), @js.Expr::RawExpr(["i + 1"], []))
  let labelled = @js.While(
    @js.Expr::RawExpr(["i < 10"], []),
    [body, @js.If(@js.Expr::RawExpr(["i == 5"], []), @js.Break, @js.Block([]))],
    Some(jname("loop")),
  )
  let expected =
    #|loop: while (i < 10) {
    #|  i = i + 1;
    #|  if (i == 5) {
    #|    break;
    #|  }
    #|}
  assert_eq(@js.show_stmt(labelled), expected)
}

///|
test "js pretty: unlabelled while loop and continue" {
  let stmt = @js.While(
    @js.Expr::RawExpr(["i < 10"], []),
    [
      @js.If(
        @js.Expr::RawExpr(["i == 5"], []),
        @js.Continue(None),
        @js.Block([]),
      ),
    ],
    None,
  )
  let expected =
    #|while (i < 10) {
    #|  if (i == 5) {
    #|    continue;
    #|  }
    #|}
  assert_eq(@js.show_stmt(stmt), expected)
}

///|
test "js pretty: calls, members and objects" {
  let e = @js.method_call(@js.effekt_field("fresh"), jname("push"), [
    @js.js_string("x"),
    @js.Expr::RawLiteral("42"),
  ])
  assert_eq(@js.show_expr(e), "$effekt.fresh.push(\"x\",42)")
}

///|
test "js pretty: object literal" {
  let e = @js.Object([
    @js.ObjectProperty::new(jname("run"), variable("main")),
    @js.ObjectProperty::new(jname("resume"), variable("k")),
  ])
  assert_eq(@js.show_expr(e), "{ run: main,resume: k }")
}

///|
test "js pretty: raw expression splicing" {
  let e = @js.Expr::RawExpr(["return ", " + ", ";"], [
    variable("x"),
    @js.Expr::RawLiteral("1"),
  ])
  assert_eq(@js.show_expr(e), "return x + 1;")
}

///|
test "js pretty: function declaration from a lambda is flattened" {
  let binding = @js.js_const(
    jname("main"),
    @js.Lambda(
      [jname("ks"), jname("k")],
      @js.Block([@js.Return(run_toplevel("main_1"))]),
    ),
  )
  assert_true(binding is @js.Function(_, _, _))
  let expected =
    #|function main(ks,k) {
    #|  return RUN_TOPLEVEL(main_1);
    #|}
  assert_eq(@js.show_stmt(binding), expected)
}

///|
test "js codegen monad: traverse, stmts, block and to_expr" {
  let b : @js.Binding[Array[@js.Expr]] = @js.traverse([1, 2], i => {
    @js.pure(variable("x\{i}"))
  })
  let with_return = b.flat_map(xs => {
    @js.pure([@js.Return(@js.call(variable("f"), xs))])
  })
  assert_eq(with_return.stmts().length(), 1)
  // a binding whose only statement is a return is the returned expression
  assert_eq(@js.show_expr(with_return.to_expr()), "f(x1,x2)")
  let two : @js.Binding[Array[@js.Stmt]] = @js.pure([
    @js.Const(@js.PatternVariable(jname("y")), @js.Expr::RawLiteral("1")),
    @js.Return(variable("y")),
  ])
  let block_js =
    #|{
    #|  const y = 1;
    #|  return y;
    #|}
  assert_eq(@js.show_stmt(two.block()), block_js)
  let expr_js =
    #|(() => {
    #|  const y = 1;
    #|  return y;
    #|})()
  assert_eq(@js.show_expr(two.to_expr()), expr_js)
}
