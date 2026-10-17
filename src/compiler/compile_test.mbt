// End-to-end smoke tests for the driver: parsing, module loading and the
// search path handling.

///|
test "module path of a file" {
  assert_eq(@compiler.module_path_of("examples/hello.effekt"), "hello")
  assert_eq(
    @compiler.module_path_of("libraries/common/effekt.effekt"),
    "effekt",
  )
  assert_eq(@compiler.module_path_of("C:\\work\\hello.effekt"), "hello")
}

///|
test "default output path" {
  assert_eq(
    @compiler.default_output("examples/hello.effekt"),
    "examples/hello.js",
  )
  assert_eq(@compiler.default_output("hello"), "hello.js")
}

///|
test "command line parsing" {
  let (opts, errors) = @compiler.parse_args([
    "-I", "lib", "--lib", "stdlib", "-o", "out.js", "main.effekt",
  ])
  assert_eq(errors.length(), 0)
  assert_eq(opts.input, "main.effekt")
  assert_eq(opts.output, Some("out.js"))
  assert_eq(opts.include_paths, ["lib"])
  assert_eq(opts.lib_path, "stdlib")
}

///|
test "command line parsing reports unknown options" {
  let (_, errors) = @compiler.parse_args(["--nope"])
  assert_eq(errors.length(), 1)
  // argparse renders the diagnostic together with the usage text.
  assert_true(errors[0].contains("unexpected argument"))
  assert_true(errors[0].contains("Usage: effekt"))
}

///|
test "command line parsing reports a missing option value" {
  let (_, errors) = @compiler.parse_args(["--output"])
  assert_eq(errors.length(), 1)
  assert_true(errors[0].contains("--output"))
}

///|
test "command line parsing rejects a second positional argument" {
  let (opts, errors) = @compiler.parse_args(["a.effekt", "b.effekt"])
  assert_eq(errors.length(), 1)
  assert_eq(opts.input, "")
}

///|
test "command line defaults" {
  let (opts, errors) = @compiler.parse_args([])
  assert_eq(errors.length(), 0)
  assert_eq(opts.input, "")
  assert_eq(opts.output, None)
  assert_eq(opts.include_paths, [])
  // argparse fills the declared default in.
  assert_eq(opts.lib_path, "libraries")
  assert_true(!opts.show_help)
  assert_true(!opts.run)
}

///|
test "command line parsing collects repeated options and all flags" {
  let (opts, errors) = @compiler.parse_args([
    "-I", "a", "--include", "b", "-I", "c", "--show-core", "--show-cps", "--show-js",
    "--run", "main.effekt",
  ])
  assert_eq(errors.length(), 0)
  assert_eq(opts.include_paths, ["a", "b", "c"])
  assert_true(opts.show_core)
  assert_true(opts.show_cps)
  assert_true(opts.show_js)
  assert_true(opts.run)
  assert_eq(opts.input, "main.effekt")
}

///|
test "the help flag is recognised in both spellings" {
  assert_true(@compiler.parse_args(["-h"]).0.show_help)
  assert_true(@compiler.parse_args(["--help"]).0.show_help)
  assert_true(@compiler.parse_args(["main.effekt", "--help"]).0.show_help)
}

///|
test "the help text documents every option" {
  let help = @compiler.usage()
  for
    flag in [
      "-h, --help", "--show-core", "--show-cps", "--show-js", "--run", "-o, --output",
      "-I, --include", "--lib", "input",
    ] {
    assert_true(help.contains(flag))
  }
  // `usage` is printed with `println`, so it must not end in a newline.
  assert_true(!help.has_suffix("\n"))
}

///|
test "parses the hello world example" {
  let ctx = @source.Context::new(@source.Config::default())
  let hello =
    #|def main() = {
    #|  println("Hello, world!")
    #|}
    #|
  let src = @util.Source::new("hello.effekt", hello)
  let tree = @source.parse_module_decl(src, ctx).unwrap()
  assert_eq(tree.path, "hello")
  assert_eq(tree.defs.length(), 1)
}

///|
test "parses an effect declaration" {
  let ctx = @source.Context::new(@source.Config::default())
  let exc =
    #|interface Exc {
    #|  def raise(msg: String): Nothing
    #|}
    #|
  let src = @util.Source::new("prog.effekt", exc)
  let tree = @source.parse_module_decl(src, ctx).unwrap()
  assert_eq(tree.defs.length(), 1)
}

///|
test "parses a namespace" {
  let ctx = @source.Context::new(@source.Config::default())
  let ns =
    #|namespace foo {
    #|  def bar(): Int = 42
    #|}
    #|
  let src = @util.Source::new("prog.effekt", ns)
  let tree = @source.parse_module_decl(src, ctx).unwrap()
  assert_eq(tree.defs.length(), 1)
}

///|
/// Runs the whole frontend on a self-contained snippet (no prelude) and
/// returns the diagnostics.
fn check_program(name : String, text : String) -> Array[@util.Message] {
  let ctx = @source.Context::new(@source.Config::default())
  let src = @util.Source::new(name, text)
  try {
    let tree = @source.parse_module_decl(src, ctx).unwrap()
    @namer.resolve(tree, ctx)
    let desugared = @typer.unbox_inference(tree, ctx)
    let _ = @typer.typecheck(desugared, ctx)
  } catch {
    @util.EffektError::Fatal(msg) => ctx.info(msg)
    @util.EffektError::Internal(msg) => ctx.info("internal: \{msg}")
  }
  ctx.messages.copy()
}

///|
test "frontend accepts a well-typed program" {
  let text =
    #|def id[A](x: A): A = x
    #|def main() = {
    #|  val y = id(42)
    #|  val z = id("hi")
    #|}
    #|
  let messages = check_program("ok.effekt", text)
  let errors = messages.filter(m => m.severity == @util.Error)
  assert_true(errors.length() == 0)
}

///|
test "frontend rejects ill-typed programs" {
  let text =
    #|def main() = {
    #|  val x: Int = "nope"
    #|}
    #|
  let messages = check_program("bad.effekt", text)
  let errors = messages.filter(m => m.severity == @util.Error)
  assert_true(errors.length() > 0)
}

///|
/// Compiles a file with the real driver (loading the standard library from
/// `libraries/`), stopping before code generation.
fn frontend_only(input : String) -> @compiler.CompileResult {
  let opts : @compiler.Options = {
    input,
    output: None,
    include_paths: [],
    lib_path: "libraries",
    show_help: false,
    show_core: false,
    show_cps: false,
    show_js: false,
    run: false,
  }
  let pipeline : @compiler.Pipeline = {
    parse: @source.parse_module_decl,
    resolve: (tree, ctx, deps) => @namer.resolve_module(tree, ctx, deps),
    typecheck: (tree, ctx) => {
      let desugared = @typer.unbox_inference(tree, ctx)
      @typer.typecheck(desugared, ctx)
      desugared
    },
    emit: (_trees, _ctx) => "",
  }
  @compiler.compile_file(opts, pipeline, @source.Config::default())
}

///|
test "loads and checks the standard library prelude" {
  let result = frontend_only("examples/hello.effekt")
  let errors = result.messages.filter(m => m.severity == @util.Error)
  if errors.length() > 0 {
    println(@compiler.render_messages(errors))
  }
  assert_true(errors.length() == 0)
}

///|
test "parses a match expression" {
  let ctx = @source.Context::new(@source.Config::default())
  let text =
    #|type List[A] { Cons(head: A, tail: List[A]); Nil() }
    #|def len[A](xs: List[A]): Int = xs match {
    #|  case Cons(h, t) => 1 + len(t)
    #|  case Nil() => 0
    #|}
    #|
  let src = @util.Source::new("m.effekt", text)
  let tree = @source.parse_module_decl(src, ctx).unwrap()
  assert_eq(tree.defs.length(), 2)
}

///|
/// Checking a program must not report warnings for the prelude.
///
/// In particular the `stop` handler of `loop` (and of `boundary`) *is* used: a
/// result annotation without a `/ …` clause binds no capability, so the effects
/// that a nested, annotated `def` performs escape the definition and are
/// attributed to the enclosing statement, where the handler sees them
/// (upstream: `Result(annotated, effs -- bound)`).
test "the prelude compiles without warnings" {
  let result = frontend_only("examples/hello.effekt")
  let warnings = result.messages.filter(m => m.severity == @util.Warning)
  if warnings.length() > 0 {
    println(@compiler.render_messages(warnings))
  }
  assert_true(warnings.length() == 0)
}

///|
/// ... but a handler for an effect the program really does not perform is still
/// reported. This is upstream's `examples/pos/unused_effects.effekt` (and its
/// `.check` file), which expects exactly one such warning.
test "an unused handler is still reported" {
  let text =
    #|effect Fail(): Unit
    #|def main() = {
    #|  try {
    #|    4
    #|  } with Fail { () => 0 }
    #|  ()
    #|}
    #|
  let messages = check_program("unused.effekt", text)
  let warnings = messages.filter(m => m.severity == @util.Warning)
  if warnings.length() != 1 {
    println(@compiler.render_messages(warnings))
  }
  assert_true(warnings.length() == 1)
}

///|
/// The effect a generic operation instantiates is recognised as handled, even
/// though it is inferred through a unification variable: `raise(1, "boom")`
/// performs `Exception[Int]`, so the `Exception[Int]` handler is used
/// (`examples/import_handler.effekt`).
test "an instantiated handler is recognised as used" {
  let text =
    #|interface Exception[E] { def raise(e: E, msg: String): Nothing }
    #|def raise[A, E](e: E, msg: String): A / Exception[E] =
    #|  do raise(e, msg) match {}
    #|def main() = {
    #|  val r = try { raise(1, "boom") } with Exception[Int] {
    #|    def raise(e, msg) = 0
    #|  }
    #|  println(r)
    #|}
    #|
  let messages = check_program("instantiated.effekt", text)
  let warnings = messages.filter(m => m.severity == @util.Warning)
  if warnings.length() > 0 {
    println(@compiler.render_messages(warnings))
  }
  assert_true(warnings.length() == 0)
}

///|
/// A handler that is passed as a *function* (`with handler[Int]`, where the
/// function's block parameter carries the handled effect) must handle a
/// polymorphic operation. The effect in the expected parameter type is still an
/// unsolved unification variable when the body starts to be checked, so it has
/// to be pruned before it is subtracted from the body's effects — otherwise the
/// operation is reported as unhandled. This is the shape of
/// `stream::zip`/`zipLongest` (`with source[A] { stream1 }`), which used to
/// fail to typecheck.
test "a handler function handles a polymorphic operation" {
  let text =
    #|effect tick[A](value: A): Unit
    #|def handler[A] { body: () => Unit / tick[A] }: Unit =
    #|  try { body() } with tick[A] { (value) => resume(()) }
    #|def main(): Unit = {
    #|  with handler[Int]
    #|  do tick[Int](1)
    #|}
    #|
  let messages = check_program("handler_function.effekt", text)
  let errors = messages.filter(m => m.severity == @util.Error)
  if errors.length() > 0 {
    println(@compiler.render_messages(errors))
  }
  assert_true(errors.length() == 0)
}

///|
/// A mutable variable allocated in an explicit region (`var k in r = ...`,
/// which the namer binds as a `RegBinder`) is a reference like any other: its
/// block type is `Ref[S]`, not `Region`. `stream::teeing` allocates one, and the
/// core transformation used to abort when it was selected.
test "a variable in an explicit region is a reference" {
  let text =
    #|def main(): Unit = {
    #|  region r {
    #|    var k in r = box { () }
    #|    k = box { () }
    #|    k()
    #|  }
    #|}
    #|
  let messages = check_program("region_var.effekt", text)
  let errors = messages.filter(m => m.severity == @util.Error)
  if errors.length() > 0 {
    println(@compiler.render_messages(errors))
  }
  assert_true(errors.length() == 0)
}

///|
/// Uniform function call syntax on a *block parameter* has to keep looking in
/// the enclosing scopes: `lookupFirstBlockParam` only stops at the innermost
/// scope that *binds* the name, so `eq` of `contains` stays visible inside the
/// nested block literal (`list.contains` in the standard library does this).
test "a block parameter is visible inside a nested block literal" {
  let text =
    #|def apply[A](x: A) { f: A => Bool }: Bool = f(x)
    #|def contains[A](x: A) { eq: (A, A) => Bool }: Bool = apply(x) { y => y.eq(x) }
    #|def main() = contains(1) { (a, b) => true }
    #|
  let messages = check_program("ufcs_block_param.effekt", text)
  let errors = messages.filter(m => m.severity == @util.Error)
  if errors.length() > 0 {
    println(@compiler.render_messages(errors))
  }
  assert_true(errors.length() == 0)
}

///|
/// `do emit(Empty())` performs `emit[Box[?T]]` because `Empty()` has no
/// argument to infer `T` from. The declaration says `emit[Box[A]]`, so the
/// capability has to be found by unifying against the capabilities in scope
/// (upstream `BindSome.tryLexicalCapabilityFor`).
test "an unsolved effect argument is solved from the declaration" {
  let text =
    #|type Box[A] {
    #|  Empty()
    #|  Full(value: A)
    #|}
    #|interface emit[T] {
    #|  def emit(value: T): Unit
    #|}
    #|def produce[A](): Unit / emit[Box[A]] = { do emit(Empty()) }
    #|
  let messages = check_program("effect_arg.effekt", text)
  let errors = messages.filter(m => m.severity == @util.Error)
  if errors.length() > 0 {
    println(@compiler.render_messages(errors))
  }
  assert_true(errors.length() == 0)
}

///|
/// `list.effekt` defines `each` and `contains` without result annotations and
/// uses them across modules (`list::each`, `list::any`); their inferred types
/// only exist in the context annotations of the module that defined them.
test "a library module that uses cross-module inferred types type-checks" {
  let result = frontend_only("libraries/common/list.effekt")
  assert_true(!result.failed)
}

///|
/// Checks a file with the real driver and prints the diagnostics when it fails.
fn frontend_accepts(input : String) -> Bool {
  let result = frontend_only(input)
  if result.failed {
    println("frontend rejected \{input}:")
    println(@compiler.render_messages(result.messages))
  }
  !result.failed
}

///|
/// `for[A] { stream: () => Unit / emit[A] } { action: A => Unit }` has to check
/// `action` *first*: its parameter annotation is what makes the effect of the
/// first block argument (`emit[Char]`) concrete before capabilities are bound
/// for it (upstream `checkCallTo` checks the arguments that do not subtract
/// effects first).
test "a block argument solves the effect argument of an earlier argument" {
  assert_true(frontend_accepts("libraries/common/string.effekt"))
}

///|
/// A program file may be named like a prelude module. The prelude module of the
/// same name still has to be loaded from the library instead of resolving to
/// the main module.
test "a program named like a prelude module still gets the prelude" {
  assert_true(frontend_accepts("examples/exception.effekt"))
}

///|
/// `<module>::foo` refers to `foo` inside the module, for a single-segment
/// module path as well (`set::collect` in `set.effekt`).
test "a module can qualify its own definitions" {
  assert_true(frontend_accepts("libraries/common/set.effekt"))
}

///|
/// The standard library's `ref` module defines a *value* type `Ref`, which must
/// not be shadowed by the core `Ref` state interface (a core builtin only, like
/// upstream's `builtins.coreBuiltins`).
test "a value type named Ref is not shadowed by the core Ref" {
  assert_true(frontend_accepts("libraries/common/dictionary.effekt"))
}

///|
/// `extern include chez "text/pregexp.scm"` is only needed by the Chez backend:
/// the file is not read (and does not have to exist) for JavaScript.
test "a Chez-only extern include is not loaded for JavaScript" {
  assert_true(frontend_accepts("libraries/common/regex.effekt"))
}
