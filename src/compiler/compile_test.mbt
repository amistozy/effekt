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
}

///|
test "parses the hello world example" {
  let ctx = @source.Context::new(@source.Config::default())
  let src = @util.Source::new(
    "hello.effekt", "def main() = {\n  println(\"Hello, world!\")\n}\n",
  )
  let tree = @source.parse_module_decl(src, ctx).unwrap()
  assert_eq(tree.path, "hello")
  assert_eq(tree.defs.length(), 1)
}

///|
test "parses an effect declaration" {
  let ctx = @source.Context::new(@source.Config::default())
  let src = @util.Source::new(
    "prog.effekt", "interface Exc {\n  def raise(msg: String): Nothing\n}\n",
  )
  let tree = @source.parse_module_decl(src, ctx).unwrap()
  assert_eq(tree.defs.length(), 1)
}

///|
test "parses a namespace" {
  let ctx = @source.Context::new(@source.Config::default())
  let src = @util.Source::new(
    "prog.effekt", "namespace foo {\n  def bar(): Int = 42\n}\n",
  )
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
    @util.EffektError::Internal(msg) => ctx.info("internal: " + msg)
  }
  ctx.messages.copy()
}

///|
test "frontend accepts a well-typed program" {
  let messages = check_program(
    "ok.effekt",
    "def id[A](x: A): A = x\n" +
    "def main() = {\n  val y = id(42)\n  val z = id(\"hi\")\n}\n",
  )
  let errors = messages.filter(m => m.severity == @util.Error)
  assert_true(errors.length() == 0)
}

///|
test "frontend rejects ill-typed programs" {
  let messages = check_program(
    "bad.effekt", "def main() = {\n  val x: Int = \"nope\"\n}\n",
  )
  let errors = messages.filter(m => m.severity == @util.Error)
  assert_true(errors.length() > 0)
}

///|
/// Compiles a file with the real driver (loading the standard library from
/// `libraries/`), stopping before code generation.
fn frontend_only(
  input : String,
) -> @compiler.CompileResult raise @util.EffektError {
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
    resolve: fn(tree, ctx, deps) raise @util.EffektError {
      @namer.resolve_module(tree, ctx, deps)
    },
    typecheck: fn(tree, ctx) raise @util.EffektError {
      let desugared = @typer.unbox_inference(tree, ctx)
      @typer.typecheck(desugared, ctx)
      desugared
    },
    emit: fn(_trees, _ctx) raise @util.EffektError { "" },
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
  let src = @util.Source::new(
    "m.effekt",
    "type List[A] { Cons(head: A, tail: List[A]); Nil() }\n" +
    "def len[A](xs: List[A]): Int = xs match {\n" +
    "  case Cons(h, t) => 1 + len(t)\n" +
    "  case Nil() => 0\n" +
    "}\n",
  )
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
  let messages = check_program(
    "unused.effekt",
    "effect Fail(): Unit\n" +
    "def main() = {\n  try {\n    4\n  } with Fail { () => 0 }\n  ()\n}\n",
  )
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
  let messages = check_program(
    "instantiated.effekt",
    "interface Exception[E] { def raise(e: E, msg: String): Nothing }\n" +
    "def raise[A, E](e: E, msg: String): A / Exception[E] =\n" +
    "  do raise(e, msg) match {}\n" +
    "def main() = {\n" +
    "  val r = try { raise(1, \"boom\") } with Exception[Int] {\n" +
    "    def raise(e, msg) = 0\n" +
    "  }\n" +
    "  println(r)\n" +
    "}\n",
  )
  let warnings = messages.filter(m => m.severity == @util.Warning)
  if warnings.length() > 0 {
    println(@compiler.render_messages(warnings))
  }
  assert_true(warnings.length() == 0)
}
