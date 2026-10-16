// Blackbox tests for the Effekt parser (`src/source/parser.mbt`).

///|
fn parse_module(src : String) -> (@source.ModuleDecl?, String) {
  let ctx = @source.Context::new(@source.Config::default())
  let source = @util.Source::new("test.effekt", src)
  let decl = @source.parse_module_decl(source, ctx) catch {
    @util.Fatal(m) => {
      println("unexpected internal failure: " + m)
      None
    }
    @util.Internal(m) => {
      println("unexpected internal error: " + m)
      None
    }
  }
  (decl, render_messages(ctx))
}

///|
fn parse_expr(src : String) -> (@source.Term?, String) {
  let ctx = @source.Context::new(@source.Config::default())
  let source = @util.Source::new("test.effekt", src)
  let term = @source.parse_term(source, ctx) catch {
    @util.Fatal(m) => {
      println("unexpected internal failure: " + m)
      None
    }
    @util.Internal(m) => {
      println("unexpected internal error: " + m)
      None
    }
  }
  (term, render_messages(ctx))
}

///|
/// Renders the *error* diagnostics (warnings are ignored).
fn render_messages(ctx : @source.Context) -> String {
  let parts : Array[String] = []
  for m in ctx.messages {
    if m.severity == @util.Error {
      parts.push(m.render())
    }
  }
  let buf = StringBuilder()
  for i = 0; i < parts.length(); i = i + 1 {
    if i > 0 {
      buf.write_string("\n")
    }
    buf.write_string(parts[i])
  }
  buf.to_string()
}

///|
/// Parses a module and asserts that there were no diagnostics.
fn module_ok(src : String) -> @source.ModuleDecl raise {
  let (decl, messages) = parse_module(src)
  assert_eq(messages, "")
  match decl {
    Some(d) => d
    None => abort("parse failed")
  }
}

///|
/// Parses a term and asserts that there were no diagnostics.
fn term_ok(src : String) -> @source.Term raise {
  let (term, messages) = parse_expr(src)
  assert_eq(messages, "")
  match term {
    Some(t) => t
    None => abort("parse failed")
  }
}

///|
fn defs_of(d : @source.ModuleDecl) -> Array[@source.Def] {
  d.defs
}

// ---------------------------------------------------------------------------
// The snippets from the tour (as required by the task)
// ---------------------------------------------------------------------------

///|
test "parse: hello world" {
  let d = module_ok("def main() = println(\"Hello, world!\")")
  assert_eq(defs_of(d).length(), 1)
  assert_true(defs_of(d)[0].kind is FunDef(_, _, _, _, _, _, _))
}

///|
test "parse: fib" {
  let d = module_ok(
    "def fib(n: Int): Int = if (n < 2) n else fib(n - 1) + fib(n - 2)",
  )
  assert_eq(defs_of(d).length(), 1)
  match defs_of(d)[0].kind {
    FunDef(_, _, vparams, _, _, ret, _) => {
      assert_eq(vparams.length(), 1)
      assert_true(ret is Some(_))
    }
    _ => abort("expected a function definition")
  }
}

///|
test "parse: val in a block" {
  let d = module_ok("def main() = { val x = 42; println(x) }")
  assert_eq(defs_of(d).length(), 1)
  match defs_of(d)[0].kind {
    FunDef(_, _, _, _, _, _, body) => assert_true(body.kind is BlockStmt(_))
    _ => abort("expected a function definition")
  }
}

///|
test "parse: call with block argument" {
  let d = module_ok("def main() = each(1, 10) { x => println(x) }")
  assert_eq(defs_of(d).length(), 1)
}

///|
test "parse: each with block parameter and if/else" {
  let d = module_ok(
    "def each(n: Int, m: Int) { f: Int => Unit }: Unit =\n" +
    "  if (n >= m) () else { f(n); each(n + 1, m) { f } }",
  )
  assert_eq(defs_of(d).length(), 1)
  match defs_of(d)[0].kind {
    FunDef(_, _, vparams, bparams, _, _, _) => {
      assert_eq(vparams.length(), 2)
      assert_eq(bparams.length(), 1)
    }
    _ => abort("expected a function definition")
  }
}

///|
test "parse: effect and try/with" {
  let d = module_ok(
    "interface Exc { def raise(msg: String): Unit }\n" +
    "def main() = try { do raise(\"boom\") } with Exc { def raise(msg) = println(msg) }",
  )
  assert_eq(defs_of(d).length(), 2)
  assert_true(defs_of(d)[0].kind is InterfaceDef(_, _, _))
  assert_true(defs_of(d)[1].kind is FunDef(_, _, _, _, _, _, _))
}

///|
test "parse: try/with with a legacy effect declaration" {
  // `effect Foo { ... }` is parsed as an interface with the wrong keyword and
  // produces the "did you mean interface" diagnostic.
  let (decl, messages) = parse_module(
    "effect Exc { def raise(msg: String): Unit }\n" +
    "def main() = try { do raise(\"boom\") } with Exc { def raise(msg) = println(msg) }",
  )
  assert_true(decl is None)
  assert_true(messages.contains("did you mean to declare an interface"))
}

///|
test "parse: mutable variables" {
  let d = module_ok(
    "def main() = {\n  var x = 1;\n  x = x + 1;\n  println(x)\n}",
  )
  assert_eq(defs_of(d).length(), 1)
  match defs_of(d)[0].kind {
    FunDef(_, _, _, _, _, _, body) =>
      match body.kind {
        BlockStmt(inner) => assert_true(inner.kind is DefStmt(_, _))
        _ => abort("expected a block")
      }
    _ => abort("expected a function definition")
  }
}

///|
test "parse: withRegion" {
  let d = module_ok("def main() = withRegion { r => println(\"region\") }")
  assert_eq(defs_of(d).length(), 1)
}

///|
test "parse: data type declaration" {
  let d = module_ok("type List[A] { Cons(head: A, tail: List[A]); Nil() }")
  assert_eq(defs_of(d).length(), 1)
  match defs_of(d)[0].kind {
    DataDef(id, tparams, ctors) => {
      assert_eq(id.name, "List")
      assert_eq(tparams.length(), 1)
      assert_eq(ctors.length(), 2)
      assert_eq(ctors[0].id.name, "Cons")
      assert_eq(ctors[0].params.length(), 2)
      assert_eq(ctors[1].id.name, "Nil")
    }
    _ => abort("expected a data definition")
  }
}

///|
test "parse: match expression" {
  let d = module_ok(
    "def map[A, B](xs: List[A]) { f: A => B }: List[B] = xs match { case Cons(h, t) => Cons(f(h), map(t) { f }); case Nil() => Nil() }",
  )
  assert_eq(defs_of(d).length(), 1)
}

///|
test "parse: extern js include followed by a definition" {
  let d = module_ok(
    "extern js \"console.log(${x})\" def log(x: String): Unit = \"\"",
  )
  assert_eq(defs_of(d).length(), 2)
  match defs_of(d)[0].kind {
    ExternInclude(flag, path, contents) => {
      assert_eq(flag.to_string(), "js")
      assert_eq(path, "")
      assert_eq(contents, Some("console.log()"))
    }
    _ => abort("expected an extern include")
  }
  assert_true(defs_of(d)[1].kind is FunDef(_, _, _, _, _, _, _))
}

///|
test "parse: extern def with feature-flagged bodies" {
  let d = module_ok(
    "extern def add(n: Int, m: Int): Int =\n" +
    "  js \"${n} + ${m}\"\n" +
    "  chez \"(+ ${n} ${m})\"",
  )
  assert_eq(defs_of(d).length(), 1)
  match defs_of(d)[0].kind {
    ExternDef(_, _, _, _, _, _, bodies) => {
      assert_eq(bodies.length(), 2)
      match bodies[0] {
        StringExternBody(flag, template) => {
          assert_eq(flag.to_string(), "js")
          assert_eq(template.strings.length(), 3)
          assert_eq(template.args.length(), 2)
        }
        _ => abort("expected a string extern body")
      }
      match bodies[1] {
        StringExternBody(flag, _) => assert_eq(flag.to_string(), "chez")
        _ => abort("expected a string extern body")
      }
    }
    _ => abort("expected an extern definition")
  }
}

///|
test "parse: extern def with an Effekt body" {
  let d = module_ok("extern def foo(): Unit = default { println(\"hi\") }")
  assert_eq(defs_of(d).length(), 1)
  match defs_of(d)[0].kind {
    ExternDef(_, _, _, _, _, _, bodies) => {
      assert_eq(bodies.length(), 1)
      assert_true(bodies[0] is EffektExternBody(_, _))
    }
    _ => abort("expected an extern definition")
  }
}

// ---------------------------------------------------------------------------
// Module structure
// ---------------------------------------------------------------------------

///|
test "parse: module declaration" {
  let d = module_ok("module foo/bar\n\ndef main() = ()")
  assert_eq(d.path, "foo/bar")
  assert_eq(defs_of(d).length(), 1)
}

///|
test "parse: imports" {
  let d = module_ok("import foo/bar\nimport baz\n\ndef main() = ()")
  assert_eq(d.includes.length(), 2)
  assert_eq(d.includes[0].path, "foo/bar")
  assert_eq(d.includes[1].path, "baz")
}

///|
test "parse: default module path" {
  let d = module_ok("def main() = ()")
  assert_eq(d.path, "test")
}

///|
test "parse: doc comments are attached" {
  let d = module_ok("/// The main function.\ndef main() = ()")
  assert_eq(defs_of(d)[0].info.doc, Some(" The main function."))
}

///|
test "parse: doc comments and comments" {
  let d = module_ok("// a normal comment\n/// doc\ndef main() = ()")
  assert_eq(defs_of(d)[0].info.doc, Some(" doc"))
}

///|
test "parse: namespaces" {
  let d = module_ok("namespace foo { def bar() = 1 }")
  assert_eq(defs_of(d).length(), 1)
  match defs_of(d)[0].kind {
    NamespaceDef(id, defs) => {
      assert_eq(id.name, "foo")
      assert_eq(defs.length(), 1)
    }
    _ => abort("expected a namespace")
  }
  let d2 = module_ok("namespace foo\ndef bar() = 1\n")
  assert_eq(defs_of(d2).length(), 1)
  match defs_of(d2)[0].kind {
    NamespaceDef(id, defs) => {
      assert_eq(id.name, "foo")
      assert_eq(defs.length(), 1)
    }
    _ => abort("expected a namespace")
  }
}

///|
test "parse: interface" {
  let d = module_ok("interface Exc { def raise(msg: String): Unit }")
  assert_eq(defs_of(d).length(), 1)
  match defs_of(d)[0].kind {
    InterfaceDef(id, _, ops) => {
      assert_eq(id.name, "Exc")
      assert_eq(ops.length(), 1)
      assert_eq(ops[0].id.name, "raise")
    }
    _ => abort("expected an interface")
  }
}

///|
test "parse: legacy effect declaration" {
  let d = module_ok("effect Exc = {}\ndef main() = 1")
  assert_eq(defs_of(d).length(), 2)
  assert_true(defs_of(d)[0].kind is EffectDef(_, _, _))
}

///|
test "parse: effect operation declaration" {
  let d = module_ok("effect raise(msg: String): Unit")
  assert_eq(defs_of(d).length(), 1)
  match defs_of(d)[0].kind {
    InterfaceDef(id, _, ops) => {
      assert_eq(id.name, "raise")
      assert_eq(ops.length(), 1)
    }
    _ => abort("expected an interface")
  }
}

///|
test "parse: record" {
  let d = module_ok("record Point(x: Int, y: Int)")
  match defs_of(d)[0].kind {
    RecordDef(id, _, params) => {
      assert_eq(id.name, "Point")
      assert_eq(params.length(), 2)
    }
    _ => abort("expected a record")
  }
}

///|
test "parse: type alias" {
  let d = module_ok("type Name = String")
  match defs_of(d)[0].kind {
    TypeDef(id, _, _) => assert_eq(id.name, "Name")
    _ => abort("expected a type alias")
  }
}

///|
test "parse: val and var at toplevel" {
  let d = module_ok("val x = 42\nvar y = 0\nvar z in r = 1")
  assert_eq(defs_of(d).length(), 3)
  assert_true(defs_of(d)[0].kind is ValDef(_, _, _))
  assert_true(defs_of(d)[1].kind is VarDef(_, _, _))
  assert_true(defs_of(d)[2].kind is RegDef(_, _, _, _))
}

///|
test "parse: extern type, resource and include" {
  let d = module_ok(
    "extern type MyRef[T]\n" +
    "extern resource file: File\n" +
    "extern include \"foo.js\"\n" +
    "extern \"raw\"",
  )
  assert_eq(defs_of(d).length(), 4)
  assert_true(defs_of(d)[0].kind is ExternType(_, _, _))
  assert_true(defs_of(d)[1].kind is ExternResource(_, _))
  assert_true(defs_of(d)[2].kind is ExternInclude(_, _, _))
  assert_true(defs_of(d)[3].kind is ExternInclude(_, _, _))
}

// ---------------------------------------------------------------------------
// Statements and layout
// ---------------------------------------------------------------------------

///|
test "parse: newline terminates statements" {
  let d = module_ok(
    "def main() = {\n" +
    "  val x = 1\n" +
    "  val y = 2\n" +
    "  println(x + y)\n" +
    "}",
  )
  assert_eq(defs_of(d).length(), 1)
}

///|
test "parse: if/else and while" {
  let d = module_ok(
    "def main() = {\n" +
    "  if (true) println(1) else println(2)\n" +
    "  while (false) println(3)\n" +
    "}",
  )
  assert_eq(defs_of(d).length(), 1)
}

///|
test "parse: return" {
  let d = module_ok("def main(): Int = { return 42 }")
  assert_eq(defs_of(d).length(), 1)
}

///|
test "parse: region" {
  let d = module_ok("def main() = region r { println(\"hi\") }")
  assert_eq(defs_of(d).length(), 1)
}

///|
test "parse: handlers with capability names" {
  let d = module_ok(
    "interface Exc { def raise(msg: String): Unit }\n" +
    "def main() = try { do raise(\"boom\") } with exc: Exc { def raise(msg) = println(msg) }",
  )
  assert_eq(defs_of(d).length(), 2)
}

///|
test "parse: new with an implementation" {
  let d = module_ok(
    "interface Exc { def raise(msg: String): Unit }\n" +
    "def main() = try { do raise(\"boom\") } with Exc { def raise(msg) = println(msg) }",
  )
  assert_eq(defs_of(d).length(), 2)
}

///|
test "parse: multiple operations and new" {
  let d = module_ok(
    "interface State { def get(): Int\n def set(n: Int): Unit }\n" +
    "def main() = {\n  val s = new State { def get() = 1\n def set(n) = () }\n  println(s.get())\n}",
  )
  assert_eq(defs_of(d).length(), 2)
}

///|
test "parse: errors are reported" {
  let (decl, messages) = parse_module("def main( = 1")
  assert_true(decl is None)
  assert_true(messages.length() > 0)
}

///|
test "parse: reports an error for stray tokens" {
  let (decl, messages) = parse_module("def main() = 1\n42 43")
  assert_true(decl is None)
  assert_true(messages.length() > 0)
}

// ---------------------------------------------------------------------------
// Terms (via parse_term)
// ---------------------------------------------------------------------------

///|
test "parse term: literals and operators" {
  assert_true(term_ok("42").kind is Literal(_, _))
  assert_true(term_ok("1 + 2").kind is Call(_, _, _, _))
  assert_true(term_ok("\"hi\"").kind is Literal(_, _))
  assert_true(term_ok("()").kind is Literal(_, _))
  assert_true(term_ok("true").kind is Literal(_, _))
  assert_true(term_ok("[1, 2]").kind is Call(_, _, _, _))
  assert_true(term_ok("(1, 2)").kind is Call(_, _, _, _))
  assert_true(term_ok("f { x => x }").kind is Call(_, _, _, _))
  assert_true(term_ok("<>").kind is Hole(_, _))
  assert_true(term_ok("box 1").kind is Box(_, _))
  assert_true(term_ok("unbox x").kind is Unbox(_))
  assert_true(term_ok("do raise(\"x\")").kind is Do(_, _, _, _))
  assert_true(term_ok("if (x) 1 else 2").kind is If(_, _, _))
  assert_true(term_ok("while (x) 1").kind is While(_, _, _))
  assert_true(term_ok("x match { case _ => 1 }").kind is Match(_, _, _))
  assert_true(term_ok("x.foo()").kind is MethodCall(_, _, _, _, _))
  assert_true(term_ok("x = 1").kind is Assign(_, _))
}

///|
test "parse term: precedence is left associative" {
  let t = term_ok("1 - 2 - 3")
  match t.kind {
    Call(target, _, vargs, _) => {
      // (1 - 2) - 3
      assert_eq(vargs.length(), 2)
      assert_true(vargs[0].value.kind is Call(_, _, _, _))
      match target {
        IdTarget(id) => assert_eq(id.name, "infixMinus")
        _ => abort("expected an identifier target")
      }
    }
    _ => abort("expected a call")
  }
}

///|
test "parse term: multiplication binds tighter" {
  let t = term_ok("1 + 2 * 3")
  match t.kind {
    Call(_, _, vargs, _) =>
      match vargs[0].value.kind {
        Call(_, _, _, _) => abort("+ should not bind tighter than *")
        _ => ()
      }
    _ => abort("expected a call")
  }
}

///|
test "parse term: thunked operators take block arguments" {
  let t = term_ok("true && false")
  match t.kind {
    Call(_, _, vargs, bargs) => {
      assert_eq(vargs.length(), 0)
      assert_eq(bargs.length(), 2)
    }
    _ => abort("expected a call")
  }
}

///|
test "parse term: string interpolation" {
  // With an explicit interpolator we get a call to `s` with a block argument.
  let t = term_ok("s\"a ${x} b\"")
  match t.kind {
    Call(target, _, _, bargs) => {
      match target {
        IdTarget(id) => assert_eq(id.name, "s")
        _ => abort("expected an identifier target")
      }
      assert_eq(bargs.length(), 1)
    }
    _ => abort("expected a call")
  }
  // Without a splicer we get a plain string literal for a constant string.
  assert_true(term_ok("\"abc\"").kind is Literal(_, _))
  // ... and a call to the implicit `s` when there *are* splices.
  assert_true(term_ok("\"Hello ${x}!\"").kind is Call(_, _, _, _))
}

///|
test "parse term: named arguments" {
  let t = term_ok("f(x = 1, y = 2)")
  match t.kind {
    Call(_, _, vargs, _) => {
      assert_eq(vargs.length(), 2)
      assert_eq(vargs[0].name, Some("x"))
      assert_eq(vargs[1].name, Some("y"))
    }
    _ => abort("expected a call")
  }
}

///|
test "parse term: type arguments" {
  let t = term_ok("f[Int](1)")
  match t.kind {
    Call(_, targs, vargs, _) => {
      assert_eq(targs.length(), 1)
      assert_eq(vargs.length(), 1)
    }
    _ => abort("expected a call")
  }
}

///|
test "parse term: guard patterns" {
  assert_true(
    term_ok("x match { case Some(y) and y > 1 => y; case _ => 0 }").kind
    is Match(_, _, _),
  )
  assert_true(term_ok("if (x is Some(y)) 1 else 2").kind is If(_, _, _))
}

///|
test "parse term: type annotations and capture sets" {
  assert_true(term_ok("box f at {x}").kind is Box(_, _))
  assert_true(term_ok("withRegion { r => r }").kind is Call(_, _, _, _))
}

///|
test "parse term: holes" {
  assert_true(term_ok("<{ 1 }>").kind is Hole(_, _))
  assert_true(term_ok("<\"some text ${x}\">").kind is Hole(_, _))
}

///|
test "parse term: term errors are reported" {
  let (term, messages) = parse_expr("1 +")
  assert_true(term is None)
  assert_true(messages.length() > 0)
  let (term2, _) = parse_expr("1 2")
  assert_true(term2 is None)
}

// ---------------------------------------------------------------------------
// A real-world module: upstream `libraries/common/exception.effekt`
// ---------------------------------------------------------------------------

///|
test "parse: upstream exception library" {
  let src = "module exception\n\nimport effekt\n\n// Exceptions\n// ==========\n\ninterface Exception[E] {\n  def raise(exception: E, msg: String): Nothing\n}\n\ndef raise[A, E](exception: E, msg: String): A / Exception[E] =\n  do raise(exception, msg) match {}\n\n/**\n * Used as a type for `Exception` in functions which expect a non-empty\n * container (e.g. option or list).\n */\nrecord MissingValue()\n\ndef missingValue(): Nothing / Exception[MissingValue] =\n  do raise(MissingValue(), \"Missing value.\")\n\n/**\n * Used as a type for `Exception` in functions where an index can be out of bounds.\n */\nrecord OutOfBounds()\n\n/**\n * Unexpected runtime exceptions that can be caught.\n */\nrecord RuntimeError()\n\ndef raise[A](msg: String): A / Exception[RuntimeError] =\n  do raise(RuntimeError(), msg) match {}\n\n/**\n * Used as a type for `Exception` in functions which expect the input\n * to be formatted in a specific way.\n */\nrecord WrongFormat()\n\ndef wrongFormat(): Nothing / Exception[WrongFormat] =\n  do raise(WrongFormat(), \"Wrong format.\")\n\ndef wrongFormat(msg: String): Nothing / Exception[WrongFormat] =\n  do raise(WrongFormat(), msg)\n\n\n// Exception Handlers\n// ==================\n\n\n/**\n * Converts exceptions of (static) type E to an uncatchable panic that aborts the program\n */\ndef panicOn[E, T] { prog: => T / Exception[E] }: T =\n  try { prog() } with Exception[E] { def raise(exception: E, msg: String) = panic(msg) }\n\n/**\n * Reports exceptions of (static) type E to the console\n */\ndef report[E] { prog: => Unit / Exception[E] }: Unit =\n  try { prog() } with Exception[E] { def raise(exception: E, msg: String) = println(msg) }\n\n/**\n * Ignores exceptions of (static) type E\n */\ndef ignore[E] { prog: => Unit / Exception[E] }: Unit =\n  try { prog() } with Exception[E] { def raise(exception: E, msg: String) = () }\n\n/**\n * Use the default value to handle the exception of type E\n */\ndef default[E, T] { default: => T } { prog: => T / Exception[E] }: T =\n  try { prog() } with Exception[E] { def raise(exception: E, msg: String) = default() }\n\n/**\n * Runs the finalizer and rethrows E\n */\ndef finalize[E, T] { finalizer: => Unit } { prog: => T / Exception[E] }: T / Exception[E] =\n  try { val res = prog(); finalizer(); res } with Exception[E] {\n    def raise(exception: E, msg: String) = { finalizer(); do raise(exception, msg) }\n  }\n\n/**\n * A proxy value to enable partial type applications, such as:\n *\n * ```\n * with on[MissingValue].ignore; ...\n * ```\n */\nrecord on[E]()\n\ndef ignore[E](proxy: on[E]) { prog: => Unit / Exception[E] }: Unit =\n  ignore[E] {prog}\n\ndef default[E, T](proxy: on[E]) { d: => T } { prog: => T / Exception[E] }: T =\n  default[E, T] {d} {prog}\n\ndef panic[E, T](proxy: on[E]) { prog: => T / Exception[E] }: T =\n  panicOn[E, T] {prog}\n\ndef report[E](proxy: on[E]) { prog: => Unit / Exception[E] }: Unit =\n  report[E] {prog}\n\ndef finalize[E, T](proxy: on[E]) { finalizer: => Unit } { prog: => T / Exception[E] }: T / Exception[E] =\n  finalize[E, T] {finalizer} {prog}"
  let (decl, messages) = parse_module(src)
  assert_eq(messages, "")
  let d = decl.unwrap()
  assert_eq(d.path, "exception")
  assert_eq(d.includes.length(), 1)
  assert_eq(d.includes[0].path, "effekt")
  // interface, records, and the definitions
  assert_true(d.defs.length() > 10)
}

// ---------------------------------------------------------------------------
// Spans
// ---------------------------------------------------------------------------

///|
/// Walks the definitions of a module and checks that all spans are well formed
/// (start <= end, and not the missing span).
fn check_spans(d : @source.ModuleDecl) -> Unit raise {
  for def in d.defs {
    assert_true(def.span.start <= def.span.end)
    assert_true(!def.span.is_missing())
    match def.kind {
      FunDef(id, _, vparams, bparams, _, ret, body) => {
        assert_true(id.span.start <= id.span.end)
        for p in vparams {
          assert_true(p.id.span.start <= p.id.span.end)
        }
        for p in bparams {
          assert_true(p.id.span.start <= p.id.span.end)
        }
        let _ = ret
        assert_true(body.span.start <= body.span.end)
      }
      _ => ()
    }
  }
}

///|
test "parse: spans are well formed" {
  check_spans(
    module_ok(
      "def main() = {\n  val x = 42\n  println(x)\n}\n\ndef fib(n: Int): Int = if (n < 2) n else fib(n - 1) + fib(n - 2)\n",
    ),
  )
  check_spans(module_ok("type List[A] { Cons(head: A, tail: List[A]); Nil() }"))
  check_spans(module_ok("interface Exc { def raise(msg: String): Unit }"))
  check_spans(module_ok("record Point(x: Int, y: Int)"))
  check_spans(module_ok("namespace foo { def bar() = 1 }"))
}

///|
test "parse: the span of a definition covers its source text" {
  let d = module_ok("def main() = println(\"hi\")")
  let text = d.defs[0].span.range_text()
  assert_eq(text, "def main() = println(\"hi\")")
}

///|
test "parse: the span of a term starts at the right token" {
  let t = term_ok("1 + 2 * 3")
  assert_eq(t.span.range_text(), "1 + 2 * 3")
}
