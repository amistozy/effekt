// Blackbox tests for the Effekt lexer (`src/source/lexer.mbt`).
//
// Most of these are ports of `effekt/jvm/src/test/scala/effekt/LexerTests.scala`,
// so that the MoonBit lexer can be compared against the Scala original.

///|
fn show_kind(k : @source.TokenKind) -> String {
  match k {
    @source.TEOF => "EOF"
    @source.TError(e) => "!err:\{e.message()}"
    @source.TNewline => "NL"
    @source.TInteger(n) => "int:\{n}"
    @source.TFloat(d) => "float:\{d}"
    @source.TStr(s, m) => if m { "str3(\"\{s}\")" } else { "str(\"\{s}\")" }
    @source.THoleStr(s) => "holestr(\"\{s}\")"
    @source.TChr(c) => "chr:\{c}"
    @source.TByt(b) => "byt:\{b}"
    @source.TIdent(s) => "id:\{s}"
    @source.TComment(s) => "//\{s}"
    @source.TDocComment(s) => "///\{s}"
    @source.TShebang(s) => "#!\{s}"
    @source.TSpace => "_"
    other =>
      if other.is_keyword() {
        other.keyword_text()
      } else {
        @source.symbol_text(other)
      }
  }
}

///|
fn lex_tokens(src : String) -> Array[@source.Token] {
  let source = @util.Source::new("test.effekt", src)
  @source.Lexer::lex(source)
}

///|
/// Renders the token kinds, dropping whitespace tokens (upstream's `assertTokensEq`).
fn kinds(src : String) -> String {
  let parts : Array[String] = []
  for t in lex_tokens(src) {
    match t.kind {
      @source.TSpace => ()
      _ => parts.push(show_kind(t.kind))
    }
  }
  join(parts)
}

///|
/// Renders all token kinds, including whitespace (upstream's
/// `assertTokensEqWithWhitespace`).
fn kinds_with_ws(src : String) -> String {
  let parts : Array[String] = []
  for t in lex_tokens(src) {
    parts.push(show_kind(t.kind))
  }
  join(parts)
}

///|
fn join(parts : Array[String]) -> String {
  let buf = StringBuilder()
  for i = 0; i < parts.length(); i = i + 1 {
    if i > 0 {
      buf.write_string(" ")
    }
    buf.write_string(parts[i])
  }
  buf.to_string()
}

///|
/// Does lexing produce any error token?
fn has_error(src : String) -> Bool {
  lex_tokens(src).any(t => t.is_error())
}

///|
test "lexer: function definition" {
  let prog =
    #|def f[A](x: A, y: A): () => (A, A) at {} =
    #|    return box { () => (x, y) }
    #|
  assert_eq(
    kinds(prog),
    "def id:f [ id:A ] ( id:x : id:A , id:y : id:A ) : ( ) => ( id:A , id:A ) id:at { } = NL " +
    "return box { ( ) => ( id:x , id:y ) } NL EOF",
  )
  assert_eq(kinds_with_ws("def f[A]"), "def _ id:f [ id:A ] EOF")
}

///|
test "lexer: braces and interpolation nesting" {
  assert_true(!has_error("${}"))
  assert_true(!has_error("\" before ${ ${} } after\""))
  assert_eq(kinds("${ ${} }"), "${ ${ }$ }$ EOF")
  assert_true(!has_error("}"))
  assert_true(!has_error("{}}"))
  assert_true(!has_error("{ 42 "))
  assert_true(!has_error("\"${}}}}\""))
  assert_true(!has_error("\"}\""))
  assert_true(!has_error("\" before ${ \"${ 42 }\" } after\""))
  assert_true(!has_error("<\"${ <{ 5 }> }\">"))
}

///|
test "lexer: numbers" {
  let num = "12.34 100 200 123.345 1 -12.34 -100 -123.345 -1 0x42"
  assert_eq(
    kinds(num),
    "float:12.34 int:100 int:200 float:123.345 int:1 float:-12.34 int:-100 " +
    "float:-123.345 int:-1 byt:66 EOF",
  )
}

///|
test "lexer: illegal byte notation" {
  assert_true(has_error("0x4"))
  assert_true(has_error("0x444"))
  assert_eq(kinds("0xFF"), "byt:255 EOF")
}

///|
test "lexer: big numbers" {
  assert_true(has_error("9223372036854775808"))
  assert_true(!has_error("9223372036854775807"))
  assert_true(has_error("-9223372036854775809"))
  assert_true(!has_error("-9223372036854775808"))
  assert_eq(
    kinds("foo(9223372036854775808)"),
    "id:foo ( !err:Invalid integer format, not a 64bit integer literal ) EOF",
  )
}

///|
test "lexer: symbols" {
  assert_eq(
    kinds("=> <= < >= > / * - && ++ +"),
    "=> <= < >= > / * - && ++ + EOF",
  )
  assert_eq(kinds("== !="), "=== !== EOF")
  assert_eq(
    kinds(":= :: .. ... ^^ ~ ~> <~ += -= *= /="),
    ":= :: .. ... ^^ ~ ~> <~ += -= *= /= EOF",
  )
}

///|
test "lexer: single line strings" {
  assert_eq(kinds("\"hello, world\""), "str(\"hello, world\") EOF")
  assert_eq(kinds("\"\\\"hello\\\"\""), "str(\"\"hello\"\") EOF")
  assert_eq(kinds("\"\\n\""), "str(\"\n\") EOF")
  assert_true(has_error("\"\\k\""))
  assert_true(!has_error("\"\\u001b\""))
  assert_true(!has_error("\"\\u{001b}\""))
  assert_eq(kinds("'\\''"), "chr:39 EOF")
  assert_eq(kinds("\"'\""), "str(\"'\") EOF")
  assert_eq(kinds("'\\\"'"), "chr:34 EOF")
}

///|
test "lexer: characters" {
  assert_eq(kinds("' '"), "chr:32 EOF")
  assert_eq(kinds("'\u{1F605}'"), "chr:128517 EOF")
  assert_eq(kinds("'\\\\'"), "chr:92 EOF")
  assert_eq(kinds("'\\n'"), "chr:10 EOF")
  assert_eq(kinds("'\\t'"), "chr:9 EOF")
  assert_eq(kinds("'\\u0000'"), "chr:0 EOF")
  assert_eq(kinds("'\\uFFFF'"), "chr:65535 EOF")
  assert_eq(kinds("'\\u10FFFF'{ val"), "chr:1114111 { val EOF")
  assert_eq(kinds("val s ='\\u0000'+ 1"), "val id:s = chr:0 + int:1 EOF")
  assert_eq(kinds("''"), "!err:Empty character literal EOF")
}

///|
test "lexer: multi line strings" {
  let prog = "\"\"\"val def interface \"\" \"\ncontinues here \t \r\n and is end\n \"\"\""
  assert_eq(
    kinds(prog),
    "str3(\"val def interface \"\" \"\ncontinues here \t \r\n and is end\n \") EOF",
  )
  assert_eq(kinds("\" \"\"\""), "str(\" \") str(\"\") EOF")
  assert_true(has_error("\"\"\" \""))
  assert_true(has_error("\"\"\""))
}

///|
test "lexer: quoted single-line string" {
  let prog = " \"this is a quote ${ xs.map { x => \" ${x + 1}\" } } after the quote\" "
  assert_eq(
    kinds(prog),
    "str(\"this is a quote \") ${ id:xs . id:map { id:x => str(\" \") ${ id:x + int:1 }$ str(\"\") } }$ str(\" after the quote\") EOF",
  )
}

///|
test "lexer: missing interpolation" {
  let prog = " \"hello ${ xs.map { x => \"${x + 1}\" } \" "
  assert_eq(
    kinds(prog),
    "str(\"hello \") ${ id:xs . id:map { id:x => str(\"\") ${ id:x + int:1 }$ str(\"\") } " +
    "!err:Unterminated single-line string; expected closing `\"` on the end of the line " +
    "!err:Unterminated string interpolation (1 unclosed splices) EOF",
  )
}

///|
test "lexer: simple interpolated string" {
  assert_eq(
    kinds("\"Hello ${ 42 } world\""),
    "str(\"Hello \") ${ int:42 }$ str(\" world\") EOF",
  )
}

///|
test "lexer: interpolated string" {
  assert_eq(
    kinds("\"${x + 1}${x + 2}\""),
    "str(\"\") ${ id:x + int:1 }$ str(\"\") ${ id:x + int:2 }$ str(\"\") EOF",
  )
}

///|
test "lexer: interpolated hole string" {
  assert_eq(
    kinds("<\" natural language text with terms like ${ 1 + 1 } inside \">"),
    "holestr(\" natural language text with terms like \") ${ int:1 + int:1 }$ holestr(\" inside \") EOF",
  )
}

///|
test "lexer: string splice hole" {
  assert_eq(kinds("<${x}>"), "< ${ id:x }$ > EOF")
}

///|
test "lexer: all holes" {
  assert_eq(kinds("<{<\"str\">; <>}>"), "<{ holestr(\"str\") ; <> }> EOF")
  assert_eq(kinds("<{< <\"str\"> >}>"), "<{ < holestr(\"str\") > }> EOF")
}

///|
test "lexer: multiline string holes" {
  let prog1 =
    #|<" Here it starts
    #|  and here it continues ">
    #|
  let expected1 =
    #|holestr(" Here it starts
    #|  and here it continues ") NL EOF
  assert_eq(kinds(prog1), expected1)
  let prog2 =
    #|<" Oh look, a number!
    #|   ${ 42 }
    #|  and here it continues ">
    #|
  let expected2 =
    #|holestr(" Oh look, a number!
    #|   ") ${ int:42 }$ holestr("
    #|  and here it continues ") NL EOF
  assert_eq(kinds(prog2), expected2)
  let prog3 =
    #|effect foo(): Int
    #|effect bar(): String
    #|def baz(x: Int): Int / {foo, bar} = <"
    #|  This is some natural language text.
    #|  ${ do foo() }
    #|  Some more text.
    #|  ${ do bar() }
    #|">
    #|
  assert_true(!has_error(prog3))
}

///|
test "lexer: quoted multi-line string" {
  let prog = "\"\"\"multi-line quote\n${x + 1}, ${y + 1} \n\"\"\""
  assert_eq(
    kinds(prog),
    "str3(\"multi-line quote\n\") ${ id:x + int:1 }$ str3(\", \") ${ id:y + int:1 }$ str3(\" \n\") EOF",
  )
}

///|
test "lexer: simple nested interpolated string" {
  assert_true(!has_error("\"${\"${1}\"2}\""))
}

///|
test "lexer: comments" {
  assert_eq(kinds("//"), "// EOF")
  assert_eq(kinds("// \u{2264}"), "// \u{2264} EOF")
  assert_eq(kinds("// foo\nval x = 2"), "// foo NL val id:x = int:2 EOF")
  assert_eq(kinds("// foo\r\nval x = 2"), "// foo NL val id:x = int:2 EOF")
  let prog =
    #|val x = 42
    #|/* comment begin def return /* * /
    #|still comment
    #|here's the end
    #|*/
    #|def main(): Unit = ()
  let expected =
    #|val id:x = int:42 NL // comment begin def return /* * /
    #|still comment
    #|here's the end
    #| NL def id:main ( ) : id:Unit = ( ) EOF
  assert_eq(kinds(prog), expected)
  assert_true(has_error("/* unterminated"))
}

///|
test "lexer: doc comments" {
  assert_eq(kinds("/// hello\nval x = 1"), "/// hello NL val id:x = int:1 EOF")
  assert_eq(
    kinds("/// a\n/// b\nval x = 1"),
    "/// a NL /// b NL val id:x = int:1 EOF",
  )
}

///|
test "lexer: newline" {
  assert_eq(
    kinds("val next = f() // Comment\ng()\n"),
    "val id:next = id:f ( ) // Comment NL id:g ( ) NL EOF",
  )
}

///|
test "lexer: empty" {
  assert_eq(kinds(""), "EOF")
}

///|
test "lexer: extra whitespace" {
  let prog =
    #|// interface definition
    #|  interface
    #|
    #|     Eff[A,
    #|  B] { def operation
    #|  [C]
    #|  (x:    C)  :
    #|
    #|  (A, B)
    #|
    #|  }
    #|
  assert_eq(
    kinds(prog),
    "// interface definition NL interface NL NL id:Eff [ id:A , NL id:B ] { def id:operation NL [ id:C ] NL " +
    "( id:x : id:C ) : NL NL ( id:A , id:B ) NL NL } NL EOF",
  )
}

///|
test "lexer: just whitespace" {
  assert_eq(
    kinds_with_ws("\n\n\n\r\n   \t val\t\t\t\t   x =\t\r\r\n42\nx"),
    "NL NL NL NL _ val _ id:x _ = _ NL int:42 NL id:x EOF",
  )
}

///|
test "lexer: resilience" {
  let prog =
    #|
    #|val a = ${}
    #|val b = 123456789012345678901234567890
    #|val c = "
    #|inspect(c)
    #|
  assert_eq(
    kinds(prog),
    "NL val id:a = ${ }$ NL val id:b = !err:Invalid integer format, not a 64bit integer literal NL " +
    "val id:c = !err:Unterminated single-line string; expected closing `\"` on the end of the line NL " +
    "id:inspect ( id:c ) NL EOF",
  )
}

///|
test "lexer: single-line string ends with newline" {
  assert_eq(
    kinds("val s = \"hello\r\n"),
    "val id:s = !err:Unterminated single-line string; expected closing `\"` on the end of the line NL EOF",
  )
  assert_eq(
    kinds("val s = \"hello\n"),
    "val id:s = !err:Unterminated single-line string; expected closing `\"` on the end of the line NL EOF",
  )
}

///|
test "lexer: token positions" {
  let tokens = lex_tokens("def f")
  assert_eq(join(tokens.map(t => show_kind(t.kind))), "def _ id:f EOF")
  assert_eq(tokens[0].start, 0)
  assert_eq(tokens[0].end, 2)
  assert_eq(tokens[2].start, 4)
  assert_eq(tokens[2].end, 4)
}

///|
test "lexer: shebang" {
  assert_eq(
    kinds("#!/usr/bin/env effekt\nval x = 1"),
    "#!/usr/bin/env effekt NL val id:x = int:1 EOF",
  )
}

///|
test "lexer: keywords and soft keywords" {
  assert_eq(kinds("resume in at _"), "id:resume id:in id:at id:_ EOF")
  assert_eq(
    kinds("namespace private extern box unbox and is"),
    "namespace private extern box unbox and is EOF",
  )
}
