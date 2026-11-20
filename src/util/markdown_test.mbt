// Tests for the literate (`.effekt.md`) source extraction: it mirrors
// upstream's `MarkdownSource`, and the case studies of the corpus depend on the
// line numbers being preserved (a diagnostic has to point at the markdown line).
//
// Every line of the markdown file produces exactly one line of the program: the
// fences themselves become blank lines, so the first code line keeps its line
// number.

///|
test "code fences keep the lines of the markdown file" {
  let markdown =
    #|# A heading
    #|
    #|```effekt
    #|def main() = ()
    #|```
    #|
    #|Some prose.
  // line 3 (the opening fence), then the body on line 4, then blanks
  assert_eq(@util.markdown_program(markdown), "\n\n\ndef main() = ()\n\n\n")
}

///|
test "a fence without a language is code, another language is dropped" {
  let markdown =
    #|```
    #|def main() = ()
    #|```
    #|```scala
    #|val x = 1
    #|```
  // the `scala` body is blanked, its three lines stay
  assert_eq(@util.markdown_program(markdown), "\ndef main() = ()\n\n\n\n")
}

///|
test "an ignored fence keeps its lines but none of its code" {
  let markdown =
    #|```effekt:ignore
    #|def hidden() = ()
    #|```
  assert_eq(@util.markdown_program(markdown), "\n\n")
}

///|
test "a repl fence is wrapped in a function and printed" {
  let markdown =
    #|```effekt:repl
    #|1 + 1
    #|```
  // the opening fence becomes the wrapper's header, and the program grows a
  // `main` that prints the result with `show` (upstream appends it verbatim,
  // including the trailing spaces of the template)
  let expected = "def repl0() = {\n1 + 1\n}" +
    "\ndef main() = {\nprintln(repl0().show)\n()\n}\n      "
  assert_eq(@util.markdown_program(markdown), expected)
}

///|
test "a fence line with trailing text is not a fence" {
  let markdown =
    #|```not a fence
    #|def main() = ()
    #|```
  // the first two lines are prose, the last one opens a fence
  assert_eq(@util.markdown_program(markdown), "\n\n")
}
