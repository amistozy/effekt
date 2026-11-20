# Upstream test corpus

`examples/` is a verbatim copy of the Effekt repository's test corpus
(`effekt/examples/pos`, `examples/stdlib`, `examples/benchmarks`,
`examples/casestudies` and `examples/neg` at the revision this port follows,
`3249937a0`), so that the port can be measured against the language's own tests
instead of only against hand-written examples.

| Directory | Files | Expectation |
|---|---|---|
| `examples/pos` | 315 | compiles, runs, stdout equals the sibling `.check` file |
| `examples/stdlib` | 131 | same, for programs that exercise the standard library |
| `examples/benchmarks` | 93 | same; every benchmark runs in *test mode* (`benchmarks/runner.effekt`) |
| `examples/casestudies` | 10 | same, for the literate `.effekt.md` case studies |
| `examples/neg` | 243 | compilation fails; the diagnostics have to cover the expected severities and lines |

The case studies are *literate* programs: each `.effekt.md` file is a markdown
document whose code fences hold the program. The compiler extracts the fences
the way upstream's `MarkdownSource` does — a fence is code when it is written as
```` ```effekt ```` or without a language, dropped when it names another
language, `:ignore`d or wrapped in a `def replN()` whose result a synthesized
`main` prints for `:repl` — and replaces everything else by blank lines, so a
diagnostic keeps pointing at the markdown line it came from. They import each
other by module path (`import examples/casestudies/lexer`), which is why the
loader has to find `lexer.effekt.md` for `lexer` as well.

The benchmarks are upstream's `examples/benchmarks`; the `config_*.txt` files in
it select the *problem sizes* used when benchmarking (`runner.effekt` reads the
size from the command line), so a test run passes no argument and the program
prints the small result the `.check` file records. Two of them cannot pass on
Windows and are listed as skipped by `scripts/upstream.ps1`:
`folklore_to_fact/cps_tak` (upstream ignores it for the JS backend, the
continuation stack overflows) and `input_output/small_files` (it accepts only
`-17`, the POSIX `EEXIST`, from `mkdir`, while node reports libuv's `-4075` on
Windows).

The expected diagnostics of a negative test come either from its `.check` file
(`[error] <path>:<line>:<col>: <message>` lines) or, when there is none, from
the `// ERROR <text>` / `// WARN <text>` comments in the source — exactly the
two sources upstream's `EffektTests.scala` uses. The port matches severity, line
and wording, and `scripts/upstream.ps1 -Strict` compares the whole rendered
diagnostics of every negative test with its `.check` file: all 240 of the
compared are identical.

Run them with `powershell -File scripts/upstream.ps1` (add `-Filter <substring>`
to run a subset). The script keeps a baseline that can only grow, apart from a
re-sync, which re-bases it.

Beyond the directories, `scripts/upstream.ps1` also runs upstream's
`withoutOptimizations` list (`JavaScriptTests.scala`, seven programs:
`pos/issue842`, `pos/issue861`, `pos/contify_block_used_as_value`, `pos/parser`,
`pos/probabilistic`, `benchmarks/folklore_to_fact/motzkin` and
`pos/loop_block_parameter`) with `--no-optimize` and compares them against the
same `.check` files: all seven have to print the same thing with and without the
optimizer.

Files imported by the corpus (`import examples/pos/lists`, `import mutable/map`,
…) are resolved with `-I testdata/upstream` and the library's `common` and `js`
directories, so the directory layout has to stay as it is.

The corpus has to sit on disk with **LF** line endings, which `.gitattributes`
(`* text=auto eol=lf`) already gives a fresh clone: `wordcount` counts the
characters of `examples/stdlib/io/filesystem/demo_file1.txt`, so a CRLF working
tree reports 15 characters where the recorded output has 14, and a multiline raw
string (`#|…`) is only terminated by a bare `\n` in the parser. A tree that was
copied from a Windows checkout instead of being cloned can be normalised by
deleting `testdata/upstream` and running `git checkout -- testdata/upstream`.
