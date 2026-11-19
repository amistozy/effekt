# Upstream test corpus

`examples/` is a verbatim copy of the Effekt repository's test corpus
(`effekt/examples/pos`, `examples/stdlib` and `examples/neg` at the revision
this port follows, `6976c7947`), so that the port can be measured against the
language's own tests instead of only against hand-written examples.

| Directory | Files | Expectation |
|---|---|---|
| `examples/pos` | 314 | compiles, runs, stdout equals the sibling `.check` file |
| `examples/stdlib` | 131 | same, for programs that exercise the standard library |
| `examples/neg` | 243 | compilation fails; the diagnostics have to cover the expected severities and lines |

The expected diagnostics of a negative test come either from its `.check` file
(`[error] <path>:<line>:<col>: <message>` lines) or, when there is none, from
the `// ERROR <text>` / `// WARN <text>` comments in the source — exactly the
two sources upstream's `EffektTests.scala` uses. The port matches severity, line
and wording, and `scripts/upstream.ps1 -Strict` compares the whole rendered
diagnostics of every negative test with its `.check` file: 189 of the 234
compared are identical. The remaining ones are tests upstream rewrote after
`6fbff0b0e` (the revision the port was at before this sync): a failed overload
now draws its candidates together with the source of each one, and a few
diagnostics lost duplicated `Expected X but got Y` errata, neither of which the
port renders yet.

Run them with `powershell -File scripts/upstream.ps1` (add `-Filter <substring>`
to run a subset). The script keeps a baseline that can only grow, apart from a
re-sync, which re-bases it.

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
