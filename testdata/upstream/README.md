# Upstream test corpus

`examples/` is a verbatim copy of the Effekt repository's test corpus
(`effekt/examples/pos`, `examples/stdlib` and `examples/neg` at the revision
this port follows), so that the port can be measured against the language's own
tests instead of only against hand-written examples.

| Directory | Files | Expectation |
|---|---|---|
| `examples/pos` | 273 | compiles, runs, stdout equals the sibling `.check` file |
| `examples/stdlib` | 122 | same, for programs that exercise the standard library |
| `examples/neg` | 170 | compilation fails; the diagnostics have to cover the expected severities and lines |

The expected diagnostics of a negative test come either from its `.check` file
(`[error] <path>:<line>:<col>: <message>` lines) or, when there is none, from
the `// ERROR <text>` / `// WARN <text>` comments in the source — exactly the
two sources upstream's `EffektTests.scala` uses. The port currently matches
severity and line, not the wording of every message (the summary counts the
files whose wording differs).

Run them with `powershell -File scripts/upstream.ps1` (add `-Filter <substring>`
to run a subset). The script keeps a baseline that can only grow.

Files imported by the corpus (`import examples/pos/lists`, `import mutable/map`,
…) are resolved with `-I testdata/upstream` and the library's `common` and `js`
directories, so the directory layout has to stay as it is.
