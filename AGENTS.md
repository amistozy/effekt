# Project Agents.md Guide

This is a [MoonBit](https://docs.moonbitlang.com) project.

You can browse and install extra skills here:
<https://github.com/moonbitlang/skills>

## Project Structure

- MoonBit packages are organized per directory; each directory contains a
  `moon.pkg` file listing its dependencies. Each package has its files and
  blackbox test files (ending in `_test.mbt`) and whitebox test files (ending in
  `_wbtest.mbt`).

- In the toplevel directory, there is a `moon.mod` file listing module
  metadata.

## Coding convention

- MoonBit code is organized in block style, each block is separated by `///|`,
  the order of each block is irrelevant. In some refactorings, you can process
  block by block independently.

- Try to keep deprecated blocks in file called `deprecated.mbt` in each
  directory.

- **Prefer the three literals below over the older idioms** (verified with
  `moon 0.1.20261012`; they keep this compiler's output-building code readable,
  and this is a compiler that writes a lot of text):

  - **Map literals** for maps whose keys are known statically:
    `let m : Map[String, Sym] = { "Unit": unit, "Bool": bool }`.
    Keys must be *literals* (a variable key is parsed as a struct field);
    dynamic keys keep `Map([])` plus `.set`. `Map` is a mutable *linked* hash
    map, so iteration order is observable: the pairs must appear in the order
    the `.set` calls ran. An empty map must stay `Map([])` — `{}` is reported
    as `ambiguous_braces`.
  - **String interpolation** `"\{expr}"` for concatenation chains. Any
    expression is allowed inside (calls, `if`, nested braces, quotes); a
    literal `{` needs no escape, a literal `\{` must be written `\\{`. The
    expression needs a `Show` instance, so interpolate things that are already
    `String` (`show_value_type(t)`, `sym.name().name`) or scalars; avoid
    interpolating `Array`/`Option`.
  - **Multi-line strings** `#|` for any string spanning two or more lines:
    ```moonbit
    let js = #|function f() {
             #|  return `${x}`;
             #|}
    ```
    The content is everything after each `#|` (the indentation before it is not
    part of the string). Escapes are **not** processed, so embedded JavaScript,
    Effekt extern templates, regexes and Windows paths need no escaping at all.
    There is no trailing newline — end with an empty `#|` line if you need one
    — and it must sit in a `let` binding or inside parentheses, otherwise the
    compiler warns `deprecated_syntax`.

  - **`$|` is the *interpolating* multi-line string** — use it when the text
    spans lines *and* has dynamic parts, which is what most diagnostics look
    like:
    ```moonbit
    let message =
      $|Expected type
      $|  \{right}
      $|but got type
      $|  \{left}
    ```
    `\{expr}` is substituted (unlike `#|`, which keeps it literal), `${x}` stays
    plain text, and `\n` is *deprecated* inside `$|` — write `\{'\n'}` for a
    real newline or `\{"\\n"}` for the two characters `\` and `n`. The `let`
    binding rule is the same as for `#|`: as a bare call argument (or even in
    call parentheses) it warns `deprecated_syntax`, so bind it first.
    Do not convert a one-line source string such as
    `msg="expected a switch:\n\{js}"` into a `$|` block just because its
    *content* has a newline — that only makes call sites longer. Convert when
    the text genuinely spans several lines, or when the alternative is a
    `"…" + (#|…|)` split or a line that would have to end in trailing
    whitespace.

  The test suite compares generated JavaScript and core IR text, and
  `scripts/e2e.ps1` runs the compiled programs, so any accidental change to a
  string's content is caught.

## Host access: prefer the standard library over `extern`

- **Do not hand-write JavaScript when `moonbitlang/core` or `moonbitlang/x` has
  the API.** Files come from `moonbitlang/x/fs`, paths (`dirname`, `join`,
  `resolve`, `node:path` semantics on either platform) from
  `moonbitlang/x/path`, the command line from `moonbitlang/core/env`, and
  subprocess-free tasks generally from the core packages. `moonbitlang/x` is a
  mooncakes dependency declared in `moon.mod`; `moon` downloads it on demand.
- The **only** `extern "js"` left in the project is `src/compiler/node.mbt`:
  the process exit code (`moonbitlang/x/sys`'s `exit` calls `process.exit()`,
  which truncates piped stdout), stderr, and `child_process`. Anything new
  belongs there, documented with the reason the library cannot do it, rather
  than in a fresh file.
- `moonbitlang/x/fs` imports Node builtins with `#module(...)`, which switches
  the JS backend to **ES module** output. `cmd/main/moon.pkg` therefore pins
  `options(link: {"js": {"format": "cjs"}})`: the generated Effekt programs and
  their runner scripts are CommonJS (`module.exports` / `require`), and the CLI
  is started with plain `node`, which would otherwise print a
  `MODULE_TYPELESS_PACKAGE_JSON` warning on every run. Keep that option (and
  the CommonJS `require` it allows) if you touch the linker settings.

## Warnings

- **Warnings are errors here:** the gate runs `moon check -d`, so any *enabled*
  warning fails the build. Do not silence a new warning class to get green —
  fix the code.
- The suppressions all live in **one place**, `moon.mod`'s `warnings`, and each
  entry is documented there with why the port produces it on purpose
  (`reserved_keyword` for Effekt's own AST vocabulary — `module`, `local`, `ref`,
  `constructor`, …; `unused_error_type` for `raise` clauses left over from the
  Scala signatures; and `implicit_impl_as_method`, which `pub impl` and
  `derive(Eq, Debug)` trigger — 523 diagnostics in total). Do not add a
  package-level `warnings =` line: `moon.pkg` lists were removed in favour of
  the shared default, and a package that needs an extra suppression should be
  discussed rather than silenced.
- Fixing one of those classes is always welcome — `unused_package`,
  `redundant_modifier`, `deprecated`, `unused_mut`, `unused_value` and
  `unused_type_declaration` were cleaned up that way (the last two by dropping
  dead declarations and unused `using` entries rather than by renaming) — but
  drop the entry only after a full clean `moon check -d` (delete `_build`: a
  cached build hides whole packages).

## Git workflow

- **Commit and push automatically.** After finishing a change, do not stop to ask
  whether to commit: run the checks below, then `git add -A`, commit with a
  descriptive message, and `git push` to `origin/main` on your own.
- Before every commit, the tree must be green:
  `moon check --target js -d` (warnings as errors), `moon test --target js`,
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/e2e.ps1` and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/stdlib.ps1`
  (use `powershell`, not `pwsh`, which is not on PATH here). The last one
  compiles every standard library module and fails when fewer modules compile
  than its recorded baseline: phase bugs hide in the standard library long
  before the small examples reach them, so raise the baseline whenever it
  improves and never lower it without removing a module.
- Run `moon info && moon fmt` first, and commit the updated `.mbti` interfaces
  together with the code that changed them.
- Direct HTTPS access to github.com is unreliable on this machine (`Recv failure:
  Connection was reset`) even though TCP/443 connects. When a plain
  `git push origin main` fails like that, retry through the local proxy that is
  usually listening on `127.0.0.1:7897`:
  `git -c http.proxy=http://127.0.0.1:7897 -c https.proxy=http://127.0.0.1:7897 push origin main`
  (a one-off `-c`, no persistent config change). Verify with
  `git rev-parse HEAD` against `git rev-parse origin/main` afterwards.
- Never commit build output: `_build/`, the JavaScript generated for the examples
  (`examples/**/*.js`, already in `.gitignore`), or scratch/debug files.

## Tooling

- `moon fmt` is used to format your code properly.

- `moon ide` provides project navigation helpers like `peek-def`, `outline`, and
  `find-references`. See $moonbit-agent-guide for details.

- `moon info` is used to update the generated interface of the package, each
  package has a generated interface file `.mbti`, it is a brief formal
  description of the package. If nothing in `.mbti` changes, this means your
  change does not bring the visible changes to the external package users, it is
  typically a safe refactoring.

- In the last step, run `moon info && moon fmt` to update the interface and
  format the code. Check the diffs of `.mbti` file to see if the changes are
  expected.

- Run `moon test` to check tests pass. MoonBit supports snapshot testing; when
  changes affect outputs, run `moon test --update` to refresh snapshots.

- Prefer `assert_eq` or `assert_true(pattern is Pattern(...))` for results that
  are stable or very unlikely to change. For snapshot tests that record
  structured debugging output, derive `Debug` and use `debug_inspect`, rather
  than deriving `Show` for debugging. For solid, well-defined results (e.g.
  scientific computations), prefer assertion tests. You can use
  `moon coverage analyze > uncovered.log` to see which parts of your code are
  not covered by tests.
