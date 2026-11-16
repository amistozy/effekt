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
    `String` (`\{t}` for the types in `src/symbols`, `sym.name().name`) or
    scalars; avoid interpolating `Array`/`Option`.
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

- **Constructors are defined `T::T` and called `T(...)`.** `pub fn
  Span::Span(...)` is written `Span(...)` at a call site (and `@util.Span(...)`
  from another package); the same holds for the structs that carry a `T::T`
  constructor for every field (`ValueParam`, `BlockParam`, `CallSite`, `Rewrite`,
  `Bail`, `Continuation`, `Renamer`, `RecursiveFunction`, …). There is no
  `T::new` left in the project — rename one whenever it appears. The two
  exceptions are `BlockVar` and `BlockLit`: their name is also a constructor of
  the `Block` enum, and MoonBit reports the bare name as ambiguous unless the
  expected type settles it, so `let lit = BlockLit(...)` (and an argument of an
  unannotated arrow closure) does *not* compile while `Reset(BlockLit(...))` does.
  Both are therefore always written `BlockVar::BlockVar(...)` /
  `BlockLit::BlockLit(...)`, so that the short `BlockVar(...)` is exactly the
  enum constructor. That enum constructor needs `Block::BlockVar(...)` /
  `Block::BlockLit(...)` in the same untyped positions (six of them:
  `show.mbt`'s `generate_def`, `transform.mbt`'s eta expansions and the two
  `bparams.map` closures); a `match` pattern and a position with a known `Block`
  type can use the bare name.

- **Write loops the way `moonbitlang/core` does.** `.reference/core` is the
  installed standard library (a symlink to `moonbitlang/core`), kept in the repo
  as the style reference for exactly this kind of question. A counted loop is
  `for i in 0..<n`, not `for i = 0; i < n; i = i + 1`; the start may be any
  expression (`for i in 1..<xs.length()`), an ignored counter is
  `for _ in 0..<n`, and two arrays walked in lockstep are
  `for i in 0..<a.length().min(b.length())` (not `i < a.length() && i < b.length()`).
  Walking a collection is `for x in xs`, `for i, x in xs` with the index,
  `for (a, b) in pairs` over tuples, `for c in s` over the characters of a
  `String` (no `s[i].to_char()`); a state machine is
  `for pat = init { … continue next }`, and an inclusive bound is `0..<=n`.
  `while` stays for scans whose bound is a predicate
  (`while i < s.length() && s[i].is_digit()`, worklists,
  `while changed`), and for loops whose index does not advance by one.
  A loop that walks right-to-left is `xs.rev_fold(init=…, (acc, x) => …)` when
  it folds a value, `for (x, y) in xs.zip(ys).rev()` when it needs two
  arrays in step, and a descending counted loop is a *reversed range*:
  `for i in n>..1` for `for i = n - 1; i > 0; i = i - 1`, or
  `for i in self.position>..0` for a scan that starts at `position - 1` and
  includes `0`. Note that the mirror of `a..<b` is `a>..b`, which excludes the
  *start* and includes the end (`3>..0` is `2, 1, 0`), while `a>=..b` includes
  both ends (`3>=..0` is `3, 2, 1, 0`); a descending range whose start is below
  its end is empty, so `pos>..0` is the safe spelling for a scan that may start
  at `0`. Write `>..`/`>=..` without spaces around it, and prefer the form
  without arithmetic in the bound. A worklist is drained with
  `while stack.pop() is Some(x) { … }` instead of
  `while !stack.is_empty() { let x = stack.pop().unwrap() }`. One thing *not*
  to copy: `.each(f)` looks like the terse spelling of a one-statement loop, but
  the core library's own code uses `for` 1287 times and `.each` only 40 (its 143
  `.each` sites are mostly tests), so a loop whose body is a single call stays a
  `for` loop — `for x in xs { f(x) }`, not `xs.each(f)`.

- **Never silence an unused parameter; prefix it with `_`.** `let _ = self` and
  `let _ = ctx` at the top of a body are the workaround this project used to
  need, and they are gone: a parameter that the body does not read is written
  `_self`, `_ctx`, `_role` in the signature (the compiler treats a leading
  underscore as intentional), and a bound pattern that is not used is `_`
  (`FunDef(id, _, vparams, _, _, _, body)`). Discarding the *value of a call* is
  `ignore(f(x))`; `let _ = pattern` stays for binding nothing.

- **Ask the standard library before writing a helper.** `xs.is_empty()` (not
  `xs.length() == 0` — the core library has 399 of the former and 28 of the
  latter), `a.min(b)`/`a.max(b)`, `xs.last()`, `xs.rev()`, `xs.contains(x)`,
  `xs.search(x)` (returns `Int32?`; `search_by(p)` for a predicate),
  `xs.sort_by(cmp)`, `xs.any/all/fold`, `xs[m..n]` views with `.to_owned()` (the
  `ArrayView::to_array` of older compilers is deprecated; `String::to_array` is
  the unrelated string → `Array[Char]` conversion and is fine).
  A helper that only renames one of those is deleted (`min2`, `array_index_of`,
  the `length() == 0`/`length() > 0` comparisons are all gone that way). An
  accumulator loop that only maps is `xs.map(f)` (`xs.mapi((i, x) => …)` when the
  index is needed, `xs.filter(p)` when the push is guarded, `xs.to_array()` when
  the element is taken as it is). Loop over tuples by destructuring in the header
  (`for (a, b) in pairs`), not by binding the pair and unpacking it inside.

  The same applies to the builders this project used to hand-roll: a
  `join_strings(xs, sep)` loop is `xs.join(sep)`, a `spaces(n)` loop is
  `" ".repeat(n)`, a `code_point_count(s)` scan is `s.char_length()` (the number
  of Unicode scalars; `s.length()` is the UTF-16 code-unit count), `xs.map(f)` +
  `out.append(…)` is `xs.map(f).flatten()`, and a push that can skip an element
  is `xs.filter_map(x => …)` with an `Option` callback. Two more core
  conversions: an accumulator that only unions/concatenates is
  `xs.fold(init=…, (acc, x) => …)` (this port writes `.fold(` 2.5x as densely as
  the core library), and `Stmt?`-shaped defaults are `x.map(s => …).unwrap_or(…)`
  rather than a two-arm `match`.

- **`Map` is `@builtin`'s linked hash map, and it has combinators too.** Build
  one from pairs with the constructor — `Map(ids.map(id => (id.uid(), id)))`, not
  a loop of `.set` — copy-merge two with `xs.merge(ys)` (the right-hand side wins
  on a conflict and new keys are appended, exactly like a `set` loop over a
  `copy`), mutate-receive with `ys.merge_in_place(xs)`, transform the values with
  `m.map((k, v) => …)`, pick a subset with `m.filter((k, v) => …)`, ask about the
  keys with `m.keys().any(f)` / `m.keys().all(f)`, and materialize with
  `m.values().to_array()` / `m.to_array()`. Iteration order is observable (it is
  the insertion order), so a conversion may only reorder the *insertions* the way
  the loop did: `merge` appends, which is what the `copy`+`set` loop did too.

- **Take `ArrayView[T]` when a function only reads a sequence.** An `Array`
  coerces to an `ArrayView` at a call site, so a reader accepts arrays, slices
  and views without copying (`fn in_bindings(bindings, path : ArrayView[String],
  select)`); the core library has 364 such parameters and this port now has 259
  (it had 8 before the sweep). Keep `Array[T]` for a parameter that is mutated,
  stored in a field, constructor or `assign_*` setter, returned, or handed to a
  callee that needs the array itself — that is why `IdRef::qualified(path :
  Array[String], …)`, `PMClause(conditions, …, targs, args)` and
  `Unification::link(…, filter : Array[Sym])` keep theirs while the readers
  around them take views. Where the body copies the sequence, the view makes
  that explicit: `let sorted = messages.to_owned()` (not `messages.copy()`),
  and `for i in n..<xs.length()` becomes `xs[n:].to_owned()` in `array_drop`
  (a slice's start clamps, so a negative `n` still yields the whole array).
  `Array::append` is the counterpart, and a loop that only copies one array into
  another is `out.append(xs)` — not `for x in xs { out.push(x) }` (a view
  appends without conversion); `xs[1:].to_owned()` is
  "everything but the first", and `[x] + xs` prepends one element. To take the
  last element off *and* keep the rest, destructure instead of indexing twice:
  `match ids { [.. init, last] => … }`. The rest binding is an `ArrayView`, so
  it needs `.to_owned()` where an `Array` has to be stored, and the empty case
  is a real arm (spell it, even when the caller guarantees a non-empty list);
  `xs[:xs.length() - 1].to_owned()` is the same slice without the element, and
  a slice's end is clamped, so both are fine on an empty array. A push loop
  that maps (`for x in xs { out.push(f(x)) }`) is `xs.map(f)` — this port now
  writes `.map(` fifteen times as densely as the core library, and the sweep
  that got it there deleted 93 such loops — and the callback is the bare
  function when it is one (`vargs.map(rewrite_expr)`, not
  `vargs.map(e => rewrite_expr(e))`). Constructors are the exception: a
  constructor is not a first-class function
  (`Using constructors as higher order function directly is forbidden`), so
  `map(PMRun)` has to stay `map(b => PMRun(b))`, and `map(ValueVar)` is doubly
  rejected because `ValueVar` is both an `Expr` and a `ValueType` constructor.
  Four parameter arrays built one after another (`tparams`, `cparams`,
  `vparams`, `bparams`) become four adjacent `let … = xs.map(…)` lines. The
  loop stays when it accumulates into several arrays at once, when the pushed
  expression is long enough that the closure buries it, and when the collection
  is a *range*: `0..<n` is not an array, so `for i in 0..<n { out.push(f(i)) }`
  has no `.map` spelling.

- **Bail out with `guard <good condition> else { … }`, not an `if` around the
  failure.** The core library spells an early exit as a guard about thirteen
  times more often than as an `if` (1849 `guard` statements against 77
  `if !cond { …bail… }` and 179 `if cond != … { …bail… }`), and this port now
  follows it: `if !started { return None }` is `guard started else { return None }`
  and `if a.length() != b.length() { return false }` is
  `guard a.length() == b.length() else { return false }`. The `else` block
  returns from the nearest enclosing *function*, so it ends in `return`/`raise`/
  `continue`/`break` or in a value of that function's result type
  (`guard x is Some(v) else { None }`). A pattern bound in the condition is in
  scope after the statement, which is what collapses a "look up or abort"
  `match` into one statement: `guard self.ctx.symbol_of(id.uid) is Some(s) else
  { raise … }` then `s`; the condition may combine it with `&&`
  (`guard expr is ValueVar(id, _) && id == ids[i] else { return false }`).
  Two limits come from the type checker and shape where a guard can go: a
  *value* `else` block is only accepted where the expected type is the
  function's result type, so inside an `if` or `for` body (expected `Unit`) it
  has to `return`/`raise`/`continue` instead; and a `guard` in tail position
  types as `Unit`, so the last statement of a function cannot be a guard — the
  bound value follows it.

- **Test an enum with a pattern condition, not a two-arm `match`.** `if e is
  Some(x) { … }` binds `x` in the condition and replaces
  `match e { Some(x) => …, None => () }` (a shape the core library writes 1489
  times); the same works for any constructor pattern
  (`if phase is Failed(kind, message) { … }`). A `match` stays when both arms do
  something, when the result is a value, or when the arms are themselves
  patterns of a larger match.

- **Update a record with `{ ..self, field: value }`, not a `with_*` helper.**
  MoonBit keeps the other fields, so a pass that rebuilds a node with one field
  changed (`BlockLit`, `Clause`, `BlockVar`, `BlockParam`, `ShiftInfo`, …) writes
  the change where it is made instead of growing a helper per node and field. The
  `with_bindings`/`with_block`-style helpers are a different thing: they run a
  computation with temporarily changed *state*.

- **Qualify a constructor by its type when the bare name is unbound.** In
  `@core`, the constructors of its own types are written bare
  (`FunctionType(…)`, `CaptureSetOf(…)`), because `prelude.mbt`'s `using` brings
  the type into scope. Such a bare name is occasionally still reported as unbound
  inside a single function (`StaticArguments::wrap_definition` was one), while
  `BlockType::FunctionType` and `Captures::CaptureSetOf` resolve fine there — the
  type name is in scope even when the constructor is not. It is the same
  constructor, so use the qualified spelling at that spot rather than moving the
  code somewhere else. Note that `ValueVar` is both a core *expression*
  (`Expr::ValueVar(id, tpe)`) and a core *type* (`ValueType::ValueVar(id)`), so a
  call in a position without an expected type (`let x = ValueVar(a, b)`) is
  ambiguous and must be qualified.

- **Core trees carry core types, not source types.** `src/core/types.mbt` is the
  core type language (upstream `core/Type.scala`): `ValueType` is
  `ValueVar | ValueData | ValueBoxed`, `BlockType` is
  `FunctionType | InterfaceType | PromptType | ResumeType`, a function type has a
  *list* of results and no effect set. `@symbols`' type language is the *source*
  language: it appears only in `Sym` annotations, `@source` nodes and
  `core.transform`, which converts at the boundary (`transform_value_type`,
  `transform_block_type`). A pass that needs the annotation of a *symbol* uses
  `Transformer::value_type_of_sym`/`block_type_of_sym` (which transform), while
  `ctx.value_type_of(uid)` returns the source type. `src/cps` uses the core types
  too, as upstream's `cps.Tree` does.

- **Write lambdas as arrows**, never as anonymous `fn` literals: `x => …`,
  `(a, b) => …`, `() => { … }`. A `fn` literal whose body may raise has to
  repeat the effect (`fn() raise EffektError { … }`), and the annotated form is
  then checked for being *unused* (`unused_error_type`) as well, so it needs
  editing whenever the body stops raising; without the annotation the compiler
  reports `deprecated_syntax` (0027). Arrows infer the effect from the body, so
  one spelling covers both the pure and the raising case — e.g.
  `self.with_bindings(() => { … })`. `moon fmt` collapses a single-expression
  body to `x => expr`.

- **Equality and printing go through the traits, not helper functions.** `Sym`,
  `Name`, `ValueType`, `BlockType`, `Captures` and `Effects` all implement
  `Eq`/`Show` in `src/symbols`, so write `a == b`, `xs.contains(x)` and
  `"\{t}"` instead of a `*_eq`/`show_*` function. Such an `impl` is only
  visible to other packages when it is `pub` — a missing `pub` is what once
  forced `namer` to reimplement `Name` equality as `name_eq` (a `#derive(Eq)`
  on a `pub` type is exported the same way, so it is the preferred form).
  Write `Eq` by hand only where the relation is *not* structural: `Sym`
  compares `uid`s, and `Captures`/`Effects` compare as sets — `Effects` through
  the coarser `interface_type_equal`, which is why that one stays a function.
  The effect-set membership check is the same relation:
  `interface_type_equal`/`value_type_equal` compare effect types up to capture
  sets and are not reflexive on function types, so they cannot be `Eq`; their
  doc comments say so. `@core`'s `Doc`-based
  pretty printer (`show_core_*`) is likewise not `Show`: it lays out a whole
  module at a fixed width.

- **Rewrite core trees through `Rewrite`, not with a new traversal.** A core
  pass that rebuilds a tree uses the congruence in `src/core/rewrite.mbt`
  (upstream `core/Tree.scala`'s `Tree.Rewrite`): `Rewrite::Rewrite(on_stmt, on_id,
  on_captures, on_block)` takes hooks that return `Some(replacement)` for the
  nodes they handle and `None` to fall back to the congruence. The default
  rebuilds *everything* — ids, capture sets, types, declarations, externs — so an
  `on_id` hook renames every occurrence, as upstream's `rewrite(id: Id)` does
  (that is a plain substitution: `renamer.mbt` is the scoped freshener). A pass
  that only *collects* something (upstream's `Tree.Query`) can run the same
  congruence with a side-effecting hook that always returns `None`.

- **Standard combinators take raising closures.** `Array::map`, `any`, `all`,
  `each`, `filter`, … declare their callback as `(T) -> U raise?`, so an arrow
  that aborts compilation is a legal argument: write `xs.map(x => …)` /
  `xs.any(x => …)` rather than hand-rolling a `map_raise` loop that pushes into
  a fresh array. When writing such a helper yourself, spell the callback *and*
  the result `raise?` (as `Template::map` does) instead of a concrete error
  type: the error is then inferred per call site, so a pure `f` keeps the
  result pure.

- **Express upstream's `boundary`/`break` with a `Bail` flag or `Option`.**
  `StaticResumptions` aborts a rule from inside a traversal, which Scala does with
  a non-local `break`. MoonBit has no non-local return, and a dedicated `suberror`
  cannot pass through `Rewrite` (whose hooks raise `EffektError`), so the pass
  carries a small `Bail` struct: the inner helper sets `aborted` and returns
  anything, and each caller checks the flag before it uses the result. Where a
  helper can simply return `Option`, that is preferred (`reuse`, `joinpoint`).

- **Restore saved state with `defer`, not `errdefer` plus a manual restore.**
  MoonBit's `defer` runs on both exits (return and raise, verified), so
  `let saved = …; …; defer { … = saved }; f()` is enough for the "run `f` with
  this state temporarily changed" helpers (`Typer::at`, `flowing_into`,
  `match_expected`, the namer's `in_*_scope`). `errdefer` alone leaves the
  success path to a second assignment, and forgetting that assignment is
  exactly the bug that leaks state into a caller after an aborted unification.
  Keep `errdefer` only when the error path must do *something else* than the
  success path.

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
  `constructor`, …; and `implicit_impl_as_method`, which `pub impl` and
  `derive(Eq, Debug)` trigger — 501 diagnostics in total). Do not add a
  package-level `warnings =` line: `moon.pkg` lists were removed in favour of
  the shared default, and a package that needs an extra suppression should be
  discussed rather than silenced.
- Fixing one of those classes is always welcome — `unused_package`,
  `redundant_modifier`, `deprecated`, `unused_mut`, `unused_value`,
  `unused_type_declaration` and `unused_error_type` were cleaned up that way
  (the last three by dropping dead declarations, unused `using` entries and
  vestigial `raise` clauses rather than by renaming) — but drop the entry only
  after a full clean `moon check -d` (delete `_build`: a cached build hides
  whole packages).

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
- `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/upstream.ps1`
  additionally runs the Effekt repository's own test corpus (`testdata/upstream`,
  copied verbatim, 565 programs with the recorded `.check` outputs). It takes
  several minutes, so run it at milestones rather than on every commit; its
  numbers are tracked by baselines inside the script, which must be raised
  whenever they improve, exactly like `scripts/stdlib.ps1`'s. The `.check`
  files record a program's output followed by the compiler's diagnostics, so a
  `pos` test compares both; the diagnostics therefore have to keep upstream's
  rendering and positions. Three tests are skipped (see `$skipped` in the
  script): they need `/dev/stdout`, `cat`, or a module that upstream does not
  have either, so they cannot pass on Windows.
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
