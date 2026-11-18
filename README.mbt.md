# Effekt in MoonBit

An implementation of the [Effekt](https://effekt-lang.org) language in
[MoonBit](https://www.moonbitlang.com), compiling to JavaScript.

Effekt is a research language built around **effect handlers**: algebraic effects
with multi-shot resumptions, capability-passing effect polymorphism (`{io}`,
`{fail}`), regions and lexical capture sets. This is a port of the reference
Scala compiler, not an implementation from the papers: lexing, name resolution,
type and effect inference, the optimizer and the JavaScript backend follow
upstream's phases and intermediate representations, and `libraries/` and the test
corpus are upstream's own files. What compiles here is the whole language, not a
subset of it.

## Status

The standard library and the corpus are upstream's, at commit `6fbff0b0e`.
`.reference/effekt` is a local, git-ignored checkout of it, and
`.reference/core` is a symlink to the installed `moonbitlang/core`, kept as the
style reference. Every gate is green on every commit:

| Gate | Result |
|---|---|
| `moon check --target js -d` | type checks, with warnings as errors |
| `moon test --target js` | 250 unit tests |
| `scripts/e2e.ps1` | 26 end-to-end checks |
| `scripts/stdlib.ps1` | 49 of 49 standard library modules compile |
| `scripts/upstream.ps1 -Strict` | 415/415 programs match, 203/203 rejections match, 203/203 diagnostics verbatim |

The corpus numbers are baselines: they may only grow. `-Strict` compares the whole
rendered diagnostics of a negative test with the `.check` file upstream recorded,
not just the message the test asks for.

## Quick start

The compiler needs [moon](https://www.moonbitlang.com/download) (developed with
`0.1.20261117`) and [Node.js](https://nodejs.org) (v24). `moon` fetches the one
dependency, [`moonbitlang/x`](https://mooncakes.io/docs/moonbitlang/x), on the
first build.

```sh
moon build --target js
node _build/js/debug/build/cmd/main/main.js --run examples/hello.effekt
```

```
Hello, world!
```

The same through `moon`:

```sh
moon run cmd/main --target js -- --run examples/hello.effekt
```

Without `--run` the compiler only writes the JavaScript module, next to the input
and with a `.js` extension (or to `-o <file>`); `--run` additionally writes a
one-line `<name>__main.js` that requires the module and calls `main()`, and
executes it with `node`. Progress messages go to stderr, the program's own output
to stdout.

```
Usage: effekt [options] [input]

The Effekt language compiler (MoonBit implementation)

Arguments:
  input  The Effekt source file to compile

Options:
  -h, --help               Show this message
  --show-core              Print the core IR instead of compiling
  --show-js                Print the generated JavaScript to stdout
  --run                    Run the program with node after compiling
  -o, --output <output>    Write the generated JavaScript to <file> (default: alongside the input, with .js extension)
  -I, --include <include>  Add <dir> to the module search path (repeatable)
  --lib <lib>              Directory containing the Effekt standard library (default: ./libraries) [default: libraries]
```

The command line is declared with `moonbitlang/core/argparse`
(`src/compiler/cli.mbt`), so this text is rendered from that declaration and
malformed arguments are reported with the same usage. `--lib <dir>` selects a
different standard library; `examples/minilib` is a stripped-down prelude that
skips the slow-to-check parts of the real one, and the end-to-end tests use it to
exercise a second path through the frontend. `--show-core` dumps the program after
the middle-end — the core IR that CPS conversion consumes, with the prelude's
externs inlined — and compiles nothing.

## A program

```effekt
// Multi-shot continuations: `flip` is resumed twice, so all four
// combinations of the two `amb` calls are explored and summed.
interface Amb {
  def flip(): Bool
}

def amb(x: Int, y: Int): Int / Amb =
  if (do flip()) x else y

def main() = {
  val result = try {
    amb(1, 2) + amb(10, 20)
  } with Amb {
    def flip() = resume(true) + resume(false)
  }
  println(result)
}
```

```
$ node _build/js/debug/build/cmd/main/main.js --run examples/amb.effekt
66
```

The handler calls `resume` twice on the same continuation, once with `true` and
once with `false`; the four branches are summed to `1 + 10 + 2 + 20`. The `/ Amb`
annotation is what makes `amb` effect-polymorphic: the capability is passed by the
caller, and `main` discharges it with `try … with`. Everything the language offers
is available to these programs — data types and pattern matching, `var`/regions,
`loop`/`each`/`stop`, `ref`, streams, namespaces, `import`, `extern` definitions
bound to JavaScript — because the standard library ships with the repository and
the tests run it.

## How it works

```
Source ─► Lexer ─► Parser ─► Namer ─► UnboxInference ─► Typer ─► ResolveExternDefs
       ─► ExplicitCapabilities ─► core.Transformer (ANF) ─► Aggregate ─► Deadcode
       ─► core.Show ─► Optimizer ─► cps.Transformer ─► cps.Contify
       ─► js.TransformerCps ─► JavaScript
```

The frontend (lexing to capability elaboration) produces a typed source tree: the
type checker infers effects and capture sets together with types, checks
exhaustivity, runs the escape checks of `Wellformedness` on the result, and
`ExplicitCapabilities` then rewrites the capability annotations into explicit
passing. The middle-end lowers the tree to the ANF core IR — what `--show-core`
prints — generates the structural `show` instances the prelude's `show` extern
needs, and runs the optimizer over the whole module. The backend goes through CPS
and contification to the JavaScript IR, where handlers become the
`RESET`/`SHIFT`/`RESUME` primitives of the runtime; that runtime is
`effekt.effekt`, which every module includes through `extern include` (the same
file upstream uses). Each package below names its upstream counterpart.

The optimizer is upstream's `core/optimizer` chain, minus the phases listed under
[Differences from upstream](#differences-from-upstream): `Deadcode`,
`StaticArguments`, three rounds of `BindSubexpressions` → `Normalizer` →
`Deadcode` → `StaticResumptions` → `DirectStyle` → `ReferencesToParameters`, and
a final `Deadcode` + `ReferencesToParameters`. `core.Show` runs before it, exactly
as in upstream's `JavaScript.scala`, so the generated show instances are optimized
along with everything else.

## Repository layout

| Package | Upstream counterpart | Contents |
|---|---|---|
| `src/util` | `effekt/util/*` | `Source`, `Span`, diagnostics (rendered like upstream's colored messaging, which the corpus compares against), a Wadler pretty printer, extern string templates, unique ids |
| `src/symbols` | `effekt/symbols/*` | The `Sym` universe (one enum for every symbol kind), the source type language (`ValueType`/`BlockType`/`Effects`/`Captures`), bindings and scopes, builtins |
| `src/source` | `effekt/source/*`, `Lexer`, `Parser` | Syntax tree, `Context`, lexer, parser, generic AST rewriting, `ResolveExternDefs`, `ExplicitCapabilities` |
| `src/namer` | `effekt/Namer.scala` | Name resolution, symbol construction, scope handling |
| `src/typer` | `effekt/Typer.scala`, `effekt/typer/*` | Type and effect inference, unification, capability annotations, exhaustivity, unboxing, the escape checks of `Wellformedness` |
| `src/core` | `effekt/core/*` | The ANF core IR and its own type language, the source→core translation, the pattern-matching compiler, the structural `show` generator, and the optimizer passes (`deadcode`, `static_arguments`, `bind_subexpressions`, `normalize`, `static_resumptions`, `direct_style`, `references_to_parameters`) with the congruence rewriter they share |
| `src/cps` | `effekt/cps/*` | The CPS IR, the core→CPS translation, contification |
| `src/js` | `effekt/generator/js/*` | The JavaScript IR, the CPS→JS translation, the JS pretty printer |
| `src/backend` | `effekt/generator/js/JavaScript.scala` | Wires core → CPS → JS and aggregates the modules |
| `src/compiler` | `effekt/Compiler.scala`, `Driver` | Module loading, the compilation pipeline, the command line (declared with `moonbitlang/core/argparse`), the host layer |
| `cmd/main` | `effekt/Main.scala` | The `effekt` executable |
| `libraries/` | `libraries/` | The Effekt standard library (`common/`), plus the backend-specific runtime files (`js/`, `chez/`, `llvm/`), copied verbatim |
| `testdata/upstream/` | `examples/{pos,stdlib,neg}` | The upstream test corpus, copied verbatim, with the recorded `.check` outputs |
| `examples/` | | Small Effekt programs used for smoke testing, plus `minilib` |
| `scripts/` | | The end-to-end, standard-library and upstream-corpus gates (PowerShell) |

## Testing

| Command | What it covers |
|---|---|
| `moon check --target js -d` | The compiler type checks with warnings as errors |
| `moon test --target js` | 250 unit tests across every package: lexer (ported from upstream `LexerTests.scala`), parser (the tour snippets), namer, typer, the core ANF transformation, pattern matching, the structural `show` generator, CPS, JS code generation (`node --check`ed golden output), the driver's host layer |
| `scripts/e2e.ps1` | 14 example programs in 25 runs — 11 compiled against both the real standard library and `examples/minilib`, 3 that need the real one — plus a `--show-core` dump check: 26 checks. Compiled, executed with `node`, output compared |
| `scripts/stdlib.ps1` | Every `.effekt` module under `libraries/` compiled. A module counts when it produces JavaScript or stops only at "no `main` function defined", which is reported by code generation, after every phase has run; the run fails below 49 modules |
| `scripts/upstream.ps1` | The upstream corpus in `testdata/upstream`: 623 programs, 618 compared, 5 skipped on this platform |

The corpus is the real measure. A `pos`/`stdlib` test is compiled, run, and its
stdout together with our diagnostics compared to upstream's `.check` file — the
diagnostics are rendered in upstream's `[warning] path:line:column message` style,
with the source excerpt and carets — so these tests police both execution and
error reporting. A `neg` test has to fail with the expected severity on the
expected line and with upstream's message, either according to its `.check` file or
to its `// ERROR` / `// WARN` comments, which is what upstream's own test driver
does. `-Strict` additionally compares the whole rendered diagnostics of a negative
test verbatim against its `.check` file, the way upstream's `assertNoDiff` does;
all 203 match, and that number is a baseline like the others.

Five tests are skipped: one writes to `/dev/stdout`; three spawn POSIX tools that
Windows does not have (`cat`, and `sh`/`sleep`/`echo`/`seq`/`yes` in the two `io`
process tests); and one imports a module that does not exist upstream either
(`unsafe/cont`, in upstream's own ignore list for the JavaScript backend).

`scripts/stdlib.ps1` and `scripts/upstream.ps1` record baselines, which may only
grow; they are how a phase regression is caught long before the small examples
would notice. They run the compiler once per module, which is why they take
minutes — run them at milestones, not on every edit.

## Differences from upstream

These are deliberate, and documented at the point of use in the sources:

- **Object identity is replaced by unique integer ids.** Every syntax tree node
  carries a `uid`, and the `Context` keys its side tables (symbols, types,
  effects, captures, capability annotations) by that id instead of by object
  identity. This removes the need for the annotation-map machinery of
  `effekt/context/Annotations.scala`.
- **The trait hierarchy is flattened into one `Sym` enum**, with
  `is_value_symbol()` / `is_block_symbol()` / … predicates replacing the
  `TermSymbol`/`TypeSymbol` traits. Symbol identity is `uid` equality, exactly as
  upstream.
- **Capture-set and region inference is reduced.** Effects and value types are
  inferred properly; capture sets use a simplified constraint solver, so the
  capture information that reaches the backends is coarser than upstream's. The
  escape checks of `Wellformedness` run on the checked tree (a region, a block
  literal, an operation clause, a handler and a region-allocated variable each
  check the inferred type against their own binders), and both escapes are
  reported: a capture the binder drops (`Capture X escapes through type …`) and a
  type parameter of an existential pattern or of a higher-rank block that would
  leave its scope (`Type A escapes through type …`).
- **The optimizer is ported and runs.** The JavaScript pipeline performs
  upstream's `core/optimizer` chain (see `optimize` in `src/backend/emit.mbt`):
  `Deadcode`, `StaticArguments`, three rounds of `BindSubexpressions` →
  `Normalizer` → `Deadcode` → `StaticResumptions` → `DirectStyle` →
  `ReferencesToParameters`, and two final cleanups (`Deadcode`,
  `ReferencesToParameters`). `core.Show` runs *before* it, exactly as in
  upstream's `JavaScript.scala`, so the structural show instances the compiler
  generates are optimized along with everything else. The passes are
  `src/core/{deadcode,static_arguments,bind_subexpressions,normalize,
  static_resumptions,direct_style,references_to_parameters}.mbt`; they share the
  congruence rewriter `src/core/rewrite.mbt` (upstream's `Tree.Rewrite`) and the
  normalizer its `InliningPolicy`, the `Renamer` (`src/core/renamer.mbt`) and the
  node counts of `core/Tree.scala`'s `sizes` (`src/core/size.mbt`).
  `StaticArguments` comes with the call analysis of `core/Recursive.scala`
  (`src/core/recursive.mbt`). The types the passes read — `Type.inferType` and
  `Type.inferCapt`, which upstream keeps separate from its debug-only checker —
  come from `src/core/type.mbt`.
  Deliberate differences, each documented at the point of use:
  - `Deadcode` does not drop a local `val` whose binding is a provably pure call
    (`Deadcode.isPureCall`), which needs precise capture sets; with the
    approximate capture sets of this port such a call can look pure while
    capturing a region (a `while` loop is exactly this shape), so the rule would
    drop live calls.
  - `Mono`, `LambdaSets`, `ArityRaising` and `DropBindings` are not ported.
  - the normalizer has five deviations: the sharing of pure expressions
    (`Context.facts`, keyed by structural expression equality) is not ported,
    `covers`/`selecting` (which need the scrutinee's data type) are skipped, the
    `Shift` rule of `normalizeVal` is skipped (it retypes the continuation with
    the type of the enclosing statement, which the normalizer does not infer),
    join-point parameters carry `unknown_value_type()` rather than the inferred
    types of the branches, and the "return the unit value" rule compares the bound
    statement against `()` syntactically instead of comparing result types.
  - a few tree annotations that upstream always knows are still the `unknown_*`
    sentinels (`unknown_value_type()`/`unknown_block_type()`), e.g. the value a
    `Bind::bind_impure_app` binds; `Type.inferType` propagates them instead of
    failing.
- **The Chez Scheme, LLVM and VM backends are not ported**, nor the LSP server,
  the REPL or the documentation generator.

## Details worth knowing

- Core has **its own type language** (`src/core/types.mbt`, upstream
  `core/Type.scala`), separate from the source language of `src/symbols`:
  `ValueType` is `Var | Data | Boxed` and `BlockType` is
  `Function | Interface | Prompt | Resume`. Two things the source language cannot
  express are needed by the prompt/shift encoding the transformer produces and the
  optimizer removes — a function type has a *list* of results (a prompt answers
  with several values) and a shift continuation has the resumption type
  `(result) ~> (answer)`, which is what `DirectStyle` matches on. A core function
  type also carries **no effect set**: by the time the tree is built the
  capabilities are explicit block parameters. `core.transform` converts the source
  types at the boundary (capabilities become extra block parameters), and
  everything downstream — `src/cps` included, as upstream's `cps.Tree` — keeps the
  core types. Types are *annotations*, not an inferred property of the tree:
  `Type.inferType`/`inferCapt` (`src/core/type.mbt`) recover what the optimizer
  reads.
- A `reset` returns to a continuation of its **own arity**: the JavaScript backend
  emits one `RETURN_n` per arity the program needs (upstream's
  `TransformerCps.returnFrom`), which is the number of values the reset's body
  returns. This matters as soon as a node answers with several values — the
  prompt/shift encoding of a multi-value `return`, or the extra result that
  `ReferencesToParameters` threads through a definition.
- The parser wraps *every* annotated result type in `Effectful(t, {})`, exactly
  like upstream's `Parser.effectful` ("if it's not a `${tpe} / ${effs}`, then
  pretend the effect set is empty"). An annotation without `/ …` therefore means
  "no effect is declared": no capability is bound for that definition, and every
  effect its body performs — including the effects of nested definitions — escapes
  to the enclosing statement. That is what makes the standard library's
  `stop`/`fail` loops work, but it also means `: T` and `: T / {}` are the same
  thing, upstream included.
- The implicit prelude mirrors upstream's `Runner.prelude` (`effekt`, `option`,
  `partial`, `stream`, `control`, `list`, `result`, `exception`, `array`, `char`,
  `bytearray`, `stringbuffer`, `string`, `ref`): every module gets those includes,
  the prelude modules themselves do not, and a program file that happens to be
  named like one of them (`exception.effekt`) still gets the real module.
  `extern include` directives are only read for the current backend's feature
  flags, as upstream's `Namer` does.
- The command line is rendered from an `argparse` declaration rather than
  hand-written, and `--help` is an ordinary flag: argparse's built-in help action
  calls `process.exit`, which truncates piped output, so the help text goes
  through the same stdout path as everything else.
- The compiler depends on [`moonbitlang/x`](https://mooncakes.io/docs/moonbitlang/x)
  for everything it needs from its host: `moonbitlang/x/fs` reads and writes
  files, `moonbitlang/x/path` implements `node:path`'s rules, and the command line
  comes from `moonbitlang/core/env`. The only hand-written JavaScript left is
  `src/compiler/node.mbt` (the exit code, stderr, and running a script with
  `node`), which the standard library does not provide.

## License

This port is released under the Apache License 2.0 (see [LICENSE](LICENSE)).
Upstream Effekt is MIT-licensed; `libraries/` and `testdata/upstream/` are copied
from it verbatim and keep that license.
