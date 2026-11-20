# Effekt in MoonBit

An implementation of the [Effekt](https://effekt-lang.org) language in
[MoonBit](https://www.moonbitlang.com), compiling to JavaScript.

Effekt is a research language built around **effect handlers**: algebraic effects
with multi-shot resumptions and capability-passing effect polymorphism (`{io}`,
`{fail}`). This is a port of the reference Scala compiler, not an implementation
from the papers: it follows upstream's phases and intermediate representations
from lexing to JavaScript, and `libraries/` and the test corpus are upstream's own
files. The whole language compiles, not a subset.

## Status

| Gate | Result |
|---|---|
| `moon check --target js -d` | type checks, warnings as errors |
| `moon test --target js` | 256 unit tests |
| `scripts/e2e.ps1` | 26 end-to-end checks |
| `scripts/stdlib.ps1` | 49 of 49 standard library modules compile |
| `scripts/upstream.ps1 -Strict` | 440 of 440 programs match, 91 of 91 benchmarks run and match, 10 of 10 case studies run and match, 243 of 243 rejections match, 240 of 240 diagnostics verbatim |

Every gate is green on every commit, against the baselines `upstream.ps1` keeps;
they may only grow, apart from a re-sync that moves the corpus. The corpus,
copied verbatim from upstream at commit `6976c7947` (314 `pos`, 131 `stdlib`, 93
`benchmarks`, 10 literate `casestudies`, 243 `neg`), is the real measure: a
positive program is compiled, run, and its stdout together with our diagnostics
is compared against upstream's `.check` file, and a `neg` program has to fail
with the expected severity, on the expected line, with upstream's message —
`-Strict` compares the whole rendered diagnostics verbatim, as upstream's
`assertNoDiff` does. 784 of the 791 programs are compared; the seven skipped
here write to `/dev/stdout`, spawn POSIX tools or check a POSIX errno Windows
lacks, overflow the stack (upstream ignores that benchmark for JavaScript), or
import a module that upstream itself does not ship.

Every program of the corpus compiles and runs, and every rejection is a rejection
of the expected severity on the expected line. The diagnostics are rendered the
way upstream's `Drawing`/`ColoredMessaging` renders them — header, source excerpt
with carets, then the nested paragraphs behind a `|` gutter — so all 240 recorded
`.check` files of rejected programs match character for character. Two
behaviours had to be mirrored to get there: the join of an `if`/`match` aborts
for concrete incompatible arms but only constrains a unification variable (so
one file reports a single extra message and another keeps checking later
definitions), and a failed nested call is never reported as a shared cause of
several overload candidates — upstream compares diagnostics as values, and their
instantiated types differ per candidate. `stdlib.ps1` and `upstream.ps1` run the
compiler once per module, so they take minutes: run them at milestones.

## Quick start

[moon](https://www.moonbitlang.com/download) (`0.1.20261117`) and
[Node.js](https://nodejs.org) (v24) are needed; `moon` fetches the one dependency,
[`moonbitlang/x`](https://mooncakes.io/docs/moonbitlang/x), on the first build.

```sh
moon build --target js
node _build/js/debug/build/cmd/main/main.js --run examples/hello.effekt
```

```
Hello, world!
```

Or through `moon`:

```sh
moon run cmd/main --target js -- --run examples/hello.effekt
```

The compiler writes the generated module next to the input, with a `.js` extension
(or to `-o <file>`), plus a one-line `<name>__main.js` that requires it and calls
`main()`; `--run` then executes that with `node`. `--show-js` prints the module to
stdout instead, `--show-core` dumps the core IR and generates no code, `-I <dir>`
adds to the module search path, and `--lib <dir>` selects a different standard
library (`examples/minilib` is a stripped-down prelude). Diagnostics go to stderr,
the program's own output to stdout. The command line is declared with
`moonbitlang/core/argparse` (`src/compiler/cli.mbt`), so `--help` and the usage for
malformed arguments come from that declaration.

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

`flip` is resumed twice, once with `true` and once with `false`, so the two `amb`
calls explore all four combinations — 11, 21, 12, 22 — summed to 66. The `/ Amb`
annotation makes `amb` effect-polymorphic: the capability is passed by the caller,
and `main` discharges it with `try … with`. Everything else the language offers
(data types and pattern matching, `var` and regions, `loop`/`each`/`stop`, `ref`,
streams, namespaces, `import`, `extern` definitions bound to JavaScript) is
available to these programs, because the standard library ships with the repository
and the gates run it.

## How it works

```
Source ─► Lexer ─► Parser ─► Namer ─► UnboxInference ─► Typer ─► ResolveExternDefs
       ─► ExplicitCapabilities ─► core.Transformer (ANF) ─► Aggregate ─► Deadcode
       ─► core.Mono ─► core.Show ─► Optimizer ─► cps.Transformer ─► cps.Contify
       ─► js.TransformerCps ─► JavaScript
```

The frontend produces a typed source tree — effects and capture sets are inferred
with types, exhaustivity is checked, the escape checks of `Wellformedness` run —
and `ExplicitCapabilities` then rewrites capability annotations into explicit
passing. The middle-end lowers the tree to the ANF core IR (what `--show-core`
prints), monomorphizes it, generates the structural `show` instances the prelude
needs, and runs upstream's optimizer chain: `Deadcode`, `StaticArguments`, three
rounds of `BindSubexpressions` → `Normalizer` → `Deadcode` → `StaticResumptions` →
`DirectStyle` → `ReferencesToParameters`, and a final `Deadcode` +
`ReferencesToParameters` (`core.Mono` and `core.Show` run before the optimizer, as
in upstream's `JavaScript.scala`). The backend goes through CPS and contification
to the JavaScript IR, where handlers become the `RESET`/`SHIFT`/`RESUME`
primitives of `effekt.effekt`, the runtime every module includes through `extern
include`.

Core has its own type language (`src/core/types.mbt`, upstream `core/Type.scala`):
result lists and resumption types, and no effect sets, since capabilities are
explicit block parameters by then. Types there are annotations, not an inferred
property of the tree: `Type.inferType` and `inferCapt` (`src/core/type.mbt`)
recover what the passes read.

## Repository layout

Source paths are relative to upstream's `effekt/shared/src/main/scala/effekt/`;
`Driver`, `Main` and `Runner` live in `effekt/jvm/`.

| Package | Upstream counterpart | Contents |
|---|---|---|
| `src/util` | `util/*` | `Source`, `Span`, diagnostics, pretty printer, extern string templates, unique ids |
| `src/symbols` | `symbols/*` | The one `Sym` enum, the source type language, bindings and scopes, builtins |
| `src/source` | `source/*`, `context/*`, `Lexer.scala`, `Parser.scala` | Syntax tree, lexer, parser, `Context`, `ResolveExternDefs`, `ExplicitCapabilities` |
| `src/namer` | `Namer.scala` | Name resolution and scope handling |
| `src/typer` | `Typer.scala`, `typer/*` | Type and effect inference, unification, exhaustivity, unboxing, escape checks |
| `src/core` | `core/*` | The ANF IR, source→core translation, pattern compiler, `show` generator, optimizer passes |
| `src/cps` | `cps/*` | The CPS IR, core→CPS translation, contification |
| `src/js` | `generator/js/*` | The JavaScript IR, CPS→JS translation, pretty printer |
| `src/backend` | `generator/js/JavaScript.scala` | Pipeline wiring and module aggregation |
| `src/compiler` | `Compiler.scala`, `Driver.scala`, `Runner.scala` | Module loading, the pipeline, the command line, the host layer |
| `cmd/main` | `Main.scala` | The `effekt` executable |
| `libraries/` | `libraries/` | The standard library and the backend runtimes, verbatim |
| `testdata/upstream/` | `examples/{pos,stdlib,neg}` | The upstream corpus, verbatim, with the recorded `.check` outputs |
| `examples/`, `scripts/` | | Smoke tests and `minilib`; the three PowerShell gates |

## Differences from upstream

Deliberate, and documented at the point of use:

- **Unique integer ids replace object identity.** Every syntax tree node carries a
  `uid`, and the `Context` keys its side tables by it instead of by object
  identity, which removes the annotation-map machinery of
  `effekt/context/Annotations.scala`.
- **One `Sym` enum instead of the trait hierarchy**, with `is_value_symbol()` /
  `is_block_symbol()` / … predicates in place of the `TermSymbol`/`TypeSymbol`
  traits. Symbol identity is `uid` equality, as upstream.
- **Capture-set and region inference is reduced.** Effects and value types are
  inferred properly, but a simplified solver yields coarser capture sets. The
  escape checks of `Wellformedness` still run, and both escapes are reported: a
  capture the binder drops, and a type parameter that would leave its scope.
- **The optimizer is ported and runs** (see above), with these deviations: no
  `Deadcode.isPureCall` rule, because with approximate capture sets a pure-looking
  call can capture a region and the rule would drop live calls; no `LambdaSets`,
  `ArityRaising` or `DropBindings`; five normalizer deviations (no
  sharing of pure expressions via `Context.facts`, `covers`/`selecting` skipped,
  the `Shift` rule of `normalizeVal` skipped, join-point parameters typed
  `unknown_value_type()`, and the unit-return rule comparing syntax rather than
  result types); and a few annotations left as `unknown_*` sentinels, which
  `Type.inferType` propagates instead of failing.
- **The Chez Scheme, LLVM and VM backends are not ported**, nor the LSP server,
  the REPL or the documentation generator.

## Notes

- The parser wraps every annotated result type in `Effectful(t, {})`, exactly like
  upstream's `Parser.effectful`, so `: T` and `: T / {}` mean the same thing: no
  effect is declared, and the effects of the body escape to the enclosing
  statement.
- The implicit prelude mirrors upstream's `Runner.prelude`: a module gets those
  includes, the prelude modules themselves do not.
- A `reset` returns to a continuation of its own arity: the JavaScript backend
  emits one `RETURN_n` per arity the program needs.

## License

Apache-2.0 (see [LICENSE](LICENSE)). Upstream Effekt is MIT-licensed; `libraries/`
and `testdata/upstream/` are copied from it verbatim.
