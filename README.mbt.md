# Effekt in MoonBit

An implementation of the [Effekt](https://effekt-lang.org) language in
[MoonBit](https://www.moonbitlang.com), compiling to JavaScript.

Effekt is a research language built around **effect handlers**: algebraic
effects with multi-shot resumptions, capability-passing effect polymorphism
(`{io}`, `{fail}`), regions and lexical capture sets. This repository is a port
of the reference Scala compiler rather than a toy: lexer, parser, typer,
optimizers and the JavaScript backend follow upstream's phase structure and
intermediate representations (`.reference/effekt`, kept read-only as the
reference), and the standard library and the runtime are upstream's own files,
so what compiles here is the whole language, not a subset of it.

**Status.** Every one of the **392** compiling-and-running programs of the
Effekt repository's own test corpus prints exactly what upstream recorded, and
**168 of the 170** programs that have to be rejected are rejected at the expected
line (81 of those with a different message). The whole standard library
compiles. The remaining differences are listed under [Differences from
upstream](#differences-from-upstream).

## Quick start

The compiler needs [moon](https://www.moonbitlang.com/download) (developed with
`0.1.20261104`) and [Node.js](https://nodejs.org) (v24). `moon` fetches the one
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

Without `--run` the compiler only writes the JavaScript module, next to the
input and with a `.js` extension (or to `-o <file>`); `--run` additionally
writes a one-line `<name>__main.js` that requires the module and calls `main()`,
and executes it with `node`. Progress messages go to stderr, the program's own
output to stdout.

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
skips the slow-to-check parts of the real one and is what the end-to-end tests
use to exercise a second path through the frontend. `--show-core` dumps the
program after the middle-end — the core IR that CPS conversion consumes, with
the prelude's externs inlined — and compiles nothing.

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
once with `false`; the four branches are summed to `1 + 10 + 2 + 20`. The
`/ Amb` annotation is what makes `amb` effect-polymorphic: the capability is
passed by the caller, and `main` discharges it with `try … with`. Everything the
language offers is available to these programs — data types and pattern
matching, `var`/regions, `loop`/`each`/`stop`, `ref`, streams, namespaces,
`import`, `extern` definitions bound to JavaScript — because the standard
library ships with the repository and the tests run it.

## How it works

```
Source ─► Lexer ─► Parser ─► Namer ─► UnboxInference ─► Typer ─► Wellformedness
       ─► ResolveExternDefs ─► ExplicitCapabilities
       ─► core.Transformer (ANF) ─► Aggregate ─► Deadcode ─► core.Show
       ─► cps.Transformer ─► cps.Contify ─► js.TransformerCps ─► JavaScript
```

The frontend (lexing to capability elaboration) produces a typed source tree;
the middle-end lowers it to the ANF core IR, which is what `--show-core` prints;
the backend goes through CPS and contification to the JavaScript IR. The effect
machinery lives in the frontend — `Typer` infers effects and capture sets
together with types and `ExplicitCapabilities` makes capability passing
explicit — and the CPS translation turns handlers into the
`RESET`/`SHIFT`/`RESUME` primitives of the runtime, which `effekt.effekt`
includes into every module through `extern include` (the same file upstream
uses). Each package below names its upstream counterpart.

## Repository layout

| Package | Upstream counterpart | Contents |
|---|---|---|
| `src/util` | `effekt/util/*` | `Source`, `Span`, diagnostics (rendered like upstream's `ColoredMessaging`, which the test corpus compares against), a Wadler pretty printer, extern string templates, unique ids |
| `src/symbols` | `effekt/symbols/*` | The `Sym` universe (one enum for every symbol kind), the type language (`ValueType`/`BlockType`/`Effects`/`Captures`), bindings and scopes, builtins |
| `src/source` | `effekt/source/*`, `Lexer`, `Parser` | Syntax tree, `Context`, lexer, parser, generic AST rewriting, `ResolveExternDefs`, `ExplicitCapabilities` |
| `src/namer` | `effekt/Namer.scala` | Name resolution, symbol construction, scope handling |
| `src/typer` | `effekt/Typer.scala`, `effekt/typer/*` | Type and effect inference, unification, capability annotations, exhaustivity, unboxing, the escape checks of `Wellformedness` |
| `src/core` | `effekt/core/*` | The ANF core IR, the source→core translation, the pattern matching compiler, the structural `show` generator, dead code elimination, free variables, substitution, `DeclarationContext` |
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
| `moon test --target js` | 206 unit tests across every package: lexer (ported from upstream `LexerTests.scala`), parser (all tour snippets), namer, typer, core ANF transformation, pattern matching, the structural `show` generator, CPS, JS code generation (`node --check`ed golden output), the driver's host layer |
| `scripts/e2e.ps1` | 14 example programs in 25 runs across the two standard libraries, plus a `--show-core` dump check (26 checks): compiled and executed with `node`, output compared |
| `scripts/stdlib.ps1` | Every module under `libraries/` compiled, failures grouped by cause; a library module counts when it gets through code generation and stops at "no `main`", and the run fails below 49 modules |
| `scripts/upstream.ps1` | The upstream test corpus (`testdata/upstream`, 565 programs) |

The corpus is the real measure. A `pos`/`stdlib` test is compiled, run, and its
stdout together with our diagnostics compared to upstream's `.check` file — the
diagnostics are rendered in upstream's `[warning] path:line:column message`
style, with the source excerpt and carets — so these tests police both
execution and error reporting. A `neg` test only has to fail with the expected
severity on the expected line, either according to its `.check` file or its
`// ERROR` / `// WARN` comments, which is what upstream's own test driver does.
Three tests are skipped: one writes to `/dev/stdout`, one spawns the POSIX `cat`,
and one imports a module that does not exist upstream either (`unsafe/cont`, in
upstream's own ignore list for the JS backend).

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
  `TermSymbol`/`TypeSymbol` traits. Symbol identity is `uid` equality, exactly
  as upstream.
- **Capture-set and region inference is reduced.** Effects and value types are
  inferred properly; capture sets use a simplified constraint solver, so the
  capture information that reaches the backends is coarser than upstream's. The
  escape checks of `Wellformedness` run on the checked tree (a region, a block
  literal, an operation clause and a handler each check the inferred type of
  their body against their own binders). Both escapes are reported: a capture
  the binder drops (`Capture X escapes through type …`), and a type parameter of
  an existential pattern or of a higher-rank block that would leave its scope
  (`Type A escapes through type …`).
- **Dead code elimination is partial.** `core/optimizer/Deadcode` (and the
  `Reachable` analysis behind it) is ported and runs where upstream runs it,
  between `Aggregate` and `core.Show`, so unreachable functions, constructors,
  externs and toplevel definitions no longer reach the backend — that is what
  keeps the prelude's LLVM-only externs from being reported as unsupported. One
  rule of it is *not* ported: upstream also drops a local `val` whose binding is
  a provably pure call (`Deadcode.isPureCall`), which needs precise capture
  sets; with the approximate capture sets of this port such a call can look pure
  while capturing a region (a `while` loop is exactly this shape), so the rule
  would drop live calls. The rest of `core/optimizer/*` (`DropBindings`,
  `Normalizer`, `DirectStyle`, `StaticArguments`, …) is still skipped; those
  passes are semantics-preserving, so omitting them only affects the quality of
  the generated code, and the JS backend already implements its own direct-style
  and loop optimizations (`src/js/transform_cps.mbt`).
- **The Chez Scheme, LLVM and VM backends are not ported**, nor the LSP server,
  the REPL or the documentation generator.

## Details worth knowing

- The parser wraps *every* annotated result type in `Effectful(t, {})`, exactly
  like upstream's `Parser.effectful` ("if it's not a `${tpe} / ${effs}`, then
  pretend the effect set is empty"). An annotation without `/ …` therefore means
  "no effect is declared": no capability is bound for that definition, and every
  effect its body performs — including the effects of nested definitions —
  escapes to the enclosing statement. That is what makes the standard library's
  `stop`/`fail` loops work, but it also means `: T` and `: T / {}` are the same
  thing, upstream included.
- The implicit prelude mirrors upstream's `Runner.prelude` (`effekt`, `option`,
  `partial`, `stream`, `control`, `list`, `result`, `exception`, `array`,
  `char`, `bytearray`, `stringbuffer`, `string`, `ref`): every module gets those
  includes, the prelude modules themselves do not, and a program file that
  happens to be named like one of them (`exception.effekt`) still gets the real
  module. `extern include` directives are only read for the current backend's
  feature flags, as upstream's `Namer` does.
- The command line is rendered from an `argparse` declaration rather than
  hand-written, and `--help` is an ordinary flag: argparse's built-in help
  action calls `process.exit`, which truncates piped output, so the help text
  goes through the same stdout path as everything else.
- The compiler depends on [`moonbitlang/x`](https://mooncakes.io/docs/moonbitlang/x)
  for everything it needs from its host: `moonbitlang/x/fs` reads and writes
  files, `moonbitlang/x/path` implements `node:path`'s rules, and the command
  line comes from `moonbitlang/core/env`. The only hand-written JavaScript left
  is `src/compiler/node.mbt` (exit code, stderr, and running a script with
  `node`), which the standard library does not provide.

## License

This port is released under the Apache License 2.0 (see [LICENSE](LICENSE)).
Upstream Effekt is MIT-licensed; `libraries/` and `testdata/upstream/` are
copied from it verbatim and keep that license.
