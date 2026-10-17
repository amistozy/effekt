# Effekt in MoonBit

A reimplementation of the [Effekt](https://effekt-lang.org) programming language
in [MoonBit](https://www.moonbitlang.com), targeting the **JavaScript** backend
only.

The compiler is a faithful port of the upstream Scala implementation
(`.reference/effekt`, used read-only as the reference); the phase structure, the
intermediate representations and the generated JavaScript follow upstream
closely, so programs compiled here link against the unmodified Effekt JS runtime
(`libraries/js/effekt_runtime.js`).

```
Source ──► Lexer ──► Parser ──► Namer ──► UnboxInference ──► Typer
       ──► ResolveExternDefs ──► ExplicitCapabilities
       ──► core.Transformer (ANF) ──► Aggregate
       ──► core.optimizer.Deadcode ──► core.Show
       ──► cps.Transformer ──► cps.Contify
       ──► js.TransformerCps ──► JavaScript
```

## Building and running

```sh
moon check                            # type check the compiler
moon test --target js                 # run the test suite
moon build --target js

# compile and run a program (against the bundled standard library)
node _build/js/debug/build/cmd/main/main.js --run examples/hello.effekt

# ... or via moon
moon run cmd/main --target js -- --run examples/hello.effekt

powershell -File scripts/e2e.ps1      # compile + run every example, compare output
```

```
$ node _build/js/debug/build/cmd/main/main.js --run examples/amb.effekt
66
```

The command line is declared with `moonbitlang/core/argparse`
(`src/compiler/cli.mbt`), so `--help` prints the reference rendered from that
declaration and malformed arguments are reported by argparse with the same
usage text. `--lib <dir>` selects a different standard library;
`examples/minilib` contains a stripped-down prelude that avoids the
slow-to-check parts of the real one. `--show-js` prints the generated
JavaScript instead of writing it, and `--show-core` prints the core program
(the middle-end's output, i.e. what CPS conversion consumes) and compiles
nothing.

The compiler depends on [`moonbitlang/x`](https://mooncakes.io/docs/moonbitlang/x)
for everything it needs from its host: `moonbitlang/x/fs` reads and writes the
files, `moonbitlang/x/path` implements `node:path`'s rules, and the command line
comes from `moonbitlang/core/env`. The only hand-written JavaScript left is the
three functions in `src/compiler/node.mbt` (exit code, stderr, running a script
with `node`) which the standard library does not provide. `moon` fetches the
dependency on the first build.

## Layout

| Package | Upstream counterpart | Contents |
|---|---|---|
| `src/util` | `effekt/util/*` | `Source`, `Span`, diagnostics, a Wadler pretty printer, extern string templates, unique ids |
| `src/symbols` | `effekt/symbols/*` | The `Sym` universe (one enum for every symbol kind), the type language (`ValueType`/`BlockType`/`Effects`/`Captures`), bindings/scopes, builtins |
| `src/source` | `effekt/source/*`, `Lexer`, `Parser` | Syntax tree, `Context`, lexer, parser, generic AST rewriting, `ResolveExternDefs`, `ExplicitCapabilities` |
| `src/namer` | `effekt/Namer.scala` | Name resolution, symbol construction, scope handling |
| `src/typer` | `effekt/Typer.scala`, `effekt/typer/*` | Type and effect inference, unification, capability annotations, exhaustivity, unboxing |
| `src/core` | `effekt/core/*` | The ANF core IR, the source→core translation, the pattern matching compiler, the structural `show` generator, dead code elimination, free variables, substitutions, `DeclarationContext` |
| `src/cps` | `effekt/cps/*` | The CPS IR, the core→CPS translation, contification |
| `src/js` | `effekt/generator/js/*` | The JavaScript IR, the CPS→JS translation, the JS pretty printer |
| `src/backend` | `effekt/generator/js/JavaScript.scala` | Wires core → CPS → JS and aggregates the modules |
| `src/compiler` | `effekt/Compiler.scala`, `Driver` | Module loading, the compilation pipeline, the command line (declared with `moonbitlang/core/argparse`), the host layer (files and paths via `moonbitlang/x`, `node.mbt` for the rest) |
| `libraries/` | `libraries/` | The Effekt standard library and the JavaScript runtime, copied verbatim from upstream |
| `examples/` | | Small Effekt programs used for smoke testing |

## Deviations from upstream

These are deliberate and are documented at the point of use in the sources:

- **Object identity is replaced by unique integer ids.** Every syntax tree node
  carries a `uid`, and the `Context` keys its side tables
  (symbols, types, effects, captures, capability annotations) by that id instead
  of by object identity. This removes the need for the annotation-map machinery
  of `effekt/context/Annotations.scala`.
- **The trait hierarchy is flattened into one `Sym` enum**, with
  `is_value_symbol()` / `is_block_symbol()` / … predicates replacing the
  `TermSymbol`/`TypeSymbol` traits. Symbol identity is `uid` equality, exactly
  as upstream.
- **Capture-set and region inference is reduced.** Effects and value types are
  inferred properly; capture sets use a simplified constraint solver, so the
  capture information that reaches the backends is coarser than upstream's.
- **Dead code elimination is partial.** `core/optimizer/Deadcode` (and the
  `Reachable` analysis behind it) is ported and runs where upstream runs it,
  between `Aggregate` and `core.Show`, so unreachable functions, constructors,
  externs and toplevel definitions no longer reach the backend — that is what
  keeps the prelude's llvm-only externs from being reported as unsupported. One
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

## Known limitations

- The core language, the effect system, handlers with multi-shot resumptions and
  the whole prelude all work: **all 49 modules of the bundled standard library
  compile** (they are library modules, so they stop at "no `main`" after code
  generation), and `scripts/stdlib.ps1` keeps them compiling. Everything the
  prelude needs — `println`, `show` (including the compiler-generated structural
  instances), `ref`, `region`, `loop`/`each`/`stop`, and `stream`'s handlers —
  compiles and runs. The implicit prelude mirrors upstream `Runner.prelude`
  (`effekt`, `option`, `partial`, `stream`, `control`, `list`, `result`,
  `exception`, `array`, `char`, `bytearray`, `stringbuffer`, `string`, `ref`):
  every module gets those includes, the prelude modules themselves do not, and a
  program file that happens to be named like one of them (`exception.effekt`)
  still gets the real module. `extern include` directives are only read for the
  current backend's feature flags, as upstream's `Namer` does.
- The parser wraps *every* annotated result type in `Effectful(t, {})`, exactly
  like upstream's `Parser.effectful` ("if it's not a `${tpe} / ${effs}`, then
  pretend the effect set is empty"). An annotation without `/ …` therefore means
  "no effect is declared": no capability is bound for that definition and every
  effect its body performs — including the effects of nested definitions —
  escapes to the enclosing statement. That is what makes the standard library's
  `stop`/`fail` loops work, but it also means `: T` and `: T / {}` are the same
  thing, upstream included.

## Testing

| Command | What it covers |
|---|---|
| `moon test --target js` | 206 unit tests across every package: lexer (ported from upstream `LexerTests.scala`), parser (all tour snippets), namer, typer, core ANF transformation, pattern matching, the structural `show` generator, CPS, JS code generation (`node --check`ed golden output), the driver's host layer |
| `powershell -File scripts/e2e.ps1` | 13 example programs (25 runs across two standard libraries) plus a `--show-core` dump check, compiled and executed with `node`, output compared |
| `powershell -File scripts/stdlib.ps1` | every module under `libraries/` compiled, with the failures grouped by cause; fails when fewer modules compile than the recorded baseline (49) — this is what catches phase bugs the small examples never reach |
| `src/source/parser_test.mbt` | additionally validated out of band against all 575 `.effekt` files of the upstream checkout |

The end-to-end cases exercise, among others: recursion (`fib`), first-class
blocks (`each { x => … }`), mutable variables and `while`, algebraic data types
with pattern matching, exception handlers (`try … with`), and multi-shot
resumptions (`amb` — a handler that resumes twice and sums all four
combinations).

