// The JavaScript backend: source modules -> core -> CPS -> JavaScript.
//
// Mirrors `effekt/generator/js/JavaScript.scala`'s `Compile` pipeline:
//
//     Frontend andThen Middleend                      (source -> core)
//     Aggregate                                       (concatenate modules)
//     Deadcode                                        (drop unreachable code)
//     core.Show                                       (structural show instances)
//     Optimizer / DropBindings                        (skipped for now)
//     cps.Transformer.transform                       (core -> cps)
//     cps.Contify.rewrite                             (cps -> cps)
//     TransformerCps.compile(...).commonjs            (cps -> js)

///|
/// The name of the entry point.
fn main_name() -> String {
  "main"
}

///|
/// The middle-end: the already typechecked modules (dependencies first, main
/// module last) become one core module, after dead-code elimination and the
/// compiler-generated structural `show` instances.
///
/// This is what `--show-core` prints and what CPS conversion consumes, together
/// with the entry point's symbol.
fn middle_end(
  modules : ArrayView[@namer.ResolvedModule],
  ctx : Context,
) -> (@core.ModuleDecl, Sym) raise EffektError {
  if modules.is_empty() {
    ctx.abort(Span::missing(), "No module to compile.")
  }
  // 0. Bind the `infixEq` overloads used to compile literal patterns. This has
  //    to happen *before* the core transformation, which is where patterns are
  //    compiled (upstream: the core `Transformer` looks the prelude's `infixEq`
  //    up while visiting a literal pattern).
  match find_infix_eqs(modules) {
    [] => @core.clear_pattern_equality_functions()
    syms => @core.set_pattern_equality_functions(syms)
  }
  // 1. Resolve externs, make capability passing explicit, then translate to
  //    core. Dependencies come first; the main module is last.
  let cores : Array[@core.ModuleDecl] = []
  for m in modules {
    let tree = @source.resolve_extern_defs(m.tree, ctx)
    let tree = @source.explicit_capabilities(tree, ctx)
    let exports = exports_of(m.module)
    let core = @core.transform_with_exports(tree, m.module.path, ctx, exports)
    cores.push(core)
  }
  // 2. Aggregate into a single core module.
  let main_module = modules[modules.length() - 1]
  let aggregated = aggregate(cores, main_module.module.path)
  // 2b. Remove the definitions and externs that `main` cannot reach (upstream:
  //     `Aggregate andThen Deadcode andThen core.Show andThen ...`). This keeps
  //     unreachable externs — e.g. the llvm-only ones of the prelude — from
  //     reaching the code generator, which would report them as unsupported.
  //     The entry points are `Context.ensureMainExists` (the `main` of the main
  //     module) plus the names `core.Show` needs in the next step.
  // `Typer.checkMain` has already rejected ambiguous mains; finding none is the
  // backend's error (upstream `Context.ensureMainExists`). The span is the main
  // module's, so the diagnostic points at the file.
  let main_sym = find_main(modules, ctx)
  if main_sym is None {
    // Upstream reports this from `Deadcode`'s `ensureMainExists`, i.e. after the
    // typer; the phase tag says so.
    ctx.abort_with(
      Message::error(main_module.tree.span, "No main function defined").with_phase(
        "deadcode-elimination",
      ),
    )
  }
  let main_sym = main_sym.unwrap()
  let required = @symbols.dedup_syms(
    [main_sym] + @core.required_names(aggregated),
  )
  let aggregated = @core.deadcode(aggregated, required)
  // 2c. Replace the prelude's `show` extern by compiler-generated structural
  //     show definitions. Upstream runs `core.Show` before its optimizer, so the
  //     instances it generates are optimized (and dead-coded) along with
  //     everything else.
  let aggregated = @core.show_phase(aggregated)
  // 2d. The optimizer: upstream's `Optimizer.optimize`, minus the phases that
  //     are not ported (`Mono`, `LambdaSets`, `ArityRaising`, `DropBindings`).
  let aggregated = optimize(aggregated, main_sym)
  (aggregated, main_sym)
}

///|
/// `Optimizer.optimize`: dead code elimination, then the static argument
/// transformation, then three rounds of normalization (each of which ends in the
/// passes that consume the normal form), and two final cleanups.
///
/// Upstream normalizes three times "since tail resumptions might only surface
/// after normalization and leave dead `Reset`s"; the rounds run the same phases on
/// a shrinking tree.
///
/// `ReferencesToParameters` is ported (`src/core/references_to_parameters.mbt`)
/// but not run: threading the state of a reference that lives across a shift
/// miscompiles `testdata/upstream/examples/stdlib/stream/map.effekt`, so the pass
/// stays out of the pipeline until that is understood.
fn optimize(
  module : @core.ModuleDecl,
  main_sym : Sym,
) -> @core.ModuleDecl raise EffektError {
  let roots = [main_sym]
  // (1) first thing we do is simply remove unused definitions (this speeds up
  //     all following analyses and rewrites)
  let module = @core.deadcode(module, roots)
  // (2) lift static arguments
  let module = @core.static_arguments(module)
  let policy = @core.InliningPolicy::default()
  let module = normalize_round(module, roots, policy)
  let module = normalize_round(module, roots, policy)
  let module = normalize_round(module, roots, policy)
  // `StaticResumptions` runs after `Deadcode` and frees stuff, so let us run
  // `Deadcode` one more time
  let module = @core.deadcode(module, roots)
  @core.references_to_parameters(module)
}

///|
/// One round of the optimizer's normalization (upstream `Optimizer.normalize`).
fn normalize_round(
  module : @core.ModuleDecl,
  roots : ArrayView[Sym],
  policy : @core.InliningPolicy,
) -> @core.ModuleDecl raise EffektError {
  let module = @core.bind_subexpressions(module)
  let module = @core.normalize(module, roots, policy)
  let module = @core.deadcode(module, roots)
  let module = @core.static_resumptions(module)
  let module = @core.direct_style(module)
  @core.references_to_parameters(module)
}

///|
/// The core program of `modules`, for `--show-core`.
pub fn show_core(
  modules : ArrayView[@namer.ResolvedModule],
  ctx : Context,
) -> String raise EffektError {
  let (aggregated, _) = middle_end(modules, ctx)
  @core.show_core(aggregated)
}

///|
/// Compiles the already typechecked modules (dependencies first, main module
/// last) into a single JavaScript source file.
pub fn emit(
  modules : ArrayView[@namer.ResolvedModule],
  ctx : Context,
) -> String raise EffektError {
  let (aggregated, main_sym) = middle_end(modules, ctx)

  // 3. CPS conversion and code generation.

  let cps_module = @cps.transform(aggregated)

  let contified = @cps.contify(cps_module)

  let js = @js.compile_cps(contified, aggregated, main_sym)

  // Externs that no body applies to are warnings, exactly as upstream. `2b`
  // has already dropped the unreachable ones, so only externs that the program
  // can actually call are reported (once per distinct message).
  let reported : Array[String] = []
  for (span, message) in @js.take_unsupported_messages() {
    if !reported.any(m => m == message) {
      reported.push(message)
      ctx.warning(span, message)
    }
  }
  js
}

///|
/// All term symbols exported by a module.
fn exports_of(module : @symbols.Module) -> Array[Sym] {
  let out : Array[Sym] = []
  for _name, syms in module.exports.terms {
    for s in syms {
      if !out.contains(s) {
        out.push(s)
      }
    }
  }
  out
}

///|
/// Finds a term by name among the exported terms of a module.
fn find_exported(module : @symbols.Module, name : String) -> Sym? {
  module.exports.terms.get(name).bind(syms => syms.get(0))
}

///|
/// The `main` symbol of the main module.
///
/// A `main` inside a namespace (`namespace app` … `def main() = …`) is the entry
/// point as well: upstream's `ensureMainExists` takes the module's `main`
/// wherever it is declared, and `Typer.check_main` has already rejected modules
/// with several of them. Namespaced definitions are not part of a module's
/// exported bindings (the namer opens a scope for a namespace), so the tree is
/// walked, exactly like `Typer.check_main` does.
fn find_main(modules : ArrayView[@namer.ResolvedModule], ctx : Context) -> Sym? {
  if modules.is_empty() {
    return None
  }
  let module = modules[modules.length() - 1]
  let found : Array[Sym] = []
  collect_mains(ctx, module.tree.defs, found)
  match found {
    [sym] => Some(sym)
    _ =>
      // Fall back to the exported binding: a driver that only resolves names
      // (`resolve`, without `check_main`) still gets its entry point.
      find_exported(module.module, main_name())
  }
}

///|
/// The `main` functions declared at the top level of `defs` or of one of its
/// namespaces, in declaration order (the same walk as `Typer.check_main`).
fn collect_mains(
  ctx : Context,
  defs : ArrayView[@source.Def],
  out : Array[Sym],
) -> Unit {
  for d in defs {
    match d.kind {
      @source.DefKind::FunDef(id, _, _, _, _, _, _) =>
        if id.name == main_name() {
          if ctx.symbol_of(id.uid) is Some(sym) {
            if !out.contains(sym) {
              out.push(sym)
            }
          }
        }
      _ => ()
    }
  }
  for d in defs {
    match d.kind {
      @source.DefKind::NamespaceDef(_, inner) => collect_mains(ctx, inner, out)
      _ => ()
    }
  }
}

///|
/// The prelude's `infixEq` overloads, used to compile literal patterns.
fn find_infix_eqs(modules : ArrayView[@namer.ResolvedModule]) -> Array[Sym] {
  for m in modules {
    if m.module.exports.terms.get("infixEq") is Some(syms) && !syms.is_empty() {
      return syms
    }
  }
  []
}

///|
/// Concatenates core modules (dependencies first) into one, mirroring
/// `Compiler.Aggregate`.
pub fn aggregate(
  cores : ArrayView[@core.ModuleDecl],
  main_path : String,
) -> @core.ModuleDecl {
  let declarations : Array[@core.Declaration] = []
  let externs : Array[@core.Extern] = []
  let definitions : Array[@core.Toplevel] = []
  let exports : Array[Sym] = []
  for c in cores {
    declarations.append(c.declarations)
    externs.append(c.externs)
    definitions.append(c.definitions)
    for e in c.exports {
      if !exports.contains(e) {
        exports.push(e)
      }
    }
  }
  @core.ModuleDecl(main_path, [], declarations, externs, definitions, exports)
}
