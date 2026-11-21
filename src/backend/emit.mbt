// The JavaScript backend: source modules -> core -> CPS -> JavaScript.
//
// Mirrors `effekt/generator/js/JavaScript.scala`'s `Compile` pipeline:
//
//     Frontend andThen Middleend                      (source -> core)
//     Aggregate                                       (concatenate modules)
//     Deadcode                                        (drop unreachable code)
//     core.Mono                                       (monomorphize)
//     core.Show                                       (structural show instances)
//     Optimizer                                       (minus the passes not ported)
//     DropBindings                                    (drop unique value bindings)
//     cps.Transformer.transform                       (core -> cps)
//     cps.Contify.rewrite                             (cps -> cps)
//     TransformerCps.compile(...).commonjs            (cps -> js)
//
// `Optimizer` honors the `--optimize`/`--no-optimize` toggle: upstream's
// `Optimizer.optimize` always eliminates dead code and returns early when
// `Context.config.optimize()` is false. That is what its `withoutOptimizations`
// test list relies on — those programs have to print the same thing either way.

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
///
/// `enabled` is the `--optimize`/`--no-optimize` toggle (upstream's
/// `Context.config.optimize()`): it only affects the optimizer, the rest of the
/// middle-end runs either way.
fn middle_end(
  modules : ArrayView[@namer.ResolvedModule],
  ctx : Context,
  enabled : Bool,
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
  let main_module = modules.last().unwrap()
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
  // 2c. Monomorphize: upstream runs `core.Mono` right here, before `core.Show`,
  //     because the structural `show` instances it generates only make sense
  //     once the data declarations have concrete field types.
  let aggregated = @core.mono_phase(aggregated)
  // 2d. Replace the prelude's `show` extern by compiler-generated structural
  //     show definitions. Upstream runs `core.Show` before its optimizer, so the
  //     instances it generates are optimized (and dead-coded) along with
  //     everything else.
  let aggregated = @core.show_phase(aggregated)
  // 2e. Arity raising: type-directed unboxing of records (upstream
  //     `core.ArityRaising`, which runs after `core.Show` and before the
  //     optimizer). Upstream runs it only when the optimizer is enabled.
  let aggregated = if enabled {
    @core.arity_raising(aggregated)
  } else {
    aggregated
  }
  // 2f. The optimizer: upstream's `Optimizer.optimize`, minus the phases that
  //     are not ported (`LambdaSets`).
  let aggregated = optimize(aggregated, main_sym, enabled)
  // 2g. Drop (inline) the unique value bindings. Upstream runs `DropBindings`
  //     after the optimizer and unconditionally — unlike `Optimizer.optimize`,
  //     it does not consult `config.optimize()` — so `--no-optimize` drops
  //     bindings as well.
  let aggregated = @core.drop_bindings(aggregated, [main_sym])
  (aggregated, main_sym)
}

///|
/// `Optimizer.optimize`: dead code elimination, then — unless the optimizer is
/// turned off — the static argument transformation, three rounds of
/// normalization (each of which ends in the passes that consume the normal form),
/// and two final cleanups.
///
/// Upstream normalizes three times "since tail resumptions might only surface
/// after normalization and leave dead `Reset`s"; the rounds run the same phases on
/// a shrinking tree.
///
/// Every round ends in `ReferencesToParameters`, and so do the final cleanups:
/// the pass threads the state of a reference through a definition's parameters,
/// which needs the per-arity `RETURN_n` that `js/transform_cps.mbt` emits.
///
/// `enabled` mirrors upstream's early return in `Optimizer.optimize`: dead code
/// elimination happens unconditionally (it is what makes the following phases
/// cheap), and `--no-optimize` skips everything after it.
fn optimize(
  module : @core.ModuleDecl,
  main_sym : Sym,
  enabled : Bool,
) -> @core.ModuleDecl raise EffektError {
  let roots = [main_sym]
  // (1) first thing we do is simply remove unused definitions (this speeds up
  //     all following analyses and rewrites)
  let module = @core.deadcode(module, roots)
  if !enabled {
    return module
  }
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
/// The core program of `modules`, for `--show-core`. `enabled` is the
/// `--optimize`/`--no-optimize` toggle, so that the dump shows what the code
/// generator would consume.
pub fn show_core(
  modules : ArrayView[@namer.ResolvedModule],
  ctx : Context,
  enabled : Bool,
) -> String raise EffektError {
  let (aggregated, _) = middle_end(modules, ctx, enabled)
  @core.show_core(aggregated)
}

///|
/// Compiles the already typechecked modules (dependencies first, main module
/// last) into a single JavaScript source file.
pub fn emit(
  modules : ArrayView[@namer.ResolvedModule],
  ctx : Context,
  enabled : Bool,
) -> String raise EffektError {
  let (aggregated, main_sym) = middle_end(modules, ctx, enabled)

  // 3. CPS conversion and code generation.

  let cps_module = @cps.transform(aggregated)

  let contified = @cps.contify(cps_module)

  let js = @js.compile_cps(contified, aggregated, main_sym)

  // Externs that no body applies to are warnings, exactly as upstream. `2b`
  // has already dropped the unreachable ones, so only externs that the program
  // can actually call are reported (once per distinct message).
  let reported : Array[String] = []
  for (span, message) in @js.take_unsupported_messages() {
    if !reported.contains(message) {
      reported.push(message)
      ctx.warning(span, message)
    }
  }
  js
}

///|
/// All term symbols exported by a module.
fn exports_of(module : @symbols.Module) -> Array[Sym] {
  @symbols.dedup_syms(module.exports.terms.values().to_array().flatten())
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
  let module = modules.last().unwrap()
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
        if id.name == main_name() &&
          ctx.symbol_of(id.uid) is Some(sym) &&
          !out.contains(sym) {
          out.push(sym)
        }
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
fn aggregate(
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
    exports.append(c.exports)
  }
  @core.ModuleDecl(
    main_path,
    [],
    declarations,
    externs,
    definitions,
    @symbols.dedup_syms(exports),
  )
}
