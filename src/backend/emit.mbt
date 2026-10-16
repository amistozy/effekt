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
pub fn main_name() -> String {
  "main"
}

///|
/// Compiles the already typechecked modules (dependencies first, main module
/// last) into a single JavaScript source file.
pub fn emit(
  modules : Array[@namer.ResolvedModule],
  ctx : Context,
) -> String raise EffektError {
  if modules.length() == 0 {
    ctx.abort(Span::missing(), "No module to compile.")
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
  let main_sym = find_main(modules)
  if main_sym is None {
    ctx.abort(
      Span::missing(),
      "Cannot find the entry point 'main' in module \{main_module.module.path}.",
    )
  }
  let main_sym = main_sym.unwrap()
  let required = @symbols.dedup_syms(
    [main_sym] + @core.required_names(aggregated),
  )
  let aggregated = @core.deadcode(aggregated, required)
  // 2c. Replace the prelude's `show` extern by compiler-generated structural
  //     show definitions.
  let aggregated = @core.show_phase(aggregated)

  // 3. Bind the `infixEq` used by the pattern matching compiler to the one
  //    from the prelude.
  match find_infix_eq(modules) {
    Some(sym) => @core.set_pattern_equality_function(sym)
    None => ()
  }

  // 4. CPS conversion and code generation.
  let cps_module = @cps.transform(aggregated)
  let contified = @cps.contify(cps_module)
  let js = @js.compile_cps(contified, aggregated, main_sym)
  // Externs that no body applies to are warnings, exactly as upstream. `2b`
  // has already dropped the unreachable ones, so only externs that the program
  // can actually call are reported (once per distinct message).
  let reported : Array[String] = []
  for message in @js.take_unsupported_messages() {
    if !reported.any(m => m == message) {
      reported.push(message)
      ctx.warning(Span::missing(), message)
    }
  }
  js
}

///|
/// All term symbols exported by a module.
pub fn exports_of(module : @symbols.Module) -> Array[Sym] {
  let out : Array[Sym] = []
  for _name, syms in module.exports.terms {
    for s in syms {
      if !sym_in(s, out) {
        out.push(s)
      }
    }
  }
  out
}

///|
/// Finds a term by name among the exported terms of a module.
pub fn find_exported(module : @symbols.Module, name : String) -> Sym? {
  match module.exports.terms.get(name) {
    Some(syms) => if syms.length() == 0 { None } else { Some(syms[0]) }
    None => None
  }
}

///|
/// The `main` symbol of the main module.
pub fn find_main(modules : Array[@namer.ResolvedModule]) -> Sym? {
  if modules.length() == 0 {
    return None
  }
  find_exported(modules[modules.length() - 1].module, main_name())
}

///|
/// The prelude's `infixEq`, used to compile literal patterns.
pub fn find_infix_eq(modules : Array[@namer.ResolvedModule]) -> Sym? {
  for m in modules {
    match find_exported(m.module, "infixEq") {
      Some(s) => return Some(s)
      None => ()
    }
  }
  None
}

///|
/// Concatenates core modules (dependencies first) into one, mirroring
/// `Compiler.Aggregate`.
pub fn aggregate(
  cores : Array[@core.ModuleDecl],
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
      if !sym_in(e, exports) {
        exports.push(e)
      }
    }
  }
  @core.ModuleDecl::new(
    main_path,
    [],
    declarations,
    externs,
    definitions,
    exports,
  )
}
