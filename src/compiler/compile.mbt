// The compilation driver: wires the phases together and talks to the outside
// world (files in, JavaScript out).
//
// Upstream this is `effekt/Compiler.scala` plus the backend-specific runners.
// The individual phases are supplied as a `Pipeline` so that this file does not
// depend on the internal representation of any particular phase.

///|
/// The phases of the compiler, as functions.
pub(all) struct Pipeline {
  /// Parses a source file into a module declaration. `None` means the input
  /// could not be parsed at all (diagnostics are in the context).
  parse : (Source, Context) -> ModuleDecl? raise EffektError
  /// Name resolution: fills `Context.symbol_of` etc. for every node. The third
  /// argument maps an include path (as written in the source) to the already
  /// resolved module, so that imports can be opened.
  resolve : (ModuleDecl, Context, Map[String, @namer.ResolvedModule]) -> @namer.ResolvedModule raise EffektError
  /// Type checking: fills value/block types, effects, captures and the
  /// capability annotations consumed by `ExplicitCapabilities`. Returns the
  /// (possibly rewritten) tree, which the later phases must use.
  typecheck : (ModuleDecl, Context) -> ModuleDecl raise EffektError
  /// Runs the middle- and back-end on the main module and all its
  /// dependencies (dependencies first), producing JavaScript.
  emit : (Array[@namer.ResolvedModule], Context) -> String raise EffektError
}

///|
/// The outcome of a compilation.
pub(all) struct CompileResult {
  /// `Some` if the driver produced output.
  output : String?
  messages : Array[Message]
  failed : Bool
}

///|
/// The directories the *library* provides: `--lib`, and its `common` and `js`
/// subdirectories, mirroring upstream's JS `EffektConfig.includes()`
/// (`List("common", "js", ".")`, relative to the library path). The implicit
/// prelude is looked up here only.
pub fn library_roots(opts : Options) -> Array[String] {
  let lib = resolve_path(opts.lib_path)
  let roots : Array[String] = [lib]
  roots.push(join_path(lib, "common"))
  // The JavaScript backend's library directory: `import mutable/map` resolves
  // to `<lib>/js/mutable/map.effekt` (upstream `backendIncludes`).
  roots.push(join_path(lib, "js"))
  roots
}

///|
/// The default module search path for a program at `input`.
///
/// The order mirrors upstream's `EffektConfig.includes()`
/// (`libPath :: backendIncludes ++ includePath`): the standard library is
/// searched *first*, then the user's include paths, and only then the
/// directory of the input file (a convenience of this port; upstream would
/// rely on `.`). Searching the input's directory first made a file next to the
/// input shadow a standard library module of the same name — e.g.
/// `examples/exception.effekt` (interface `Exc`) hid
/// `libraries/common/exception.effekt` (interface `Exception`) from
/// `examples/t_import.effekt`.
pub fn search_paths(input : String, opts : Options) -> Array[String] {
  let roots = library_roots(opts)
  for p in opts.include_paths {
    let resolved = resolve_path(p)
    if !roots.any(r => r == resolved) {
      roots.push(resolved)
    }
  }
  let input_dir = dirname(resolve_path(input))
  if !roots.any(r => r == input_dir) {
    roots.push(input_dir)
  }
  roots
}

///|
/// Compiles a single file. Returns `None` when the compilation failed (in which
/// case the diagnostics are in `messages`).
pub fn compile_file(
  opts : Options,
  pipeline : Pipeline,
  config : Config,
) -> CompileResult {
  let ctx = Context::new(config)
  let messages : Array[Message] = []
  let result = try {
    let source = match read_file(opts.input) {
      // The name is the path *as given* (upstream `Source(name, contents)`):
      // diagnostics and `sourcePosition` should print `examples/hello.effekt`
      // when that is what the user typed, not an absolute path.
      Some(c) => Source::new(opts.input, c)
      None => {
        ctx.error(Span::missing(), "Cannot read input file \{opts.input}")
        return { output: None, messages: ctx.messages.copy(), failed: true, }
      }
    }
    let loader = Loader::new(search_paths(opts.input, opts))
    // The prelude is provided by the library, never by the input's directory.
    loader.set_prelude_roots(library_roots(opts))
    let parsed = (pipeline.parse)(source, ctx)
    if parsed is None {
      return { output: None, messages: ctx.messages.copy(), failed: true, }
    }
    let tree = resolve_includes(parsed.unwrap(), source, ctx)
    let main_path = module_path_of(opts.input)
    // The main module is registered under a collision-free key: a program file
    // may be called `exception.effekt` and the prelude module of that name has
    // to remain resolvable (see `main_module_key`).
    let main_key = main_module_key(main_path)
    loader.sources.set(main_key, source)
    loader.trees.set(main_key, {
      ..tree,
      includes: loader.implicit_includes(main_key) + tree.includes,
    })

    // Topologically order the main module and all its dependencies.
    let order : Array[String] = []
    let visited : Array[String] = []
    collect_order(loader, main_key, pipeline, ctx, visited, order)

    // Name resolution and type checking, dependencies first. Each resolved
    // module is remembered so that its importers can open its exports.
    let resolved : Map[String, @namer.ResolvedModule] = Map([])
    for path in order {
      let t = loader.tree_of(path).unwrap()
      let deps : Map[String, @namer.ResolvedModule] = Map([])
      for inc in t.includes {
        match resolved.get(inc.path) {
          Some(dep) => deps.set(inc.path, dep)
          None => ()
        }
      }
      let r = (pipeline.resolve)(t, ctx, deps)
      let checked = (pipeline.typecheck)(r.tree, ctx)
      resolved.set(path, { ..r, tree: checked, })
    }
    let trees : Array[@namer.ResolvedModule] = []
    for path in order {
      match resolved.get(path) {
        Some(r) => trees.push(r)
        None => ()
      }
    }

    if ctx.has_errors() {
      None
    } else {
      Some((pipeline.emit)(trees, ctx))
    }
  } catch {
    EffektError::Fatal(msg) => {
      ctx.error(Span::missing(), msg)
      None
    }
    EffektError::Internal(msg) => {
      ctx.error(Span::missing(), "Internal compiler error: \{msg}")
      None
    }
  }
  for m in ctx.messages {
    messages.push(m)
  }
  let has_errors = messages.any(m => m.severity == Error)
  { output: result, messages, failed: has_errors, }
}

///|
fn collect_order(
  loader : Loader,
  path : String,
  pipeline : Pipeline,
  ctx : Context,
  visited : Array[String],
  order : Array[String],
) -> Unit raise EffektError {
  if visited.any(p => p == path) {
    return
  }
  visited.push(path)
  let tree = loader.load_tree(path, ctx, pipeline.parse)
  for inc in tree.includes {
    collect_order(loader, inc.path, pipeline, ctx, visited, order)
  }
  order.push(path)
}

///|
/// Replaces Windows path separators with `/`.
pub fn normalize_separators(p : String) -> String {
  p.replace_all(old="\\", new="/")
}

///|
/// The module path of a file, derived from its name (`foo/bar.effekt` -> `bar`,
/// `foo/effekt.effekt` -> `effekt`).
pub fn module_path_of(file : String) -> String {
  let normalized = normalize_separators(file)
  let segments = normalized.split("/").map(s => s.to_owned()).collect()
  let last = if segments.length() == 0 {
    normalized
  } else {
    segments[segments.length() - 1]
  }
  if last.has_suffix(".effekt") {
    last[0:last.length() - 7].to_owned()
  } else {
    last
  }
}

///|
/// Renders all diagnostics to a string.
///
/// `info` messages are hints ("Did you mean ...?"), and upstream reports them
/// next to the errors they belong to; they are what the negative corpus tests
/// check for (`[info] path:line:col: ...`), so they are rendered as well.
pub fn render_messages(messages : Array[Message]) -> String {
  let buf = StringBuilder()
  for m in messages {
    buf.write_string(m.render())
    buf.write_string("\n")
  }
  buf.to_string()
}

///|
/// The default output path for the given input file.
pub fn default_output(input : String) -> String {
  if input.has_suffix(".effekt") {
    "\{input[0:input.length() - 7].to_owned()}.js"
  } else {
    "\{input}.js"
  }
}
