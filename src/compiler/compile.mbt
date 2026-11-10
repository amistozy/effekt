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
    // The library's own prelude modules do not import the prelude (upstream
    // `Namer.name` skips it for `preludes.contains(decl.path)`), while a
    // *program* that happens to carry a prelude module's name still gets it.
    let implicit = if loader.is_library_prelude(main_path, opts.input) {
      []
    } else {
      loader.prelude_includes()
    }
    loader.trees.set(main_key, { ..tree, includes: implicit + tree.includes, })

    // Topologically order the main module and all its dependencies.
    let order : Array[String] = []
    let visited : Array[String] = []
    let stack : Array[Visit] = []
    if !collect_order(
        loader, main_key, "", pipeline, ctx, visited, stack, order,
      ) {
      // A cyclic import was reported; the modules cannot be named (each one's
      // include of the next would be "Cannot find module to include").
      return { output: None, messages: ctx.messages.copy(), failed: true, }
    }

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
      // `Context.abort` reports the diagnostic at its span and *then* aborts, so
      // the last message is already the one that ended the phase; the phases
      // that abort without reporting (the parser, the scope lookups) are the
      // ones that still need it here, and for those there is no span to use.
      let reported = match ctx.messages.last() {
        Some(m) => m.text == msg
        None => false
      }
      if !reported {
        ctx.error(Span::missing(), msg)
      }
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
/// One module on the depth-first search stack while the dependency order is
/// collected.
priv struct Visit {
  /// The key the module is registered under in the loader.
  key : String
  /// The include path it was reached by (empty for the input module). Upstream
  /// names the module in "Cannot compile dependency" by this path.
  via : String
  /// The canonical file path: the identity used to detect a cycle. The input
  /// module is registered under a key no include can name, so the key alone
  /// cannot recognize that an import leads back to it.
  source : String
}

///|
/// Collects the transitive dependencies of `path` in dependency-first order.
///
/// Returns `false` after reporting a cyclic import: upstream's `Namer` keeps a
/// stack of the modules it is currently naming and aborts when one of them is
/// imported again, which makes the whole frontend of that module fail. With no
/// frontend to run, the driver reproduces that by stopping here.
fn collect_order(
  loader : Loader,
  path : String,
  via : String,
  pipeline : Pipeline,
  ctx : Context,
  visited : Array[String],
  stack : Array[Visit],
  order : Array[String],
) -> Bool raise EffektError {
  let source = match loader.source_of(path) {
    Some(s) => resolve_path(s.name)
    // A module that has not been loaded yet: resolve its file now, so that its
    // identity does not change between the first and a later visit.
    None =>
      match loader.locate(path) {
        Some(file) => resolve_path(file)
        None => path
      }
  }
  // Already part of the order (a diamond, or the same file reached by another
  // include path): nothing to do.
  if visited.any(p => p == source) {
    return true
  }
  let mut on_stack = -1
  for i = 0; i < stack.length(); i = i + 1 {
    if stack[i].source == source {
      on_stack = i
    }
  }
  if on_stack >= 0 {
    report_cycle(loader, stack, on_stack, via, ctx)
    return false
  }
  stack.push({ key: path, via, source, })
  let tree = loader.load_tree(path, ctx, pipeline.parse)
  for inc in tree.includes {
    if !collect_order(
        loader,
        inc.path,
        inc.path,
        pipeline,
        ctx,
        visited,
        stack,
        order,
      ) {
      return false
    }
  }
  ignore(stack.pop())
  visited.push(source)
  order.push(path)
  true
}

///|
/// Reports a cyclic import the way upstream's `Namer.recursiveProtect` does:
/// the cycle is reported at the first `import` of the module that is imported
/// again, followed by one "Cannot compile dependency" per module of the cycle.
///
/// Upstream's messages are indistinguishable in position because the abort
/// leaves the focus at the re-entered module's `import` (see the comment on
/// `Context.in`), which is what the recorded `.check` file shows.
fn report_cycle(
  loader : Loader,
  stack : Array[Visit],
  from : Int32,
  via : String,
  ctx : Context,
) -> Unit {
  let root = stack[from]
  let root_tree = loader.tree_of(root.key)
  let root_name = match root_tree {
    Some(t) => t.path
    None => root.key
  }
  // `ModuleDecl.path` is the declared module name (`module cyclic_a`).
  let names : Array[String] = []
  let vias : Array[String] = []
  for i = from; i < stack.length(); i = i + 1 {
    match loader.tree_of(stack[i].key) {
      Some(t) => names.push(t.path)
      None => names.push(stack[i].key)
    }
    vias.push(stack[i].via)
  }
  // The cycle is closed by the include that led back to the root, whose path
  // names the root module.
  vias[0] = via
  let cycle = "\{names.join(" -> ")} -> \{root_name}"
  let span = match root_tree {
    Some(t) => {
      let mut first : Span? = None
      for inc in t.includes {
        if first is None && !inc.span.is_missing() {
          first = Some(inc.span)
        }
      }
      match first {
        Some(s) => s
        None => Span::missing()
      }
    }
    None => Span::missing()
  }
  // Upstream's `Source.name` for an imported module is `./<path>.effekt`
  // (`VirtualFileSource`); `moduleOf` strips the `.effekt` again.
  let dependencies : Array[String] = ["./\{vias[0]}"]
  for i = vias.length() - 1; i > 0; i = i - 1 {
    dependencies.push("./\{vias[i]}")
  }
  let message =
    $|Cyclic import: \{root_name} depends on itself, via:
    $|	\{cycle}
  ctx.error(span, message)
  for dependency in dependencies {
    ctx.error(span, "Cannot compile dependency: \{dependency}")
  }
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
/// Renders all diagnostics to a string, sorted by position and with identical
/// messages collapsed — upstream's `formatMessages` does exactly that
/// (`messages.sorted.map(formatMessage).distinct`), and the test corpus
/// records its `.check` files with this rendering.
///
/// `info` messages are hints ("Did you mean ...?"), and upstream reports them
/// next to the errors they belong to; they are what the negative corpus tests
/// check for (`[info] path:line:col ...`), so they are rendered as well.
pub fn render_messages(messages : Array[Message]) -> String {
  let sorted = messages.copy()
  // insertion sort: the lists are short and it keeps the order stable
  for i = 1; i < sorted.length(); i = i + 1 {
    let current = sorted[i]
    let mut j = i - 1
    while j >= 0 && sorted[j].span.compare(current.span) > 0 {
      sorted[j + 1] = sorted[j]
      j = j - 1
    }
    sorted[j + 1] = current
  }
  let buf = StringBuilder()
  let mut previous = ""
  for m in sorted {
    let rendered = m.render()
    if rendered != previous {
      buf.write_string(rendered)
      buf.write_string("\n")
      previous = rendered
    }
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
