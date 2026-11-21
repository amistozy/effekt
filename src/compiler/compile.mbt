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
fn library_roots(opts : Options) -> Array[String] {
  let lib = resolve_path(opts.lib_path)
  // The JavaScript backend's library directory: `import mutable/map` resolves
  // to `<lib>/js/mutable/map.effekt` (upstream `backendIncludes`).
  [lib, join_path(lib, "common"), join_path(lib, "js")]
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
  let input_dir = dirname(resolve_path(input))
  for p in opts.include_paths.map(resolve_path) + [input_dir] {
    if !roots.contains(p) {
      roots.push(p)
    }
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
  let ctx = Context(config)
  let messages : Array[Message] = []
  let result = try {
    let source = match read_file(opts.input) {
      // The name is the path *as given* (upstream `Source(name, contents)`):
      // diagnostics and `sourcePosition` should print `examples/hello.effekt`
      // when that is what the user typed, not an absolute path.
      //
      // A literate program (`.effekt.md`) is the program its code fences
      // contain (upstream `Driver.compileSource` wraps the source in a
      // `MarkdownSource`); the lines stay those of the markdown file.
      Some(c) =>
        if opts.input.has_suffix(".md") {
          Source(opts.input, @util.markdown_program(c))
        } else {
          Source(opts.input, c)
        }
      None => {
        ctx.error(Span::missing(), "Cannot read input file \{opts.input}")
        return { output: None, messages: ctx.messages.copy(), failed: true, }
      }
    }
    let loader = Loader(search_paths(opts.input, opts))
    // The standard library reads as `/libraries/...` in diagnostics, no matter
    // where it is installed (upstream `EffektConfig.includes`).
    let roots = library_roots(opts)
    let shown_roots = ["/libraries", "/libraries/common", "/libraries/js"]
    for i, root in roots {
      loader.set_shown(root, shown_roots[i])
    }
    // The prelude is provided by the library, never by the input's directory.
    loader.set_prelude_roots(roots)
    guard (pipeline.parse)(source, ctx) is Some(parsed) else {
      return { output: None, messages: ctx.messages.copy(), failed: true, }
    }
    let tree = resolve_includes(parsed, source, ctx)
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
        if resolved.get(inc.path) is Some(dep) {
          deps.set(inc.path, dep)
        }
      }
      let r = (pipeline.resolve)(t, ctx, deps)
      let checked = (pipeline.typecheck)(r.tree, ctx)
      resolved.set(path, { ..r, tree: checked, })
    }
    let trees = order.filter_map(path => resolved.get(path))

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
  messages.append(ctx.messages)
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
        Some((file, _)) => resolve_path(file)
        None => path
      }
  }
  // Already part of the order (a diamond, or the same file reached by another
  // include path): nothing to do.
  guard !visited.contains(source) else { return true }
  if stack.search_by(entry => entry.source == source) is Some(on_stack) {
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
  stack : ArrayView[Visit],
  from : Int32,
  via : String,
  ctx : Context,
) -> Unit {
  let root = stack[from]
  let root_tree = loader.tree_of(root.key)
  let root_name = module_name(loader, root.key)
  // `ModuleDecl.path` is the declared module name (`module cyclic_a`).
  let names = stack[from:].map(entry => module_name(loader, entry.key))
  let vias = stack[from:].map(entry => entry.via)
  // The cycle is closed by the include that led back to the root, whose path
  // names the root module.
  vias[0] = via
  let cycle = "\{names.join(" -> ")} -> \{root_name}"
  let span = match root_tree {
    Some(t) => {
      let mut first = Span::missing()
      for inc in t.includes {
        if !inc.span.is_missing() {
          first = inc.span
          break
        }
      }
      first
    }
    None => Span::missing()
  }
  // Upstream's `Source.name` for an imported module is `./<path>.effekt`
  // (`VirtualFileSource`); `moduleOf` strips the `.effekt` again.
  let dependencies = vias.map(v => "./\{v}")
  // The cycle is reported on the loader's view of the root, i.e. under the
  // include path that closed the cycle (`./<path>.effekt`).
  let cycle_span = if span.origin == Missing {
    span
  } else {
    { ..span, source: span.source.renamed("./\{vias[0]}.effekt"), }
  }
  let message = Message::error(
    cycle_span,
    "Cyclic import: \{root_name} depends on itself.",
  ).note("Import cycle: \{cycle}", None)
  // Upstream reports the cycle from its loader, which is part of naming.
  ctx.set_phase("namer")
  ctx.report(message)
  // Each "Cannot compile dependency" is reported at the include that caused it:
  // the first one closes the cycle, in the last module on the stack, and the
  // others are the includes of the modules that follow the root.
  let closing = stack.last().unwrap()
  ctx.error(
    visited_span(include_span_of(loader, closing.key, vias[0]), closing),
    "Cannot compile dependency: \{dependencies[0]}",
  )
  for i in vias.length()>..1 {
    ctx.error(
      visited_span(
        include_span_of(loader, stack[i - 1].key, vias[i]),
        stack[i - 1],
      ),
      "Cannot compile dependency: ./\{vias[i]}",
    )
  }
}

///|
/// A span of a module that was reached through an include is reported under the
/// include path it was reached by (`./<path>.effekt`), like upstream's
/// `VirtualFileSource`; the input module keeps the path it was given on the
/// command line.
fn visited_span(span : Span, visit : Visit) -> Span {
  if visit.via == "" || span.origin == Missing {
    span
  } else {
    { ..span, source: span.source.renamed("./\{visit.via}.effekt"), }
  }
}

///|
/// The declared module name of the module registered under `key` (`ModuleDecl.path`
/// is the declared name, `module cyclic_a`), or the key itself when it has not
/// been loaded.
fn module_name(loader : Loader, key : String) -> String {
  match loader.tree_of(key) {
    Some(t) => t.path
    None => key
  }
}

///|
/// The span of the `include "<path>"` in the module registered under `key`, or
/// a missing span when there is none (it may have been resolved through a
/// search path).
fn include_span_of(loader : Loader, key : String, path : String) -> Span {
  guard loader.tree_of(key) is Some(t) else { return Span::missing() }
  for inc in t.includes {
    if inc.path == path {
      return inc.span
    }
  }
  Span::missing()
}

///|
/// The module path of a file, derived from its name (`foo/bar.effekt` -> `bar`,
/// `foo/effekt.effekt` -> `effekt`).
pub fn module_path_of(file : String) -> String {
  // A literate program is named like the module it defines: `ad.effekt.md` is
  // `ad` (upstream strips `.md` from the source name before it is used as a
  // module path, see `Driver.compileSource`).
  without_suffix(without_suffix(base_name(file), ".md"), ".effekt")
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
pub fn render_messages(messages : ArrayView[Message]) -> String {
  // upstream `messages.sortBy(...)` is a stable sort on the message positions,
  // so the order diagnostics were reported in is kept where they coincide
  let sorted = messages.to_owned()
  sorted.mut_view().stable_sort_by((a, b) => compare_positions(a.span, b.span))
  let lines = sorted.map(m => m.render())
  // `distinct` on the *formatted* messages, which the sort above made adjacent
  lines.dedup()
  if lines.is_empty() {
    ""
  } else {
    "\{lines.join("\n")}\n"
  }
}

///|
/// Orders two spans the way upstream sorts diagnostics: by line, then column,
/// and *not* by file, so that the insertion order of diagnostics in different
/// files is kept when they are on the same line.
fn compare_positions(a : Span, b : Span) -> Int32 {
  let pa = a.position()
  let pb = b.position()
  if pa.line != pb.line {
    pa.line - pb.line
  } else {
    pa.column - pb.column
  }
}

///|
/// The default output path for the given input file.
pub fn default_output(input : String) -> String {
  "\{without_suffix(input, ".effekt")}.js"
}
