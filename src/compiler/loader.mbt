// Loading and ordering modules.
//
// Mirrors `effekt/context/ModuleDB.scala` + the dependency handling in
// `effekt/Namer.scala`. Modules are located by include path in a list of
// search roots; the prelude modules are implicitly available to every module.

///|
/// The prelude, in the order upstream's `Runner.prelude` lists it: dependencies
/// first, so that every module can be resolved in include order.
pub fn prelude_paths() -> Array[String] {
  [
    "effekt", "option", "partial", "stream", "control", "list", "result", "exception",
    "array", "char", "bytearray", "stringbuffer", "string", "ref",
  ]
}

///|
pub fn is_prelude_path(path : String) -> Bool {
  prelude_paths().any(p => p == path)
}

///|
/// The includes every module gets implicitly: the prelude modules the library
/// provides, except for the prelude modules themselves (importing the prelude
/// *into* the prelude would make the dependency graph cyclic — upstream
/// `Namer.name` skips it the same way). They come first, so a module's own
/// imports shadow prelude names.
///
/// Modules the library does not provide are skipped: `examples/minilib` ships a
/// reduced prelude (just `effekt`) on purpose, and the names of the modules it
/// misses simply stay unresolvable.
pub fn Loader::implicit_includes(
  self : Loader,
  path : String,
) -> Array[Include] {
  let out : Array[Include] = []
  if is_prelude_path(path) {
    return out
  }
  for p in prelude_paths() {
    match locate_in(self.prelude_roots, p) {
      Some(_) => out.push({ path: p, span: Span::missing(), })
      None => ()
    }
  }
  out
}

///|
/// The key under which the driver registers the main module in a `Loader`.
///
/// Programs may be named like a prelude module (`examples/exception.effekt`,
/// `examples/char.effekt`); registering the main tree under its plain module
/// path would make it shadow the prelude module of the same name, so the main
/// module gets a key that no include path can have (upstream does not add the
/// main module to the module database at all).
pub fn main_module_key(path : String) -> String {
  "main:\{path}"
}

///|
/// A module that has been located on disk.
pub(all) struct LoadedModule {
  path : String
  source : Source
  tree : ModuleDecl
}

///|
pub struct Loader {
  /// Directories searched for `<module-path>.effekt`.
  roots : Array[String]
  /// Directories the implicit prelude is searched in. This is the library only,
  /// not the input's directory: a program file that happens to be called
  /// `exception.effekt` must not shadow the prelude module of that name.
  mut prelude_roots : Array[String]
  sources : Map[String, Source]
  trees : Map[String, ModuleDecl]
  modules : Map[String, @symbols.Module]
}

///|
pub fn Loader::new(roots : Array[String]) -> Loader {
  {
    roots,
    prelude_roots: roots.copy(),
    sources: Map([]),
    trees: Map([]),
    modules: Map([]),
  }
}

///|
/// Restricts the directories the implicit prelude is searched in.
pub fn Loader::set_prelude_roots(self : Loader, roots : Array[String]) -> Unit {
  self.prelude_roots = roots
}

///|
fn locate_in(roots : Array[String], path : String) -> String? {
  for root in roots {
    let candidate = join_path(root, "\{path}.effekt")
    if file_exists(candidate) {
      return Some(candidate)
    }
  }
  None
}

///|
/// Locates the file for a module path, e.g. `list` -> `<root>/list.effekt`.
///
/// Prelude modules are only searched in the library (see `prelude_roots`);
/// everything else is searched in all roots, the input's directory last.
pub fn Loader::locate(self : Loader, path : String) -> String? {
  if is_prelude_path(path) {
    locate_in(self.prelude_roots, path)
  } else {
    locate_in(self.roots, path)
  }
}

///|
/// Locates an `extern include` target, which is a path relative to the file
/// that contains the include.
pub fn Loader::locate_relative(
  self : Loader,
  importer_source : Source,
  relative : String,
) -> String? {
  let _ = self
  let base = dirname(importer_source.name)
  let candidate = join_path(base, relative)
  if file_exists(candidate) {
    Some(candidate)
  } else {
    None
  }
}

///|
/// Reads and parses the module at `path`, caching the result.
pub fn Loader::load_tree(
  self : Loader,
  path : String,
  ctx : Context,
  parse : (Source, Context) -> ModuleDecl? raise EffektError,
) -> ModuleDecl raise EffektError {
  match self.trees.get(path) {
    Some(t) => t
    None => {
      let located = self.locate(path)
      if located is None {
        ctx.abort(
          Span::missing(),
          "Could not find module '\{path}' in include path.",
        )
      }
      let file = located.unwrap()
      let source = Source::new(
        file,
        match read_file(file) {
          Some(c) => c
          None => ""
        },
      )
      let parsed = parse(source, ctx)
      if parsed is None {
        ctx.abort(Span::missing(), "Could not parse module '\{path}'.")
      }
      let tree = resolve_includes(parsed.unwrap(), source, ctx)
      // Every module implicitly imports the whole prelude; the prelude modules
      // themselves do not (see `implicit_includes`).
      let tree = {
        ..tree,
        includes: self.implicit_includes(path) + tree.includes,
      }
      self.sources.set(path, source)
      self.trees.set(path, tree)
      tree
    }
  }
}

///|
/// The include paths named by a module, in order.
pub fn includes_of(tree : ModuleDecl) -> Array[Include] {
  tree.includes
}

///|
/// Computes the transitive dependency closure of `path` in topological order
/// (dependencies first). The prelude is not included here.
pub fn Loader::closure(
  self : Loader,
  path : String,
  ctx : Context,
  parse : (Source, Context) -> ModuleDecl? raise EffektError,
) -> Array[String] raise EffektError {
  let order : Array[String] = []
  let visited : Array[String] = []
  self.visit(path, ctx, parse, visited, order)
  order
}

///|
fn Loader::visit(
  self : Loader,
  path : String,
  ctx : Context,
  parse : (Source, Context) -> ModuleDecl? raise EffektError,
  visited : Array[String],
  order : Array[String],
) -> Unit raise EffektError {
  if visited.any(p => p == path) {
    return
  }
  visited.push(path)
  let tree = self.load_tree(path, ctx, parse)
  for inc in tree.includes {
    self.visit(inc.path, ctx, parse, visited, order)
  }
  order.push(path)
}

///|
pub fn Loader::source_of(self : Loader, path : String) -> Source? {
  self.sources.get(path)
}

///|
pub fn Loader::tree_of(self : Loader, path : String) -> ModuleDecl? {
  self.trees.get(path)
}
