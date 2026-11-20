// Loading and ordering modules.
//
// Mirrors `effekt/context/ModuleDB.scala` + the dependency handling in
// `effekt/Namer.scala`. Modules are located by include path in a list of
// search roots; the prelude modules are implicitly available to every module.

///|
/// The prelude, in the order upstream's `Runner.prelude` lists it: dependencies
/// first, so that every module can be resolved in include order.
fn prelude_paths() -> Array[String] {
  [
    "effekt", "option", "partial", "stream", "control", "list", "result", "exception",
    "array", "char", "bytearray", "stringbuffer", "string", "ref",
  ]
}

///|
fn is_prelude_path(path : String) -> Bool {
  prelude_paths().contains(path)
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
fn Loader::implicit_includes(self : Loader, path : String) -> Array[Include] {
  if is_prelude_path(path) {
    return []
  }
  self.prelude_includes()
}

///|
/// The implicit includes themselves, regardless of the importing module.
fn Loader::prelude_includes(self : Loader) -> Array[Include] {
  prelude_paths()
  .filter(p => locate_in(self.prelude_roots, p) is Some(_))
  .map(p => { path: p, span: Span::missing(), })
}

///|
/// Is the input file the library's own prelude module `path`?
///
/// Upstream decides with `preludes.contains(decl.path)` alone, which would also
/// take a *program* that declares `module exception` for the prelude module.
/// Comparing the located file keeps this port's convenience that
/// `examples/exception.effekt` still sees the prelude.
fn Loader::is_library_prelude(
  self : Loader,
  path : String,
  input : String,
) -> Bool {
  guard is_prelude_path(path) else { return false }
  match self.locate(path) {
    Some((file, _)) => resolve_path(file) == resolve_path(input)
    None => false
  }
}

///|
/// The key under which the driver registers the main module in a `Loader`.
///
/// Programs may be named like a prelude module (`examples/exception.effekt`,
/// `examples/char.effekt`); registering the main tree under its plain module
/// path would make it shadow the prelude module of the same name, so the main
/// module gets a key that no include path can have (upstream does not add the
/// main module to the module database at all).
fn main_module_key(path : String) -> String {
  "main:\{path}"
}

///|
pub struct Loader {
  /// Directories searched for `<module-path>.effekt`.
  roots : Array[String]
  /// Directories the implicit prelude is searched in. This is the library only,
  /// not the input's directory: a program file that happens to be called
  /// `exception.effekt` must not shadow the prelude module of that name.
  mut prelude_roots : Array[String]
  /// How a root is named by the diagnostics: the standard library reads as
  /// /libraries/... no matter where it lives on disk (upstream
  /// IncludeRoot.shown). A root without an entry shows the path it was found
  /// at.
  shown : Map[String, String]
  sources : Map[String, Source]
  trees : Map[String, ModuleDecl]
}

///|
pub fn Loader::Loader(roots : Array[String]) -> Loader {
  {
    roots,
    prelude_roots: roots.copy(),
    shown: Map([]),
    sources: Map([]),
    trees: Map([]),
  }
}

///|
/// The name diagnostics print for a module found under `root` (upstream
/// IncludeRoot.shown): the root's shown prefix plus the module's path.
fn Loader::set_shown(self : Loader, root : String, shown : String) -> Unit {
  self.shown.set(root, shown)
}

///|
/// Restricts the directories the implicit prelude is searched in.
fn Loader::set_prelude_roots(self : Loader, roots : Array[String]) -> Unit {
  self.prelude_roots = roots
}

///|
/// The file a module path names, searched in each root in turn: `<path>.effekt`
/// first, then the literate `<path>.effekt.md` (upstream `IOModuleDB.findSource`
/// does the same per root).
fn locate_in(roots : ArrayView[String], path : String) -> (String, String)? {
  for root in roots {
    let candidate = join_path(root, "\{path}.effekt")
    if file_exists(candidate) {
      return Some((candidate, root))
    }
    let literate = join_path(root, "\{path}.effekt.md")
    if file_exists(literate) {
      return Some((literate, root))
    }
  }
  None
}

///|
/// Locates the file for a module path, e.g. `list` -> `<root>/list.effekt`.
///
/// Prelude modules are only searched in the library (see `prelude_roots`);
/// everything else is searched in all roots, the input's directory last.
fn Loader::locate(self : Loader, path : String) -> (String, String)? {
  if is_prelude_path(path) {
    locate_in(self.prelude_roots, path)
  } else {
    locate_in(self.roots, path)
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
      let (file, root) = located.unwrap()
      let raw = read_file(file).unwrap_or("")
      // A literate module (`.effekt.md`) is the program its code fences
      // contain, at the lines of the markdown file (upstream `MarkdownSource`).
      let literate = file.has_suffix(".md")
      let content = if literate { @util.markdown_program(raw) } else { raw }
      let extension = if literate { ".effekt.md" } else { ".effekt" }
      // A file the standard library provides is named the way upstream mounts
      // it (/libraries/common/list.effekt), so that a diagnostic about a
      // library declaration does not depend on where the library is installed.
      let source = match self.shown.get(root) {
        Some(prefix) =>
          Source::included(file, content, "\{prefix}/\{path}\{extension}")
        None => Source(file, content)
      }
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
fn Loader::source_of(self : Loader, path : String) -> Source? {
  self.sources.get(path)
}

///|
fn Loader::tree_of(self : Loader, path : String) -> ModuleDecl? {
  self.trees.get(path)
}
