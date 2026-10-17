// Loading and ordering modules.
//
// Mirrors `effekt/context/ModuleDB.scala` + the dependency handling in
// `effekt/Namer.scala`. Modules are located by include path in a list of
// search roots; the prelude module `effekt` is implicitly available to every
// module.

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
  sources : Map[String, Source]
  trees : Map[String, ModuleDecl]
  modules : Map[String, @symbols.Module]
}

///|
pub fn Loader::new(roots : Array[String]) -> Loader {
  { roots, sources: Map([]), trees: Map([]), modules: Map([]), }
}

///|
/// Locates the file for a module path, e.g. `list` -> `<root>/list.effekt`.
pub fn Loader::locate(self : Loader, path : String) -> String? {
  for root in self.roots {
    let candidate = join_path(root, "\{path}.effekt")
    if file_exists(candidate) {
      return Some(candidate)
    }
  }
  None
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
      // Every module implicitly imports the prelude (`effekt`); the prelude
      // itself does not.
      let tree = if path == "effekt" {
        tree
      } else {
        {
          ..tree,
          includes: [
            { path: "effekt", span: Span::missing(), },
            ..tree.includes,
          ],
        }
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
