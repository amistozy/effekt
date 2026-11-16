// Modules: a compilation unit together with its exported bindings.
//
// Mirrors `effekt/symbols/symbols.scala` (case class Module).

///|
pub(all) struct Module {
  uid : Int32
  /// The include path of the module, e.g. `examples/hello`.
  path : String
  name : Name
  mut includes : Array[Module]
  mut exports : Bindings
  /// The source file this module was loaded from.
  source : Span
}

///|
pub fn Module::Module(path : String, source : Span) -> Module {
  let segments : Array[String] = path
    .split("/")
    .map(s => s.to_owned())
    .collect()
  let prefix : Array[String] = if segments.length() <= 1 {
    []
  } else {
    segments[0:segments.length() - 1].to_owned()
  }
  let local = if segments.is_empty() {
    path
  } else {
    segments[segments.length() - 1]
  }
  {
    uid: fresh_uid(),
    path,
    name: Name::qualified(prefix, local),
    includes: [],
    exports: Bindings::empty(),
    source,
  }
}

///|
/// A topological ordering of all transitive dependencies: the order in which
/// modules need to be compiled.
pub fn Module::dependencies(self : Module) -> Array[Module] {
  let out : Array[Module] = []
  for inc in self.includes {
    for dep in inc.dependencies() {
      if !out.any(m => m.uid == dep.uid) {
        out.push(dep)
      }
    }
    if !out.any(m => m.uid == inc.uid) {
      out.push(inc)
    }
  }
  out
}

///|
pub impl Show for Module with fn output(self, logger) {
  logger.write_string(self.path)
}
