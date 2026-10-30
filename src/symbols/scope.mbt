// Bindings and scopes.
//
// Mirrors `effekt/symbols/Scope.scala`. Where upstream uses immutable maps and
// rebuilds scopes on every binding, we rely on the fact that MoonBit `Map`s are
// mutable objects: entering a scope allocates a *fresh* `Bindings`, so mutating
// the current one in place is safe, and nested namespaces are shared by
// reference and therefore stay up to date.

///|
/// A container of bindings for one scope.
pub(all) struct Bindings {
  terms : Map[String, Array[Sym]]
  types : Map[String, Sym]
  captures : Map[String, Sym]
  namespaces : Map[String, Bindings]
}

///|
pub fn Bindings::empty() -> Bindings {
  { terms: Map([]), types: Map([]), captures: Map([]), namespaces: Map([]), }
}

///|
/// Copies the *bindings maps* of `self` but shares the namespace objects.
pub fn Bindings::fork(self : Bindings) -> Bindings {
  {
    terms: self.terms.copy(),
    types: self.types.copy(),
    captures: self.captures.copy(),
    namespaces: self.namespaces.copy(),
  }
}

///|
pub fn Bindings::import_all(self : Bindings, other : Bindings) -> Unit {
  for name, syms in other.terms {
    let existing = self.terms.get(name).unwrap_or([])
    let combined = existing.copy()
    for sym in syms {
      if !combined.contains(sym) {
        combined.push(sym)
      }
    }
    self.terms.set(name, combined)
  }
  for name, tpe in other.types {
    self.types.set(name, tpe)
  }
  for name, capt in other.captures {
    self.captures.set(name, capt)
  }
  for name, other_ns in other.namespaces {
    let child = self.namespace(name)
    child.import_all(other_ns)
  }
}

///|
/// Binds `sym` under `name`. A scope holds a *set* of symbols per name (upstream
/// `Bindings.terms` is a `Set`), so binding the same symbol twice is a no-op:
/// opening one module through two import paths must not make its terms look
/// ambiguous.
pub fn Bindings::add_term(self : Bindings, name : String, sym : Sym) -> Unit {
  let existing = self.terms.get(name).unwrap_or([]).copy()
  if !existing.contains(sym) {
    existing.push(sym)
  }
  self.terms.set(name, existing)
}

///|
pub fn Bindings::set_type(self : Bindings, name : String, sym : Sym) -> Unit {
  self.types.set(name, sym)
}

///|
pub fn Bindings::set_capture(
  self : Bindings,
  name : String,
  capt : Sym,
) -> Unit {
  self.captures.set(name, capt)
}

///|
/// Returns (creating if necessary) the child bindings for `name`.
pub fn Bindings::namespace(self : Bindings, name : String) -> Bindings {
  match self.namespaces.get(name) {
    Some(child) => child
    None => {
      let child = Bindings::empty()
      self.namespaces.set(name, child)
      child
    }
  }
}

///|
pub fn Bindings::get_namespace(self : Bindings, name : String) -> Bindings? {
  self.namespaces.get(name)
}

///|
/// A chain of lexical scopes. The `Bindings` attached to a scope are mutable
/// and owned by that scope.
pub(all) enum Scope {
  /// The toplevel global scope ("project scope").
  Global(Bindings)
  /// A scope introducing a new namespace.
  Named(String, Bindings, Scope)
  /// A local scope introduced by functions, blocks, etc.
  Local(String?, Bindings, Scope)
}

///|
pub fn Scope::bindings(self : Scope) -> Bindings {
  match self {
    Global(b) => b
    Named(_, b, _) => b
    Local(_, b, _) => b
  }
}

///|
/// The mutable scoping state used by the namer.
pub(all) struct Scoping {
  module_path : Array[String]
  mut scope : Scope
}

///|
pub fn toplevel(module_path : Array[String], prelude : Bindings) -> Scoping {
  let global = Bindings::empty()
  global.import_all(prelude)
  { module_path, scope: Global(global), }
}

///|
pub fn Scoping::import_all(self : Scoping, imports : Bindings) -> Unit {
  self.scope.bindings().import_all(imports)
}

///|
pub fn Scoping::import_as(
  self : Scoping,
  bindings : Bindings,
  path : Array[String],
) -> Unit {
  let mut ns = self.scope.bindings()
  for seg in path {
    ns = ns.namespace(seg)
  }
  ns.import_all(bindings)
}

// Searching
// ---------

///|
fn[T] qualified_first(
  path : Array[String],
  bindings : Bindings,
  select : (Bindings) -> T? raise EffektError,
) -> T? raise EffektError {
  if path.length() == 0 {
    select(bindings)
  } else {
    match bindings.namespaces.get(path[0]) {
      None => None
      Some(ns) => qualified_first(path[1:].to_owned(), ns, select)
    }
  }
}

///|
fn[T] first(
  path : Array[String],
  scope : Scope,
  select : (Bindings) -> T? raise EffektError,
) -> T? raise EffektError {
  match scope {
    Global(bindings) => qualified_first(path, bindings, select)
    Named(_, bindings, outer) =>
      or_else(qualified_first(path, bindings, select), () => {
        first(path, outer, select)
      })
    Local(_, bindings, outer) =>
      or_else(qualified_first(path, bindings, select), () => {
        first(path, outer, select)
      })
  }
}

///|
fn[T] qualified_all(
  path : Array[String],
  bindings : Bindings,
  select : (Bindings) -> T,
) -> Array[T] {
  if path.length() == 0 {
    [select(bindings)]
  } else {
    match bindings.namespaces.get(path[0]) {
      None => []
      Some(ns) => qualified_all(path[1:].to_owned(), ns, select)
    }
  }
}

///|
fn[T] all(
  path : Array[String],
  scope : Scope,
  select : (Bindings) -> T,
) -> Array[T] {
  match scope {
    Global(bindings) => qualified_all(path, bindings, select)
    Named(_, bindings, outer) =>
      qualified_all(path, bindings, select) + all(path, outer, select)
    Local(_, bindings, outer) =>
      qualified_all(path, bindings, select) + all(path, outer, select)
  }
}

///|
/// Searches the nested scopes for the first term with the given name.
pub fn Scoping::lookup_first_term_option(
  self : Scoping,
  path : Array[String],
  name : String,
) -> Sym? raise EffektError {
  first(path, self.scope, b => {
    match b.terms.get(name) {
      None => None
      Some(syms) =>
        if syms.length() > 1 {
          raise EffektError::Fatal("Ambiguous reference to \{name}")
        } else if syms.length() == 0 {
          None
        } else {
          Some(syms[0])
        }
    }
  })
}

///|
pub fn Scoping::lookup_type_option(
  self : Scoping,
  path : Array[String],
  name : String,
) -> Sym? raise EffektError {
  first(path, self.scope, b => b.types.get(name))
}

///|
pub fn Scoping::lookup_capture(
  self : Scoping,
  path : Array[String],
  name : String,
) -> Sym? raise EffektError {
  first(path, self.scope, b => b.captures.get(name))
}

///|
pub fn Scoping::lookup_overloaded(
  self : Scoping,
  path : Array[String],
  name : String,
  filter : (Sym) -> Bool,
) -> Array[Array[Sym]] {
  all(path, self.scope, b => b.terms.get(name).unwrap_or([]).filter(filter))
}

///|
pub fn Scoping::lookup_overloaded_method(
  self : Scoping,
  path : Array[String],
  name : String,
) -> Array[Array[Sym]] {
  all(path, self.scope, b => {
    b.terms.get(name).unwrap_or([]).filter(s => s.is_operation())
  }).filter(ns => ns.length() > 0)
}

///|
/// Looks a term up in a scope chain. The type checker needs this for
/// name-based implicit arguments: the name only becomes known once the
/// callee's parameter list is, which is after the namer has run.
pub fn Scope::lookup_term_option(
  self : Scope,
  path : Array[String],
  name : String,
) -> Sym? raise EffektError {
  first(path, self, b => {
    match b.terms.get(name) {
      None => None
      Some(syms) =>
        if syms.length() > 1 {
          raise EffektError::Fatal("Ambiguous reference to \{name}")
        } else if syms.length() == 0 {
          None
        } else {
          Some(syms[0])
        }
    }
  })
}

///|
/// All scopes that bind `name` to a callable (non-operation) symbol,
/// innermost first. Used to eta-expand an implicit block argument.
pub fn Scope::lookup_functions(
  self : Scope,
  name : String,
) -> Array[Array[Sym]] {
  all([], self, b => {
    b.terms
    .get(name)
    .unwrap_or([])
    .filter(s => s.is_callable() && !s.is_operation())
  }).filter(ns => ns.length() > 0)
}

///|
/// Looks `name` up in the scope chain, then in the module's imports.
///
/// An implicit argument is resolved like an ordinary reference, and those see
/// the names opened from other modules (upstream's `Scoping` keeps the imports
/// of a scope and searches both). The imports are not part of a `Scope`, so the
/// caller passes them along.
pub fn lookup_term_in_scope(
  scope : Scope,
  imports : Bindings,
  name : String,
) -> Sym? raise EffektError {
  match scope.lookup_term_option([], name) {
    Some(sym) => Some(sym)
    None =>
      match imports.terms.get(name) {
        None => None
        Some(syms) =>
          if syms.length() > 1 {
            raise EffektError::Fatal("Ambiguous reference to \{name}")
          } else if syms.length() == 0 {
            None
          } else {
            Some(syms[0])
          }
      }
  }
}

///|
/// The names of all types bound in the scope chain and in the imports, for a
/// "Did you mean ...?" suggestion (upstream `Scope.all(path, scope)` over
/// `bindings.types`).
pub fn available_type_names(scope : Scope, imports : Bindings) -> Array[String] {
  let out : Array[String] = []
  collect_type_names(scope, out)
  add_type_names(imports, out)
  out
}

///|
fn collect_type_names(scope : Scope, out : Array[String]) -> Unit {
  match scope {
    Global(b) => add_type_names(b, out)
    Named(_, b, outer) => {
      add_type_names(b, out)
      collect_type_names(outer, out)
    }
    Local(_, b, outer) => {
      add_type_names(b, out)
      collect_type_names(outer, out)
    }
  }
}

///|
fn add_type_names(b : Bindings, out : Array[String]) -> Unit {
  for name, _ in b.types {
    if !out.contains(name) {
      out.push(name)
    }
  }
}

///|
/// All groups of callables bound to `name`, scope chain first, imports last.
pub fn lookup_functions_in_scope(
  scope : Scope,
  imports : Bindings,
  name : String,
) -> Array[Array[Sym]] {
  let groups = scope.lookup_functions(name)
  let imported = imports.terms
    .get(name)
    .unwrap_or([])
    .filter(s => s.is_callable() && !s.is_operation())
  if imported.length() > 0 {
    groups + [imported]
  } else {
    groups
  }
}

///|
pub fn Scoping::lookup_operation(
  self : Scoping,
  path : Array[String],
  name : String,
) -> Array[Array[Sym]] {
  all(path, self.scope, b => {
    b.terms.get(name).unwrap_or([]).filter(s => s.is_operation())
  }).filter(ns => ns.length() > 0)
}

///|
pub fn Scoping::lookup_function(
  self : Scoping,
  path : Array[String],
  name : String,
) -> Array[Array[Sym]] {
  all(path, self.scope, b => {
    b.terms
    .get(name)
    .unwrap_or([])
    .filter(s => s.is_callable() && !s.is_operation())
  }).filter(ns => ns.length() > 0)
}

///|
pub fn Scoping::lookup_first_block_param(
  self : Scoping,
  path : Array[String],
  name : String,
) -> Array[Sym] raise EffektError {
  first(path, self.scope, b => {
    match b.terms.get(name) {
      // The name is not bound in this scope: keep looking in the outer ones
      // (upstream `lookupFirstBlockParam` only stops at the innermost scope
      // that *binds* the name, which is what makes a block parameter of an
      // enclosing definition visible inside a nested block literal).
      None => None
      Some(syms) =>
        Some(
          syms.filter(s => {
            match s {
              BlockParam(_) => true
              _ => false
            }
          }),
        )
    }
  }).unwrap_or([])
}

///|
/// Looks up either a term or a type symbol, disambiguating the two.
pub fn Scoping::lookup_first_option(
  self : Scoping,
  path : Array[String],
  name : String,
) -> Sym? raise EffektError {
  first(path, self.scope, b => {
    let terms = b.terms.get(name)
    let tpe = b.types.get(name)
    match (terms, tpe) {
      (Some(ts), None) =>
        if ts.length() == 1 {
          Some(ts[0])
        } else {
          raise EffektError::Fatal("Ambiguous reference to \{name}")
        }
      (None, Some(t)) => Some(t)
      (Some(ts), Some(t)) =>
        if ts.length() == 1 && ts[0].is_operation() {
          match t {
            Interface(_) => Some(t)
            _ => raise EffektError::Fatal("Ambiguous reference to \{name}")
          }
        } else {
          raise EffektError::Fatal(
            "Ambiguous reference to \{name}. Can refer to a term or a type.",
          )
        }
      (None, None) => None
    }
  })
}

///|
pub fn Scoping::lookup_first(
  self : Scoping,
  path : Array[String],
  name : String,
) -> Sym raise EffektError {
  match self.lookup_first_option(path, name) {
    Some(s) => s
    None => raise EffektError::Fatal("Could not resolve \{name}")
  }
}

///|
pub fn Scoping::current_terms_for(self : Scoping, name : String) -> Array[Sym] {
  self.scope.bindings().terms.get(name).unwrap_or([])
}

///|
pub fn Scoping::define_term(
  self : Scoping,
  name : String,
  sym : Sym,
) -> Unit raise EffektError {
  let in_scope = self.current_terms_for(name)
  match sym {
    ValueParam(_) | ValBinder(_) | Hole(_) | Wildcard(_) | TmpValue(_) =>
      if in_scope.any(s => s.is_block_symbol()) {
        raise EffektError::Fatal(
          "Value \{name} has the same name as a block definition in the same scope, which is not allowed.",
        )
      }
    _ =>
      if in_scope.any(s => s.is_value_symbol()) {
        raise EffektError::Fatal(
          "Block \{name} has the same name as a value definition in the same scope, which is not allowed.",
        )
      }
  }
  self.scope.bindings().add_term(name, sym)
}

///|
pub fn Scoping::define_type(self : Scoping, name : String, sym : Sym) -> Unit {
  self.scope.bindings().set_type(name, sym)
}

///|
pub fn Scoping::define_capture(
  self : Scoping,
  name : String,
  sym : Sym,
) -> Unit {
  self.scope.bindings().set_capture(name, sym)
}

///|
pub fn Scoping::exports(self : Scoping) -> Bindings {
  self.scope.bindings()
}

///|
/// Runs `f` in a fresh local scope.
pub fn[T] Scoping::scoped(self : Scoping, f : () -> T) -> T {
  let before = self.scope
  self.scope = Local(None, Bindings::empty(), before)
  let result = f()
  self.scope = before
  result
}

///|
/// Runs `f` in a fresh local scope with a name (for diagnostics).
pub fn[T] Scoping::scoped_named(
  self : Scoping,
  name : String,
  f : () -> T,
) -> T {
  let before = self.scope
  self.scope = Local(Some(name), Bindings::empty(), before)
  let result = f()
  self.scope = before
  result
}

///|
/// Re-enters a namespace, making previously defined members visible again.
pub fn[T] Scoping::namespace(self : Scoping, name : String, f : () -> T) -> T {
  let before = self.scope
  let child = before.bindings().namespace(name)
  self.scope = Named(name, child, before)
  let result = f()
  self.scope = before
  result
}

///|
/// The current namespace path, if inside a namespace.
pub fn Scoping::path(self : Scoping) -> Array[String]? {
  fn collect(scope : Scope, module_path : Array[String]) -> Array[String]? {
    match scope {
      Global(_) => Some(module_path)
      Named(name, _, outer) =>
        match collect(outer, module_path) {
          Some(p) => Some(p + [name])
          None => Some([name])
        }
      Local(_, _, _) => None
    }
  }
  collect(self.scope, self.module_path)
}
