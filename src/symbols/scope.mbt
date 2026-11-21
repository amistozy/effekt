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
  /// A local scope introduced by functions, blocks, etc. `ended` are the terms
  /// whose scope has ended in it: leaving a nested local scope records them in
  /// the enclosing one (upstream `Scope.Local.ended`), which is how a diagnostic
  /// can point at a binder that is no longer in scope. Only a local scope keeps
  /// them; a namespace or the global scope drops them.
  Local(String?, Bindings, Scope, Array[Sym])
}

///|
pub fn Scope::bindings(self : Scope) -> Bindings {
  match self {
    Global(b) => b
    Named(_, b, _) => b
    Local(_, b, _, _) => b
  }
}

///|
/// The same scope, recording the terms whose scope has ended in it. Only a local
/// scope keeps them (upstream `Scope.withEnded`).
pub fn Scope::with_ended(self : Scope, terms : ArrayView[Sym]) -> Scope {
  match self {
    Local(name, bindings, outer, ended) =>
      Local(name, bindings, outer, terms.to_owned() + ended)
    _ => self
  }
}

///|
/// The terms whose scope ends when the local scope `inner` is left: everything
/// bound in it, then the ones that already ended inside it (upstream `local`).
pub fn ended_by(inner : Scope) -> Array[Sym] {
  let ended : Array[Sym] = []
  for _, syms in inner.bindings().terms {
    ended.append(syms)
  }
  ended.append(inner.ended())
  ended
}

///|
/// The terms whose scope has ended within this scope, the latest first
/// (upstream `endedTerms`).
pub fn ended_terms(scope : Scope) -> Array[Sym] {
  match scope {
    Local(_, _, outer, ended) => ended + ended_terms(outer)
    _ => []
  }
}

///|
/// The latest term named `name` whose scope has ended, if `name` is unqualified
/// (upstream `endedTerm`).
pub fn ended_term(
  scope : Scope,
  path : ArrayView[String],
  name : String,
) -> Sym? {
  guard path.is_empty() else { return None }
  for sym in ended_terms(scope) {
    if sym.name().name == name {
      return Some(sym)
    }
  }
  None
}

///|
/// The mutable scoping state used by the namer.
pub(all) struct Scoping {
  module_path : Array[String]
  mut scope : Scope
}

///|
/// The scope a module starts in (upstream `Scoping.toplevel`).
///
/// Upstream puts the prelude into the *imports* of the global scope and leaves
/// its `bindings` empty, so a module may define a type that has the same name as
/// a builtin (`examples/benchmarks/advent_of_code_2025/day12` declares
/// `record Region`, and `Region` is a builtin interface). The port keeps imports
/// in `Namer.imports` instead of in the scope, so the caller passes the prelude
/// there.
pub fn toplevel(module_path : Array[String]) -> Scoping {
  { module_path, scope: Global(Bindings::empty()), }
}

///|
pub fn Scoping::import_all(self : Scoping, imports : Bindings) -> Unit {
  self.scope.bindings().import_all(imports)
}

///|
pub fn Scoping::import_as(
  self : Scoping,
  bindings : Bindings,
  path : ArrayView[String],
) -> Unit {
  let ns = path.fold(init=self.scope.bindings(), (ns, seg) => ns.namespace(seg))
  ns.import_all(bindings)
}

// Searching
// ---------

///|
fn[T] qualified_first(
  path : ArrayView[String],
  bindings : Bindings,
  select : (Bindings) -> T? raise EffektError,
) -> T? raise EffektError {
  if path.is_empty() {
    select(bindings)
  } else {
    match bindings.namespaces.get(path[0]) {
      None => None
      Some(ns) => qualified_first(path[1:], ns, select)
    }
  }
}

///|
fn[T] first(
  path : ArrayView[String],
  scope : Scope,
  select : (Bindings) -> T? raise EffektError,
) -> T? raise EffektError {
  match scope {
    Global(bindings) => qualified_first(path, bindings, select)
    Named(_, bindings, outer) =>
      or_else(qualified_first(path, bindings, select), () => {
        first(path, outer, select)
      })
    Local(_, bindings, outer, _) =>
      or_else(qualified_first(path, bindings, select), () => {
        first(path, outer, select)
      })
  }
}

///|
fn[T] qualified_all(
  path : ArrayView[String],
  bindings : Bindings,
  select : (Bindings) -> T,
) -> Array[T] {
  if path.is_empty() {
    [select(bindings)]
  } else {
    match bindings.namespaces.get(path[0]) {
      None => []
      Some(ns) => qualified_all(path[1:], ns, select)
    }
  }
}

///|
fn[T] all(
  path : ArrayView[String],
  scope : Scope,
  select : (Bindings) -> T,
) -> Array[T] {
  match scope {
    Global(bindings) => qualified_all(path, bindings, select)
    Named(_, bindings, outer) =>
      qualified_all(path, bindings, select) + all(path, outer, select)
    Local(_, bindings, outer, _) =>
      qualified_all(path, bindings, select) + all(path, outer, select)
  }
}

///|
/// The unique symbol bound to `name` in `terms`: `None` when the name is not
/// bound, and an abort when it is bound more than once. Upstream reports the
/// ambiguous reference from `lookupFirstTerm`, which is why every *plain*
/// lookup goes through this and only `lookupOverloaded` keeps the list.
pub fn unique_term(
  terms : Map[String, Array[Sym]],
  name : String,
) -> Sym? raise EffektError {
  match terms.get(name) {
    None => None
    Some(syms) => {
      guard syms.length() <= 1 else {
        raise EffektError::Fatal("Ambiguous reference to \{name}")
      }
      syms.get(0)
    }
  }
}

///|
/// Searches the nested scopes for the first term with the given name.
pub fn Scoping::lookup_first_term_option(
  self : Scoping,
  path : ArrayView[String],
  name : String,
) -> Sym? raise EffektError {
  first(path, self.scope, b => unique_term(b.terms, name))
}

///|
pub fn Scoping::lookup_type_option(
  self : Scoping,
  path : ArrayView[String],
  name : String,
) -> Sym? raise EffektError {
  first(path, self.scope, b => b.types.get(name))
}

///|
pub fn Scoping::lookup_capture(
  self : Scoping,
  path : ArrayView[String],
  name : String,
) -> Sym? raise EffektError {
  first(path, self.scope, b => b.captures.get(name))
}

///|
pub fn Scoping::lookup_overloaded(
  self : Scoping,
  path : ArrayView[String],
  name : String,
  filter : (Sym) -> Bool,
) -> Array[Array[Sym]] {
  all(path, self.scope, b => b.terms.get(name).unwrap_or([]).filter(filter))
}

///|
/// Looks a term up in a scope chain. The type checker needs this for
/// name-based implicit arguments: the name only becomes known once the
/// callee's parameter list is, which is after the namer has run.
fn Scope::lookup_term_option(
  self : Scope,
  path : ArrayView[String],
  name : String,
) -> Sym? raise EffektError {
  first(path, self, b => unique_term(b.terms, name))
}

///|
/// All scopes that bind `name` to a callable (non-operation) symbol,
/// innermost first. Used to eta-expand an implicit block argument.
fn Scope::lookup_functions(self : Scope, name : String) -> Array[Array[Sym]] {
  all([], self, b => {
    b.terms
    .get(name)
    .unwrap_or([])
    .filter(s => s.is_callable() && !s.is_operation())
  }).filter(ns => !ns.is_empty())
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
    None => unique_term(imports.terms, name)
  }
}

///|
/// The names of all types bound in the scope chain and in the imports, grouped
/// by scope (nearest first) and sorted within a group, for a "Did you mean
/// ...?" suggestion (upstream `Scope.all(path, scope)` over `bindings.types`,
/// which sorts each scope's names before comparing).
pub fn available_type_names(
  scope : Scope,
  imports : Bindings,
) -> Array[Array[String]] {
  let out = all([], scope, b => sorted_names(b.types.keys()))
  let imported = sorted_names(imports.types.keys())
  if imported.is_empty() {
    out
  } else {
    out + [imported]
  }
}

///|
/// The terms visible in the scope chain and in the imports, grouped by scope
/// (nearest first) and sorted by name within a group (upstream `visibleTerms`,
/// which `explainMissingTerm` and `didYouMeanMethod` use for a "Did you mean
/// ...?" suggestion).
pub fn visible_terms(
  scope : Scope,
  imports : Bindings,
  path : ArrayView[String],
) -> Array[Array[(String, Array[Sym])]] {
  let out = all(path, scope, b => sorted_terms(b))
  let imported = sorted_terms(imports)
  if imported.is_empty() {
    out
  } else {
    out + [imported]
  }
}

///|
fn sorted_terms(bindings : Bindings) -> Array[(String, Array[Sym])] {
  let out : Array[(String, Array[Sym])] = []
  for name, syms in bindings.terms {
    out.push((name, syms))
  }
  out.mut_view().stable_sort_by((a, b) => a.0.lexical_compare(b.0))
  out
}

///|
fn sorted_names(names : Iter[String]) -> Array[String] {
  let out : Array[String] = []
  for name in names {
    out.push(name)
  }
  out.mut_view().stable_sort_by((a, b) => a.lexical_compare(b))
  out
}

///|
/// What is wrong with a term that could not be resolved, as the notes and helps
/// of the diagnostic (upstream `Scoping.explainMissingTerm`): a term of that
/// name whose scope has ended is pointed at, otherwise a close name is
/// suggested.
pub fn explain_missing_term(
  scope : Scope,
  imports : Bindings,
  path : ArrayView[String],
  name : String,
) -> Array[@util.Subdiagnostic] {
  match ended_term(scope, path, name) {
    Some(binder) => [note_ended(binder)]
    None =>
      match did_you_mean_term(scope, imports, path, name) {
        Some(help) => [@util.Subdiagnostic::Help(help)]
        None => []
      }
  }
}

///|
/// Points at the binder of a term whose scope has ended (upstream `noteEnded`).
/// The position is the *name* of the binder, not its whole definition.
pub fn note_ended(binder : Sym) -> @util.Subdiagnostic {
  let at = binder.def_id()
  @util.Subdiagnostic::Note(
    "There is a `\{binder.name().name}` bound here, but not in the current scope.",
    if at.is_missing() {
      None
    } else {
      Some(at)
    },
  )
}

///|
/// A "Did you mean ...?" hint for a term that is bound nowhere: a heuristic for
/// names that are keywords elsewhere, then the closest of the terms in scope.
fn did_you_mean_term(
  scope : Scope,
  imports : Bindings,
  path : ArrayView[String],
  name : String,
) -> String? {
  let specific = (candidate : String) => {
    match candidate {
      // literal constructors are keywords, not terms in scope; suggest `None()`
      // only if it is in scope
      "True" | "TRUE" => @util.suggestion(["true"])
      "False" | "FALSE" => @util.suggestion(["false"])
      "null" | "nullptr" =>
        if scope.any_term_named(imports, "None") {
          @util.suggestion(["None()"])
        } else {
          None
        }
      _ => None
    }
  }
  @util.did_you_mean(
    name,
    visible_terms(scope, imports, path).map(group => group.map(pair => pair.0)),
    specific,
  )
}

///|
/// Is a term of that name bound anywhere in the scope chain or the imports?
fn Scope::any_term_named(
  self : Scope,
  imports : Bindings,
  name : String,
) -> Bool {
  let found = first([], self, b => b.terms.get(name)) catch { _ => None }
  found is Some(_) || imports.terms.get(name) is Some(_)
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
  if !imported.is_empty() {
    groups + [imported]
  } else {
    groups
  }
}

///|
/// All groups of terms bound to `name`, whatever their kind, scope chain first
/// and imports last (upstream `scope.lookupOverloaded(id, _ => true)`).
pub fn lookup_terms_in_scope(
  scope : Scope,
  imports : Bindings,
  name : String,
) -> Array[Array[Sym]] {
  let groups = all([], scope, b => b.terms.get(name).unwrap_or([])).filter(ns => {
    !ns.is_empty()
  })
  let imported = imports.terms.get(name).unwrap_or([])
  if !imported.is_empty() {
    groups + [imported]
  } else {
    groups
  }
}

///|
/// Mutable variables are treated as values, not as blocks.
pub fn is_value_target(sym : Sym) -> Bool {
  sym.is_value_symbol() || sym.is_ref_binder()
}

///|
pub fn is_block_target(sym : Sym) -> Bool {
  sym.is_block_symbol() && !sym.is_ref_binder()
}

///|
/// The block candidates of a call target `f(...)` among `groups` (innermost scope
/// first): a single value in the tightest scope shadows the blocks, otherwise the
/// blocks of every scope are the candidates. An empty result means there is no
/// block to call — either the name is unbound or a value shadows it (upstream
/// `Namer.resolveFunctionCalltarget`; the type checker uses the same rule for an
/// implicit block argument).
pub fn block_candidates(groups : ArrayView[Array[Sym]]) -> Array[Array[Sym]] {
  for terms in groups {
    guard !terms.is_empty() else { continue }
    if terms.all(is_block_target) {
      let out : Array[Array[Sym]] = []
      for group in groups {
        let blocks = group.filter(is_block_target)
        if !blocks.is_empty() {
          out.push(blocks)
        }
      }
      return out
    }
    if terms.any(is_value_target) {
      return []
    }
  }
  []
}

///|
pub fn Scoping::lookup_operation(
  self : Scoping,
  path : ArrayView[String],
  name : String,
) -> Array[Array[Sym]] {
  all(path, self.scope, b => {
    b.terms.get(name).unwrap_or([]).filter(s => s.is_operation())
  }).filter(ns => !ns.is_empty())
}

///|
pub fn Scoping::lookup_function(
  self : Scoping,
  path : ArrayView[String],
  name : String,
) -> Array[Array[Sym]] {
  all(path, self.scope, b => {
    b.terms
    .get(name)
    .unwrap_or([])
    .filter(s => s.is_callable() && !s.is_operation())
  }).filter(ns => !ns.is_empty())
}

///|
pub fn Scoping::lookup_first_block_param(
  self : Scoping,
  path : ArrayView[String],
  name : String,
) -> Array[Sym] raise EffektError {
  first(path, self.scope, b => {
    match b.terms.get(name) {
      // The name is not bound in this scope: keep looking in the outer ones
      // (upstream `lookupFirstBlockParam` only stops at the innermost scope
      // that *binds* the name, which is what makes a block parameter of an
      // enclosing definition visible inside a nested block literal).
      None => None
      Some(syms) => Some(syms.filter(s => s is BlockParam(_)))
    }
  }).unwrap_or([])
}

///|
fn Scoping::current_terms_for(self : Scoping, name : String) -> Array[Sym] {
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
/// Is the type name defined in the *current* scope (not an enclosing one)?
pub fn Scoping::current_type_for(self : Scoping, name : String) -> Sym? {
  self.scope.bindings().types.get(name)
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
/// Runs `f` in a fresh local scope. Leaving it ends the scope of everything bound
/// inside, which the enclosing *local* scope records so that a later reference
/// can point at the binder (upstream `local`).
pub fn[T] Scoping::scoped(self : Scoping, f : () -> T) -> T {
  let before = self.scope
  self.scope = Local(None, Bindings::empty(), before, [])
  defer {
    // the terms of the inner scope first, then the ones that ended inside it,
    // each *prepended* to the outer scope's list so that the latest comes first
    self.scope = before.with_ended(ended_by(self.scope))
  }
  f()
}

///|
/// The terms whose scope has ended in this very scope (not in an enclosing one).
fn Scope::ended(self : Scope) -> Array[Sym] {
  match self {
    Local(_, _, _, ended) => ended
    _ => []
  }
}

///|
/// Re-enters a namespace, making previously defined members visible again.
pub fn[T] Scoping::namespace(self : Scoping, name : String, f : () -> T) -> T {
  let before = self.scope
  defer {
    self.scope = before
  }
  let child = before.bindings().namespace(name)
  self.scope = Named(name, child, before)
  f()
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
      Local(_, _, _, _) => None
    }
  }
  collect(self.scope, self.module_path)
}
