// The namer: resolves all names in a module and creates the corresponding
// symbols.
//
// Mirrors `effekt/namer/Namer.scala`. Upstream keeps the current `Scoping`,
// the stack of parent definitions and the hole counter in dynamically scoped
// variables on `Context`; in this port they are fields of the `Namer` struct,
// which is threaded through the traversal. All side tables are keyed by the
// `uid` of the tree node (upstream keys them by object identity).
//
// This phase does *not* infer effects or captures: those are the job of the
// typer. It only resolves names, creates symbols and maintains scopes.

///|
/// The result of running the namer on one module.
pub(all) struct ResolvedModule {
  /// The resolved module symbol: its exports and includes.
  module : Module
  /// The tree the module was resolved from.
  tree : @source.ModuleDecl
  /// The holes (`???`) of the module, in the order they were resolved.
  holes : Array[Sym]
}

///|
/// Resolves all names in `module`, writes symbols into `context`, and returns
/// the resolved module together with the resolved tree.
///
/// `deps` maps the include paths of the module (as written in `include "..."`)
/// to the modules they refer to. A dependency is imported fully qualified
/// (`foo::bar::baz`), under its last segment (`baz`) and opened, exactly like
/// upstream's `importDependency`. Includes that are not in `deps` are reported
/// as errors; a module without includes can be resolved with an empty map.
pub fn resolve_module(
  module : @source.ModuleDecl,
  context : @source.Context,
  deps : Map[String, ResolvedModule],
) -> ResolvedModule raise EffektError {
  let mod = Module::new(module.path, module.span)
  let namer = new_namer(context, mod, deps)
  namer.resolve_toplevel(module)
  mod.exports = namer.scoping.exports()
  { module: mod, tree: module, holes: namer.holes, }
}

///|
/// Resolves all names in `module` and publishes the resolved module symbol in
/// `context` (see `Context::resolved_module`). This is the entry point for
/// drivers that only need the annotations on the tree; use `resolve_module`
/// when you also need the exports, includes or holes.
pub fn resolve(
  module : @source.ModuleDecl,
  context : @source.Context,
) -> Unit raise EffektError {
  let resolved = resolve_module(module, context, Map([]))
  context.set_resolved_module(resolved.module)
}

// ---------------------------------------------------------------------------
// Namer state
// ---------------------------------------------------------------------------

///|
/// The state of one namer run.
priv struct Namer {
  context : @source.Context
  scoping : Scoping
  module : Module
  /// The namespace of the module itself, e.g. `["examples", "hello"]`. Used to
  /// resolve `<module>::foo` to `foo` (upstream: `Context.importSelfAs`).
  self_namespace : Array[String]
  /// The names imported from other modules (upstream: `Scope.imports`).
  /// Imports are deliberately kept *out* of the module's bindings: a local
  /// definition shadows an import of the same name instead of clashing with it,
  /// and a module does not re-export what it imports.
  imports : Bindings
  /// The definitions we are currently inside, innermost last.
  /// (Upstream: `parentDefinitions`.)
  parent_definitions : Array[Def]
  /// Disambiguates hole identifiers. (Upstream: `holeCount`.)
  hole_count : Map[String, Int32]
  /// The holes of this module, for later phases (e.g. the LSP).
  holes : Array[Sym]
  /// Already resolved modules, by include path.
  deps : Map[String, ResolvedModule]
  /// The include paths that have already been imported. A module may be
  /// included more than once (the driver prepends the implicit prelude include,
  /// so `import effekt` shows up twice); importing is idempotent, but we only
  /// merge a dependency's exports once.
  imported : Array[String]
}

///|
fn new_namer(
  context : @source.Context,
  module : Module,
  deps : Map[String, ResolvedModule],
) -> Namer {
  // The toplevel scope is the namespace of the module, e.g. `examples::hello`.
  let namespace = module.name.path + [module.name.name]
  {
    context,
    scoping: @symbols.toplevel(namespace, @symbols.root_bindings()),
    module,
    self_namespace: namespace,
    imports: Bindings::empty(),
    parent_definitions: [],
    hole_count: Map([]),
    holes: [],
    deps,
    imported: [],
  }
}

// ---------------------------------------------------------------------------
// Scoping
//
// `src/symbols/scope.mbt` provides the scope stack, but its `scoped`,
// `scopedWithName` and `namespace` take non-raising closures. Since resolving
// a module can fail, we re-implement the three combinators here on top of the
// public `Scoping`/`Scope`/`Bindings` API.
// ---------------------------------------------------------------------------

///|
fn[T] Namer::in_local_scope(
  self : Namer,
  f : () -> T raise EffektError,
) -> T raise EffektError {
  let before = self.scoping.scope
  self.scoping.scope = @symbols.Scope::Local(None, Bindings::empty(), before)
  let result = f()
  self.scoping.scope = before
  result
}

///|
fn[T] Namer::in_named_scope(
  self : Namer,
  name : String,
  f : () -> T raise EffektError,
) -> T raise EffektError {
  let before = self.scoping.scope
  self.scoping.scope = @symbols.Scope::Local(
    Some(name),
    Bindings::empty(),
    before,
  )
  let result = f()
  self.scoping.scope = before
  result
}

///|
/// (Re-)enters the namespace `name`, making previously defined members visible
/// again. Namespaces are shared by reference, so definitions made inside stay
/// visible to the enclosing scope.
fn[T] Namer::in_namespace(
  self : Namer,
  name : String,
  f : () -> T raise EffektError,
) -> T raise EffektError {
  let before = self.scoping.scope
  let child = before.bindings().namespace(name)
  self.scoping.scope = @symbols.Scope::Named(name, child, before)
  let result = f()
  self.scoping.scope = before
  result
}

///|
fn[T] Namer::in_namespace_path(
  self : Namer,
  path : Array[String],
  f : () -> T raise EffektError,
) -> T raise EffektError {
  if path.length() == 0 {
    f()
  } else {
    self.in_namespace(path[0], () => {
      self.in_namespace_path(path[1:].to_owned(), f)
    })
  }
}

///|
/// Records what a call site needs from the lexical environment: the scope chain
/// and the imports. The type checker resolves name-based implicit arguments at
/// that site, which is the one lookup that happens without an `IdRef`; both the
/// scope and the imports are namer state.
fn Namer::record_call_site(self : Namer, uid : Int32) -> Unit {
  self.context.assign_call_scope(uid, self.scoping.scope)
  self.context.assign_call_imports(uid, self.imports)
}

// ---------------------------------------------------------------------------
// Module
// ---------------------------------------------------------------------------

///|
fn Namer::resolve_toplevel(
  self : Namer,
  decl : ModuleDecl,
) -> Unit raise EffektError {
  // Process all includes, updating the terms and types in scope.
  let includes : Array[Module] = []
  for inc in decl.includes {
    match self.import_dependency(inc.path, inc.span) {
      Some(dep) =>
        if !includes.any(m => m.uid == dep.uid) {
          includes.push(dep)
        }
      None => ()
    }
  }
  self.module.includes = includes
  self.hole_count.clear()
  // To allow mutually recursive definitions, we first only resolve the
  // declarations, not the bodies of functions.
  for d in decl.defs {
    self.preresolve(d)
  }
  for d in decl.defs {
    self.resolve_def(d)
  }
}

///|
fn Namer::import_dependency(
  self : Namer,
  path : String,
  span : Span,
) -> Module? {
  match self.deps.get(path) {
    None => {
      self.context.error(span, "Cannot find module to include: \{path}")
      None
    }
    Some(dep) => {
      let included = dep.module
      // Importing the same module twice is a no-op (the driver prepends the
      // implicit prelude include, so `import effekt` occurs twice).
      if self.imported.any(p => p == path) {
        return Some(included)
      }
      self.imported.push(path)
      let namespace = included.name.path + [included.name.name]
      // Fully qualified:
      //   include "foo/bar/baz" as foo::bar::baz
      self.import_as(included.exports, namespace)
      // Bind the module itself:
      //   include "foo/bar/baz" as baz
      self.import_as(included.exports, [included.name.name])
      // Open it:
      //   import baz::*
      merge_bindings(self.imports, included.exports)
      Some(included)
    }
  }
}

// ---------------------------------------------------------------------------
// Imports
//
// Upstream keeps imports in a `Bindings` of their own, next to the bindings of
// the scope. Since `Scoping` in this port merges both, we keep the imports in
// the namer and consult them whenever a lookup in the scope chain fails. This
// also means a definition shadows an import (like upstream) instead of making
// the reference ambiguous.
// ---------------------------------------------------------------------------

///|
/// Imports `bindings` under `path` (upstream: `Scoping.importAs`).
fn Namer::import_as(
  self : Namer,
  bindings : Bindings,
  path : Array[String],
) -> Unit {
  let mut target = self.imports
  for segment in path {
    target = target.namespace(segment)
  }
  merge_bindings(target, bindings)
}

///|
/// Deep-merges `source` into `target`. Every level is snapshotted first, so
/// that a structure which (indirectly) contains `target` does not extend the
/// traversal indefinitely.
fn merge_bindings(target : Bindings, source : Bindings) -> Unit {
  let terms = source.terms.copy()
  let types = source.types.copy()
  let captures = source.captures.copy()
  let namespaces = source.namespaces.copy()
  for name, syms in terms {
    for sym in syms {
      target.add_term(name, sym)
    }
  }
  for name, tpe in types {
    target.set_type(name, tpe)
  }
  for name, capt in captures {
    target.set_capture(name, capt)
  }
  for name, child in namespaces {
    merge_bindings(target.namespace(name), child)
  }
}

///|
/// Navigates `path` in `bindings` and selects from the bindings found.
fn[T] in_bindings(
  bindings : Bindings,
  path : Array[String],
  select : (Bindings) -> T? raise EffektError,
) -> T? raise EffektError {
  if path.length() == 0 {
    select(bindings)
  } else {
    match bindings.get_namespace(path[0]) {
      None => None
      Some(child) => in_bindings(child, path[1:].to_owned(), select)
    }
  }
}

///|
/// The paths a reference may use to reach the module's own definitions.
///
/// A module may refer to its own definitions by qualified name,
/// `<module>::foo` (upstream: `Context.importSelfAs`). The module's bindings
/// *are* the toplevel scope, so the path without the module's namespace is
/// looked up as usual and stays up to date; a path that *is* the module
/// namespace (`set::collect` in module `set`) strips to the empty path, i.e.
/// the toplevel scope.
///
/// The path *as written* is tried first: a program is registered under its
/// file name (`examples/stdlib/buffer.effekt` is the module `buffer`), which
/// may be the name of a module it imports. Stripping `buffer::examples` to
/// `examples` would then reach the *prelude's* `examples` namespace (opened by
/// `import stringbuffer`) and report the reference as ambiguous.
fn Namer::lookup_paths(
  self : Namer,
  path : Array[String],
) -> Array[Array[String]] {
  let ns = self.self_namespace
  if path.length() < ns.length() {
    return [path]
  }
  for i = 0; i < ns.length(); i = i + 1 {
    if path[i] != ns[i] {
      return [path]
    }
  }
  let stripped = path[ns.length():].to_owned()
  if stripped.length() == path.length() {
    [path]
  } else {
    [path, stripped]
  }
}

///|
/// Looks up a unique term in the scope chain, then in the imports.
fn Namer::lookup_term(
  self : Namer,
  path : Array[String],
  name : String,
) -> Sym? raise EffektError {
  for p in self.lookup_paths(path) {
    match self.scoping.lookup_first_term_option(p, name) {
      Some(sym) => return Some(sym)
      None =>
        match
          in_bindings(self.imports, p, bindings => {
            match bindings.terms.get(name) {
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
          }) {
          Some(sym) => return Some(sym)
          None => ()
        }
    }
  }
  None
}

///|
fn Namer::lookup_type(
  self : Namer,
  path : Array[String],
  name : String,
) -> Sym? raise EffektError {
  for p in self.lookup_paths(path) {
    match self.scoping.lookup_type_option(p, name) {
      Some(sym) => return Some(sym)
      None =>
        match
          in_bindings(self.imports, p, bindings => bindings.types.get(name)) {
          Some(sym) => return Some(sym)
          None => ()
        }
    }
  }
  None
}

///|
fn Namer::lookup_capture(
  self : Namer,
  path : Array[String],
  name : String,
) -> Sym? raise EffektError {
  for p in self.lookup_paths(path) {
    match self.scoping.lookup_capture(p, name) {
      Some(sym) => return Some(sym)
      None =>
        match
          in_bindings(self.imports, p, bindings => bindings.captures.get(name)) {
          Some(sym) => return Some(sym)
          None => ()
        }
    }
  }
  None
}

///|
/// All symbols bound to `name` under `path`, one group per scope plus one for
/// the imports (upstream: `Scoping.lookupOverloaded`).
fn Namer::lookup_overloaded_at(
  self : Namer,
  path : Array[String],
  name : String,
  filter : (Sym) -> Bool,
) -> Array[Array[Sym]] raise EffektError {
  let groups = self.scoping.lookup_overloaded(path, name, filter)
  let imported = in_bindings(self.imports, path, bindings => {
    match bindings.terms.get(name) {
      Some(syms) => Some(syms.filter(filter))
      None => None
    }
  })
  match imported {
    Some(group) => groups + [group]
    None => groups
  }
}

///|
/// All groups of candidates for `name`, see `lookup_paths` for the order of
/// the paths tried.
fn Namer::lookup_overloaded(
  self : Namer,
  path : Array[String],
  name : String,
  filter : (Sym) -> Bool,
) -> Array[Array[Sym]] raise EffektError {
  let mut result = self.lookup_overloaded_at(path, name, filter)
  if result.all(group => group.length() == 0) {
    let paths = self.lookup_paths(path)
    if paths.length() > 1 {
      result = self.lookup_overloaded_at(paths[1], name, filter)
    }
  }
  result
}

///|
/// Operations bound to `name` under `path` (upstream: `Scoping.lookupOperation`).
fn Namer::lookup_operation(
  self : Namer,
  path : Array[String],
  name : String,
) -> Array[Array[Sym]] raise EffektError {
  self
  .lookup_overloaded(path, name, sym => sym.is_operation())
  .filter(group => group.length() > 0)
}

///|
/// Callables bound to `name` under `path` (upstream: `Scoping.lookupFunction`).
fn Namer::lookup_function(
  self : Namer,
  path : Array[String],
  name : String,
) -> Array[Array[Sym]] raise EffektError {
  self
  .lookup_overloaded(path, name, sym => sym.is_callable() && !sym.is_operation())
  .filter(group => group.length() > 0)
}

///|
/// The block parameters bound to `name` in the innermost scope that binds it
/// (upstream: `Scoping.lookupFirstBlockParam`).
fn Namer::lookup_first_block_param(
  self : Namer,
  path : Array[String],
  name : String,
) -> Array[Sym] raise EffektError {
  for p in self.lookup_paths(path) {
    let local = self.scoping.lookup_first_block_param(p, name)
    if local.length() > 0 {
      return local
    }
    let imported = in_bindings(self.imports, p, bindings => {
      match bindings.terms.get(name) {
        Some(syms) =>
          Some(
            syms.filter(sym => {
              match sym {
                @symbols.Sym::BlockParam(_) => true
                _ => false
              }
            }),
          )
        None => None
      }
    })
    match imported {
      Some(params) => if params.length() > 0 { return params }
      None => ()
    }
  }
  []
}

// ---------------------------------------------------------------------------
// Defining, binding and looking up names (upstream: `NamerOps`)
// ---------------------------------------------------------------------------

///|
fn Namer::path(self : Namer) -> Array[String]? {
  self.scoping.path()
}

///|
/// The name of a definition, qualified with the current namespace path.
/// Mirrors upstream's `Context.nameFor`.
fn Namer::name_for(self : Namer, id : IdDef) -> Name {
  let prefix : Array[String] = match self.path() {
    Some(p) => p
    None => []
  }
  let full = prefix + id.path
  if full.length() == 0 {
    Name::local(id.name)
  } else {
    Name::qualified(full, id.name)
  }
}

///|
fn Namer::require_toplevel(self : Namer, kind : String) -> Unit {
  match self.path() {
    None =>
      self.context.error(
        Span::missing(),
        "\{kind} declarations are only allowed on the toplevel of a module or in a namespace.",
      )
    Some(_) => ()
  }
}

///|
fn Namer::require_not_toplevel(self : Namer, kind : String) -> Unit {
  match self.path() {
    Some(_) =>
      self.context.error(
        Span::missing(),
        "\{kind} declarations are not allowed on the toplevel of a module or in a namespace.",
      )
    None => ()
  }
}

///|
/// Defines `sym` under the name of `id`, in every suffix of the path of `id`
/// (so `def a::b::f` is also visible as `b::f` and `f`), mirroring upstream's
/// `defineInPaths`.
fn Namer::define_id(
  self : Namer,
  id : IdDef,
  sym : Sym,
) -> Unit raise EffektError {
  self.context.assign_symbol(id.uid, sym)
  let is_type = sym.is_type_symbol()
  for i = 0; i <= id.path.length(); i = i + 1 {
    let suffix = id.path[i:].to_owned()
    self.in_namespace_path(suffix, () => {
      if is_type {
        self.scoping.define_type(id.name, sym)
      } else {
        self.scoping.define_term(id.name, sym)
      }
    })
  }
}

///|
/// Defines a symbol for a whole definition: the symbol is attached to the
/// identifier *and* to the definition node, so later phases can look either up.
fn Namer::define_def(
  self : Namer,
  d : Def,
  id : IdDef,
  sym : Sym,
) -> Unit raise EffektError {
  self.define_id(id, sym)
  self.context.assign_symbol(d.uid, sym)
}

///|
fn Namer::bind_term(self : Namer, sym : Sym) -> Unit raise EffektError {
  let name = sym.name()
  for i = 0; i <= name.path.length(); i = i + 1 {
    let suffix = name.path[i:].to_owned()
    self.in_namespace_path(suffix, () => {
      self.scoping.define_term(name.name, sym)
    })
  }
}

///|
fn Namer::bind_type(self : Namer, sym : Sym) -> Unit raise EffektError {
  let name = sym.name()
  for i = 0; i <= name.path.length(); i = i + 1 {
    let suffix = name.path[i:].to_owned()
    self.in_namespace_path(suffix, () => {
      self.scoping.define_type(name.name, sym)
    })
  }
}

///|
fn Namer::bind_capture(self : Namer, sym : Sym) -> Unit {
  self.scoping.define_capture(sym.name().name, sym)
}

///|
/// Binds a tracked block parameter as a term and its capture parameter.
fn Namer::bind_block(self : Namer, sym : Sym) -> Unit raise EffektError {
  self.bind_term(sym)
  self.bind_capture(capture_of(sym))
}

///|
fn Namer::bind_values(
  self : Namer,
  params : Array[Sym],
) -> Unit raise EffektError {
  for p in params {
    self.bind_term(p)
  }
}

///|
fn Namer::bind_blocks(
  self : Namer,
  params : Array[Sym],
) -> Unit raise EffektError {
  for p in params {
    self.bind_block(p)
  }
}

///|
/// The symbol of a tree node we have resolved before (a definition).
fn Namer::symbol_of_node(self : Namer, uid : Int32) -> Sym raise EffektError {
  match self.context.symbol_of(uid) {
    Some(sym) => sym
    None => {
      self.context.panic("Cannot find symbol for node \{uid}")
      @symbols.Sym::wildcard()
    }
  }
}

// ---------------------------------------------------------------------------
// Declarations (first pass)
// ---------------------------------------------------------------------------

///|
fn Namer::preresolve(self : Namer, d : Def) -> Unit raise EffektError {
  match d.kind {
    @source.ValDef(_, _, _) => ()
    @source.VarDef(_, _, _) => self.require_not_toplevel("Mutable variable")
    @source.RegDef(_, _, _, _) =>
      self.require_not_toplevel("Mutable variable in a region")
    @source.NamespaceDef(id, definitions) => {
      self.require_toplevel("Namespace")
      self.in_namespace(id.name, () => {
        for inner in definitions {
          self.preresolve(inner)
        }
      })
    }
    // Allow recursive definitions of objects.
    @source.DefDef(id, captures, _, binding) =>
      match binding.kind {
        @source.New(implementation) => {
          let tpe = self.resolve_block_ref(implementation.interface)
          let caps = match captures {
            Some(cs) => Some(self.resolve_capture_set(cs).to_array())
            None => None
          }
          self.define_def(
            d,
            id,
            mk_def_binder(self.name_for(id), caps, Some(tpe), d.span),
          )
        }
        _ => ()
      }
    @source.FunDef(id, tparams, vparams, bparams, captures, annot, _) => {
      let unique = self.name_for(id)
      let caps = match captures {
        Some(cs) => Some(self.resolve_capture_set(cs).to_array())
        None => None
      }
      // We create a new scope, since resolving type params introduces them.
      let sym = self.in_local_scope(() => {
        let tps = tparams.map(t => self.resolve_type_param(t))
        let vps = vparams.map(p => self.resolve_value_param(p, true))
        let bps = bparams.map(p => self.resolve_block_param(p))
        let ret = self.in_local_scope(() => {
          self.bind_values(vps)
          self.bind_blocks(bps)
          match annot {
            Some(t) => Some(self.resolve_effectful(t))
            None => None
          }
        })
        mk_user_function(
          unique,
          tps,
          vps,
          bps,
          caps,
          ret.map(pair => pair.0),
          ret.map(pair => pair.1),
          d.span,
        )
      })
      self.define_def(d, id, sym)
    }
    @source.InterfaceDef(id, tparams, _) => {
      self.require_toplevel("Interface")
      let name = self.name_for(id)
      // We do not resolve the effect operations here to allow them to refer to
      // types that are defined later in the file.
      let sym = self.in_local_scope(() => {
        let tps = tparams.map(t => self.resolve_type_param(t))
        mk_interface(name, tps, d.span)
      })
      self.define_def(d, id, sym)
    }
    @source.TypeDef(id, tparams, tpe) => {
      self.require_toplevel("Type")
      let tps = self.in_local_scope(() => {
        tparams.map(t => self.resolve_type_param(t))
      })
      let alias = self.in_local_scope(() => {
        for t in tps {
          self.bind_type(t)
        }
        mk_type_alias(
          self.name_for(id),
          tps,
          self.resolve_value_type(tpe, false),
          d.span,
        )
      })
      self.define_def(d, id, alias)
    }
    @source.EffectDef(id, tparams, effs) => {
      self.require_toplevel("Effect")
      let tps = self.in_local_scope(() => {
        tparams.map(t => self.resolve_type_param(t))
      })
      let alias = self.in_local_scope(() => {
        for t in tps {
          self.bind_type(t)
        }
        mk_effect_alias(
          self.name_for(id),
          tps,
          self.resolve_effects(effs),
          d.span,
        )
      })
      self.define_def(d, id, alias)
    }
    @source.DataDef(id, tparams, _) => {
      self.require_toplevel("Datatype")
      // We do not resolve the constructors here to allow them to refer to types
      // that are defined later in the file.
      let sym = self.in_local_scope(() => {
        let tps = tparams.map(t => self.resolve_type_param(t))
        mk_data_type(self.name_for(id), tps, d.span)
      })
      self.define_def(d, id, sym)
    }
    @source.RecordDef(id, tparams, _) => {
      self.require_toplevel("Record")
      let sym = self.in_local_scope(() => {
        let tps = tparams.map(t => self.resolve_type_param(t))
        mk_record(self.name_for(id), tps, d.span)
      })
      self.define_def(d, id, sym)
    }
    @source.ExternType(id, tparams, _) => {
      self.require_toplevel("Extern type")
      let sym = self.in_local_scope(() => {
        let tps = tparams.map(t => self.resolve_type_param(t))
        mk_extern_type(self.name_for(id), tps, d.span)
      })
      self.define_def(d, id, sym)
    }
    @source.ExternInterface(id, tparams, _) => {
      self.require_toplevel("Extern interface")
      let sym = self.in_local_scope(() => {
        let tps = tparams.map(t => self.resolve_type_param(t))
        mk_extern_interface(self.name_for(id), tps, d.span)
      })
      self.define_def(d, id, sym)
    }
    @source.ExternDef(id, tparams, vparams, bparams, captures, ret, _) => {
      self.require_toplevel("Extern definition")
      let name = self.name_for(id)
      let capt = self.resolve_capture_set(captures).to_array()
      let sym = self.in_local_scope(() => {
        let tps = tparams.map(t => self.resolve_type_param(t))
        let vps = vparams.map(p => self.resolve_value_param(p, true))
        let bps = bparams.map(p => self.resolve_block_param(p))
        let (tpe, eff) = self.in_local_scope(() => {
          self.bind_blocks(bps)
          self.resolve_effectful(ret)
        })
        mk_extern_function(name, tps, vps, bps, tpe, eff, capt, d.span)
      })
      self.define_def(d, id, sym)
    }
    @source.ExternResource(id, tpe) => {
      self.require_toplevel("Extern resource")
      let name = self.name_for(id)
      let btpe = self.resolve_block_type(tpe, false)
      let sym = mk_extern_resource(
        name,
        btpe,
        @symbols.Sym::resource(name),
        d.span,
      )
      self.define_def(d, id, sym)
      self.bind_block(sym)
    }
    @source.ExternInclude(_, _, _) => self.require_toplevel("Extern include")
  }
}

// ---------------------------------------------------------------------------
// Bodies (second pass)
// ---------------------------------------------------------------------------

///|
/// Tracks the current toplevel definition (used for hole identifiers).
fn[T] Namer::with_definition(
  self : Namer,
  d : Def,
  f : () -> T raise EffektError,
) -> T raise EffektError {
  self.parent_definitions.push(d)
  let result = f()
  ignore(self.parent_definitions.pop())
  result
}

///|
fn Namer::resolve_def(self : Namer, d : Def) -> Unit raise EffektError {
  self.with_definition(d, () => {
    match d.kind {
      @source.ValDef(id, annot, binding) => {
        let tpe = match annot {
          Some(t) => Some(self.resolve_value_type(t, false))
          None => None
        }
        self.resolve_stmt(binding)
        self.define_def(d, id, mk_val_binder(self.name_for(id), tpe, d.span))
      }
      // Local mutable state
      @source.VarDef(id, annot, binding) => {
        let tpe = match annot {
          Some(t) => Some(self.resolve_value_type(t, false))
          None => None
        }
        self.resolve_stmt(binding)
        let name = self.name_for(id)
        let sym = mk_var_binder(
          name,
          tpe,
          @symbols.Sym::lexical_region(name, d.span),
          d.span,
        )
        self.define_def(d, id, sym)
        self.bind_capture(capture_of(sym))
      }
      // Allocation into a region
      @source.RegDef(id, annot, region, binding) => {
        let tpe = match annot {
          Some(t) => Some(self.resolve_value_type(t, false))
          None => None
        }
        let reg = self.resolve_id_ref(region)
        if !reg.is_block_symbol() {
          self.context.abort(region.span, "Region needs to be a block.")
        }
        self.resolve_stmt(binding)
        self.define_def(
          d,
          id,
          mk_reg_binder(self.name_for(id), tpe, reg, d.span),
        )
      }
      // Already has been preresolved (to enable recursive definitions).
      @source.DefDef(id, captures, annot, binding) =>
        match binding.kind {
          @source.New(implementation) =>
            self.resolve_implementation(implementation)
          _ => {
            let tpe = match annot {
              Some(t) => Some(self.resolve_block_type(t, false))
              None => None
            }
            self.resolve_term(binding)
            let caps = match captures {
              Some(cs) => Some(self.resolve_capture_set(cs).to_array())
              None => None
            }
            self.define_def(
              d,
              id,
              mk_def_binder(self.name_for(id), caps, tpe, d.span),
            )
          }
        }
      @source.FunDef(id, _, vparams, bparams, _, _, body) => {
        self.check_implicit_value_params(vparams, Optional)
        self.check_implicit_block_params(bparams, Optional)
        let sym = self.symbol_of_node(d.uid)
        match sym.as_callable() {
          Some(callable) =>
            self.in_named_scope(id.name, () => {
              for tp in callable.tparams {
                self.bind_type(tp)
              }
              self.bind_values(callable.vparams)
              self.bind_blocks(callable.bparams)
              self.resolve_stmt(body)
            })
          None =>
            self.context.panic("Expected the symbol of a function definition.")
        }
      }
      @source.ExternDef(id, _, vparams, bparams, _, _, bodies) => {
        self.check_implicit_value_params(vparams, Optional)
        self.check_implicit_block_params(bparams, Optional)
        let sym = self.symbol_of_node(d.uid)
        match sym.as_callable() {
          Some(callable) =>
            self.in_named_scope(id.name, () => {
              for tp in callable.tparams {
                self.bind_type(tp)
              }
              self.bind_values(callable.vparams)
              self.bind_blocks(callable.bparams)
              for body in bodies {
                match body {
                  @source.StringExternBody(_, template) =>
                    for arg in template.args {
                      self.resolve_term(arg)
                    }
                  @source.EffektExternBody(_, stmt) => self.resolve_stmt(stmt)
                  @source.Unsupported(_) => ()
                }
              }
            })
          None =>
            self.context.panic("Expected the symbol of an extern definition.")
        }
      }
      @source.InterfaceDef(id, _, operations) => {
        let interface = self.symbol_of_node(d.uid)
        let ops : Array[Sym] = []
        for op in operations {
          ops.push(self.resolve_operation(op, interface, id.name))
        }
        set_interface_operations(interface, ops)
      }
      @source.NamespaceDef(id, definitions) =>
        self.in_namespace(id.name, () => {
          for inner in definitions {
            self.resolve_def(inner)
          }
        })
      // The type itself has already been resolved, now resolve constructors.
      @source.DataDef(id, _, ctors) => {
        let data = self.symbol_of_node(d.uid)
        let constructors : Array[Sym] = []
        for c in ctors {
          let ctor = self.in_local_scope(() => {
            let name = self.name_for(c.id)
            let tps = c.tparams.map(t => self.resolve_type_param(t))
            mk_constructor(name, data_tparams(data) + tps, data, c.span)
          })
          // DataType::Constructor()
          self.in_namespace(id.name, () => {
            self.define_id(c.id, ctor)
            self.context.assign_symbol(c.uid, ctor)
          })
          set_constructor_fields(
            ctor,
            self.resolve_fields(c.params, ctor, false),
          )
          constructors.push(ctor)
        }
        // export DataType::{Constructor1, ...}
        for c in constructors {
          self.bind_term(c)
        }
        set_data_constructors(data, constructors)
      }
      // The record has been resolved as part of the preresolution step.
      @source.RecordDef(id, _, fields) => {
        let record = self.symbol_of_node(d.uid)
        let name = self.name_for(id)
        let ctor = mk_constructor(name, data_tparams(record), record, d.span)
        // We define the constructor on a copy to avoid confusion with symbols.
        self.define_id(clone_id_def(id), ctor)
        set_record_constructor(record, ctor)
        set_constructor_fields(ctor, self.resolve_fields(fields, ctor, true))
      }
      _ => ()
    }
  })
}

///|
/// Resolves the constructors' fields, mirroring upstream's `resolveFields`.
/// For data types the field symbols are only recorded (selectors are resolved
/// through the constructor), for records they are also defined as accessors.
fn Namer::resolve_fields(
  self : Namer,
  params : Array[ValueParam],
  ctor : Sym,
  define_accessors : Bool,
) -> Array[Sym] raise EffektError {
  let vps = self.in_local_scope(() => {
    // Bind the type parameters
    for t in @symbols.constructor_tparams(ctor) {
      self.bind_type(t)
    }
    params.map(p => self.resolve_nonfunction_value_param(p))
  })
  let fields : Array[Sym] = []
  for i = 0; i < params.length(); i = i + 1 {
    let param_tree = params[i]
    let field_id = clone_id_def(param_tree.id)
    let field = mk_field(
      self.name_for(field_id),
      vps[i],
      ctor,
      param_tree.id.span,
    )
    if define_accessors {
      self.define_id(field_id, field)
    } else {
      self.context.assign_symbol(field_id.uid, field)
    }
    fields.push(field)
  }
  fields
}

///|
fn Namer::resolve_operation(
  self : Namer,
  op : Operation,
  interface : Sym,
  interface_name : String,
) -> Sym raise EffektError {
  self.check_implicit_value_params(op.vparams, Optional)
  self.check_implicit_block_params(op.bparams, Optional)
  let name = self.name_for(op.id)
  let op_sym = self.in_named_scope(op.id.name, () => {
    // The parameters of the interface are in scope.
    for tp in interface_tparams(interface) {
      self.bind_type(tp)
    }
    let tps = op.tparams.map(t => self.resolve_type_param(t))
    let vps = op.vparams.map(p => self.resolve_value_param(p, true))
    let bps = op.bparams.map(p => self.resolve_block_param(p))
    // Bring capture names in scope that are introduced by block parameters.
    for b in bps {
      self.bind_capture(capture_of(b))
    }
    // The type parameters of an effect op are all type parameters on the
    // effect, followed by the annotated type parameters on the operation.
    let (result, effects) = self.resolve_effectful(op.ret)
    mk_operation(
      name,
      interface_tparams(interface) + tps,
      vps,
      bps,
      result,
      effects,
      interface,
      op.span,
    )
  })
  // Define in namespace ... and bind outside.
  self.in_namespace(interface_name, () => {
    self.define_id(op.id, op_sym)
    self.context.assign_symbol(op.uid, op_sym)
  })
  self.bind_term(op_sym)
  op_sym
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
fn Namer::resolve_stmt(self : Namer, s : Stmt) -> Unit raise EffektError {
  match s.kind {
    @source.DefStmt(d, rest) => {
      // Resolve declarations but do not resolve bodies (mutual recursion), then
      // resolve bodies.
      self.preresolve(d)
      self.resolve_def(d)
      self.resolve_stmt(rest)
    }
    @source.ExprStmt(term, rest) => {
      self.resolve_term(term)
      self.resolve_stmt(rest)
    }
    @source.Return(term) => self.resolve_term(term)
    @source.BlockStmt(stmts) =>
      self.in_local_scope(() => self.resolve_stmt(stmts))
  }
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

///|
fn Namer::resolve_term(self : Namer, t : Term) -> Unit raise EffektError {
  match t.kind {
    @source.Literal(_, _) => ()
    @source.Hole(id, template) => {
      let hole = mk_hole(Name::local(self.fresh_hole_id()), t.span)
      self.holes.push(hole)
      self.context.assign_symbol(id.uid, hole)
      self.context.assign_symbol(t.uid, hole)
      self.in_local_scope(() => {
        for arg in template.args {
          self.resolve_stmt(arg)
        }
      })
    }
    @source.Unbox(inner) => self.resolve_term(inner)
    @source.New(implementation) => self.resolve_implementation(implementation)
    @source.Match(scrutinees, clauses, default) => {
      for scrutinee in scrutinees {
        self.resolve_term(scrutinee)
      }
      for clause in clauses {
        self.resolve_clause(clause)
      }
      self.in_local_scope(() => {
        match default {
          Some(stmt) => self.resolve_stmt(stmt)
          None => ()
        }
      })
    }
    @source.If(guards, thn, els) => {
      self.in_local_scope(() => {
        for g in guards {
          self.resolve_guard(g)
        }
        self.resolve_stmt(thn)
      })
      self.in_local_scope(() => self.resolve_stmt(els))
    }
    @source.While(guards, block, default) => {
      self.in_local_scope(() => {
        for g in guards {
          self.resolve_guard(g)
        }
        self.resolve_stmt(block)
      })
      self.in_local_scope(() => {
        match default {
          Some(stmt) => self.resolve_stmt(stmt)
          None => ()
        }
      })
    }
    @source.TryHandle(body, handlers) => {
      for handler in handlers {
        self.resolve_handler(handler)
      }
      self.in_local_scope(() => {
        // Bind all annotated capabilities.
        for handler in handlers {
          match handler.capability {
            Some(param) => self.bind_block(self.resolve_block_param(param))
            None => ()
          }
        }
        self.resolve_stmt(body)
      })
    }
    @source.Region(name, body) => {
      let region_name = Name::local(name.name)
      let region = mk_block_param(
        region_name,
        Some(@symbols.t_region()),
        @symbols.Sym::capture_param(region_name),
        false,
        t.span,
      )
      self.define_id(name, region)
      self.in_local_scope(() => {
        self.bind_block(region)
        self.resolve_stmt(body)
      })
    }
    @source.BlockLiteral(tparams, vparams, bparams, stmt) => {
      self.check_implicit_value_params(vparams, Forbidden)
      self.check_implicit_block_params(bparams, Forbidden)
      self.in_local_scope(() => {
        let tps = tparams.map(t => self.resolve_type_param(t))
        ignore(tps)
        let vps = vparams.map(p => self.resolve_value_param(p, true))
        let bps = bparams.map(p => self.resolve_block_param(p))
        self.bind_values(vps)
        self.bind_blocks(bps)
        self.resolve_stmt(stmt)
      })
    }
    @source.Box(capt, block) => {
      match capt {
        Some(cs) => ignore(self.resolve_capture_set(cs))
        None => ()
      }
      self.resolve_term(block)
    }
    // NOTE: upstream panics here, since `Select` is introduced by a later
    // phase. In this port the parser produces it, so we resolve it like a
    // method call on a field: the field selector is looked up as a call target.
    @source.Select(receiver, target) => {
      self.resolve_term(receiver)
      let sym = self.resolve_select(target)
      self.context.assign_symbol(t.uid, sym)
    }
    @source.MethodCall(receiver, target, targs, vargs, bargs) => {
      self.record_call_site(t.uid)
      self.resolve_term(receiver)
      // We are a bit context sensitive in resolving the method.
      match receiver.kind {
        @source.Var(id) => {
          let sym = self.resolve_id_ref(id)
          if sym.is_value_symbol() {
            // (foo: ValueType).bar(args)  = Call(bar, foo :: args)
            if !self.resolve_overloaded_function(target) {
              self.context.abort(
                target.span,
                "Cannot resolve function \{id_text(target)}, called on a value receiver.",
              )
            }
          } else if sym.is_ref_binder() {
            if !self.resolve_overloaded_function(target) {
              self.context.abort(
                target.span,
                "Cannot resolve function \{id_text(target)}, called on a receiver that is a reference.",
              )
            }
          } else if sym.is_block_symbol() {
            // (foo: BlockType).bar(args)  = Invoke(foo, bar, args)
            if !self.resolve_overloaded_operation(target) {
              self.context.abort(
                target.span,
                "Cannot resolve operation \{id_text(target)}, called on a computation.",
              )
            }
          }
        }
        @source.Unbox(_) =>
          if !self.resolve_overloaded_function(target) {
            self.context.abort(
              target.span,
              "Cannot resolve operation \{id_text(target)}, called on an unboxed computation.",
            )
          }
        // expr.bar(args) = Call(bar, expr :: args)
        _ =>
          if !self.resolve_overloaded_function(target) {
            self.context.abort(
              target.span,
              "Cannot resolve function \{id_text(target)}, called on an expression.",
            )
          }
      }
      for arg in targs {
        ignore(self.resolve_value_type(arg, false))
      }
      for arg in vargs {
        self.resolve_value_arg(arg)
      }
      for arg in bargs {
        self.resolve_term(arg)
      }
      match self.context.symbol_of(target.uid) {
        Some(sym) => self.context.assign_symbol(t.uid, sym)
        None => ()
      }
    }
    @source.Do(target, targs, vargs, bargs) => {
      self.record_call_site(t.uid)
      let sym = self.resolve_effect_call(target)
      self.context.assign_symbol(t.uid, sym)
      for arg in targs {
        ignore(self.resolve_value_type(arg, false))
      }
      for arg in vargs {
        self.resolve_value_arg(arg)
      }
      for arg in bargs {
        self.resolve_term(arg)
      }
    }
    @source.Call(target, targs, vargs, bargs) => {
      self.record_call_site(t.uid)
      match target {
        @source.IdTarget(id) => {
          let sym = self.resolve_function_calltarget(id)
          self.context.assign_symbol(t.uid, sym)
        }
        @source.ExprTarget(expr) => self.resolve_term(expr)
      }
      for arg in targs {
        ignore(self.resolve_value_type(arg, false))
      }
      for arg in vargs {
        self.resolve_value_arg(arg)
      }
      for arg in bargs {
        self.resolve_term(arg)
      }
    }
    @source.Var(id) => {
      let sym = self.resolve_var(id)
      self.context.assign_symbol(t.uid, sym)
    }
    @source.Assign(id, expr) => {
      let sym = self.resolve_id_ref(id)
      self.context.assign_symbol(t.uid, sym)
      match sym {
        @symbols.Sym::VarBinder(_) | @symbols.Sym::RegBinder(_) =>
          self.resolve_term(expr)
        @symbols.Sym::ValBinder(_) | @symbols.Sym::ValueParam(_) =>
          self.context.abort(
            id.span,
            "Can only assign to mutable variables, but \{id.name} is a constant.",
          )
        @symbols.Sym::Wildcard(_) =>
          self.context.abort(
            id.span,
            "Trying to assign to a wildcard, which is not allowed.",
          )
        _ =>
          self.context.abort(id.span, "Can only assign to mutable variables.")
      }
    }
  }
}

///|
fn Namer::resolve_value_arg(
  self : Namer,
  arg : ValueArg,
) -> Unit raise EffektError {
  self.resolve_term(arg.value)
}

// ---------------------------------------------------------------------------
// Patterns, guards, clauses, handlers, implementations
// ---------------------------------------------------------------------------

///|
/// Resolves pattern matching and returns the value params it binds.
fn Namer::resolve_pattern(
  self : Namer,
  pattern : MatchPattern,
) -> Array[Sym] raise EffektError {
  match pattern.kind {
    @source.IgnorePattern => []
    @source.LiteralPattern(_, _) => []
    @source.AnyPattern(id) => {
      let sym = mk_value_param(name_of_id(id), None, false, id.span)
      self.context.assign_symbol(id.uid, sym)
      self.context.assign_symbol(pattern.uid, sym)
      [sym]
    }
    @source.TagPattern(id, patterns) => {
      let sym = self.resolve_id_ref(id)
      self.context.assign_symbol(pattern.uid, sym)
      match sym {
        @symbols.Sym::Constructor(_) => ()
        _ =>
          self.context.error(
            id.span,
            "Can only pattern match on constructors of data types.",
          )
      }
      let out : Array[Sym] = []
      for sub in patterns {
        for p in self.resolve_pattern(sub) {
          out.push(p)
        }
      }
      out
    }
    @source.MultiPattern(patterns) => {
      let out : Array[Sym] = []
      for sub in patterns {
        for p in self.resolve_pattern(sub) {
          out.push(p)
        }
      }
      out
    }
  }
}

///|
fn Namer::resolve_guard(self : Namer, g : MatchGuard) -> Unit raise EffektError {
  match g.kind {
    @source.BooleanGuard(condition) => self.resolve_term(condition)
    @source.PatternGuard(scrutinee, pattern) => {
      self.resolve_term(scrutinee)
      for p in self.resolve_pattern(pattern) {
        self.bind_term(p)
      }
    }
  }
}

///|
fn Namer::resolve_clause(
  self : Namer,
  clause : MatchClause,
) -> Unit raise EffektError {
  let ps = self.resolve_pattern(clause.pattern)
  self.in_local_scope(() => {
    // Variables bound by patterns are available in the guards.
    for p in ps {
      self.bind_term(p)
    }
    for g in clause.guards {
      self.resolve_guard(g)
    }
    // wellformedness: only linear patterns
    let names : Array[Name] = []
    for p in ps {
      let name = p.name()
      if names.any(n => n == name) {
        self.context.error(
          clause.span,
          "Patterns have to be linear: names can only occur once, but \{name.name} shows up multiple times.",
        )
      }
      let cs = self.all_constructors_for(name)
      if cs.length() > 0 {
        self.context.warning(
          clause.span,
          "Pattern binds variable \{name.name}. Maybe you meant to match on equally named constructor of type \{constructor_type_text(cs[0])}?",
        )
      }
      names.push(name)
    }
    self.in_local_scope(() => self.resolve_stmt(clause.body))
  })
}

///|
fn Namer::resolve_handler(
  self : Namer,
  handler : Handler,
) -> Unit raise EffektError {
  self.resolve_implementation(handler.implementation)
  match handler.capability {
    Some(param) => self.bind_term(self.resolve_block_param(param))
    None => ()
  }
}

///|
fn Namer::resolve_implementation(
  self : Namer,
  implementation : Implementation,
) -> Unit raise EffektError {
  let eff = match self.resolve_block_ref(implementation.interface) {
    @symbols.InterfaceType(ctor, _) => ctor
    _ => {
      self.context.error(
        implementation.interface.span,
        "Expected an interface type.",
      )
      @symbols.Sym::error_block_type(implementation.interface.span)
    }
  }
  self.context.assign_symbol(implementation.uid, eff)
  for clause in implementation.clauses {
    // Try to find the operation in the handled effect.
    let mut found : Sym? = None
    for op in interface_operations(eff) {
      if op.name().name == clause.id.name {
        found = Some(op)
      }
    }
    let op_sym = match found {
      Some(op) => {
        self.context.assign_symbol(clause.id.uid, op)
        op
      }
      None => {
        self.context.abort(
          clause.span,
          "Operation \{id_text(clause.id)} is not part of interface \{eff.name().qualified_name()}.",
        )
        @symbols.Sym::wildcard()
      }
    }
    self.context.assign_symbol(clause.uid, op_sym)
    self.in_local_scope(() => {
      let tps = clause.tparams.map(t => self.resolve_type_param(t))
      ignore(tps)
      let vps = clause.vparams.map(p => self.resolve_value_param(p, true))
      let bps = clause.bparams.map(p => self.resolve_block_param(p))
      self.bind_values(vps)
      self.bind_blocks(bps)
      self.define_id(clause.resume, @symbols.Sym::resume_param())
      self.resolve_stmt(clause.body)
    })
  }
}

// ---------------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------------

///|
fn Namer::resolve_value_param(
  self : Namer,
  param : ValueParam,
  is_param : Bool,
) -> Sym raise EffektError {
  let tpe = match param.tpe {
    Some(t) => Some(self.resolve_value_type(t, is_param))
    None => None
  }
  let sym = mk_value_param(
    name_of_id(param.id),
    tpe,
    param.is_implicit,
    param.id.span,
  )
  self.context.assign_symbol(param.id.uid, sym)
  sym
}

///|
/// Used for fields, where "please wrap this in braces" is not good advice.
fn Namer::resolve_nonfunction_value_param(
  self : Namer,
  param : ValueParam,
) -> Sym raise EffektError {
  self.resolve_value_param(param, false)
}

///|
fn Namer::resolve_block_param(
  self : Namer,
  param : BlockParam,
) -> Sym raise EffektError {
  let name = name_of_id(param.id)
  let tpe = match param.tpe {
    Some(t) => Some(self.resolve_block_type(t, true))
    None => None
  }
  let sym = mk_block_param(
    name,
    tpe,
    @symbols.Sym::capture_param(name),
    param.is_implicit,
    param.id.span,
  )
  self.context.assign_symbol(param.id.uid, sym)
  sym
}

///|
fn Namer::resolve_type_param(self : Namer, id : IdDef) -> Sym raise EffektError {
  let sym = @symbols.Sym::type_param(name_of_id(id), id.span)
  self.define_id(id, sym)
  sym
}

///|
/// How many implicit parameters are allowed at this position.
/// Mirrors `effekt.util.RequirementLevel`.
priv enum RequirementLevel {
  Forbidden
  Optional
  Required
} derive(Eq)

///|
/// Checks that there are no implicit parameters if there shouldn't be (or that
/// there are, if there must be), and that there are no non-implicit parameters
/// after implicit ones. Mirrors upstream's `checkImplicitParams`.
fn Namer::check_implicit_flags(
  self : Namer,
  flags : Array[(Bool, String, Span)],
  level : RequirementLevel,
) -> Unit {
  let mut current = level
  for flag in flags {
    let (is_implicit, name, span) = flag
    let text = match span.text() {
      Some(t) => t
      None => name
    }
    if is_implicit && current == Forbidden {
      self.context.error(
        span,
        "Implicit parameter \{text} can never be passed implicitly to here.",
      )
      return
    }
    if !is_implicit && current == Required {
      self.context.error(
        span,
        "Parameter \{text} needs to be implicit so earlier implicit parameters can be passed implicitly.",
      )
      return
    }
    if is_implicit && current == Optional {
      current = Required
    }
  }
}

///|
fn Namer::check_implicit_value_params(
  self : Namer,
  params : Array[ValueParam],
  level : RequirementLevel,
) -> Unit {
  self.check_implicit_flags(
    params.map(p => (p.is_implicit, p.id.name, p.id.span)),
    level,
  )
}

///|
fn Namer::check_implicit_block_params(
  self : Namer,
  params : Array[BlockParam],
  level : RequirementLevel,
) -> Unit {
  self.check_implicit_flags(
    params.map(p => (p.is_implicit, p.id.name, p.id.span)),
    level,
  )
}

// ---------------------------------------------------------------------------
// Name resolution (upstream: the `resolve*` helpers of `NamerOps`)
// ---------------------------------------------------------------------------

///|
/// Tries to find a _unique_ term symbol in the current scope under `id`, and
/// stores the binding in the symbol table.
fn Namer::resolve_id_ref(self : Namer, id : IdRef) -> Sym raise EffektError {
  match self.lookup_term(id.path, id.name) {
    Some(sym) => {
      self.context.assign_symbol(id.uid, sym)
      sym
    }
    None => {
      self.context.abort(id.span, "Could not resolve term \{id_text(id)}")
      @symbols.Sym::wildcard()
    }
  }
}

///|
/// Resolves a term that can be a value or a block (e.g. a region).
fn Namer::resolve_var(self : Namer, id : IdRef) -> Sym raise EffektError {
  self.resolve_id_ref(id)
}

///|
fn Namer::all_constructors_for(
  self : Namer,
  name : Name,
) -> Array[Sym] raise EffektError {
  flatten_syms(
    self.lookup_overloaded(name.path, name.name, sym => {
      match sym {
        @symbols.Sym::Constructor(_) => true
        _ => false
      }
    }),
  )
}

///|
/// Resolves a potentially overloaded method target; the receiver is a
/// computation, so we look for an operation first.
fn Namer::resolve_overloaded_operation(
  self : Namer,
  id : IdRef,
) -> Bool raise EffektError {
  let syms = self.lookup_operation(id.path, id.name)
  let syms2 = if syms.length() == 0 {
    self.lookup_function(id.path, id.name)
  } else {
    syms
  }
  if syms2.length() > 0 {
    self.context.assign_symbol(id.uid, @symbols.Sym::call_target(syms2))
    true
  } else {
    false
  }
}

///|
/// Resolves a potentially overloaded method target; the receiver is a value or
/// an expression, so we look for a function first.
fn Namer::resolve_overloaded_function(
  self : Namer,
  id : IdRef,
) -> Bool raise EffektError {
  let syms = self.lookup_function(id.path, id.name)
  let syms2 = if syms.length() == 0 {
    self.lookup_operation(id.path, id.name)
  } else {
    syms
  }
  // Lookup the first block parameter and do not collect multiple since we do
  // not (yet?) permit overloading on block parameters.
  let syms3 = if syms2.length() == 0 {
    [self.lookup_first_block_param(id.path, id.name)]
  } else {
    syms2
  }
  if syms3.length() > 0 {
    self.context.assign_symbol(id.uid, @symbols.Sym::call_target(syms3))
    true
  } else {
    false
  }
}

///|
/// Resolves a potentially overloaded function call.
fn Namer::resolve_function_calltarget(
  self : Namer,
  id : IdRef,
) -> Sym raise EffektError {
  let candidates = self.lookup_overloaded(id.path, id.name, sym => {
    !sym.is_operation()
  })
  match self.resolve_target_candidates(id, candidates) {
    SingleTarget(sym) => {
      self.context.assign_symbol(id.uid, sym)
      sym
    }
    BlockTargets(blocks) => {
      if blocks.length() == 0 {
        let ops = flatten_syms(self.lookup_operation(id.path, id.name))
        // Provide specific info messages for operations.
        for op in ops {
          self.context.info(
            "There is an equally named effect operation \{op.name().qualified_name()} of interface \{operation_interface(op).name().qualified_name()}. Use syntax `do \{id_text(id)}()` to call it.",
          )
        }
        // Always abort with the generic message.
        self.context.abort(
          id.span,
          "Cannot find a function named `\{id_text(id)}`.",
        )
      }
      let sym = @symbols.Sym::call_target(blocks)
      self.context.assign_symbol(id.uid, sym)
      sym
    }
  }
}

///|
/// Resolves a potentially overloaded field access.
fn Namer::resolve_select(self : Namer, id : IdRef) -> Sym raise EffektError {
  let syms = self.lookup_overloaded(id.path, id.name, sym => {
    match sym {
      @symbols.Sym::Field(_) => true
      _ => false
    }
  })
  if syms.length() == 0 {
    self.context.abort(id.span, "Cannot resolve field access \{id_text(id)}")
  }
  let sym = @symbols.Sym::call_target(syms)
  self.context.assign_symbol(id.uid, sym)
  sym
}

///|
/// Resolves a potentially overloaded call to an effect.
fn Namer::resolve_effect_call(
  self : Namer,
  id : IdRef,
) -> Sym raise EffektError {
  let syms = self.lookup_operation(id.path, id.name)
  if syms.length() == 0 {
    self.context.abort(
      id.span,
      "Cannot resolve effect operation \{id_text(id)}",
    )
  }
  let sym = @symbols.Sym::call_target(syms)
  self.context.assign_symbol(id.uid, sym)
  sym
}

///|
/// The result of applying the scoping rules for blocks and values.
priv enum TargetResolution {
  SingleTarget(Sym)
  BlockTargets(Array[Array[Sym]])
}

///|
/// Implements the scoping rules for blocks and values:
///
/// 1) A single value in the tightest scope shadows blocks.
/// 2) If the tightest scope contains blocks, then we ignore all values and
///    resolve to an overloaded target.
fn Namer::resolve_target_candidates(
  self : Namer,
  id : IdRef,
  candidates : Array[Array[Sym]],
) -> TargetResolution raise EffektError {
  for terms in candidates {
    // Should not occur by construction.
    if terms.length() == 0 {
      continue
    }
    if terms.all(sym => is_block_target(sym)) {
      let blocks : Array[Array[Sym]] = []
      for group in candidates {
        let bs = group.filter(sym => sym.is_block_symbol())
        if bs.length() > 0 {
          blocks.push(bs)
        }
      }
      return BlockTargets(blocks)
    }
    if terms.any(sym => is_value_target(sym)) {
      if terms.any(sym => is_block_target(sym)) {
        self.context.panic("Should not happen by construction.")
        return BlockTargets([])
      }
      // It is only a SINGLE value in the current scope => take it.
      if terms.length() == 1 {
        return SingleTarget(terms[0])
      }
      self.context.abort(
        id.span,
        "Multiple values with the same name \{id_text(id)} in one scope. Values cannot be overloaded.",
      )
    }
  }
  BlockTargets([])
}

///|
/// Mutable variables are treated as values, not as blocks.
fn is_value_target(sym : Sym) -> Bool {
  sym.is_value_symbol() || sym.is_ref_binder()
}

///|
fn is_block_target(sym : Sym) -> Bool {
  sym.is_block_symbol() && !sym.is_ref_binder()
}

///|
/// Resolves a type name, storing the symbol on the identifier and on the type
/// tree (so later phases can look up either).
fn Namer::resolve_type_ref(
  self : Namer,
  id : IdRef,
  node_uid : Int32,
) -> Sym raise EffektError {
  match self.lookup_type(id.path, id.name) {
    Some(sym) => {
      self.context.assign_symbol(id.uid, sym)
      self.context.assign_symbol(node_uid, sym)
      sym
    }
    None => {
      self.context.abort(id.span, "Could not resolve type \{id_text(id)}")
      @symbols.Sym::wildcard()
    }
  }
}

///|
fn Namer::resolve_capture_id(self : Namer, id : IdRef) -> Sym raise EffektError {
  match self.lookup_capture(id.path, id.name) {
    Some(sym) => {
      self.context.assign_symbol(id.uid, sym)
      sym
    }
    None => {
      self.context.abort(id.span, "Could not resolve capture \{id_text(id)}")
      @symbols.Sym::wildcard()
    }
  }
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

///|
/// Runs `f` and records the resulting value type on the tree, so the typer can
/// pick it up later (upstream: `Context.annotateResolvedType`).
fn Namer::resolving_value_type(
  self : Namer,
  tpe : TypeTree,
  f : (TypeTree) -> ValueType raise EffektError,
) -> ValueType raise EffektError {
  let res = f(tpe)
  self.context.assign_value_type(tpe.uid, res)
  wellformed_value_type(self.context, res, tpe.span)
  res
}

///|
fn Namer::resolving_block_type(
  self : Namer,
  tpe : TypeTree,
  f : (TypeTree) -> BlockType raise EffektError,
) -> BlockType raise EffektError {
  let res = f(tpe)
  self.context.assign_block_type(tpe.uid, res)
  wellformed_block_type(self.context, res, tpe.span)
  res
}

///|
/// Resolves a type in value position.
///
/// We dealias on the fly so that aliases can never show up again in the
/// remaining compiler, exactly like upstream.
fn Namer::resolve_value_type(
  self : Namer,
  tpe : TypeTree,
  is_param : Bool,
) -> ValueType raise EffektError {
  self.resolving_value_type(tpe, t => {
    match t.kind {
      @source.TypeRef(id, args) => {
        let sym = self.resolve_type_ref(id, t.uid)
        match sym {
          @symbols.Sym::TypeAlias(alias) => {
            let targs = args.map(a => self.resolve_value_type(a, false))
            if alias.tparams.length() != targs.length() {
              self.context.abort(
                t.span,
                "Type alias \{alias.base.name.name} expects \{alias.tparams.length()} type arguments, but got \{targs.length()}.",
              )
            }
            TypeSubst::new(alias.tparams, targs).value_type(alias.tpe)
          }
          _ =>
            if sym.is_value_type_constructor() {
              @symbols.ValueTypeApp(
                sym,
                args.map(a => self.resolve_value_type(a, false)),
              )
            } else if sym.is_type_var() {
              if args.length() > 0 {
                self.context.abort(
                  t.span,
                  "Type variables cannot be applied, but received \{args.length()} arguments.",
                )
              }
              @symbols.ValueTypeRef(sym)
            } else {
              self.context.error(
                t.span,
                "Expected value type, but got block type \{sym.name().qualified_name()}.",
              )
              if sym.is_block_type_constructor() {
                self.context.info(
                  "Did you mean to box the interface \{sym.name().qualified_name()}, i.e. `\{sym.name().qualified_name()} at {}`?",
                )
              }
              // Dummy value type in order to aggregate more errors.
              @symbols.ValueTypeApp(@symbols.Sym::error_value_type(t.span), [])
            }
        }
      }
      @source.ValueTypeTree(tpe) => tpe
      @source.BoxedType(inner, capt) =>
        @symbols.BoxedType(
          self.resolve_block_type(inner, false),
          self.resolve_capture_set(capt),
        )
      _ => {
        self.context.error(
          t.span,
          "Expected value type, but got \{describe_type(t)}.",
        )
        match t.kind {
          @source.FunctionType(_, _, _, _, _) => {
            if is_param {
              self.context.info(
                "Did you mean to use braces in order to receive a block type `\{tree_text(t)}`?",
              )
            }
            self.context.info(
              "Did you mean to use a first-class, boxed function type `\{tree_text(t)} at {}`?",
            )
          }
          @source.Effectful(inner, effects) =>
            match inner.kind {
              @source.FunctionType(_, _, _, _, fun_effects) => {
                let combined = pretty_source_effect_set(
                  fun_effects.effs + effects.effs,
                )
                self.context.info(
                  "A function type cannot have multiple effect sets, did you mean to use `/ \{combined}` instead of `/ \{tree_text(inner)} / \{span_text(effects.span)}`?",
                )
              }
              _ => {
                if is_param {
                  self.context.info(
                    "Did you mean to use braces and a function type `() => \{tree_text(inner)} / \{span_text(effects.span)}`?",
                  )
                }
                self.context.info(
                  "Did you mean to use a first-class, boxed type `() => \{tree_text(inner)} at {} / \{span_text(effects.span)}`?",
                )
              }
            }
          _ => ()
        }
        // Dummy value type in order to aggregate more errors.
        @symbols.ValueTypeApp(@symbols.Sym::error_value_type(t.span), [])
      }
    }
  })
}

///|
/// Resolves a type in block position (function types and interfaces).
fn Namer::resolve_block_type(
  self : Namer,
  tpe : TypeTree,
  is_param : Bool,
) -> BlockType raise EffektError {
  self.resolving_block_type(tpe, t => {
    match t.kind {
      @source.FunctionType(_, _, _, _, _) => self.resolve_function_type(t)
      @source.BlockTypeTree(eff) => eff
      @source.TypeRef(_, _) => self.resolve_block_ref(t)
      _ => {
        self.context.error(
          t.span,
          "Expected block type, but got \{describe_type(t)}.",
        )
        match t.kind {
          @source.BoxedType(inner, _) => {
            if is_param {
              self.context.info(
                "Did you mean to use parentheses in order to receive a value type \{tree_text(t)}?",
              )
            }
            self.context.info(
              "Did you mean to use the block type \{tree_text(inner)} without `at ...`?",
            )
          }
          @source.Effectful(inner, effects) =>
            match inner.kind {
              @source.FunctionType(_, _, _, _, fun_effects) => {
                let combined = pretty_source_effect_set(
                  fun_effects.effs + effects.effs,
                )
                self.context.info(
                  "A function type cannot have multiple effect sets, did you mean to use `/ \{combined}` instead of `/ \{tree_text(inner)} / \{span_text(effects.span)}`?",
                )
              }
              _ =>
                self.context.info(
                  "Did you mean to use a function type () => \{tree_text(inner)} / \{span_text(effects.span)}?",
                )
            }
          _ => ()
        }
        // Dummy interface type in order to aggregate more errors.
        @symbols.InterfaceType(@symbols.Sym::error_block_type(t.span), [])
      }
    }
  })
}

///|
/// Resolves a (second-class) function type.
fn Namer::resolve_function_type(
  self : Namer,
  tpe : TypeTree,
) -> BlockType raise EffektError {
  self.resolving_block_type(tpe, t => {
    match t.kind {
      @source.FunctionType(tparams, vparams, bparams, ret, effects) =>
        self.in_local_scope(() => {
          let tps = tparams.map(tp => self.resolve_type_param(tp))
          let vps = vparams.map(v => self.resolve_value_type(v, false))
          // One capture parameter per block parameter, then one per effect.
          let caps : Array[Sym] = []
          let bps : Array[BlockType] = []
          for i = 0; i < bparams.length(); i = i + 1 {
            let (id, btype) = bparams[i]
            let name = match id {
              Some(i) => name_of_id(i)
              None => Name::anon()
            }
            caps.push(@symbols.Sym::capture_param(name))
            bps.push(self.resolve_block_type(btype, false))
          }
          let effs = self.resolve_effects(effects).distinct()
          for eff in @symbols.canonical_order(effs.effects) {
            let name = match eff.interface_name() {
              Some(n) => n
              None => Name::anon()
            }
            caps.push(@symbols.Sym::capture_param(name))
          }
          for cap in caps {
            self.bind_capture(cap)
          }
          let res = self.resolve_value_type(ret, false)
          @symbols.FunctionType(
            tps,
            caps.map(c => @symbols.CaptureSetOf([c])),
            vps,
            bps,
            res,
            effs,
          )
        })
      _ => {
        self.context.error(t.span, "Expected a function type.")
        @symbols.InterfaceType(@symbols.Sym::error_block_type(t.span), [])
      }
    }
  })
}

///|
/// Resolves a block reference into an interface type, potentially with effect
/// aliases on the top level.
fn Namer::resolve_with_aliases(
  self : Namer,
  tpe : TypeTree,
) -> Array[BlockType] raise EffektError {
  let resolved : Array[BlockType] = match tpe.kind {
    @source.TypeRef(id, args) => {
      let sym = self.resolve_type_ref(id, tpe.uid)
      match sym {
        @symbols.Sym::EffectAlias(alias) => {
          if alias.tparams.length() != args.length() {
            self.context.abort(
              tpe.span,
              "Effect alias \{alias.base.name.name} expects \{alias.tparams.length()} type arguments, but got \{args.length()}.",
            )
          }
          let targs = args.map(a => self.resolve_value_type(a, false))
          let subst = TypeSubst::new(alias.tparams, targs)
          alias.effs.to_list().map(e => subst.block_type(e))
        }
        _ =>
          if sym.is_block_type_constructor() {
            [
              @symbols.InterfaceType(
                sym,
                args.map(a => self.resolve_value_type(a, false)),
              ),
            ]
          } else {
            self.context.error(
              tpe.span,
              "Expected an interface type, but got value type \{sym.name().qualified_name()}.",
            )
            // Dummy interface type in order to aggregate more errors.
            [
              @symbols.InterfaceType(@symbols.Sym::error_block_type(tpe.span), []),
            ]
          }
      }
    }
    _ => {
      self.context.error(tpe.span, "Expected an interface type.")
      [@symbols.InterfaceType(@symbols.Sym::error_block_type(tpe.span), [])]
    }
  }
  for r in resolved {
    wellformed_block_type(self.context, r, tpe.span)
  }
  resolved
}

///|
fn Namer::resolve_block_ref(
  self : Namer,
  tpe : TypeTree,
) -> BlockType raise EffektError {
  self.resolving_block_type(tpe, t => {
    let resolved = self.resolve_with_aliases(t)
    if resolved.length() == 0 {
      self.context.abort(
        t.span,
        "Expected a single interface type, not an empty effect set.",
      )
      @symbols.InterfaceType(@symbols.Sym::error_block_type(t.span), [])
    } else if resolved.length() == 1 {
      resolved[0]
    } else {
      self.context.abort(
        t.span,
        "Expected a single interface type, arbitrary effect aliases are not allowed.",
      )
      @symbols.InterfaceType(@symbols.Sym::error_block_type(t.span), [])
    }
  })
}

///|
fn Namer::resolve_effects(
  self : Namer,
  effs : EffectsTree,
) -> Effects raise EffektError {
  let all : Array[BlockType] = []
  for eff in effs.effs {
    for resolved in self.resolve_with_aliases(eff) {
      all.push(resolved)
    }
  }
  @symbols.Effects::new(all)
}

///|
/// Resolves a type together with its effects, i.e. `T / {E}`.
fn Namer::resolve_effectful(
  self : Namer,
  tpe : TypeTree,
) -> (ValueType, Effects) raise EffektError {
  match tpe.kind {
    @source.Effectful(inner, effs) =>
      (self.resolve_value_type(inner, false), self.resolve_effects(effs))
    // Synthesized annotations need not be wrapped in an `Effectful`.
    _ => (self.resolve_value_type(tpe, false), @symbols.Effects::empty())
  }
}

///|
fn Namer::resolve_capture_set(
  self : Namer,
  capt : CaptureSetTree,
) -> Captures raise EffektError {
  let syms : Array[Sym] = []
  for id in capt.captures {
    syms.push(self.resolve_capture_id(id))
  }
  @symbols.CaptureSetOf(@symbols.dedup_syms(syms))
}

// ---------------------------------------------------------------------------
// Holes and diagnostics
// ---------------------------------------------------------------------------

///|
/// Generates a fresh hole id that is unique in the current module: the names of
/// the enclosing definitions, disambiguated by a counter that increments in
/// depth-first order as the namer traverses the syntax tree.
fn Namer::fresh_hole_id(self : Namer) -> String {
  let prefix = if self.parent_definitions.length() == 0 {
    "hole"
  } else {
    let parts : Array[String] = []
    for d in self.parent_definitions {
      parts.push(def_id_name(d))
    }
    parts.join("_")
  }
  let count = match self.hole_count.get(prefix) {
    Some(c) => c
    None => 0
  }
  self.hole_count.set(prefix, count + 1)
  "\{prefix}\{count}"
}

///|
/// The name of the identifier a definition binds, without creating a new
/// identifier for `ExternInclude`.
fn def_id_name(d : Def) -> String {
  match d.kind {
    @source.FunDef(id, _, _, _, _, _, _) => id.name
    @source.ValDef(id, _, _) => id.name
    @source.RegDef(id, _, _, _) => id.name
    @source.VarDef(id, _, _) => id.name
    @source.DefDef(id, _, _, _) => id.name
    @source.NamespaceDef(id, _) => id.name
    @source.InterfaceDef(id, _, _) => id.name
    @source.DataDef(id, _, _) => id.name
    @source.RecordDef(id, _, _) => id.name
    @source.TypeDef(id, _, _) => id.name
    @source.EffectDef(id, _, _) => id.name
    @source.ExternType(id, _, _) => id.name
    @source.ExternDef(id, _, _, _, _, _, _) => id.name
    @source.ExternResource(id, _) => id.name
    @source.ExternInterface(id, _, _) => id.name
    @source.ExternInclude(_, _, _) => ""
  }
}

///|
/// The name of a type tree for diagnostics. Without source text (synthesized
/// nodes), we fall back to a description of the tree.
fn tree_text(t : TypeTree) -> String {
  match t.span.text() {
    Some(text) => text
    None => "<type>"
  }
}

///|
fn span_text(span : Span) -> String {
  match span.text() {
    Some(text) => text
    None => "<effect set>"
  }
}

///|
/// Used for nice error messages in `resolve_value_type` / `resolve_block_type`.
fn describe_type(t : TypeTree) -> String {
  match t.kind {
    @source.TypeRef(_, _) => "a type reference \{tree_text(t)}"
    @source.BoxedType(_, _) => "a boxed type \{tree_text(t)}"
    @source.FunctionType(_, _, _, _, _) =>
      "a second-class function type \{tree_text(t)}"
    @source.Effectful(_, _) => "a type-and-effect annotation \{tree_text(t)}"
    @source.ValueTypeTree(tpe) => "a value type tree \{value_type_text(tpe)}"
    @source.BlockTypeTree(eff) => "a block type tree \{block_type_text(eff)}"
  }
}

///|
fn pretty_source_effect_set(effects : Array[TypeTree]) -> String {
  let texts = effects.map(e => tree_text(e))
  if texts.length() == 0 {
    "{}"
  } else if texts.length() == 1 {
    texts[0]
  } else {
    "{\{texts.join(", ")}}"
  }
}

///|
/// Renders a resolved value type for diagnostics.
fn value_type_text(tpe : ValueType) -> String {
  match tpe {
    @symbols.ValueTypeRef(x) => x.name().qualified_name()
    @symbols.ValueTypeApp(ctor, args) =>
      if args.length() == 0 {
        ctor.name().qualified_name()
      } else {
        "\{ctor.name().qualified_name()}[\{args.map(a => value_type_text(a)).join(", ")}]"
      }
    @symbols.BoxedType(inner, _) => "(\{block_type_text(inner)} at {...})"
  }
}

///|
/// Renders a resolved block type for diagnostics.
fn block_type_text(tpe : BlockType) -> String {
  match tpe {
    @symbols.InterfaceType(ctor, args) =>
      if args.length() == 0 {
        ctor.name().qualified_name()
      } else {
        "\{ctor.name().qualified_name()}[\{args.map(a => value_type_text(a)).join(", ")}]"
      }
    @symbols.FunctionType(_, _, _, _, _, _) => "<function type>"
  }
}
