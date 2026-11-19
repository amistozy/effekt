// The unification state.
//
// Mirrors `effekt/typer/Unification.scala` and `effekt/typer/Constraints.scala`.
//
// Upstream keeps the solution of a unification variable *inside* the variable
// (or in a `Constraints` object keyed by variable identity). Here the payloads
// of `Sym::UnificationVar` / `Sym::CaptUnificationVar` are immutable, so the
// whole solution table lives in this struct, keyed by the variable's `uid`.
//
// NOTE: fresh unification variables are represented as `Sym::type_param` /
// `Sym::capture_param` symbols with a `?` prefix. Which of those symbols are
// unification variables (as opposed to rigid type parameters) is recorded in
// the tables below (`var_of` / `capt_var`).

///|
pub struct Unification {
  /// Solution of type unification variables (already pruned).
  types : Map[Int32, ValueType]
  /// Solution of capture unification variables.
  capts : Map[Int32, Captures]
  /// Concrete *lower* bounds of capture unification variables.
  lower : Map[Int32, Array[Sym]]
  /// Concrete *upper* bounds of capture unification variables. Absence means
  /// "no bound learned yet" (i.e. top).
  upper : Map[Int32, Array[Sym]]
  /// Subcapturing links `(lower, upper, filter)`; see `propagate`.
  links : Array[(Int32, Int32, Array[Sym])]
  /// The type parameter a unification variable was instantiated for.
  var_of : Map[Int32, Sym]
  /// Capture unification variables.
  capt_var : Map[Int32, Sym]
}

///|
pub fn Unification::Unification() -> Unification {
  {
    types: Map([]),
    capts: Map([]),
    lower: Map([]),
    upper: Map([]),
    links: [],
    var_of: Map([]),
    capt_var: Map([]),
  }
}

///|
pub fn Unification::copy(self : Unification) -> Unification {
  {
    types: self.types.copy(),
    capts: self.capts.copy(),
    lower: self.lower.copy(),
    upper: self.upper.copy(),
    links: self.links.copy(),
    // `var_of`/`capt_var` are only ever *read by key* and only grow: a variable
    // created by a rolled-back candidate is never looked up again (every fresh
    // variable gets a fresh uid), so a snapshot can share them instead of
    // copying two module-wide tables.
    var_of: self.var_of,
    capt_var: self.capt_var,
  }
}

// Creating fresh variables
// ------------------------

///|
/// A fresh *value type* unification variable. `underlying` is the type
/// parameter it was instantiated for (used for error messages).
fn Unification::fresh_type_var(self : Unification, underlying : Sym) -> Sym {
  let x = Sym::type_param(Name::local(underlying.name().name), Span::missing())
  self.var_of.set(x.uid(), underlying)
  x
}

///|
/// A fresh *capture* unification variable.
///
/// Upstream's `CaptUnificationVar` is always called `?C` (`val name =
/// Name.local("?C")`); the role only shows up in its `toString`, which no
/// diagnostic uses. The parameter is kept (unused) to say at the call site what
/// the variable stands for.
fn Unification::fresh_capt_var(self : Unification, _role : String) -> Sym {
  let x = Sym::capture_param(Name::local("?C"))
  self.capt_var.set(x.uid(), x)
  x
}

///|
/// Is `x` one of the unification variables created by this table?
pub fn Unification::is_type_var(self : Unification, x : Sym) -> Bool {
  self.var_of.contains(x.uid())
}

///|
fn Unification::is_capt_var(self : Unification, x : Sym) -> Bool {
  self.capt_var.contains(x.uid())
}

///|
pub fn Unification::underlying(self : Unification, x : Sym) -> Sym {
  self.var_of.get(x.uid()).unwrap_or(x)
}

// Substitution
// ------------

///|
fn Unification::prune_value(self : Unification, t : ValueType) -> ValueType {
  match t {
    @symbols.ValueType::ValueTypeRef(x) =>
      match self.types.get(x.uid()) {
        Some(s) => self.prune_value(s)
        None => t
      }
    @symbols.ValueType::ValueTypeApp(c, args) =>
      @symbols.ValueType::ValueTypeApp(c, args.map(a => self.prune_value(a)))
    @symbols.ValueType::BoxedType(b, c) =>
      @symbols.ValueType::BoxedType(self.prune_block(b), self.prune_captures(c))
  }
}

///|
fn Unification::prune_block(self : Unification, t : BlockType) -> BlockType {
  match t {
    @symbols.BlockType::InterfaceType(c, args) =>
      @symbols.BlockType::InterfaceType(c, args.map(a => self.prune_value(a)))
    @symbols.BlockType::FunctionType(cps, capts, vps, bps, ret, effs) =>
      @symbols.BlockType::FunctionType(
        cps,
        capts.map(c => self.prune_captures(c)),
        vps.map(v => self.prune_value(v)),
        bps.map(b => self.prune_block(b)),
        self.prune_value(ret),
        Effects(effs.effects.map(e => self.prune_block(e))),
      )
  }
}

///|
fn Unification::prune_captures(self : Unification, c : Captures) -> Captures {
  match c {
    @symbols.Captures::CaptVar(x) =>
      match self.capts.get(x.uid()) {
        Some(s) => self.prune_captures(s)
        None => c
      }
    @symbols.Captures::CaptureSetOf(cs) =>
      @symbols.captures_union(cs, s => {
        self.capts.get(s.uid()).map(sol => self.prune_captures(sol))
      })
  }
}

///|
fn Unification::prune_effects(self : Unification, effs : Effects) -> Effects {
  Effects(effs.effects.map(e => self.prune_block(e)))
}

// Type constraints
// ----------------

///|
/// Records that `x` is `t`. Assumes the caller already checked consistency.
pub fn Unification::set_type(
  self : Unification,
  x : Sym,
  t : ValueType,
) -> Unit {
  let t = self.prune_value(t)
  match t {
    @symbols.ValueType::ValueTypeRef(y) =>
      if y.uid() != x.uid() && self.is_type_var(y) {
        // Union by smallest uid; this makes the substitution acyclic.
        let lo = if x.uid() < y.uid() { x } else { y }
        let hi = if x.uid() < y.uid() { y } else { x }
        match self.types.get(lo.uid()) {
          Some(sol) => self.types.set(hi.uid(), sol)
          None => self.types.set(hi.uid(), @symbols.ValueType::ValueTypeRef(lo))
        }
        self.update_substitution()
      } else if y.uid() == x.uid() {
        ()
      } else {
        self.types.set(x.uid(), t)
      }
    _ => {
      self.types.set(x.uid(), t)
      self.update_substitution()
    }
  }
}

///|
/// Re-normalises the substitution, so that solutions never mention solved
/// variables (`{?B} -> Box[?R]` becomes `{?B} -> Box[Int]` once `?R := Int`).
///
/// This runs after every `set_type`, so it must not rebuild solutions that
/// cannot change: the `mentions_*` test below is a cheap walk without
/// allocation, and the updates are collected and applied after the iteration
/// (the substitution reads the live tables instead of copying them).
fn Unification::update_substitution(self : Unification) -> Unit {
  let subst : Substitutions = { values: self.types, captures: self.capts, }
  let type_updates : Array[(Int32, ValueType)] = []
  for k, v in self.types {
    if self.mentions_solution(v) {
      let updated = subst.substitute_value(v)
      if !(updated == v) {
        type_updates.push((k, updated))
      }
    }
  }
  let capt_updates : Array[(Int32, Captures)] = []
  for k, v in self.capts {
    if self.mentions_solved_capture(v) {
      let updated = subst.substitute_captures(v)
      if !(updated == v) {
        capt_updates.push((k, updated))
      }
    }
  }
  for (k, v) in type_updates {
    self.types.set(k, v)
  }
  for (k, v) in capt_updates {
    self.capts.set(k, v)
  }
}

///|
/// Whether substituting `t` could change it: it mentions a type variable that
/// has a solution (directly, or inside a block type, an effect or a capture
/// set).
fn Unification::mentions_solution(self : Unification, t : ValueType) -> Bool {
  match t {
    @symbols.ValueType::ValueTypeRef(x) => self.types.contains(x.uid())
    @symbols.ValueType::ValueTypeApp(_, args) =>
      args.any(a => self.mentions_solution(a))
    @symbols.ValueType::BoxedType(b, c) =>
      self.mentions_solution_in_block(b) || self.mentions_solved_capture(c)
  }
}

///|
fn Unification::mentions_solution_in_block(
  self : Unification,
  t : BlockType,
) -> Bool {
  match t {
    @symbols.BlockType::InterfaceType(_, args) =>
      args.any(a => self.mentions_solution(a))
    @symbols.BlockType::FunctionType(_, capts, vps, bps, ret, effs) =>
      capts.any(c => self.mentions_solved_capture(c)) ||
      vps.any(v => self.mentions_solution(v)) ||
      bps.any(b => self.mentions_solution_in_block(b)) ||
      self.mentions_solution(ret) ||
      effs.effects.any(e => self.mentions_solution_in_block(e))
  }
}

///|
/// Whether substituting `c` could change it: it mentions a capture variable
/// that has a solution.
fn Unification::mentions_solved_capture(
  self : Unification,
  c : Captures,
) -> Bool {
  match c {
    @symbols.Captures::CaptVar(x) => self.capts.contains(x.uid())
    @symbols.Captures::CaptureSetOf(cs) =>
      cs.any(s => self.capts.contains(s.uid()))
  }
}

// Capture constraints
// -------------------

///|
fn Unification::lower_of(self : Unification, uid : Int32) -> Array[Sym] {
  self.lower.get(uid).unwrap_or([])
}

///|
/// The diagnostic for capture bounds that are not included in the solution
/// (upstream's `Constraints.checkConsistency`).
fn captures_not_allowed(diff : Array[Sym]) -> String {
  "Not allowed \{@symbols.Captures::CaptureSetOf(diff)}"
}

///|
/// Adds a subcapturing link `lo - filter <: hi`.
fn Unification::link(
  self : Unification,
  lo : Int32,
  hi : Int32,
  filter : Array[Sym],
) -> Unit {
  if lo == hi {
    return
  }
  self.links.push((lo, hi, filter))
}

///|
/// Propagates all known bounds along the links until a fixed point is reached.
/// Returns a diagnostic if the constraint system became inconsistent.
fn Unification::propagate(self : Unification) -> String? {
  let mut rounds = 0
  let mut changed = true
  while changed && rounds < 200 {
    changed = false
    rounds = rounds + 1
    for (a, b, filter) in self.links {
      // lower(a) - filter flows into lower(b). The lower bound of `b` is copied
      // at most once per link and written back at the end, instead of looking
      // it up and copying it for every propagated capture.
      if self.lower.get(a) is Some(la) {
        let mut lower_b : Array[Sym]? = None
        for c in la {
          if filter.contains(c) {
            continue
          }
          let present = match lower_b {
            Some(lb) => lb.contains(c)
            None =>
              match self.lower.get(b) {
                Some(lb) => lb.contains(c)
                None => false
              }
          }
          if !present {
            let lb = match lower_b {
              Some(lb) => lb
              None =>
                match self.lower.get(b) {
                  Some(lb) => lb.copy()
                  None => []
                }
            }
            lb.push(c)
            lower_b = Some(lb)
            changed = true
          }
        }
        if lower_b is Some(lb) {
          self.lower.set(b, lb)
        }
      }
      // upper(b) + filter flows into upper(a)
      if self.upper.get(b) is Some(ub) {
        let target : Array[Sym] = []
        target.append(ub)
        for c in filter {
          if !target.contains(c) {
            target.push(c)
          }
        }
        match self.upper.get(a) {
          None => {
            self.upper.set(a, target)
            changed = true
          }
          Some(ua) =>
            // Only build the intersection when it can shrink the bound.
            if !ua.all(c => target.contains(c)) {
              self.upper.set(a, ua.filter(c => target.contains(c)))
              changed = true
            }
        }
      }
    }
  }
  // consistency of all nodes
  for uid, lo in self.lower {
    if self.upper.get(uid) is Some(up) {
      let diff = lo.filter(c => !up.contains(c))
      // Upstream's `Constraints.checkConsistency`.
      guard diff.is_empty() else { return Some(captures_not_allowed(diff)) }
    }
  }
  None
}

///|
/// `bounds <: ?x`
fn Unification::require_lower(
  self : Unification,
  bounds : ArrayView[Sym],
  x : Sym,
) -> String? {
  match self.capts.get(x.uid()) {
    Some(sol) => {
      let solved = sol.to_array()
      let diff = bounds.filter(c => !solved.contains(c))
      guard diff.is_empty() else { Some(captures_not_allowed(diff)) }
      None
    }
    None => {
      if self.upper.get(x.uid()) is Some(up) {
        let diff = bounds.filter(c => !up.contains(c))
        guard diff.is_empty() else { return Some(captures_not_allowed(diff)) }
      }
      let current = self.lower_of(x.uid())
      let next = current.copy()
      for c in bounds {
        if !next.contains(c) {
          next.push(c)
        }
      }
      self.lower.set(x.uid(), next)
      self.propagate()
    }
  }
}

///|
/// `?x <: bounds`
fn Unification::require_upper(
  self : Unification,
  bounds : ArrayView[Sym],
  x : Sym,
) -> String? {
  match self.capts.get(x.uid()) {
    Some(sol) => {
      let solved = sol.to_array()
      let diff = solved.filter(c => !bounds.contains(c))
      guard diff.is_empty() else { Some(captures_not_allowed(diff)) }
      None
    }
    None => {
      if self.lower.get(x.uid()) is Some(lo) {
        let diff = lo.filter(c => !bounds.contains(c))
        guard diff.is_empty() else { return Some(captures_not_allowed(diff)) }
      }
      match self.upper.get(x.uid()) {
        Some(up) => {
          let intersection = up.filter(c => bounds.contains(c))
          self.upper.set(x.uid(), intersection)
        }
        None => self.upper.set(x.uid(), bounds.to_owned())
      }
      self.propagate()
    }
  }
}

///|
/// Solves an out-of-scope capture variable with its lower bound.
fn Unification::solve_capt_var(self : Unification, x : Sym) -> String? {
  if self.capts.contains(x.uid()) {
    return None
  }
  let bounds = self.lower_of(x.uid())
  if self.upper.get(x.uid()) is Some(up) {
    let diff = bounds.filter(c => !up.contains(c))
    guard diff.is_empty() else { return Some(captures_not_allowed(diff)) }
  }
  self.capts.set(x.uid(), @symbols.Captures::CaptureSetOf(bounds))
  None
}

///|
/// Solves capture variables that went out of scope.
fn Unification::solve_all(
  self : Unification,
  xs : ArrayView[Sym],
) -> Array[String] {
  let errors : Array[String] = []
  for x in xs {
    if self.solve_capt_var(x) is Some(msg) {
      errors.push(msg)
    }
  }
  errors
}

// ---------------------------------------------------------------------------
// Unification scopes
// ---------------------------------------------------------------------------

///|
/// Every fresh unification variable is associated with a scope. When a scope is
/// left, all its variables are solved (capture variables take their lower
/// bound) or reported as not inferable (type variables).
pub(all) enum UnifScope {
  GlobalScope
  LocalScope(Array[Sym], Array[Sym], UnifScope)
}

///|
fn UnifScope::type_vars(self : UnifScope) -> Array[Sym] {
  match self {
    GlobalScope => []
    LocalScope(ts, _, _) => ts
  }
}

///|
fn UnifScope::capt_vars(self : UnifScope) -> Array[Sym] {
  match self {
    GlobalScope => []
    LocalScope(_, cs, _) => cs
  }
}

///|
pub fn UnifScope::parent(self : UnifScope) -> UnifScope {
  match self {
    GlobalScope => GlobalScope
    LocalScope(_, _, p) => p
  }
}

///|
/// Registers a fresh type variable in the current scope.
fn UnifScope::register_type_var(self : UnifScope, x : Sym) -> Unit {
  if self is LocalScope(ts, _, _) {
    ts.push(x)
  }
}

///|
/// Registers a fresh capture variable in the current scope.
fn UnifScope::register_capt_var(self : UnifScope, x : Sym) -> Unit {
  if self is LocalScope(_, cs, _) {
    cs.push(x)
  }
}
