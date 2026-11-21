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
  types : CowMap[ValueType]
  /// Solution of capture unification variables.
  capts : CowMap[Captures]
  /// Concrete *lower* bounds of capture unification variables.
  lower : CowMap[Array[Sym]]
  /// Concrete *upper* bounds of capture unification variables. Absence means
  /// "no bound learned yet" (i.e. top).
  upper : CowMap[Array[Sym]]
  /// Subcapturing links `(lower, upper, filter)`; see `propagate`.
  links : Array[(Int32, Int32, Array[Sym])]
  /// The solutions of `types` that mention some type variable. Solving one
  /// variable can only change those (upstream's `withUnknowns`, see
  /// `update_substitution`), so the set is what the re-normalisation iterates.
  type_candidates : Map[Int32, Bool]
  /// The solutions of `capts` that mention some capture variable.
  capt_candidates : Map[Int32, Bool]
  /// The variables that some link reads as its lower end. A bound of a variable
  /// that is not in here flows nowhere, which is what keeps most bound updates
  /// from running the propagation at all (see `propagate_lower_of`).
  lower_ends : Map[Int32, Bool]
  /// The variables that some link reads as its upper end.
  upper_ends : Map[Int32, Bool]
  /// The type parameter a unification variable was instantiated for.
  var_of : Map[Int32, Sym]
  /// Capture unification variables.
  capt_var : Map[Int32, Sym]
}

///|
pub fn Unification::Unification() -> Unification {
  {
    types: CowMap::new(),
    capts: CowMap::new(),
    lower: CowMap::new(),
    upper: CowMap::new(),
    links: [],
    type_candidates: Map([]),
    capt_candidates: Map([]),
    lower_ends: Map([]),
    upper_ends: Map([]),
    var_of: Map([]),
    capt_var: Map([]),
  }
}

///|
pub fn Unification::copy(self : Unification) -> Unification {
  {
    types: self.types.snapshot(),
    capts: self.capts.snapshot(),
    lower: self.lower.snapshot(),
    upper: self.upper.snapshot(),
    links: self.links.copy(),
    // Unlike the marks below, the candidate sets *shrink*: a candidate whose
    // solution became concrete leaves the set, and a rolled-back candidate could
    // leave a solution that mentions a variable out of it. They are small (the
    // solutions that still mention a variable), so they are copied.
    type_candidates: self.type_candidates.copy(),
    capt_candidates: self.capt_candidates.copy(),
    // `lower_ends`/`upper_ends`/`var_of`/`capt_var` are only ever *read by key*
    // and only grow, so a snapshot can share them instead of copying four
    // module-wide tables. A variable only a rolled-back candidate linked keeps
    // its mark, which costs one propagation that finds nothing to do; a *missing*
    // mark would lose a propagation, and that cannot happen while the marks and
    // the links that need them are written together.
    lower_ends: self.lower_ends,
    upper_ends: self.upper_ends,
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
          Some(sol) => self.set_solution(hi.uid(), sol)
          None =>
            self.set_solution(hi.uid(), @symbols.ValueType::ValueTypeRef(lo))
        }
        self.update_substitution()
      } else if y.uid() == x.uid() {
        ()
      } else {
        self.set_solution(x.uid(), t)
      }
    _ => {
      self.set_solution(x.uid(), t)
      self.update_substitution()
    }
  }
}

///|
/// Re-normalises the substitution, so that solutions never mention solved
/// variables (`{?B} -> Box[?R]` becomes `{?B} -> Box[Int]` once `?R := Int`).
///
/// This runs after every solution, so it must not look at solutions that cannot
/// change. Only the ones that still mention *some* variable can: a solution made
/// of concrete types is already normal (no substitution can rewrite it), and it
/// leaves `type_candidates` when it is written. That is upstream's
/// `withUnknowns` set, which the port was missing — it re-walked the whole
/// substitution table after every solution and found something to rewrite in
/// about one entry in a thousand.
///
/// The updates are collected and applied after the iteration: the substitution
/// reads the live tables, so it must not see the writes of this pass.
fn Unification::update_substitution(self : Unification) -> Unit {
  let subst : Substitutions = {
    values: self.types.view(),
    captures: self.capts.view(),
  }
  let type_updates : Array[(Int32, ValueType)] = []
  for k, _ in self.type_candidates {
    // the candidate is only dropped when it is rewritten, so it is still there
    if self.types.get(k) is Some(v) && self.mentions_solution(v) {
      let updated = subst.substitute_value(v)
      if !(updated == v) {
        type_updates.push((k, updated))
      }
    }
  }
  let capt_updates : Array[(Int32, Captures)] = []
  for k, _ in self.capt_candidates {
    if self.capts.get(k) is Some(v) && self.mentions_solved_capture(v) {
      let updated = subst.substitute_captures(v)
      if !(updated == v) {
        capt_updates.push((k, updated))
      }
    }
  }
  for (k, v) in type_updates {
    self.set_solution(k, v)
  }
  for (k, v) in capt_updates {
    self.set_capt_solution(k, v)
  }
}

///|
/// Whether `t` mentions a type variable at all, solved or not: that is what makes
/// a solution a *candidate* for `update_substitution`, see the note there.
fn Unification::mentions_var(self : Unification, t : ValueType) -> Bool {
  match t {
    @symbols.ValueType::ValueTypeRef(_) => true
    @symbols.ValueType::ValueTypeApp(_, args) =>
      args.any(a => self.mentions_var(a))
    @symbols.ValueType::BoxedType(b, c) =>
      self.mentions_var_in_block(b) || self.mentions_var_in_captures(c)
  }
}

///|
fn Unification::mentions_var_in_block(
  self : Unification,
  t : BlockType,
) -> Bool {
  match t {
    @symbols.BlockType::InterfaceType(_, args) =>
      args.any(a => self.mentions_var(a))
    @symbols.BlockType::FunctionType(_, capts, vps, bps, ret, effs) =>
      capts.any(c => self.mentions_var_in_captures(c)) ||
      vps.any(v => self.mentions_var(v)) ||
      bps.any(b => self.mentions_var_in_block(b)) ||
      self.mentions_var(ret) ||
      effs.effects.any(e => self.mentions_var_in_block(e))
  }
}

///|
/// Whether `c` mentions a capture variable, solved or not. A capture set holds
/// symbols, so each of them has to be asked: a capability is not a variable.
fn Unification::mentions_var_in_captures(
  self : Unification,
  c : Captures,
) -> Bool {
  match c {
    @symbols.Captures::CaptVar(_) => true
    @symbols.Captures::CaptureSetOf(cs) => {
      for s in cs {
        if self.capt_var.contains(s.uid()) {
          return true
        }
      }
      false
    }
  }
}

///|
/// Records the solution of `x` and keeps the candidate set of
/// `update_substitution` in step: a solution that mentions no variable can never
/// be rewritten again, so it does not have to be looked at.
fn Unification::set_solution(
  self : Unification,
  uid : Int32,
  t : ValueType,
) -> Unit {
  self.types.set(uid, t)
  if self.mentions_var(t) {
    self.type_candidates.set(uid, true)
  } else {
    self.type_candidates.remove(uid)
  }
}

///|
/// Records the solution of a capture variable, the same way.
fn Unification::set_capt_solution(
  self : Unification,
  uid : Int32,
  c : Captures,
) -> Unit {
  self.capts.set(uid, c)
  if self.mentions_var_in_captures(c) {
    self.capt_candidates.set(uid, true)
  } else {
    self.capt_candidates.remove(uid)
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
    // a loop rather than `any`: this runs inside the constraint solver, once per
    // capture and per round, and the closure would be allocated each time
    @symbols.Captures::CaptureSetOf(cs) => {
      for s in cs {
        if self.capts.contains(s.uid()) {
          return true
        }
      }
      false
    }
  }
}

// Capture constraints
// -------------------

///|
fn Unification::lower_of(self : Unification, uid : Int32) -> Array[Sym] {
  self.lower.get(uid).unwrap_or([])
}

///|
/// The captures of `lower` that `upper` does not allow. `None` when `lower` is
/// included in `upper`, which is the case that has to cost nothing: every
/// consistency check here runs over bounds that were just propagated, and most
/// of them are consistent.
fn disallowed(lower : ArrayView[Sym], upper : ArrayView[Sym]) -> Array[Sym]? {
  let n = lower.length()
  let mut first = -1
  for i in 0..<n {
    if !upper.contains(lower[i]) {
      first = i
      break
    }
  }
  guard first >= 0 else { return None }
  // Collecting the tail keeps the order of `lower` (nothing before `first` is
  // disallowed), which is what the message prints. This is the failing path, so
  // it is the only one that allocates.
  let diff : Array[Sym] = []
  for i in first..<n {
    let c = lower[i]
    if !upper.contains(c) {
      diff.push(c)
    }
  }
  Some(diff)
}

///|
/// The diagnostic for capture bounds that are not included in the solution
/// (upstream's `Constraints.checkConsistency`).
fn captures_not_allowed(diff : Array[Sym]) -> String {
  "Not allowed \{@symbols.Captures::CaptureSetOf(diff)}"
}

///|
/// `target ∪ (items - minus)`, or `None` when that would add nothing.
///
/// Both places that grow a bound need the same three things: the items a link
/// carries are cut down by the link's filter, what is left is appended only when
/// the target does not have it yet, and the copy of the target happens with the
/// first item that is genuinely new. That copy matters: a propagation round
/// visits every link and almost none of them adds a capture.
fn added_to(
  target : Array[Sym]?,
  items : ArrayView[Sym],
  minus : ArrayView[Sym],
) -> Array[Sym]? {
  let mut added : Array[Sym]? = None
  for c in items {
    if minus.contains(c) {
      continue
    }
    let present = match added {
      Some(out) => out.contains(c)
      None =>
        match target {
          Some(out) => out.contains(c)
          None => false
        }
    }
    if !present {
      let out = match added {
        Some(out) => out
        None =>
          match target {
            Some(out) => out.copy()
            None => []
          }
      }
      out.push(c)
      added = Some(out)
    }
  }
  added
}

///|
/// Adds a subcapturing link `lo - filter <: hi`.
fn Unification::link(
  self : Unification,
  lo : Int32,
  hi : Int32,
  filter : Array[Sym],
) -> Unit {
  guard lo != hi else { return }
  self.links.push((lo, hi, filter))
  self.lower_ends.set(lo, true)
  self.upper_ends.set(hi, true)
}

///|
/// Adds the link and propagates it — unless neither end carries a bound *yet*,
/// in which case the link cannot add anything now: an empty lower end has
/// nothing to pass on, and an absent upper end has nothing to pass back. The
/// link stays in `links`, and the bound that arrives later is what makes the
/// propagation run (see `propagate_lower_of` / `propagate_upper_of`).
fn Unification::link_and_propagate(
  self : Unification,
  lo : Int32,
  hi : Int32,
  filter : Array[Sym],
) -> String? {
  let carries = self.lower.get(lo) is Some(_) || self.upper.get(hi) is Some(_)
  self.link(lo, hi, filter)
  guard carries else { return None }
  self.propagate()
}

///|
/// Runs the propagation after `lower(uid)` was extended, unless no link reads
/// that bound: then nothing can have flowed and the fixpoint is still the
/// fixpoint.
fn Unification::propagate_lower_of(self : Unification, uid : Int32) -> String? {
  guard self.lower_ends.contains(uid) else { return None }
  self.propagate()
}

///|
/// The same for a bound that was just restricted in `upper`.
fn Unification::propagate_upper_of(self : Unification, uid : Int32) -> String? {
  guard self.upper_ends.contains(uid) else { return None }
  self.propagate()
}

///|
/// Checks that the bounds of `uid` do not exclude each other, returning the
/// diagnostic of upstream's `Constraints.checkConsistency` if they do.
///
/// This runs at the point where a bound is *written*, not once over the whole
/// system: the invariant holds before the write, so the only pair that can have
/// become inconsistent is the one that just changed.
fn Unification::check_consistency(self : Unification, uid : Int32) -> String? {
  guard self.lower.get(uid) is Some(lo) else { return None }
  guard self.upper.get(uid) is Some(up) else { return None }
  disallowed(lo, up).map(captures_not_allowed)
}

///|
/// Propagates all known bounds along the links until a fixed point is reached.
/// Returns a diagnostic if the constraint system became inconsistent.
///
/// The consistency check runs on write: a system that was consistent before the
/// call can only become inconsistent where this call changes a bound, so the
/// pass does not have to re-walk every node afterwards. The first violation
/// found is reported after the fixpoint has run to completion, so that a
/// failure leaves the same bounds behind as a successful call would.
fn Unification::propagate(self : Unification) -> String? {
  let mut violation : String? = None
  let mut rounds = 0
  let mut changed = true
  while changed && rounds < 200 {
    changed = false
    rounds += 1
    for (a, b, filter) in self.links {
      // lower(a) - filter flows into lower(b)
      if self.lower.get(a) is Some(la) {
        if added_to(self.lower.get(b), la, filter) is Some(lb) {
          self.lower.set(b, lb)
          changed = true
          if violation is None {
            violation = self.check_consistency(b)
          }
        }
      }
      // upper(b) + filter flows into upper(a)
      if self.upper.get(b) is Some(ub) {
        let existing = self.upper.get(a)
        // The union is only built when it can shrink the bound: every capture of
        // `upper(a)` that `upper(b)` does not have is either filtered out here
        // or keeps the bound as it is.
        let shrinks = match existing {
          Some(ua) => ua.any(c => !ub.contains(c) && !filter.contains(c))
          None => true
        }
        if shrinks {
          let target : Array[Sym] = []
          target.append(ub)
          for c in filter {
            if !target.contains(c) {
              target.push(c)
            }
          }
          self.upper.set(
            a,
            match existing {
              Some(ua) => ua.filter(c => target.contains(c))
              None => target
            },
          )
          changed = true
          if violation is None {
            violation = self.check_consistency(a)
          }
        }
      }
    }
  }
  violation
}

///|
/// `bounds <: ?x`
fn Unification::require_lower(
  self : Unification,
  bounds : ArrayView[Sym],
  x : Sym,
) -> String? {
  match self.capts.get(x.uid()) {
    Some(sol) => disallowed(bounds, sol.to_array()).map(captures_not_allowed)
    None => {
      if self.upper.get(x.uid()) is Some(up) {
        if disallowed(bounds, up) is Some(diff) {
          return Some(captures_not_allowed(diff))
        }
      }
      // A bound that is already known must not restart the propagation: adding
      // nothing leaves the system as consistent as it was.
      match added_to(self.lower.get(x.uid()), bounds, []) {
        Some(lb) => {
          self.lower.set(x.uid(), lb)
          self.propagate_lower_of(x.uid())
        }
        // Nothing new was learnt. An absent bound and an empty one are the same
        // set everywhere (`lower_of` reads both as `[]`), so there is no state
        // to write and nothing to propagate or re-check.
        None => None
      }
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
    Some(sol) => disallowed(sol.to_array(), bounds).map(captures_not_allowed)
    None => {
      if self.lower.get(x.uid()) is Some(lo) {
        if disallowed(lo, bounds) is Some(diff) {
          return Some(captures_not_allowed(diff))
        }
      }
      match self.upper.get(x.uid()) {
        Some(up) =>
          // An upper bound that does not shrink is not news: the fixpoint and
          // the consistency check would both come out the same.
          if up.all(c => bounds.contains(c)) {
            None
          } else {
            self.upper.set(x.uid(), up.filter(c => bounds.contains(c)))
            self.propagate_upper_of(x.uid())
          }
        None => {
          self.upper.set(x.uid(), bounds.to_owned())
          self.propagate_upper_of(x.uid())
        }
      }
    }
  }
}

///|
/// Solves an out-of-scope capture variable with its lower bound.
fn Unification::solve_capt_var(self : Unification, x : Sym) -> String? {
  guard !self.capts.contains(x.uid()) else { return None }
  let bounds = self.lower_of(x.uid())
  if self.upper.get(x.uid()) is Some(up) {
    if disallowed(bounds, up) is Some(diff) {
      return Some(captures_not_allowed(diff))
    }
  }
  self.set_capt_solution(x.uid(), @symbols.Captures::CaptureSetOf(bounds))
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
