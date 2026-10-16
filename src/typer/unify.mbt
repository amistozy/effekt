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
pub fn Unification::new() -> Unification {
  {
    types: Map::new(),
    capts: Map::new(),
    lower: Map::new(),
    upper: Map::new(),
    links: [],
    var_of: Map::new(),
    capt_var: Map::new(),
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
    var_of: self.var_of.copy(),
    capt_var: self.capt_var.copy(),
  }
}

// Creating fresh variables
// ------------------------

///|
/// A fresh *value type* unification variable. `underlying` is the type
/// parameter it was instantiated for (used for error messages).
pub fn Unification::fresh_type_var(self : Unification, underlying : Sym) -> Sym {
  let x = Sym::type_param(
    Name::local("?\{underlying.name().name}"),
    Span::missing(),
  )
  self.var_of.set(x.uid(), underlying)
  x
}

///|
/// A fresh *capture* unification variable.
pub fn Unification::fresh_capt_var(self : Unification, role : String) -> Sym {
  let x = Sym::capture_param(Name::local("?\{role}"))
  self.capt_var.set(x.uid(), x)
  x
}

///|
/// Is `x` one of the unification variables created by this table?
pub fn Unification::is_type_var(self : Unification, x : Sym) -> Bool {
  self.var_of.contains(x.uid())
}

///|
pub fn Unification::is_capt_var(self : Unification, x : Sym) -> Bool {
  self.capt_var.contains(x.uid())
}

///|
pub fn Unification::underlying(self : Unification, x : Sym) -> Sym {
  self.var_of.get(x.uid()).unwrap_or(x)
}

// Substitution
// ------------

///|
pub fn Unification::substitution(self : Unification) -> Substitutions {
  { values: self.types.copy(), captures: self.capts.copy(), }
}

///|
pub fn Unification::prune_value(self : Unification, t : ValueType) -> ValueType {
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
pub fn Unification::prune_block(self : Unification, t : BlockType) -> BlockType {
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
        Effects::new(effs.effects.map(e => self.prune_block(e))),
      )
  }
}

///|
pub fn Unification::prune_captures(
  self : Unification,
  c : Captures,
) -> Captures {
  match c {
    @symbols.Captures::CaptVar(x) =>
      match self.capts.get(x.uid()) {
        Some(s) => self.prune_captures(s)
        None => c
      }
    @symbols.Captures::CaptureSetOf(cs) => {
      let out : Array[Sym] = []
      for s in cs {
        match self.capts.get(s.uid()) {
          Some(sol) =>
            for y in self.prune_captures(sol).to_array() {
              if !sym_in(y, out) {
                out.push(y)
              }
            }
          None => if !sym_in(s, out) { out.push(s) }
        }
      }
      @symbols.Captures::CaptureSetOf(out)
    }
  }
}

///|
pub fn Unification::prune_effects(
  self : Unification,
  effs : Effects,
) -> Effects {
  Effects::new(effs.effects.map(e => self.prune_block(e)))
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
pub fn Unification::update_substitution(self : Unification) -> Unit {
  let subst = self.substitution()
  for k, v in self.types {
    let updated = subst.substitute_value(v)
    if !value_type_eq(updated, v) {
      self.types.set(k, updated)
    }
  }
  for k, v in self.capts {
    let updated = subst.substitute_captures(v)
    if !captures_eq(updated, v) {
      self.capts.set(k, updated)
    }
  }
}

// Capture constraints
// -------------------

///|
pub fn Unification::lower_of(self : Unification, uid : Int32) -> Array[Sym] {
  self.lower.get(uid).unwrap_or([])
}

///|
/// Adds a subcapturing link `lo - filter <: hi`.
pub fn Unification::link(
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
pub fn Unification::propagate(self : Unification) -> String? {
  let mut rounds = 0
  let mut changed = true
  while changed && rounds < 200 {
    changed = false
    rounds = rounds + 1
    for link in self.links {
      let (a, b, filter) = link
      // lower(a) - filter flows into lower(b)
      for c in self.lower_of(a) {
        if !sym_in(c, filter) && !sym_in(c, self.lower_of(b)) {
          let next = self.lower_of(b).copy()
          next.push(c)
          self.lower.set(b, next)
          changed = true
        }
      }
      // upper(b) + filter flows into upper(a)
      match self.upper.get(b) {
        None => ()
        Some(ub) => {
          let target : Array[Sym] = []
          for c in ub {
            target.push(c)
          }
          for c in filter {
            if !sym_in(c, target) {
              target.push(c)
            }
          }
          match self.upper.get(a) {
            None => {
              self.upper.set(a, target)
              changed = true
            }
            Some(ua) => {
              let intersection = ua.filter(c => sym_in(c, target))
              if intersection.length() != ua.length() {
                self.upper.set(a, intersection)
                changed = true
              }
            }
          }
        }
      }
    }
  }
  // consistency of all nodes
  for uid, lo in self.lower {
    match self.upper.get(uid) {
      Some(up) =>
        for c in lo {
          if !sym_in(c, up) {
            return Some(
              "Capture \{c.name().name} is not allowed in the inferred capture set",
            )
          }
        }
      None => ()
    }
  }
  None
}

///|
/// `bounds <: ?x`
pub fn Unification::require_lower(
  self : Unification,
  bounds : Array[Sym],
  x : Sym,
) -> String? {
  match self.capts.get(x.uid()) {
    Some(sol) => {
      let solved = sol.to_array()
      for c in bounds {
        if !sym_in(c, solved) {
          return Some(
            "Capture \{c.name().name} is not included in \{show_captures(sol)}",
          )
        }
      }
      None
    }
    None => {
      match self.upper.get(x.uid()) {
        Some(up) =>
          for c in bounds {
            if !sym_in(c, up) {
              return Some(
                "Used capture \{c.name().name} is not in the allowed set {\{up.map(s => s.name().name).join(", ")}}",
              )
            }
          }
        None => ()
      }
      let current = self.lower_of(x.uid())
      let next = current.copy()
      for c in bounds {
        if !sym_in(c, next) {
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
pub fn Unification::require_upper(
  self : Unification,
  bounds : Array[Sym],
  x : Sym,
) -> String? {
  match self.capts.get(x.uid()) {
    Some(sol) => {
      let solved = sol.to_array()
      for c in solved {
        if !sym_in(c, bounds) {
          return Some(
            "Used capture \{c.name().name} is not in the allowed set {\{bounds.map(s => s.name().name).join(", ")}}",
          )
        }
      }
      None
    }
    None => {
      match self.lower.get(x.uid()) {
        Some(lo) =>
          for c in lo {
            if !sym_in(c, bounds) {
              return Some(
                "Used capture \{c.name().name} is not in the allowed set {\{bounds.map(s => s.name().name).join(", ")}}",
              )
            }
          }
        None => ()
      }
      match self.upper.get(x.uid()) {
        Some(up) => {
          let intersection = up.filter(c => sym_in(c, bounds))
          self.upper.set(x.uid(), intersection)
        }
        None => self.upper.set(x.uid(), bounds.copy())
      }
      self.propagate()
    }
  }
}

///|
/// Solves an out-of-scope capture variable with its lower bound.
pub fn Unification::solve_capt_var(self : Unification, x : Sym) -> String? {
  if self.capts.contains(x.uid()) {
    return None
  }
  let bounds = self.lower_of(x.uid())
  match self.upper.get(x.uid()) {
    Some(up) =>
      for c in bounds {
        if !sym_in(c, up) {
          return Some(
            "Used capture \{c.name().name} is not in the allowed set {\{up.map(s => s.name().name).join(", ")}}",
          )
        }
      }
    None => ()
  }
  self.capts.set(x.uid(), @symbols.Captures::CaptureSetOf(bounds))
  None
}

///|
/// Solves capture variables that went out of scope.
pub fn Unification::solve_all(
  self : Unification,
  xs : Array[Sym],
) -> Array[String] {
  let errors : Array[String] = []
  for x in xs {
    match self.solve_capt_var(x) {
      Some(msg) => errors.push(msg)
      None => ()
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
pub fn UnifScope::type_vars(self : UnifScope) -> Array[Sym] {
  match self {
    GlobalScope => []
    LocalScope(ts, _, _) => ts
  }
}

///|
pub fn UnifScope::capt_vars(self : UnifScope) -> Array[Sym] {
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
pub fn UnifScope::is_global(self : UnifScope) -> Bool {
  match self {
    GlobalScope => true
    LocalScope(_, _, _) => false
  }
}

///|
/// Registers a fresh type variable in the current scope.
pub fn UnifScope::register_type_var(self : UnifScope, x : Sym) -> Unit {
  match self {
    GlobalScope => ()
    LocalScope(ts, _, _) => ts.push(x)
  }
}

///|
/// Registers a fresh capture variable in the current scope.
pub fn UnifScope::register_capt_var(self : UnifScope, x : Sym) -> Unit {
  match self {
    GlobalScope => ()
    LocalScope(_, cs, _) => cs.push(x)
  }
}
