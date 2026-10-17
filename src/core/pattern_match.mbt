// The pattern matching compiler.
//
// Mirrors `effekt/core/PatternMatchingCompiler.scala`, which follows closely the
// short paper
//
//   Jules Jacobs, "How to compile pattern matching"
//   https://julesjacobs.com/notes/patternmatching/patternmatching.pdf
//
// A match is represented as a list of [[PMClause]]s, e.g.
//
//    case a is Some(x) => j1(x)
//    case a is None    => j2()
//
// Each clause represents one disjunct. That is, one of the clauses needs to
// match. We compile them to match in order (from top-to-bottom).
//
// One clause is the conjunction of multiple [[PMCondition]]s, e.g.:
//
//    case a is Some(x); val tmp = comp(x); pred(tmp)? => j(x, tmp)
//
// Conditions are compiled to be evaluated left-to-right.
//
// `core.Transformer.preprocess` translates a source pattern match into this
// internal representation; it is designed to have all information readily
// available to immediately generate the [[Stmt]] corresponding to the compiled
// pattern.
//
// Changes here need to be synchronized with the exhaustivity checker, sadly.

// ---------------------------------------------------------------------------
// Variables
// ---------------------------------------------------------------------------

///|
/// A value variable together with its annotated type. Upstream core couples the
/// id and the type in `core.ValueVar`; here the two travel together explicitly.
pub(all) struct PMVar {
  id : Sym
  tpe : ValueType
}

///|
pub fn PMVar::new(id : Sym, tpe : ValueType) -> PMVar {
  { id, tpe, }
}

///|
pub fn PMVar::to_expr(self : PMVar) -> Expr {
  ValueVar(self.id, self.tpe)
}

///|
pub fn PMVar::to_param(self : PMVar) -> ValueParam {
  ValueParam::new(self.id, self.tpe)
}

// ---------------------------------------------------------------------------
// Patterns
// ---------------------------------------------------------------------------

///|
/// How to compare a scrutinee with a literal pattern.
///
/// Upstream stores a closure `(Expr, Expr) => Expr` obtained from the prelude's
/// `infixEq`; since the symbol is all we need, we store it (plus the type
/// arguments to pass) and build the `PureApp` on demand.
pub(all) struct PMEquals {
  symbol : Sym
  targs : Array[ValueType]
}

///|
pub fn PMEquals::new(symbol : Sym, targs : Array[ValueType]) -> PMEquals {
  { symbol, targs, }
}

///|
pub fn PMEquals::pm_apply(self : PMEquals, lhs : Expr, rhs : Expr) -> Expr {
  PureApp(
    BlockVar::new(self.symbol, unknown_block_type(), Captures::empty()),
    self.targs,
    [lhs, rhs],
  )
}

///|
/// A nested pattern together with the type of the scrutinee it matches on.
pub(all) struct PMSubPattern {
  pattern : PMPattern
  tpe : ValueType
}

///|
pub fn PMSubPattern::new(pattern : PMPattern, tpe : ValueType) -> PMSubPattern {
  { pattern, tpe, }
}

///|
/// The pattern matching compiler requires some information:
/// - the type of the scrutinee on subpatterns, i.e. `Cons(Some(x : Int), xs)`
/// - the variants of the data type, i.e. `Tag("Red", ..., ["Red", "Green"])`
///
/// `Or` is never produced by the source-to-core transformer; it is kept for
/// parity with upstream (where only the tests use it).
pub(all) enum PMPattern {
  PMTag(Sym, Array[Sym], Array[Sym], Array[PMSubPattern])
  PMIgnore
  PMAny(Sym)
  PMOr(Array[PMPattern])
  PMLiteral(LiteralValue, ValueType, PMEquals?)
}

// ---------------------------------------------------------------------------
// Conditions and clauses
// ---------------------------------------------------------------------------

///|
/// A variable and the pattern it is matched against.
pub(all) struct PMVarPattern {
  variable : PMVar
  pattern : PMPattern
}

///|
pub fn PMVarPattern::new(variable : PMVar, pattern : PMPattern) -> PMVarPattern {
  { variable, pattern, }
}

///|
/// The conditions need to be met in sequence before the block at the clause's
/// label can be evaluated with the given type and value arguments.
pub(all) enum PMCondition {
  /// All of the patterns need to match for this condition to be met.
  PMPatterns(Map[Int32, PMVarPattern])
  /// A boolean predicate that needs to be branched on at runtime.
  PMPredicate(Expr)
  /// A predicate trivially met by running and binding the statement.
  PMRun(Binding)
}

///|
/// One disjunct of a match: a conjunction of conditions and the joinpoint to
/// call when all of them are met.
pub(all) struct PMClause {
  conditions : Array[PMCondition]
  label : BlockVar
  targs : Array[ValueType]
  args : Array[PMVar]
}

///|
pub fn PMClause::new(
  conditions : Array[PMCondition],
  label : BlockVar,
  targs : Array[ValueType],
  args : Array[PMVar],
) -> PMClause {
  { conditions, label, targs, args, }
}

// ---------------------------------------------------------------------------
// Small array helpers (MoonBit has no `List` with O(1) tail)
// ---------------------------------------------------------------------------

///|
fn[T] pm_drop_first(xs : Array[T]) -> Array[T] {
  let out : Array[T] = []
  let mut i = 1
  while i < xs.length() {
    out.push(xs[i])
    i = i + 1
  }
  out
}

///|
fn[T] pm_prepend(x : T, xs : Array[T]) -> Array[T] {
  let out : Array[T] = [x]
  for y in xs {
    out.push(y)
  }
  out
}

// ---------------------------------------------------------------------------
// Literal helpers
// ---------------------------------------------------------------------------

///|
fn pm_literal_equal(a : LiteralValue, b : LiteralValue) -> Bool {
  match (a, b) {
    (LUnit, LUnit) => true
    (LBool(x), LBool(y)) => x == y
    (LInt(x), LInt(y)) => x == y
    (LDouble(x), LDouble(y)) => x == y
    (LString(x), LString(y)) => x == y
    (LChar(x), LChar(y)) => x == y
    (LByte(x), LByte(y)) => x == y
    _ => false
  }
}

///|
/// The (finite) set of values a type can take, if it is finite. Mirrors the
/// special cases of `splitOnLiteral` for `Bool`, `Unit` and `Nothing`.
fn pm_finite_literals(tpe : ValueType) -> Array[LiteralValue]? {
  match tpe {
    ValueTypeApp(sym, _) =>
      match core_builtin_to_string(sym) {
        Some("Bool") => Some([LBool(true), LBool(false)])
        Some("Unit") => Some([LUnit])
        Some("Nothing") => {
          let empty : Array[LiteralValue] = []
          Some(empty)
        }
        _ => None
      }
    _ => None
  }
}

///|
fn pm_literal_index(variants : Array[LiteralValue], v : LiteralValue) -> Int32 {
  for i = 0; i < variants.length(); i = i + 1 {
    if pm_literal_equal(variants[i], v) {
      return i
    }
  }
  -1
}

// ---------------------------------------------------------------------------
// The compiler
// ---------------------------------------------------------------------------

///|
/// Compiles the given clauses to a (nested) pattern match producing a value of
/// type `motif`.
pub fn pm_compile(
  clauses : Array[PMClause],
  motif : ValueType,
) -> Stmt raise EffektError {
  // This shouldn't be reachable anymore since we specialize matching on void
  // before calling compile.
  if clauses.length() == 0 {
    return Hole(motif, Span::missing())
  }

  // (0) normalize clauses
  let normalized : Array[PMClause] = []
  for c in clauses {
    normalized.push(pm_normalize(c))
  }

  let head = normalized[0]
  let remaining = pm_drop_first(normalized)

  // (1) Check the first clause to be matched (we can immediately handle
  //     non-pattern cases)
  if head.conditions.length() == 0 {
    // - The top-most clause already matches successfully
    return App(
      BlockVar(head.label),
      head.targs,
      head.args.map(a => a.to_expr()),
      [],
    )
  }

  let rest_clause = PMClause::new(
    pm_drop_first(head.conditions),
    head.label,
    head.targs,
    head.args,
  )

  match head.conditions[0] {
    // - We need to perform a computation
    PMRun(binding) =>
      binding.to_stmt(pm_compile(pm_prepend(rest_clause, remaining), motif))
    // - We need to check a predicate
    PMPredicate(pred) =>
      If(
        pred,
        pm_compile(pm_prepend(rest_clause, remaining), motif),
        pm_compile(remaining, motif),
      )
    // - We need to match on a pattern
    PMPatterns(patterns) => {
      // (2) Choose the variable to split on
      let scrutinee = pm_branching_heuristic(patterns, normalized)
      let scrutinee_pattern = match patterns.get(scrutinee.id.uid()) {
        Some(vp) => vp.pattern
        None =>
          raise EffektError::Internal(
            "Pattern matching: the scrutinee is not among the patterns.",
          )
      }
      match scrutinee_pattern {
        // (3a) Match on a literal
        PMLiteral(value, tpe, eq) =>
          pm_split_on_literal(scrutinee, value, tpe, eq, normalized, motif)
        // (3b) Match on a data type constructor
        PMTag(id, _, variants, _) =>
          pm_split_on_tag(scrutinee, id, variants, normalized, motif)
        _ =>
          raise EffektError::Internal(
            "Pattern matching: cannot split on \{pm_show_pattern_kind(scrutinee_pattern)}",
          )
      }
    }
  }
}

///|
fn pm_show_pattern_kind(p : PMPattern) -> String {
  match p {
    PMTag(id, _, _, _) => "tag \{id.name().name}"
    PMIgnore => "ignore"
    PMAny(id) => "any \{id.name().name}"
    PMOr(_) => "or"
    PMLiteral(_, _, _) => "literal"
  }
}

///|
/// Splits the first condition of a clause on the given scrutinee. Returns the
/// pattern for the scrutinee, the remaining patterns, and the remaining
/// conditions -- or `None` if this clause does not match on the scrutinee.
fn pm_split_clause(
  c : PMClause,
  scrutinee : PMVar,
) -> (PMPattern, Map[Int32, PMVarPattern], Array[PMCondition])? {
  if c.conditions.length() == 0 {
    return None
  }
  match c.conditions[0] {
    PMPatterns(patterns) =>
      match patterns.get(scrutinee.id.uid()) {
        Some(vp) => {
          let rest = patterns.copy()
          rest.remove(scrutinee.id.uid())
          Some((vp.pattern, rest, pm_drop_first(c.conditions)))
        }
        None => None
      }
    _ => None
  }
}

///|
/// (3a) Match on a literal: group the clauses by the literal they match and
/// compile the resulting cascade of `if`s.
fn pm_split_on_literal(
  scrutinee : PMVar,
  _lit_value : LiteralValue,
  lit_tpe : ValueType,
  eq : PMEquals?,
  normalized : Array[PMClause],
  motif : ValueType,
) -> Stmt raise EffektError {
  // the different literal values that we match on
  let variants : Array[LiteralValue] = []
  for c in normalized {
    match pm_split_clause(c, scrutinee) {
      Some((PMLiteral(v, _, _), _, _)) =>
        if pm_literal_index(variants, v) < 0 {
          variants.push(v)
        }
      _ => ()
    }
  }

  // for each literal, we collect the clauses that match it correctly
  let clauses_for : Array[Array[PMClause]] = variants.map(_ => {
    ([] : Array[PMClause])
  })
  // default clauses always match with respect to the current scrutinee
  let defaults : Array[PMClause] = []

  for c in normalized {
    match pm_split_clause(c, scrutinee) {
      Some((PMLiteral(v, _, _), rest_patterns, rest_conds)) => {
        let idx = pm_literal_index(variants, v)
        if idx >= 0 {
          clauses_for[idx].push(
            PMClause::new(
              pm_prepend(PMPatterns(rest_patterns), rest_conds),
              c.label,
              c.targs,
              c.args,
            ),
          )
        }
      }
      _ =>
        match pm_finite_literals(lit_tpe) {
          Some(values) => {
            if values.any(b => pm_literal_index(variants, b) < 0) {
              defaults.push(c)
            }
            for i = 0; i < variants.length(); i = i + 1 {
              clauses_for[i].push(c)
            }
          }
          None => {
            defaults.push(c)
            for i = 0; i < variants.length(); i = i + 1 {
              clauses_for[i].push(c)
            }
          }
        }
    }
  }

  // (4) assemble syntax tree for the pattern match
  let mut result = pm_compile(defaults, motif)
  for i = variants.length() - 1; i >= 0; i = i - 1 {
    let value = variants[i]
    let thn = pm_compile(clauses_for[i], motif)
    let els = result
    result = match value {
      LUnit => thn
      LBool(true) => If(scrutinee.to_expr(), thn, els)
      LBool(false) => If(scrutinee.to_expr(), els, thn)
      _ => {
        let eq_fun = match eq {
          Some(e) => e
          None =>
            raise EffektError::Internal(
              "Pattern matching: cannot compile literal patterns without an equality function. " +
              "Call `set_pattern_equality_function` with the prelude's `infixEq`.",
            )
        }
        If(
          eq_fun.pm_apply(scrutinee.to_expr(), Literal(value, lit_tpe)),
          thn,
          els,
        )
      }
    }
  }
  result
}

///|
/// The names of the fields of a constructor, padded with `"y"` when the symbol
/// does not carry them (which only happens for hand-built trees).
fn pm_constructor_field_names(
  constructor : Sym,
  arity : Int32,
) -> Array[String] {
  let names : Array[String] = match constructor {
    Constructor(c) => c.fields.map(f => f.name().name)
    _ => []
  }
  while names.length() < arity {
    names.push("y")
  }
  names
}

///|
/// (3b) Match on a data type constructor.
fn pm_split_on_tag(
  scrutinee : PMVar,
  _id : Sym,
  all_variants : Array[Sym],
  normalized : Array[PMClause],
  motif : ValueType,
) -> Stmt raise EffektError {
  // collect all variants that are mentioned in the clauses
  let variants : Array[Sym] = []
  for c in normalized {
    match pm_split_clause(c, scrutinee) {
      Some((PMTag(cid, _, _, _), _, _)) =>
        if !sym_in(cid, variants) {
          variants.push(cid)
        }
      _ => ()
    }
  }

  // for each tag, we collect the clauses that match it correctly
  let clauses_for : Map[Int32, Array[PMClause]] = Map([])
  // default clauses always match with respect to the current scrutinee
  let defaults : Array[PMClause] = []

  // used to make up new scrutinees
  let vars_for : Map[Int32, Array[PMVar]] = Map([])
  let tvars_for : Map[Int32, Array[Sym]] = Map([])

  for c in normalized {
    match pm_split_clause(c, scrutinee) {
      Some(
        (
          PMTag(constructor, tparams, _, patterns_and_types),
          rest_patterns,
          rest_conds,
        )
      ) => {
        // NOTE: Ideally, we would use a `DeclarationContext` here, but we
        // cannot: we're currently in the Source->Core transformer, so we do not
        // have all of the details yet.
        if !vars_for.contains(constructor.uid()) {
          let field_names = pm_constructor_field_names(
            constructor,
            patterns_and_types.length(),
          )
          let vars : Array[PMVar] = []
          for i = 0; i < patterns_and_types.length(); i = i + 1 {
            let tpe = patterns_and_types[i].tpe
            let name = match patterns_and_types[i].pattern {
              // if it's a pattern named by the user in the program, use that name
              PMAny(aid) => aid.name().name
              // otherwise, use the field name of the given field
              _ => field_names[i]
            }
            vars.push(
              PMVar::new(
                Sym::value_param(Name::local(name), Some(tpe), Span::missing()),
                tpe,
              ),
            )
          }
          vars_for.set(constructor.uid(), vars)
          tvars_for.set(constructor.uid(), tparams)
        }
        let field_vars = match vars_for.get(constructor.uid()) {
          Some(v) => v
          None => ([] : Array[PMVar])
        }
        let nested : Map[Int32, PMVarPattern] = Map([])
        for i = 0; i < field_vars.length(); i = i + 1 {
          nested.set(
            field_vars[i].id.uid(),
            PMVarPattern::new(field_vars[i], patterns_and_types[i].pattern),
          )
        }
        // it is important to add nested matches first, since they might include
        // substitutions for the rest.
        let conds : Array[PMCondition] = [
          PMPatterns(nested),
          PMPatterns(rest_patterns),
        ]
        for cond in rest_conds {
          conds.push(cond)
        }
        let cl = PMClause::new(conds, c.label, c.targs, c.args)
        match clauses_for.get(constructor.uid()) {
          Some(list) => list.push(cl)
          None => clauses_for.set(constructor.uid(), [cl])
        }
      }
      _ => {
        // Clauses that don't match on that var are duplicated.
        // So we want to choose our branching heuristic to minimize this.
        for v in variants {
          match clauses_for.get(v.uid()) {
            Some(list) => list.push(c)
            None => clauses_for.set(v.uid(), [c])
          }
        }
        // only if the variants do not cover the data type, add a default!
        if all_variants.any(v => !sym_in(v, variants)) {
          defaults.push(c)
        }
      }
    }
  }

  // (4) assemble syntax tree for the pattern match
  let branches : Array[Clause] = []
  for v in variants {
    let body = pm_compile(
      match clauses_for.get(v.uid()) {
        Some(l) => l
        None => ([] : Array[PMClause])
      },
      motif,
    )
    let tparams = match tvars_for.get(v.uid()) {
      Some(t) => t
      None => ([] : Array[Sym])
    }
    let params = match vars_for.get(v.uid()) {
      Some(p) => p.map(x => x.to_param())
      None => ([] : Array[ValueParam])
    }
    branches.push(Clause::new(v, BlockLit::new(tparams, [], params, [], body)))
  }

  let default = if defaults.length() == 0 {
    None
  } else {
    Some(pm_compile(defaults, motif))
  }

  Match(scrutinee.to_expr(), motif, branches, default)
}

///|
/// The variable to split on next: the one that is mentioned in the most
/// clauses (this minimizes the duplication of clauses that do not mention it).
///
/// NOTE: upstream writes `clauses.count { case Clause(ps, _, _, _) => ps.contains(v) }`
/// on a `List[Condition]`, which type-checks through covariance but is always
/// false. We implement the intended heuristic.
fn pm_branching_heuristic(
  patterns : Map[Int32, PMVarPattern],
  clauses : Array[PMClause],
) -> PMVar raise EffektError {
  let mut best : PMVar? = None
  let mut best_count = -1
  for _, vp in patterns {
    let mut count = 0
    for c in clauses {
      for cond in c.conditions {
        match cond {
          PMPatterns(m) =>
            if m.contains(vp.variable.id.uid()) {
              count = count + 1
            }
          _ => ()
        }
      }
    }
    if count > best_count {
      best_count = count
      best = Some(vp.variable)
    }
  }
  match best {
    Some(v) => v
    None =>
      raise EffektError::Internal("Pattern matching: no patterns to split on.")
  }
}

// ---------------------------------------------------------------------------
// Normalization
// ---------------------------------------------------------------------------

///|
/// Normalizes a clause, substituting away `Any` patterns.
pub fn pm_normalize(clause : PMClause) -> PMClause raise EffektError {
  let (conditions, substitution) = pm_normalize_conditions(
    Map([]),
    clause.conditions,
    Map([]),
  )
  // TODO also substitute types?
  let args = clause.args.map(a => {
    match substitution.get(a.id.uid()) {
      Some(v) => v
      None => a
    }
  })
  PMClause::new(conditions, clause.label, clause.targs, args)
}

///|
/// 1) merges all subsequent `Patterns(ps) :: Patterns(qs) :: ...` into
///    `Patterns(ps ::: qs) :: ...`
/// 2) drops all `Ignore` and `Any` patterns and substitutes them in the
///    remaining patterns
/// 3) returns the substitution that needs to be applied to the body of the
///    clause
///
///     case a is x; x is Cons => f(a, x)
///       ~=
///     case a is Cons => f(a, a)
fn pm_normalize_conditions(
  patterns : Map[Int32, PMVarPattern],
  conditions : Array[PMCondition],
  substitution : Map[Int32, PMVar],
) -> (Array[PMCondition], Map[Int32, PMVar]) raise EffektError {
  if conditions.length() == 0 {
    return (pm_prefix(patterns, []), substitution)
  }
  let rest = pm_drop_first(conditions)
  match conditions[0] {
    PMPatterns(other) => {
      let substituted : Map[Int32, PMVarPattern] = Map([])
      let additional : Array[(Int32, PMVar)] = []
      for k, vp in other {
        let sc = match substitution.get(vp.variable.id.uid()) {
          Some(v) => v
          None => vp.variable
        }
        substituted.set(k, PMVarPattern::new(sc, vp.pattern))
        match vp.pattern {
          PMAny(aid) => additional.push((aid.uid(), sc))
          _ => ()
        }
      }
      let filtered : Map[Int32, PMVarPattern] = Map([])
      for k, vp in substituted {
        match vp.pattern {
          PMTag(_, _, _, _) | PMLiteral(_, _, _) => filtered.set(k, vp)
          _ => ()
        }
      }
      let new_patterns = patterns.copy()
      for k, v in filtered {
        new_patterns.set(k, v)
      }
      let new_substitution = substitution.copy()
      for pair in additional {
        new_substitution.set(pair.0, pair.1)
      }
      pm_normalize_conditions(new_patterns, rest, new_substitution)
    }
    PMRun(binding) => {
      let substituted = substitute_binding(
        binding,
        pm_value_substitution(substitution),
      )
      let (res_cond, res_subst) = pm_normalize_conditions(
        Map([]),
        rest,
        substitution,
      )
      (pm_prefix(patterns, pm_prepend(PMRun(substituted), res_cond)), res_subst)
    }
    PMPredicate(pred) => {
      let substituted = substitute_expr(
        pred,
        pm_value_substitution(substitution),
      )
      let (res_cond, res_subst) = pm_normalize_conditions(
        Map([]),
        rest,
        substitution,
      )
      (
        pm_prefix(patterns, pm_prepend(PMPredicate(substituted), res_cond)),
        res_subst,
      )
    }
  }
}

///|
fn pm_value_substitution(substitution : Map[Int32, PMVar]) -> Substitution {
  let values : Map[Int32, Expr] = Map([])
  for k, v in substitution {
    values.set(k, v.to_expr())
  }
  Substitution::new(Map([]), Map([]), values, Map([]))
}

///|
fn pm_prefix(
  patterns : Map[Int32, PMVarPattern],
  cs : Array[PMCondition],
) -> Array[PMCondition] {
  if patterns.length() == 0 {
    cs
  } else {
    pm_prepend(PMPatterns(patterns), cs)
  }
}
