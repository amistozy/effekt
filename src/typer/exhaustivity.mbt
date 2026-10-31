// Exhaustivity and redundancy checking for `match`.
//
// A port of `effekt/typer/ExhaustivityChecker.scala`. Clauses are translated
// into *conditions* (pattern matches and guards), every scrutinee is identified
// by the trace of constructors leading to it, and `check_scrutinee` /
// `match_clauses` walk the clause matrix the way the upstream checker does. The
// result is a list of missing cases and of clauses that no value can reach;
// `report` turns them into diagnostics.

///|
/// A pattern whose constructors are already resolved.
priv enum Pat {
  PAny
  PTag(Sym, Array[Pat])
  PLit(@source.LiteralValue, ValueType)
}

///|
/// Identifies a scrutinee: the root of the match, or a field of a constructor
/// applied to an outer scrutinee.
priv enum Trace {
  TRoot(Int32)
  TChild(Sym, Int32, Trace)
}

///|
priv enum Cond {
  CPatterns(Array[(Trace, Pat)])
  /// `and <guard>`: the following conditions are only reached when the guard
  /// is true.
  CGuard(Span)
}

///|
priv struct Clause {
  conds : Array[Cond]
  /// The index of the clause among the original ones; `-1` marks the clause
  /// synthesized from a `default` branch, which is never reported.
  index : Int32
}

///|
priv enum Missing {
  MTag(Sym, Trace)
  MGuard(Span)
  MLit(@source.LiteralValue, Trace)
  MDefault(ValueType, Trace)
}

// ---------------------------------------------------------------------------
// Traces and patterns
// ---------------------------------------------------------------------------

///|
fn trace_equal(a : Trace, b : Trace) -> Bool {
  match (a, b) {
    (TRoot(x), TRoot(y)) => x == y
    (TChild(c1, f1, o1), TChild(c2, f2, o2)) =>
      c1 == c2 && f1 == f2 && trace_equal(o1, o2)
    _ => false
  }
}

///|
fn pattern_under(patterns : Array[(Trace, Pat)], t : Trace) -> Pat? {
  for entry in patterns {
    if trace_equal(entry.0, t) {
      return Some(entry.1)
    }
  }
  None
}

///|
fn without_trace(
  patterns : Array[(Trace, Pat)],
  t : Trace,
) -> Array[(Trace, Pat)] {
  let out : Array[(Trace, Pat)] = []
  for entry in patterns {
    if !trace_equal(entry.0, t) {
      out.push(entry)
    }
  }
  out
}

///|
/// Wildcards cover everything, so matching on them is not a condition the
/// checker has to satisfy: they are dropped, exactly like upstream's
/// `Clause.normalized`.
fn normalize_patterns(patterns : Array[(Trace, Pat)]) -> Array[(Trace, Pat)] {
  let out : Array[(Trace, Pat)] = []
  for entry in patterns {
    match entry.1 {
      PAny => ()
      _ => out.push(entry)
    }
  }
  out
}

///|
fn normalize_conds(conds : Array[Cond], index : Int32) -> Clause {
  let out : Array[Cond] = []
  for c in conds {
    match c {
      CPatterns(ps) => {
        let norm = normalize_patterns(ps)
        if norm.length() > 0 {
          out.push(CPatterns(norm))
        }
      }
      _ => out.push(c)
    }
  }
  { conds: out, index, }
}

///|
fn Clause::matches_on(self : Clause, t : Trace) -> Pat? {
  if self.conds.length() == 0 {
    return None
  }
  match self.conds[0] {
    CPatterns(ps) => pattern_under(ps, t)
    _ => None
  }
}

///|
/// The clause with `t` removed from its pattern conditions: it no longer
/// matches on that scrutinee.
fn Clause::minus(self : Clause, t : Trace) -> Clause {
  if self.conds.length() == 0 {
    return self
  }
  match self.conds[0] {
    CPatterns(ps) => {
      let conds : Array[Cond] = [CPatterns(without_trace(ps, t))]
      for i = 1; i < self.conds.length(); i = i + 1 {
        conds.push(self.conds[i])
      }
      normalize_conds(conds, self.index)
    }
    _ => self
  }
}

///|
/// The clause with the patterns of the constructor's fields added.
fn Clause::plus(self : Clause, others : Array[(Trace, Pat)]) -> Clause {
  let conds : Array[Cond] = []
  let mut start = 0
  if self.conds.length() > 0 {
    match self.conds[0] {
      CPatterns(ps) => {
        conds.push(CPatterns(ps + others))
        start = 1
      }
      _ => conds.push(CPatterns(others))
    }
  } else {
    conds.push(CPatterns(others))
  }
  for i = start; i < self.conds.length(); i = i + 1 {
    conds.push(self.conds[i])
  }
  normalize_conds(conds, self.index)
}

///|
fn Clause::rest(self : Clause) -> Array[Cond] {
  let out : Array[Cond] = []
  for i = 1; i < self.conds.length(); i = i + 1 {
    out.push(self.conds[i])
  }
  out
}

// ---------------------------------------------------------------------------
// The checker
// ---------------------------------------------------------------------------

///|
priv struct Exhaustivity {
  typer : Typer
  /// The clauses of the match, for redundancy reporting.
  clauses : Array[MatchClause]
  /// Position of the `match`, where missing cases are reported.
  span : Span
  scrutinees : Array[Term]
  used : Array[Bool]
  mut missing : Array[Missing]
}

///|
fn constructor_fields(ctor : Sym) -> Array[Sym] {
  match ctor {
    @symbols.Sym::Constructor(c) => c.fields
    _ => []
  }
}

///|
fn literal_equal(a : @source.LiteralValue, b : @source.LiteralValue) -> Bool {
  match (a, b) {
    (@source.LiteralValue::LUnit, @source.LiteralValue::LUnit) => true
    (@source.LiteralValue::LBool(x), @source.LiteralValue::LBool(y)) => x == y
    (@source.LiteralValue::LInt(x), @source.LiteralValue::LInt(y)) => x == y
    (@source.LiteralValue::LDouble(x), @source.LiteralValue::LDouble(y)) =>
      x == y
    (@source.LiteralValue::LString(x), @source.LiteralValue::LString(y)) =>
      x == y
    (@source.LiteralValue::LChar(x), @source.LiteralValue::LChar(y)) => x == y
    (@source.LiteralValue::LByte(x), @source.LiteralValue::LByte(y)) => x == y
    _ => false
  }
}

///|
fn is_literal_type(t : ValueType) -> Bool {
  t == @symbols.t_int() ||
  t == @symbols.t_double() ||
  t == @symbols.t_string() ||
  t == @symbols.t_bool() ||
  t == @symbols.t_unit() ||
  t == @symbols.t_bottom() ||
  t == @symbols.t_char() ||
  t == @symbols.t_byte()
}

///|
/// The values of a type with a finite domain; `None` for types that only a
/// default case can cover (`Int`, `String`, ...).
fn literal_domain(t : ValueType) -> Array[@source.LiteralValue]? {
  if t == @symbols.t_bool() {
    return Some([
      @source.LiteralValue::LBool(true),
      @source.LiteralValue::LBool(false),
    ])
  }
  if t == @symbols.t_unit() {
    return Some([@source.LiteralValue::LUnit])
  }
  if t == @symbols.t_bottom() {
    return Some([])
  }
  None
}

///|
fn Exhaustivity::use(self : Exhaustivity, index : Int32) -> Unit {
  if index >= 0 && index < self.used.length() {
    self.used[index] = true
  }
}

///|
fn Exhaustivity::missing_tag(
  self : Exhaustivity,
  ctor : Sym,
  at : Trace,
) -> Unit {
  let next : Array[Missing] = [MTag(ctor, at)]
  for m in self.missing {
    next.push(m)
  }
  self.missing = next
}

///|
fn Exhaustivity::missing_guard(self : Exhaustivity, span : Span) -> Unit {
  let next : Array[Missing] = [MGuard(span)]
  for m in self.missing {
    next.push(m)
  }
  self.missing = next
}

///|
fn Exhaustivity::missing_literal(
  self : Exhaustivity,
  value : @source.LiteralValue,
  at : Trace,
) -> Unit {
  let next : Array[Missing] = [MLit(value, at)]
  for m in self.missing {
    next.push(m)
  }
  self.missing = next
}

///|
fn Exhaustivity::missing_default(
  self : Exhaustivity,
  tpe : ValueType,
  at : Trace,
) -> Unit {
  let next : Array[Missing] = [MDefault(tpe, at)]
  for m in self.missing {
    next.push(m)
  }
  self.missing = next
}

///|
fn Exhaustivity::resolve(self : Exhaustivity, id : IdRef) -> Sym? {
  self.typer.ctx.symbol_of(id.uid)
}

///|
fn Exhaustivity::preprocess_pattern(
  self : Exhaustivity,
  p : MatchPattern,
) -> Pat {
  match p.kind {
    @source.PatternKind::AnyPattern(_) => PAny
    @source.PatternKind::IgnorePattern => PAny
    @source.PatternKind::LiteralPattern(value, tpe) => PLit(value, tpe)
    @source.PatternKind::TagPattern(id, patterns) =>
      match self.resolve(id) {
        Some(c) => PTag(c, patterns.map(q => self.preprocess_pattern(q)))
        None => PAny
      }
    @source.PatternKind::MultiPattern(_) => PAny
  }
}

///|
fn Exhaustivity::preprocess_guard(self : Exhaustivity, g : MatchGuard) -> Cond {
  match g.kind {
    @source.GuardKind::BooleanGuard(_) => CGuard(g.span)
    @source.GuardKind::PatternGuard(scrutinee, pattern) =>
      CPatterns([(TRoot(scrutinee.uid), self.preprocess_pattern(pattern))])
  }
}

///|
fn Exhaustivity::preprocess(
  self : Exhaustivity,
  clause : MatchClause,
  index : Int32,
) -> Clause? {
  let arity = self.scrutinees.length()
  let patterns : Array[(Trace, Pat)] = []
  match clause.pattern.kind {
    @source.PatternKind::MultiPattern(ps) => {
      if ps.length() != arity {
        return None
      }
      for i = 0; i < ps.length(); i = i + 1 {
        patterns.push(
          (TRoot(self.scrutinees[i].uid), self.preprocess_pattern(ps[i])),
        )
      }
    }
    _ => {
      if arity != 1 {
        return None
      }
      patterns.push(
        (TRoot(self.scrutinees[0].uid), self.preprocess_pattern(clause.pattern)),
      )
    }
  }
  let conds : Array[Cond] = [CPatterns(patterns)]
  for g in clause.guards {
    conds.push(self.preprocess_guard(g))
  }
  Some(normalize_conds(conds, index))
}

///|
fn Exhaustivity::check_scrutinees(
  self : Exhaustivity,
  traces : Array[Trace],
  tpes : Array[ValueType],
  clauses : Array[Clause],
) -> Unit {
  if traces.length() == 1 {
    self.check_scrutinee(traces[0], tpes[0], clauses)
    return
  }
  if clauses.length() == 0 {
    self.missing_default(tpes[0], traces[0])
    return
  }
  self.match_clauses(clauses[0], clauses[1:].to_owned())
}

///|
/// Checks whether the `clauses` cover all values the scrutinee at `trace` can
/// take.
fn Exhaustivity::check_scrutinee(
  self : Exhaustivity,
  trace : Trace,
  tpe : ValueType,
  clauses : Array[Clause],
) -> Unit {
  let tpe = self.typer.st.u.prune_value(tpe)
  if tpe == @symbols.t_top() {
    // `Any` is not enumerable: only a default case covers it.
    self.check_other(trace, tpe, clauses)
    return
  }
  match tpe {
    @symbols.ValueType::ValueTypeApp(ctor, _) =>
      match ctor {
        @symbols.Sym::DataType(d) =>
          self.check_datatype(trace, d.constructors, clauses)
        @symbols.Sym::Record(r) =>
          self.check_datatype(trace, [r.constructor], clauses)
        _ =>
          if is_literal_type(tpe) {
            self.check_literal(trace, tpe, clauses)
          } else {
            self.check_other(trace, tpe, clauses)
          }
      }
    _ =>
      if is_literal_type(tpe) {
        self.check_literal(trace, tpe, clauses)
      } else {
        self.check_other(trace, tpe, clauses)
      }
  }
}

///|
fn Exhaustivity::check_other(
  self : Exhaustivity,
  trace : Trace,
  tpe : ValueType,
  clauses : Array[Clause],
) -> Unit {
  if clauses.length() == 0 {
    self.missing_default(tpe, trace)
  } else {
    self.match_clauses(clauses[0], clauses[1:].to_owned())
  }
}

///|
fn Exhaustivity::check_datatype(
  self : Exhaustivity,
  trace : Trace,
  constructors : Array[Sym],
  clauses : Array[Clause],
) -> Unit {
  for ctor in constructors {
    let covered : Array[Clause] = []
    for cl in clauses {
      match cl.matches_on(trace) {
        Some(PTag(c, patterns)) =>
          if c == ctor {
            let fields = constructor_fields(ctor)
            let nested : Array[(Trace, Pat)] = []
            let count = if fields.length() < patterns.length() {
              fields.length()
            } else {
              patterns.length()
            }
            for i = 0; i < count; i = i + 1 {
              nested.push((TChild(ctor, i, trace), patterns[i]))
            }
            covered.push(cl.minus(trace).plus(nested))
          }
        // a clause matching another constructor does not apply
        _ => covered.push(cl)
      }
    }
    if covered.length() == 0 {
      self.missing_tag(ctor, trace)
    } else {
      self.match_clauses(covered[0], covered[1:].to_owned())
    }
  }
}

///|
fn push_covered(
  table : Array[(@source.LiteralValue, Array[Clause])],
  value : @source.LiteralValue,
  clause : Clause,
) -> Unit {
  for entry in table {
    if literal_equal(entry.0, value) {
      entry.1.push(clause)
      return
    }
  }
  table.push((value, [clause]))
}

///|
fn covered_by(
  table : Array[(@source.LiteralValue, Array[Clause])],
  value : @source.LiteralValue,
) -> Array[Clause]? {
  for entry in table {
    if literal_equal(entry.0, value) {
      return Some(entry.1)
    }
  }
  None
}

///|
fn Exhaustivity::check_literal(
  self : Exhaustivity,
  trace : Trace,
  tpe : ValueType,
  clauses : Array[Clause],
) -> Unit {
  let all_literals : Array[@source.LiteralValue] = []
  for cl in clauses {
    match cl.matches_on(trace) {
      Some(PLit(value, _)) =>
        if !all_literals.any(v => literal_equal(v, value)) {
          all_literals.push(value)
        }
      _ => ()
    }
  }
  let table : Array[(@source.LiteralValue, Array[Clause])] = []
  let defaults : Array[Clause] = []
  for cl in clauses {
    match cl.matches_on(trace) {
      Some(PLit(value, _)) => push_covered(table, value, cl.minus(trace))
      _ => {
        // a clause with a wildcard applies to every literal, so it is
        // duplicated for each of them
        for v in all_literals {
          push_covered(table, v, cl)
        }
        defaults.push(cl)
      }
    }
  }
  match literal_domain(tpe) {
    Some(values) =>
      for value in values {
        match covered_by(table, value) {
          Some(cs) =>
            if cs.length() > 0 {
              self.match_clauses(cs[0], cs[1:].to_owned())
            }
          None =>
            if defaults.length() == 0 {
              self.missing_literal(value, trace)
            } else {
              self.match_clauses(defaults[0], defaults[1:].to_owned())
            }
        }
      }
    None => {
      for entry in table {
        if entry.1.length() > 0 {
          self.match_clauses(entry.1[0], entry.1[1:].to_owned())
        }
      }
      if defaults.length() == 0 {
        self.missing_default(tpe, trace)
      } else {
        self.match_clauses(defaults[0], defaults[1:].to_owned())
      }
    }
  }
}

///|
fn Exhaustivity::match_clauses(
  self : Exhaustivity,
  head : Clause,
  alternatives : Array[Clause],
) -> Unit {
  if head.conds.length() == 0 {
    self.use(head.index)
    return
  }
  match head.conds[0] {
    CGuard(span) => {
      // the guard is true: the rest of this clause has to match
      self.match_clauses(normalize_conds(head.rest(), head.index), alternatives)
      // the guard is false: the remaining clauses have to match
      if alternatives.length() == 0 {
        self.missing_guard(span)
      } else {
        self.match_clauses(alternatives[0], alternatives[1:].to_owned())
      }
    }
    CPatterns(patterns) =>
      if patterns.length() == 0 {
        self.match_clauses(
          normalize_conds(head.rest(), head.index),
          alternatives,
        )
      } else {
        // The next scrutinee to check is the one the first condition matches
        // on; its type is the one the pattern expects.
        let (trace, pattern) = patterns[0]
        match pattern {
          PTag(ctor, _) => {
            let tpe = @symbols.constructor_applied_datatype(ctor)
            let all : Array[Clause] = [head]
            for a in alternatives {
              all.push(a)
            }
            self.check_scrutinee(trace, tpe, all)
          }
          PLit(_, tpe) => {
            let all : Array[Clause] = [head]
            for a in alternatives {
              all.push(a)
            }
            self.check_scrutinee(trace, tpe, all)
          }
          PAny => ()
        }
      }
  }
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

///|
fn constructor_pattern(ctor : Sym) -> String {
  let fields = constructor_fields(ctor)
  let name = ctor.name().name
  if fields.length() == 0 {
    return "\{name}()"
  }
  let parts : Array[String] = []
  for _ in fields {
    parts.push("_")
  }
  "\{name}(\{parts.join(", ")})"
}

///|
/// Renders the missing case `acc` at the trace `at`, filling in `_` for the
/// siblings along the way (`Add(Mul(_, Mul(_, _)), _)`).
fn Exhaustivity::trace_to_case(
  self : Exhaustivity,
  at : Trace,
  acc : String,
) -> String {
  match at {
    TRoot(uid) =>
      if self.scrutinees.length() == 1 {
        acc
      } else {
        let parts : Array[String] = []
        for s in self.scrutinees {
          parts.push(if s.uid == uid { acc } else { "_" })
        }
        parts.join(", ")
      }
    TChild(ctor, field, outer) => {
      let fields = constructor_fields(ctor)
      let parts : Array[String] = []
      for i = 0; i < fields.length(); i = i + 1 {
        parts.push(if i == field { acc } else { "_" })
      }
      let text = "\{ctor.name().name}(\{parts.join(", ")})"
      self.trace_to_case(outer, text)
    }
  }
}

///|
fn Exhaustivity::report(self : Exhaustivity) -> Unit {
  for m in self.missing {
    match m {
      MTag(ctor, at) => {
        let text = self.trace_to_case(at, constructor_pattern(ctor))
        self.typer.error(
          self.span,
          "Non-exhaustive pattern matching, missing case \{text}",
        )
      }
      MGuard(span) =>
        self.typer.error(
          span, "Non-exhaustive pattern matching, guard could be false which is not covered",
        )
      MLit(value, at) => {
        let text = self.trace_to_case(at, "\{value}")
        self.typer.error(
          self.span,
          "Non-exhaustive pattern matching, missing case \{text}",
        )
      }
      MDefault(tpe, at) => {
        let text = self.trace_to_case(at, "_")
        self.typer.error(
          self.span,
          "Non-exhaustive pattern matching, scrutinees of type \{tpe} require a default case \{text}",
        )
      }
    }
  }
  for i = 0; i < self.clauses.length(); i = i + 1 {
    if !self.used[i] {
      let clause = self.clauses[i]
      let target = match clause.pattern.kind {
        @source.PatternKind::AnyPattern(_)
        | @source.PatternKind::IgnorePattern => clause.body.span
        _ => clause.span
      }
      self.typer.warning(target, "Unreachable case.")
    }
  }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

///|
/// A `match` whose exhaustiveness is checked once the whole module has been
/// typed. Upstream does this in its wellformedness phase, which is also why an
/// exhaustivity error cannot disqualify an overload candidate here.
pub(all) struct PendingMatch {
  uid : Int32
  scrutinees : Array[Term]
  tpes : Array[ValueType]
  clauses : Array[MatchClause]
  has_default : Bool
  span : Span
}

///|
/// Remembers a `match` for `check_pending_matches`. Repeated visits of the same
/// match (overload resolution checks the same tree more than once) are
/// recorded only once.
fn Typer::defer_exhaustivity(
  self : Typer,
  uid : Int32,
  scrutinees : Array[Term],
  tpes : Array[ValueType],
  clauses : Array[MatchClause],
  has_default : Bool,
  span : Span,
) -> Unit {
  if scrutinees.length() == 0 {
    return
  }
  for p in self.pending_matches {
    if p.uid == uid {
      return
    }
  }
  self.pending_matches.push({
    uid,
    scrutinees,
    tpes,
    clauses,
    has_default,
    span,
  })
}

///|
/// Checks that `clauses` cover every value of the `scrutinees` and reports the
/// clauses no value can reach. `has_default` appends an irrefutable clause for
/// the `else` branch of a `with val`, which (as upstream) makes the match
/// exhaustive.
fn Typer::check_pending_matches(self : Typer) -> Unit {
  for pending in self.pending_matches {
    // the committed annotations hold the final types
    let types : Array[ValueType] = []
    for i = 0; i < pending.scrutinees.length(); i = i + 1 {
      let from_annotation = match
        self.ctx.value_type_of(pending.scrutinees[i].uid) {
        Some(t) => Some(t)
        None => None
      }
      let t = match from_annotation {
        Some(t) => t
        None =>
          if i < pending.tpes.length() {
            pending.tpes[i]
          } else {
            t_top()
          }
      }
      types.push(self.st.u.prune_value(t))
    }
    let clauses = pending.clauses
    let used : Array[Bool] = []
    for i = 0; i <= clauses.length(); i = i + 1 {
      used.push(false)
    }
    let checker : Exhaustivity = {
      typer: self,
      clauses,
      span: pending.span,
      scrutinees: pending.scrutinees,
      used,
      missing: [],
    }
    let initial : Array[Clause] = []
    let mut arity_ok = true
    for i = 0; i < clauses.length(); i = i + 1 {
      match checker.preprocess(clauses[i], i) {
        Some(c) => initial.push(c)
        // the arity mismatch has already been reported while type checking
        None => arity_ok = false
      }
    }
    if !arity_ok {
      continue
    }
    if pending.has_default {
      initial.push({ conds: [], index: -1, })
    }
    let traces : Array[Trace] = pending.scrutinees.map(s => TRoot(s.uid))
    checker.check_scrutinees(traces, types, initial)
    checker.report()
  }
}
