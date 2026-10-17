// Exhaustivity checking for `match`.
//
// Mirrors `effekt/typer/ExhaustivityChecker.scala`, simplified: we check the
// *top level* of each clause pattern for missing constructors and treat any
// irrefutable pattern (wildcard, variable, or a `default` branch) as covering
// everything. Nested patterns, literal coverage and the "informative" error
// messages of upstream are not implemented (see the report).

///|
/// The constructors of the data type a value type refers to.
pub fn datatype_constructors(t : ValueType) -> Array[Sym] {
  match t {
    @symbols.ValueType::ValueTypeApp(ctor, _) =>
      match ctor {
        @symbols.Sym::DataType(d) => d.constructors
        @symbols.Sym::Record(r) => [r.constructor_]
        _ => []
      }
    _ => []
  }
}

///|
/// Reports missing cases of a `match` with a single scrutinee.
pub fn Typer::check_exhaustive(
  self : Typer,
  scrutinee : Term,
  clauses : Array[MatchClause],
  span : Span,
) -> Unit {
  let scrutinee_type = match self.st.ann.value.get(scrutinee.uid) {
    Some(t) => self.st.u.prune_value(t)
    None => return
  }
  let constructors = datatype_constructors(scrutinee_type)
  if constructors.length() == 0 {
    // An abstract or primitive type: we cannot enumerate its values.
    return
  }
  let covered : Array[Sym] = []
  for clause in clauses {
    match clause.pattern.kind {
      // Irrefutable patterns cover everything.
      @source.PatternKind::IgnorePattern => return
      @source.PatternKind::AnyPattern(_) => return
      @source.PatternKind::MultiPattern(_) =>
        // We do not check matches with several scrutinees.
        return
      @source.PatternKind::LiteralPattern(_, _) =>
        // Literals only cover a single value; we cannot enumerate the rest.
        return
      @source.PatternKind::TagPattern(id, _) =>
        match self.ctx.symbol_of(id.uid) {
          Some(s) => covered.push(s)
          None => ()
        }
    }
  }
  let missing = constructors.filter(c => !sym_in(c, covered))
  if missing.length() > 0 {
    let names : Array[String] = missing.map(c => c.name().name)
    self.error(
      span,
      "Non-exhaustive match: missing case" +
      (if missing.length() == 1 { "" } else { "s" }) +
      " for \{names.join(", ")}.",
    )
  }
}
