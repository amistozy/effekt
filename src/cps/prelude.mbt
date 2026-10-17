// Names used unqualified throughout the `cps` package.

///|
using @util {type Span, type EffektError, type Template}

///|
using @symbols {type Sym, type ValueType, type BlockType, sym_eq}

///|
using @source {type FeatureFlag, type LiteralValue}

///|
using @core {type Declaration}

///|
/// Raises an internal compiler error. The polymorphic result type lets it stand
/// in for any expected value.
pub fn[T] internal_error(msg : String) -> T raise EffektError {
  raise EffektError::Internal("Internal compiler error: \{msg}")
}

// ---------------------------------------------------------------------------
// Constructor tags of match clauses
// ---------------------------------------------------------------------------

///|
/// The CPS `Clause` of `tree.mbt` has no constructor-tag field (upstream it is
/// `List[(Id, Clause)]`), but the JavaScript backend needs the tag both to emit
/// `switch` cases and to look up the fields of the matched constructor.
///
/// Until `Clause` grows a `tag` field, `cps.transform` appends the tag as the
/// **last** entry of `Clause.vparams`: the value parameters stay first, so
/// `vparams zip fields` (as used by `TransformerCps`) keeps working, and these
/// two helpers are the only place that knows about the encoding.
///
/// Note that the tag is a constructor symbol, so it can never occur free in the
/// clause body; `Clause::free`, `substitute_clause` and `Contify` are therefore
/// unaffected by the extra entry.
pub fn clause_with_tag(vparams : Array[Sym], tag : Sym, body : Stmt) -> Clause {
  Clause::new(vparams + [tag], body)
}

///|
/// The constructor tag of a clause; see `clause_with_tag`.
pub fn clause_tag(clause : Clause) -> Sym {
  clause.vparams[clause.vparams.length() - 1]
}
