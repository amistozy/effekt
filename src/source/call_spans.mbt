// The spans of a call's argument lists.
//
// Upstream's AST carries the arguments of a call as `Many[T]` — a list together
// with the span it was written at — and a diagnostic about an implicit argument
// points at the list the argument would be filled into (`GenerateImplicitArgs`
// passes `vargs.span` / `bargs.span` on to the generated tree, and the failure is
// reported at that tree's span). This port keeps the arguments as plain arrays,
// so the parser records the two spans here, keyed by the uid of the call node.
//
// Keys are term uids, which are unique for the whole process, and only call
// nodes are recorded. `clear_argument_spans` lets the driver drop them between
// modules.

///|
let argument_spans : Map[Int32, (Span, Span)] = Map([])

///|
/// Records the spans of the value and block arguments of a call node.
pub fn record_argument_spans(uid : Int32, vargs : Span, bargs : Span) -> Unit {
  argument_spans.set(uid, (vargs, bargs))
}

///|
/// The spans of the value and block arguments of a call node, if it was parsed
/// (a synthesized call has none).
pub fn argument_spans_of(uid : Int32) -> (Span, Span)? {
  argument_spans.get(uid)
}

///|
pub fn clear_argument_spans() -> Unit {
  argument_spans.clear()
}
