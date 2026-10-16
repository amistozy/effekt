// Unique identifiers.
//
// Every syntax tree node carries a unique `Int` id. The compiler uses these
// ids to key side tables (resolved symbols, inferred types, capture sets),
// which replaces the object-identity based annotation maps of the upstream
// Scala implementation.

///|
let uid_counter : Ref[Int32] = Ref(0)

///|
pub fn fresh_uid() -> Int32 {
  let n = uid_counter.val
  uid_counter.val = n + 1
  n
}

///|
/// Resets the counter. Only used by tests to get deterministic output.
pub fn reset_uid() -> Unit {
  uid_counter.val = 0
}
