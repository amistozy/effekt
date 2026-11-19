// Copy-on-write tables for the backtrackable typer state.
//
// `TyperState::backup` has to hand the snapshot and the live state independent
// tables, but the state is a handful of module-wide maps and an overload
// candidate writes only some of them before it is rolled back. Copying them
// eagerly costs a full walk of every table for every candidate *and* for every
// state that is kept; here a snapshot shares the tables and marks them frozen,
// and the first write through either side copies that one table.

///|
/// A table that copies itself when it is written while shared.
pub(all) struct CowMap[V] {
  mut data : Map[Int32, V]
  mut frozen : Bool
}

///|
fn[V] CowMap::new() -> CowMap[V] {
  { data: Map([]), frozen: false, }
}

///|
fn[V] CowMap::get(self : CowMap[V], key : Int32) -> V? {
  self.data.get(key)
}

///|
fn[V] CowMap::contains(self : CowMap[V], key : Int32) -> Bool {
  self.data.contains(key)
}

///|
fn[V] CowMap::set(self : CowMap[V], key : Int32, value : V) -> Unit {
  if self.frozen {
    self.data = self.data.copy()
    self.frozen = false
  }
  self.data.set(key, value)
}

///|
fn[V] CowMap::iter2(self : CowMap[V]) -> Iter2[Int32, V] {
  self.data.iter2()
}

///|
/// The underlying table, shared for reading. The caller must not write it (the
/// type checker uses this to read the live tables through Substitutions).
fn[V] CowMap::view(self : CowMap[V]) -> Map[Int32, V] {
  self.data
}

///|
/// The snapshot side of a table: shares it and freezes both sides, so neither
/// writes it in place again.
fn[V] CowMap::snapshot(self : CowMap[V]) -> CowMap[V] {
  self.frozen = true
  { data: self.data, frozen: true, }
}
