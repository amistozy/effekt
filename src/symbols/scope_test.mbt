// Tests for the bindings that the namer builds while opening modules.
//
// Upstream models a scope as a *set* of symbols per name (`Bindings.terms` is a
// `Set`), so opening the same module through two import paths cannot make its
// terms look ambiguous. `Bindings` here holds arrays, so binding the same symbol
// twice has to be a no-op — `Tuple2` used to become ambiguous in `list`/`array`
// and in everything that imports them.

///|
test "binding the same symbol twice is a no-op" {
  let b = @symbols.Bindings::empty()
  let sym = @symbols.Sym::capture_param(@symbols.Name::local("Tuple2"))
  b.add_term("Tuple2", sym)
  b.add_term("Tuple2", sym)
  assert_true(b.terms.get("Tuple2") is Some([s]) && @symbols.sym_eq(s, sym))
}

///|
test "binding different symbols under one name stays ambiguous" {
  let b = @symbols.Bindings::empty()
  let first = @symbols.Sym::capture_param(@symbols.Name::local("Tuple2"))
  let second = @symbols.Sym::capture_param(@symbols.Name::local("Tuple2"))
  b.add_term("Tuple2", first)
  b.add_term("Tuple2", second)
  let bound = b.terms.get("Tuple2").unwrap()
  assert_eq(bound.length(), 2)
  assert_false(@symbols.sym_eq(bound[0], bound[1]))
}

///|
test "importing a module twice does not duplicate its terms" {
  let source = @symbols.Bindings::empty()
  let sym = @symbols.Sym::capture_param(@symbols.Name::local("Nil"))
  source.add_term("Nil", sym)
  let target = @symbols.Bindings::empty()
  target.import_all(source)
  target.import_all(source)
  assert_eq(target.terms.get("Nil").unwrap().length(), 1)
}
