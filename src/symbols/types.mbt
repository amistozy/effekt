// The type language of Effekt.
//
// Mirrors `effekt/symbols/types.scala`. Types mention symbols (type
// constructors, type parameters, effect interfaces), so the `Sym` enum lives
// in the same package.

///|
/// Value types.
pub(all) enum ValueType {
  /// The type of a first-class (boxed) block.
  BoxedType(BlockType, Captures)
  /// A reference to a type variable (value or unification variable).
  ValueTypeRef(Sym)
  /// A reference to a type constructor applied to arguments.
  ValueTypeApp(Sym, Array[ValueType])
}

///|
/// Block types: functions and interfaces (effects).
pub(all) enum BlockType {
  /// A (second-class) function type.
  ///
  /// `cparams` holds one capture per block parameter and one per effect.
  FunctionType(
    Array[Sym],
    Array[Captures],
    Array[ValueType],
    Array[BlockType],
    ValueType,
    Effects
  )
  /// An effect / capability type, e.g. `State[Int]`.
  InterfaceType(Sym, Array[ValueType])
}

///|
/// Convenience: is this block type an interface (effect) type?
pub fn BlockType::is_interface(self : BlockType) -> Bool {
  match self {
    InterfaceType(_, _) => true
    _ => false
  }
}

///|
pub fn BlockType::interface_name(self : BlockType) -> Name? {
  match self {
    InterfaceType(ctor, _) => Some(ctor.name())
    _ => None
  }
}

///|
pub fn BlockType::interface_ctor(self : BlockType) -> Sym? {
  match self {
    InterfaceType(ctor, _) => Some(ctor)
    _ => None
  }
}

///|
/// A set of effects. Effect sets carry no order and are deduplicated on
/// demand; keeping duplicates around is important while substituting types.
pub(all) struct Effects {
  effects : Array[BlockType]
}

///|
pub fn Effects::new(effects : Array[BlockType]) -> Effects {
  { effects, }
}

///|
pub fn Effects::empty() -> Effects {
  { effects: [], }
}

///|
pub fn Effects::is_empty(self : Effects) -> Bool {
  self.effects.length() == 0
}

///|
pub fn Effects::non_empty(self : Effects) -> Bool {
  self.effects.length() != 0
}

///|
pub fn Effects::size(self : Effects) -> Int32 {
  self.effects.length()
}

///|
pub fn Effects::to_list(self : Effects) -> Array[BlockType] {
  dedup_blocks(self.effects)
}

///|
pub fn Effects::union(self : Effects, other : Effects) -> Effects {
  { effects: self.effects + other.effects, }
}

///|
pub fn Effects::filter_not(self : Effects, p : (BlockType) -> Bool) -> Effects {
  { effects: self.effects.filter(x => !p(x)), }
}

///|
pub fn Effects::forall(self : Effects, p : (BlockType) -> Bool) -> Bool {
  self.effects.all(p)
}

///|
pub fn Effects::exists(self : Effects, p : (BlockType) -> Bool) -> Bool {
  self.effects.any(p)
}

///|
pub fn Effects::distinct(self : Effects) -> Effects {
  { effects: dedup_blocks(self.effects), }
}

///|
fn dedup_blocks(xs : Array[BlockType]) -> Array[BlockType] {
  let out : Array[BlockType] = []
  for x in xs {
    if !out.any(y => block_type_equal(x, y)) {
      out.push(x)
    }
  }
  out
}

///|
/// Structural equality on block types.
pub fn block_type_equal(a : BlockType, b : BlockType) -> Bool {
  interface_type_equal(a, b)
}

///|
/// Structural equality specialised to interface (effect) types. Used for
/// effect-set membership and for the canonical ordering substitute.
pub fn interface_type_equal(a : BlockType, b : BlockType) -> Bool {
  match (a, b) {
    (InterfaceType(c1, args1), InterfaceType(c2, args2)) =>
      c1.uid() == c2.uid() && value_types_equal(args1, args2)
    (FunctionType(_, _, _, _, _, _), _) => false
    (_, FunctionType(_, _, _, _, _, _)) => false
  }
}

///|
pub fn value_types_equal(a : Array[ValueType], b : Array[ValueType]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i = 0; i < a.length(); i = i + 1 {
    if !value_type_equal(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
pub fn value_type_equal(a : ValueType, b : ValueType) -> Bool {
  match (a, b) {
    (ValueTypeRef(s1), ValueTypeRef(s2)) => s1.uid() == s2.uid()
    (ValueTypeApp(c1, args1), ValueTypeApp(c2, args2)) =>
      c1.uid() == c2.uid() && value_types_equal(args1, args2)
    (BoxedType(t1, _), BoxedType(t2, _)) => interface_type_equal(t1, t2)
    _ => false
  }
}

///|
/// The canonical ordering of effects. This must be stable and total on
/// concrete (unification-variable free) types, otherwise capability passing
/// gets out of sync — see upstream issue #108.
pub fn canonical_order(effs : Array[BlockType]) -> Array[BlockType] {
  let sorted = effs.copy()
  sorted.sort_by((a, b) => canonical_compare(a, b))
  sorted
}

///|
pub fn canonical_compare(a : BlockType, b : BlockType) -> Int32 {
  match (a, b) {
    (InterfaceType(c1, args1), InterfaceType(c2, args2)) =>
      if c1.uid() != c2.uid() {
        c1.uid() - c2.uid()
      } else {
        canonical_compare_value_lists(args1, args2)
      }
    (InterfaceType(_, _), _) => -1
    (_, InterfaceType(_, _)) => 1
    _ => 0
  }
}

///|
fn canonical_compare_value_lists(
  a : Array[ValueType],
  b : Array[ValueType],
) -> Int32 {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  for i = 0; i < n; i = i + 1 {
    let c = canonical_compare_value(a[i], b[i])
    if c != 0 {
      return c
    }
  }
  a.length() - b.length()
}

///|
pub fn canonical_compare_value(a : ValueType, b : ValueType) -> Int32 {
  match (a, b) {
    (ValueTypeRef(s1), ValueTypeRef(s2)) => s1.uid() - s2.uid()
    (ValueTypeRef(_), _) => -1
    (_, ValueTypeRef(_)) => 1
    (ValueTypeApp(c1, args1), ValueTypeApp(c2, args2)) =>
      if c1.uid() != c2.uid() {
        c1.uid() - c2.uid()
      } else {
        canonical_compare_value_lists(args1, args2)
      }
    (ValueTypeApp(_, _), _) => -1
    (_, ValueTypeApp(_, _)) => 1
    (BoxedType(t1, _), BoxedType(t2, _)) => canonical_compare(t1, t2)
  }
}
