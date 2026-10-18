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
    if !out.any(y => interface_type_equal(x, y)) {
      out.push(x)
    }
  }
  out
}

///|
/// The effect-set membership relation. It is *coarser* than `Eq`:
/// capture sets are ignored, and function types compare as false even to
/// themselves (they never occur in effect sets, and unfolding them here can
/// loop). Keep it separate from `Eq` — an equivalence relation has to be
/// reflexive, this one is not.
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
/// Equality up to capture sets, used by `interface_type_equal` for the
/// arguments of an effect. This is *not* the structural `Eq` (see below):
/// it ignores captures and treats boxed function types as never equal.
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

// ---------------------------------------------------------------------------
// Structural equality and printing
//
// These are `Eq` / `Show` instead of ad-hoc helpers so that `==` and
// `"\{t}"` work at every call site. `value_type_equal` and
// `interface_type_equal` above are a *different*, coarser relation: they
// ignore capture sets and are not reflexive on function types, so they cannot
// be `Eq` without breaking its laws.
// ---------------------------------------------------------------------------

///|
/// Structural equality: same constructor, symbols by identity, capture sets
/// compared as sets (see `Eq for Captures`).
pub impl Eq for ValueType with fn equal(self, other) {
  match (self, other) {
    (ValueTypeRef(x), ValueTypeRef(y)) => x == y
    (ValueTypeApp(c1, args1), ValueTypeApp(c2, args2)) =>
      c1 == c2 && args1 == args2
    (BoxedType(b1, c1), BoxedType(b2, c2)) => b1 == b2 && c1 == c2
    _ => false
  }
}

///|
/// Structural equality, including function types (which the effect-set
/// relation refuses to compare at all).
pub impl Eq for BlockType with fn equal(self, other) {
  match (self, other) {
    (InterfaceType(c1, args1), InterfaceType(c2, args2)) =>
      c1 == c2 && args1 == args2
    (
      FunctionType(cps1, capts1, vps1, bps1, ret1, effs1),
      FunctionType(cps2, capts2, vps2, bps2, ret2, effs2),
    ) =>
      cps1 == cps2 &&
      capts1 == capts2 &&
      vps1 == vps2 &&
      bps1 == bps2 &&
      ret1 == ret2 &&
      effs1 == effs2
    _ => false
  }
}

///|
/// Effect sets are unordered and keep duplicates, so equality is set equality
/// of their interfaces.
pub impl Eq for Effects with fn equal(self, other) {
  let xs = self.distinct().effects
  let ys = other.distinct().effects
  xs.length() == ys.length() &&
  xs.all(x => ys.any(y => interface_type_equal(x, y)))
}

///|
fn show_type_application(name : Name, args : Array[ValueType]) -> String {
  if args.length() == 0 {
    name.qualified_name()
  } else {
    let rendered = args.map(a => "\{a}")
    "\{name.qualified_name()}[\{rendered.join(", ")}]"
  }
}

///|
/// Effekt surface syntax, qualified and on one line: this is what diagnostics
/// print. It is not what `--show-core` prints — that is `@core.pretty`, which
/// lays out a whole module through `Doc` at a fixed width.
pub impl Show for ValueType with fn output(self, logger) {
  match self {
    ValueTypeRef(s) => logger.write_string(s.name().qualified_name())
    ValueTypeApp(c, args) =>
      logger.write_string(show_type_application(c.name(), args))
    BoxedType(b, c) => logger.write_string("box \{b} at \{c}")
  }
}

///|
pub impl Show for BlockType with fn output(self, logger) {
  match self {
    InterfaceType(c, args) =>
      logger.write_string(show_type_application(c.name(), args))
    FunctionType(_, _, vps, bps, ret, effs) => {
      let args : Array[String] = vps.map(v => "\{v}")
      for b in bps {
        args.push("{\{b}}")
      }
      logger.write_string("(\{args.join(", ")} => \{ret} / \{effs})")
    }
  }
}

///|
pub impl Show for Effects with fn output(self, logger) {
  let names = self.distinct().effects.map(e => "\{e}")
  logger.write_string("{\{names.join(", ")}}")
}
