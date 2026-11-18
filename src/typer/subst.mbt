// Substitutions.
//
// Mirrors `effekt/typer/Substitution.scala`. A substitution maps
//   - value type variables (by symbol uid) to value types, and
//   - capture variables (by symbol uid) to capture sets.

///|
pub struct Substitutions {
  values : Map[Int32, ValueType]
  captures : Map[Int32, Captures]
}

///|
pub fn Substitutions::empty() -> Substitutions {
  { values: Map([]), captures: Map([]), }
}

///|
pub fn Substitutions::types(
  keys : ArrayView[Sym],
  values : ArrayView[ValueType],
) -> Substitutions {
  let m : Map[Int32, ValueType] = Map([])
  for i in 0..<keys.length().min(values.length()) {
    m.set(keys[i].uid(), values[i])
  }
  { values: m, captures: Map([]), }
}

///|
pub fn Substitutions::captures(
  keys : ArrayView[Sym],
  values : ArrayView[Captures],
) -> Substitutions {
  let m : Map[Int32, Captures] = Map([])
  for i in 0..<keys.length().min(values.length()) {
    m.set(keys[i].uid(), values[i])
  }
  { values: Map([]), captures: m, }
}

///|
pub fn Substitutions::is_empty(self : Substitutions) -> Bool {
  self.values.is_empty() && self.captures.is_empty()
}

///|
/// Parallel composition (`++` upstream): the right-hand side wins.
fn Substitutions::compose(
  self : Substitutions,
  other : Substitutions,
) -> Substitutions {
  {
    values: self.values.merge(other.values),
    captures: self.captures.merge(other.captures),
  }
}

///|
pub fn Substitutions::bind_value(
  self : Substitutions,
  key : Sym,
  value : ValueType,
) -> Unit {
  self.values.set(key.uid(), value)
}

///|
/// Removes the given type and capture parameters (shadowing).
pub fn Substitutions::without(
  self : Substitutions,
  tps : ArrayView[Sym],
  cps : ArrayView[Sym],
) -> Substitutions {
  let values : Map[Int32, ValueType] = Map([])
  for k, v in self.values {
    if !tps.any(t => t.uid() == k) {
      values.set(k, v)
    }
  }
  let captures : Map[Int32, Captures] = Map([])
  for k, v in self.captures {
    if !cps.any(c => c.uid() == k) {
      captures.set(k, v)
    }
  }
  { values, captures, }
}

// Substitution
// ------------

///|
/// Applies the substitution to a capture set. Capture variables that are
/// substituted by a concrete set are expanded; everything else is kept.
pub fn Substitutions::substitute_captures(
  self : Substitutions,
  c : Captures,
) -> Captures {
  match c {
    @symbols.Captures::CaptVar(x) => self.captures.get(x.uid()).unwrap_or(c)
    @symbols.Captures::CaptureSetOf(cs) =>
      @symbols.captures_union(cs, s => self.captures.get(s.uid()))
  }
}

///|
fn Substitutions::substitute_value(
  self : Substitutions,
  t : ValueType,
) -> ValueType {
  match t {
    @symbols.ValueType::ValueTypeRef(x) => self.values.get(x.uid()).unwrap_or(t)
    @symbols.ValueType::ValueTypeApp(c, args) =>
      @symbols.ValueType::ValueTypeApp(
        c,
        args.map(a => self.substitute_value(a)),
      )
    @symbols.ValueType::BoxedType(b, c) =>
      @symbols.ValueType::BoxedType(
        self.substitute_block(b),
        self.substitute_captures(c),
      )
  }
}

///|
fn Substitutions::substitute_effects(
  self : Substitutions,
  e : Effects,
) -> Effects {
  Effects(e.effects.map(x => self.substitute_block(x)))
}

///|
pub fn Substitutions::substitute_block(
  self : Substitutions,
  t : BlockType,
) -> BlockType {
  match t {
    @symbols.BlockType::InterfaceType(c, args) =>
      @symbols.BlockType::InterfaceType(
        c,
        args.map(a => self.substitute_value(a)),
      )
    @symbols.BlockType::FunctionType(tparams, capts, vps, bps, ret, effs) => {
      // Do not substitute the parameters bound by this function.
      let inner = self.without(tparams, capture_params_of(capts))
      @symbols.BlockType::FunctionType(
        tparams,
        capts.map(c => inner.substitute_captures(c)),
        vps.map(v => inner.substitute_value(v)),
        bps.map(b => inner.substitute_block(b)),
        inner.substitute_value(ret),
        inner.substitute_effects(effs),
      )
    }
  }
}
