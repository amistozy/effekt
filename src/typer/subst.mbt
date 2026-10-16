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
  { values: Map::new(), captures: Map::new(), }
}

///|
pub fn Substitutions::types(
  keys : Array[Sym],
  values : Array[ValueType],
) -> Substitutions {
  let m : Map[Int32, ValueType] = Map::new()
  for i = 0; i < keys.length() && i < values.length(); i = i + 1 {
    m.set(keys[i].uid(), values[i])
  }
  { values: m, captures: Map::new(), }
}

///|
pub fn Substitutions::captures(
  keys : Array[Sym],
  values : Array[Captures],
) -> Substitutions {
  let m : Map[Int32, Captures] = Map::new()
  for i = 0; i < keys.length() && i < values.length(); i = i + 1 {
    m.set(keys[i].uid(), values[i])
  }
  { values: Map::new(), captures: m, }
}

///|
pub fn Substitutions::is_empty(self : Substitutions) -> Bool {
  self.values.size() == 0 && self.captures.size() == 0
}

///|
/// Parallel composition (`++` upstream): the right-hand side wins.
pub fn Substitutions::compose(
  self : Substitutions,
  other : Substitutions,
) -> Substitutions {
  let values = self.values.copy()
  for k, v in other.values {
    values.set(k, v)
  }
  let captures = self.captures.copy()
  for k, v in other.captures {
    captures.set(k, v)
  }
  { values, captures, }
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
pub fn Substitutions::bind_captures(
  self : Substitutions,
  key : Sym,
  value : Captures,
) -> Unit {
  self.captures.set(key.uid(), value)
}

///|
/// Removes the given type and capture parameters (shadowing).
pub fn Substitutions::without(
  self : Substitutions,
  tps : Array[Sym],
  cps : Array[Sym],
) -> Substitutions {
  let values : Map[Int32, ValueType] = Map::new()
  for k, v in self.values {
    if !tps.any(t => t.uid() == k) {
      values.set(k, v)
    }
  }
  let captures : Map[Int32, Captures] = Map::new()
  for k, v in self.captures {
    if !cps.any(c => c.uid() == k) {
      captures.set(k, v)
    }
  }
  { values, captures, }
}

///|
pub fn Substitutions::value_of(self : Substitutions, x : Sym) -> ValueType? {
  self.values.get(x.uid())
}

///|
pub fn Substitutions::captures_of(self : Substitutions, x : Sym) -> Captures? {
  self.captures.get(x.uid())
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
    @symbols.Captures::CaptVar(x) =>
      match self.captures.get(x.uid()) {
        Some(s) => s
        None => c
      }
    @symbols.Captures::CaptureSetOf(cs) => {
      let out : Array[Sym] = []
      for s in cs {
        match self.captures.get(s.uid()) {
          Some(@symbols.Captures::CaptureSetOf(ys)) =>
            for y in ys {
              if !sym_in(y, out) {
                out.push(y)
              }
            }
          Some(@symbols.Captures::CaptVar(y)) =>
            if !sym_in(y, out) {
              out.push(y)
            }
          None => if !sym_in(s, out) { out.push(s) }
        }
      }
      @symbols.Captures::CaptureSetOf(out)
    }
  }
}

///|
pub fn Substitutions::substitute_value(
  self : Substitutions,
  t : ValueType,
) -> ValueType {
  match t {
    @symbols.ValueType::ValueTypeRef(x) =>
      match self.values.get(x.uid()) {
        Some(t) => t
        None => t
      }
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
pub fn Substitutions::substitute_effects(
  self : Substitutions,
  e : Effects,
) -> Effects {
  Effects::new(e.effects.map(x => self.substitute_block(x)))
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
