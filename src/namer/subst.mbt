// Type-only substitution, used by the namer to dealias type and effect
// aliases on the fly (see `resolve_value_type` / `resolve_with_aliases`).
//
// This is the type part of `effekt/typer/Substitution.scala`. The namer never
// substitutes captures: `Substitutions.types` upstream is built with an empty
// capture map, so capture sets are left untouched.

///|
/// A substitution of type variables (type parameters) by value types.
priv struct TypeSubst {
  keys : Array[Sym]
  values : Array[ValueType]
}

///|
fn TypeSubst::new(keys : Array[Sym], values : Array[ValueType]) -> TypeSubst {
  { keys, values, }
}

///|
fn TypeSubst::lookup(self : TypeSubst, key : Sym) -> ValueType? {
  for i = 0; i < self.keys.length(); i = i + 1 {
    if self.keys[i].uid() == key.uid() {
      return Some(self.values[i])
    }
  }
  None
}

///|
/// The substitution without the given (shadowed) type parameters.
fn TypeSubst::without(self : TypeSubst, shadowed : Array[Sym]) -> TypeSubst {
  let keys : Array[Sym] = []
  let values : Array[ValueType] = []
  for i = 0; i < self.keys.length(); i = i + 1 {
    if !shadowed.contains(self.keys[i]) {
      keys.push(self.keys[i])
      values.push(self.values[i])
    }
  }
  { keys, values, }
}

///|
fn TypeSubst::value_type(self : TypeSubst, tpe : ValueType) -> ValueType {
  match tpe {
    @symbols.ValueTypeRef(x) =>
      match self.lookup(x) {
        Some(t) => t
        None => tpe
      }
    @symbols.ValueTypeApp(ctor, args) =>
      @symbols.ValueTypeApp(ctor, args.map(a => self.value_type(a)))
    @symbols.BoxedType(inner, capt) =>
      @symbols.BoxedType(self.block_type(inner), capt)
  }
}

///|
fn TypeSubst::block_type(self : TypeSubst, tpe : BlockType) -> BlockType {
  match tpe {
    @symbols.InterfaceType(ctor, args) =>
      @symbols.InterfaceType(ctor, args.map(a => self.value_type(a)))
    @symbols.FunctionType(tparams, caps, vparams, bparams, result, effects) => {
      // Do not substitute the type parameters bound by this function type.
      let inner = self.without(tparams)
      @symbols.FunctionType(
        tparams,
        caps,
        vparams.map(v => inner.value_type(v)),
        bparams.map(b => inner.block_type(b)),
        inner.value_type(result),
        inner.effects(effects),
      )
    }
  }
}

///|
fn TypeSubst::effects(self : TypeSubst, effs : Effects) -> Effects {
  @symbols.Effects::new(effs.effects.map(e => self.block_type(e)))
}
