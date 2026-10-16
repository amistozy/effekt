// Kind well-formedness checks on resolved types.
//
// Mirrors `effekt/symbols/kinds.scala`, trimmed to what the namer can produce:
// type constructor arity and the capture parameter invariant of function
// types. Upstream checks these in `Namer.resolvingType`, so a type alias that
// is applied to the wrong number of arguments is reported at its use site.

///|
/// The number of type parameters a value type constructor expects, or -1 if
/// the symbol is not a value type constructor (in which case we do not check).
fn value_type_constructor_arity(ctor : Sym) -> Int32 {
  match ctor {
    @symbols.Sym::DataType(d) => d.tparams.length()
    @symbols.Sym::Record(r) => r.tparams.length()
    @symbols.Sym::ExternType(t) => t.tparams.length()
    @symbols.Sym::ErrorValueType(t) => t.tparams.length()
    _ => -1
  }
}

///|
/// The number of type parameters a block type constructor expects, or -1.
fn block_type_constructor_arity(ctor : Sym) -> Int32 {
  match ctor {
    @symbols.Sym::Interface(i) => i.tparams.length()
    @symbols.Sym::ExternInterface(i) => i.tparams.length()
    @symbols.Sym::ErrorBlockType(t) => t.tparams.length()
    _ => -1
  }
}

///|
fn wellformed_value_type(
  context : @source.Context,
  tpe : ValueType,
  span : Span,
) -> Unit raise EffektError {
  match tpe {
    @symbols.BoxedType(inner, _) => wellformed_block_type(context, inner, span)
    @symbols.ValueTypeRef(_) => ()
    @symbols.ValueTypeApp(ctor, args) => {
      let arity = value_type_constructor_arity(ctor)
      if arity == 0 && args.length() > 0 {
        context.abort(
          span,
          "Cannot apply type " +
          ctor.name().qualified_name() +
          ". Type " +
          ctor.name().qualified_name() +
          " does not expect any arguments, but is applied to " +
          args.length().to_string() +
          ".",
        )
      } else if arity > 0 && args.length() != arity {
        context.abort(
          span,
          "Wrong type constructor arity. Type constructor " +
          ctor.name().qualified_name() +
          " expects " +
          arity.to_string() +
          " parameters, but got " +
          args.length().to_string() +
          " arguments.",
        )
      }
      for a in args {
        wellformed_value_type(context, a, span)
      }
    }
  }
}

///|
fn wellformed_block_type(
  context : @source.Context,
  tpe : BlockType,
  span : Span,
) -> Unit raise EffektError {
  match tpe {
    @symbols.InterfaceType(ctor, args) => {
      let arity = block_type_constructor_arity(ctor)
      if arity > 0 && args.length() != arity {
        context.abort(
          span,
          "Wrong number of type arguments. Interface " +
          ctor.name().qualified_name() +
          " expects " +
          arity.to_string() +
          " parameters, but got " +
          args.length().to_string() +
          " arguments.",
        )
      }
      for a in args {
        wellformed_value_type(context, a, span)
      }
    }
    @symbols.FunctionType(_, caps, vparams, bparams, result, effects) => {
      let distinct = effects.distinct()
      if caps.length() != bparams.length() + distinct.effects.length() {
        context.panic(
          "Compiler invariant violated: different number of capture parameters and block parameters.",
        )
      }
      for v in vparams {
        wellformed_value_type(context, v, span)
      }
      for b in bparams {
        wellformed_block_type(context, b, span)
      }
      wellformed_value_type(context, result, span)
      for e in distinct.effects {
        wellformed_block_type(context, e, span)
      }
    }
  }
}
