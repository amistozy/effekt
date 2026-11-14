// Core type inference: upstream `core/Type.scala`'s `Type.inferType` and
// `Type.inferCapt`.
//
// Upstream keeps the type of a core node implicit but recoverable: the
// transformer annotates value variables, block variables, `Match` and `Hole`
// with the types it looked up in the typing context, and `inferType` is a
// syntactic recursion over those annotations. The rest of `Type.scala` is a
// checker (`Typing`, `Constraints`, `Type.typecheck`) that upstream only runs
// in debug mode; the optimizer reads types through `inferType`.
//
// The deviations are all consequences of core reusing the source type language
// (see the README):
//
// - `FunctionType` has a single result, so a block that returns zero or several
//   values has no core type; `single` raises `Internal` for it, as upstream's
//   `single` reports a type error.
// - `Match` and `Hole` carry one annotated type, so the inferred list has one
//   element.
// - `BlockType.Resume` does not exist: the transformer types a shift
//   continuation as the one-argument function type `(result) => answer` (see
//   `Transformer::transform_op_clause`), so `Shift` reads the result off that
//   function's value parameter and `Resume` off its result.
// - `Make` records the data type constructor and the type arguments separately,
//   so the inferred type is `ValueTypeApp(data, targs)`.

///|
/// Upstream `Type.single`: expressions (and thus FFI calls) produce exactly one
/// value.
fn single(tpes : Array[ValueType]) -> ValueType raise EffektError {
  if tpes.length() == 1 {
    return tpes[0]
  }
  raise EffektError::Internal(
    "Expected exactly one value, but got: \{tpes.map(t => "\{t}").join(", ")}",
  )
}

///|
/// Upstream `Type.instantiate`: substitutes the type and capture arguments of a
/// function type and drops the parameters, which the arguments have bound.
fn instantiate(
  tpe : BlockType,
  targs : Array[ValueType],
  cargs : Array[Captures],
) -> BlockType raise EffektError {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result, _effects) => {
      if targs.length() != tparams.length() {
        raise EffektError::Internal(
          "Wrong number of type arguments: expected \{tparams.length()}, got \{targs.length()}",
        )
      }
      if cargs.length() != cparams.length() {
        raise EffektError::Internal(
          "Wrong number of capture arguments: expected \{cparams.length()}, got \{cargs.length()}",
        )
      }
      let tsubst : Map[Int32, ValueType] = Map([])
      for i = 0; i < tparams.length(); i = i + 1 {
        tsubst.set(tparams[i].uid(), targs[i])
      }
      let csubst : Map[Int32, Captures] = Map([])
      for i = 0; i < cparams.length(); i = i + 1 {
        // A capture parameter is a (usually singleton) capture set here, while
        // upstream stores the id directly.
        for c in cparams[i].to_array() {
          csubst.set(c.uid(), cargs[i])
        }
      }
      FunctionType(
        [],
        [],
        vparams.map(t => substitute_value_type_with(t, tsubst, Map([]))),
        bparams.map(t => substitute_block_type_with(t, tsubst, Map([]))),
        substitute_value_type_with(result, tsubst, csubst),
        Effects::empty(),
      )
    }
    _ =>
      raise EffektError::Internal("Expected a function type, but got: \{tpe}")
  }
}

///|
/// The result of a function type.
fn function_result(tpe : BlockType) -> ValueType raise EffektError {
  match tpe {
    FunctionType(_, _, _, _, result, _) => result
    _ =>
      raise EffektError::Internal("Expected a function type, but got: \{tpe}")
  }
}

///|
/// The result of applying a block of type `tpe`. A callee whose type is the
/// placeholder `unknown_block_type()` yields the unknown value type: the port's
/// trees contain such callees where the transformer had no annotation (e.g. the
/// join points of the pattern-match compiler), while upstream always has a
/// function type at this point.
fn instantiated_result(
  tpe : BlockType,
  targs : Array[ValueType],
  cargs : Array[Captures],
) -> ValueType raise EffektError {
  if is_unknown_block_type(tpe) {
    return unknown_value_type()
  }
  function_result(instantiate(tpe, targs, cargs))
}

///|
/// Unions the captures of the given items, as upstream's `allCapt`.
fn[T] union_captures(
  xs : Array[T],
  f : (T) -> Captures raise EffektError,
) -> Captures raise EffektError {
  let mut out = Captures::empty()
  for x in xs {
    out = out.union(f(x))
  }
  out
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

///|
/// Upstream `Type.inferType` on statements.
fn Stmt::infer_type(self : Stmt) -> Array[ValueType] raise EffektError {
  match self {
    Def(_, _, body) => body.infer_type()
    Let(_, _, body) => body.infer_type()
    ImpureApp(_, _, _, _, _, body) => body.infer_type()
    Return(exprs) => exprs.map(e => e.infer_type())
    Val(_, _, body) => body.infer_type()
    App(callee, targs, _, bargs) =>
      [
        instantiated_result(
          callee.infer_type(),
          targs,
          bargs.map(b => b.infer_capt()),
        ),
      ]
    Invoke(_, _, method_tpe, targs, _, bargs) =>
      [instantiated_result(method_tpe, targs, bargs.map(b => b.infer_capt()))]
    If(_, thn, _) => thn.infer_type()
    Match(_, annotated, _, _) => [annotated]
    // A region (like `reset`) returns what its body returns.
    Region(body) => body.body.infer_type()
    Alloc(_, _, _, body) => body.infer_type()
    Var(_, _, _, body) => body.infer_type()
    Get(_, _, _, _, body) => body.infer_type()
    Put(_, _, _, body) => body.infer_type()
    Reset(body) => body.body.infer_type()
    Shift(_, k, _) =>
      // Upstream: `k.tpe` is a resumption `(from) ~> to` and the answer is
      // `from`; the port types `k` as `(from) => to` (see the file header).
      match k.tpe {
        FunctionType(_, _, vparams, _, _, _) =>
          match vparams {
            [tpe] => [tpe]
            _ =>
              raise EffektError::Internal(
                "A shift continuation should take exactly one value, but takes \{vparams.length()}.",
              )
          }
        _ =>
          raise EffektError::Internal(
            "A shift continuation should have a function type, but has: \{k.tpe}",
          )
      }
    Resume(k, _) =>
      // Upstream: `k.annotatedTpe` is a resumption and the answer is its `to`.
      [function_result(k.annotated_tpe)]
    Hole(annotated, _) => [annotated]
  }
}

///|
/// Upstream `Type.inferType` on expressions.
fn Expr::infer_type(self : Expr) -> ValueType raise EffektError {
  match self {
    ValueVar(_, annotated) => annotated
    Literal(_, annotated) => annotated
    PureApp(callee, targs, _) =>
      instantiated_result(callee.annotated_tpe, targs, [])
    Make(data, _, targs, _) => ValueTypeApp(data, targs)
    Box(block, annotated_capt) => BoxedType(block.infer_type(), annotated_capt)
  }
}

///|
/// Upstream `Type.inferType` on block literals.
fn BlockLit::infer_type(self : BlockLit) -> BlockType raise EffektError {
  FunctionType(
    self.tparams,
    self.cparams.map(c => CaptureSetOf([c])),
    self.vparams.map(p => p.tpe),
    self.bparams.map(p => p.tpe),
    single(self.body.infer_type()),
    Effects::empty(),
  )
}

///|
/// Upstream `Type.inferType` on blocks.
fn Block::infer_type(self : Block) -> BlockType raise EffektError {
  match self {
    BlockVar(block) => block.annotated_tpe
    BlockLit(lit) => lit.infer_type()
    Unbox(pure) =>
      match pure.infer_type() {
        BoxedType(tpe, _) => tpe
        other =>
          if is_unknown_value_type(other) {
            unknown_block_type()
          } else {
            raise EffektError::Internal(
              "Expected a boxed type, but got: \{other}",
            )
          }
      }
    New(implementation) => implementation.interface
  }
}

// ---------------------------------------------------------------------------
// Captures
// ---------------------------------------------------------------------------

///|
/// Upstream `Type.inferCapt` on statements.
fn Stmt::infer_capt(self : Stmt) -> Captures raise EffektError {
  match self {
    Def(_, _, body) => body.infer_capt()
    Let(_, _, body) => body.infer_capt()
    ImpureApp(_, callee, _, _, bargs, body) =>
      callee.annotated_capt
      .union(union_captures(bargs, b => b.infer_capt()))
      .union(body.infer_capt())
    Return(_) => Captures::empty()
    Val(_, binding, body) => body.infer_capt().union(binding.infer_capt())
    App(callee, _, _, bargs) =>
      callee.infer_capt().union(union_captures(bargs, b => b.infer_capt()))
    Invoke(callee, _, _, _, _, bargs) =>
      callee.infer_capt().union(union_captures(bargs, b => b.infer_capt()))
    If(_, thn, els) => thn.infer_capt().union(els.infer_capt())
    Match(_, _, clauses, default) => {
      let captures = union_captures(clauses, clause => clause.body.infer_capt())

      match default {
        Some(body) => captures.union(body.infer_capt())
        None => captures
      }
    }
    Region(body) => body.infer_capt()
    Alloc(_, _, region, body) => body.infer_capt().union(CaptureSetOf([region]))
    Var(_, _, capture, body) => body.infer_capt().diff(CaptureSetOf([capture]))
    Get(_, _, _, annotated_capt, body) =>
      body.infer_capt().union(annotated_capt)
    Put(_, annotated_capt, _, body) => body.infer_capt().union(annotated_capt)
    Reset(body) => body.infer_capt()
    Shift(prompt, k, body) =>
      body.infer_capt().diff(k.capt).union(CaptureSetOf([prompt.id]))
    Resume(k, body) => body.infer_capt().union(k.annotated_capt)
    Hole(_, _) => Captures::empty()
  }
}

///|
/// Upstream `Type.inferCapt` on block literals: the body's captures minus the
/// capture parameters the literal binds.
fn BlockLit::infer_capt(self : BlockLit) -> Captures raise EffektError {
  self.body.infer_capt().diff(CaptureSetOf(self.cparams))
}

///|
/// Upstream `Type.inferCapt` on blocks.
fn Block::infer_capt(self : Block) -> Captures raise EffektError {
  match self {
    BlockVar(block) => block.annotated_capt
    BlockLit(lit) => lit.infer_capt()
    Unbox(pure) =>
      match pure.infer_type() {
        BoxedType(_, captures) => captures
        other =>
          if is_unknown_value_type(other) {
            Captures::empty()
          } else {
            raise EffektError::Internal(
              "Expected a boxed type, but got: \{other}",
            )
          }
      }
    New(implementation) => implementation.infer_capt()
  }
}

///|
/// Upstream `Type.inferCapt` on implementations.
fn Implementation::infer_capt(
  self : Implementation,
) -> Captures raise EffektError {
  union_captures(self.operations, op => op.infer_capt())
}

///|
/// Upstream `Type.inferCapt` on operations.
fn Operation::infer_capt(self : Operation) -> Captures raise EffektError {
  self.body.infer_capt().diff(CaptureSetOf(self.cparams))
}
