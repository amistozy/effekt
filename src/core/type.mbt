// Core type inference: upstream `core/Type.scala`'s `Type.inferType` and
// `Type.inferCapt`.
//
// Upstream keeps the type of a core node implicit but recoverable: the
// transformer annotates value variables, block variables, `Match`, `Hole` and
// `Make` with the types it looked up in the typing context, and `inferType` is a
// syntactic recursion over those annotations. The rest of `Type.scala` is a
// checker (`Typing`, `Constraints`, `Type.typecheck`) that upstream only runs in
// debug mode; the optimizer reads types through `inferType`.
//
// Two adaptations of the port are visible here:
//
// - The trees contain `unknown_value_type()` / `unknown_block_type()` where the
//   transformer had no annotation (the pattern-match compiler types its join
//   points that way, for instance). The inference propagates the sentinel
//   instead of failing, where upstream always has a real type.
// - `Captures` is `@symbols.Captures`, so a capture parameter is a singleton set
//   rather than a bare id; the tree stores the ids and this module wraps them.

///|
/// The results of a function type (upstream `BlockType.Function.result`).
fn result_of(tpe : BlockType) -> Array[ValueType] raise EffektError {
  match tpe {
    FunctionType(_, _, _, _, result) => result
    _ =>
      raise EffektError::Internal("Expected a function type, but got: \{tpe}")
  }
}

///|
/// The results of applying a block of type `tpe`. A callee whose type is the
/// placeholder `unknown_block_type()` yields the unknown value type.
fn instantiated_results(
  tpe : BlockType,
  targs : Array[ValueType],
  cargs : Array[Captures],
) -> Array[ValueType] raise EffektError {
  if is_unknown_block_type(tpe) {
    return [unknown_value_type()]
  }
  result_of(instantiate(tpe, targs, cargs))
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
      instantiated_results(
        callee.infer_type(),
        targs,
        bargs.map(b => b.infer_capt()),
      )
    Invoke(_, _, method_tpe, targs, _, bargs) =>
      instantiated_results(method_tpe, targs, bargs.map(b => b.infer_capt()))
    If(_, thn, _) => thn.infer_type()
    Match(_, annotated, _, _) => annotated
    // A region (like `reset`) returns what its body returns.
    Region(body) => body.body.infer_type()
    Alloc(_, _, _, body) => body.infer_type()
    Var(_, _, _, body) => body.infer_type()
    Get(_, _, _, _, body) => body.infer_type()
    Put(_, _, _, body) => body.infer_type()
    Reset(body) => body.body.infer_type()
    Shift(_, k, _) =>
      // `k.tpe` is a resumption `(from) ~> to`, and the shift answers with
      // `from`.
      match k.tpe {
        ResumeType(result, _) => result
        _ =>
          raise EffektError::Internal(
            "A shift continuation should have a resumption type, but has: \{k.tpe}",
          )
      }
    Resume(k, _) =>
      // `k.annotated_tpe` is a resumption and the answer is its `to`.
      match k.annotated_tpe {
        ResumeType(_, answer) => answer
        _ =>
          raise EffektError::Internal(
            "A resumed continuation should have a resumption type, but has: \{k.annotated_tpe}",
          )
      }
    Hole(annotated, _) => annotated
  }
}

///|
/// Upstream `Type.inferType` on expressions.
fn Expr::infer_type(self : Expr) -> ValueType raise EffektError {
  match self {
    ValueVar(_, annotated) => annotated
    Literal(_, annotated) => annotated
    PureApp(callee, targs, _) =>
      single(instantiated_results(callee.annotated_tpe, targs, []))
    Make(data, _, _, _) => data
    Box(block, annotated_capt) => ValueBoxed(block.infer_type(), annotated_capt)
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
    self.body.infer_type(),
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
        ValueBoxed(tpe, _) => tpe
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
        ValueBoxed(_, captures) => captures
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
