// Substitutions on core trees.
//
// Mirrors `object substitutions` of `effekt/core/Tree.scala` plus the type
// substitution of `effekt/core/Type.scala` (`Type.substitute`). Used by the
// inliner and the other core optimizers.
//
// Upstream keys the four maps by symbol; MoonBit maps need `Hash + Eq` on
// their keys, so all maps are keyed by `Sym.uid()`.

///|
/// A simultaneous substitution. Shadowing subtracts from the respective map
/// (creating a fresh copy, since MoonBit maps are mutable).
pub(all) struct Substitution {
  /// uid -> type
  vtypes : Map[Int32, ValueType]
  /// uid -> captures
  captures : Map[Int32, Captures]
  /// uid -> value
  values : Map[Int32, Expr]
  /// uid -> block
  blocks : Map[Int32, Block]
}

///|
pub fn Substitution::empty() -> Substitution {
  { vtypes: Map([]), captures: Map([]), values: Map([]), blocks: Map([]), }
}

///|
pub fn Substitution::new(
  vtypes : Map[Int32, ValueType],
  captures : Map[Int32, Captures],
  values : Map[Int32, Expr],
  blocks : Map[Int32, Block],
) -> Substitution {
  { vtypes, captures, values, blocks, }
}

///|
fn[V] shadowed(m : Map[Int32, V], ids : Array[Sym]) -> Map[Int32, V] {
  let copy = m.copy()
  for id in ids {
    copy.remove(id.uid())
  }
  copy
}

///|
pub fn Substitution::shadow_types(
  self : Substitution,
  shadowed_ids : Array[Sym],
) -> Substitution {
  {
    vtypes: shadowed(self.vtypes, shadowed_ids),
    captures: self.captures,
    values: self.values,
    blocks: self.blocks,
  }
}

///|
pub fn Substitution::shadow_captures(
  self : Substitution,
  shadowed_ids : Array[Sym],
) -> Substitution {
  {
    vtypes: self.vtypes,
    captures: shadowed(self.captures, shadowed_ids),
    values: self.values,
    blocks: self.blocks,
  }
}

///|
pub fn Substitution::shadow_values(
  self : Substitution,
  shadowed_ids : Array[Sym],
) -> Substitution {
  {
    vtypes: self.vtypes,
    captures: self.captures,
    values: shadowed(self.values, shadowed_ids),
    blocks: self.blocks,
  }
}

///|
pub fn Substitution::shadow_blocks(
  self : Substitution,
  shadowed_ids : Array[Sym],
) -> Substitution {
  {
    vtypes: self.vtypes,
    captures: self.captures,
    values: self.values,
    blocks: shadowed(self.blocks, shadowed_ids),
  }
}

///|
pub fn Substitution::shadow_params(
  self : Substitution,
  vparams : Array[ValueParam],
  bparams : Array[BlockParam],
) -> Substitution {
  self
  .shadow_values(vparams.map(p => p.id))
  .shadow_blocks(bparams.map(p => p.id))
}

// ---------------------------------------------------------------------------
// Type substitution (core/Type.scala)
// ---------------------------------------------------------------------------

///|
pub fn substitute_captures_with(
  capt : Captures,
  csubst : Map[Int32, Captures],
) -> Captures {
  if csubst.length() == 0 {
    return capt
  }
  match capt {
    CaptureSetOf(cs) => {
      let mut changed = false
      for c in cs {
        if csubst.contains(c.uid()) {
          changed = true
        }
      }
      if !changed {
        return capt
      }
      let out : Array[Sym] = []
      for c in cs {
        match csubst.get(c.uid()) {
          Some(replacement) =>
            for x in replacement.to_array() {
              out.push(x)
            }
          None => out.push(c)
        }
      }
      CaptureSetOf(dedup_syms(out))
    }
    CaptVar(_) => capt
  }
}

///|
pub fn substitute_value_type_with(
  tpe : ValueType,
  vsubst : Map[Int32, ValueType],
  csubst : Map[Int32, Captures],
) -> ValueType {
  match tpe {
    ValueTypeRef(id) =>
      match vsubst.get(id.uid()) {
        Some(replacement) => replacement
        None => tpe
      }
    ValueTypeApp(sym, targs) =>
      ValueTypeApp(
        sym,
        targs.map(t => substitute_value_type_with(t, vsubst, csubst)),
      )
    BoxedType(b, capt) =>
      BoxedType(
        substitute_block_type_with(b, vsubst, csubst),
        substitute_captures_with(capt, csubst),
      )
  }
}

///|
/// The ids occurring in a list of capture sets. In `@symbols` the capture
/// parameters of a function type are stored as (singleton) capture sets, while
/// upstream core stores the ids directly.
fn capture_ids(cs : Array[Captures]) -> Array[Sym] {
  let out : Array[Sym] = []
  for c in cs {
    for x in c.to_array() {
      out.push(x)
    }
  }
  out
}

///|
pub fn substitute_block_type_with(
  tpe : BlockType,
  vsubst : Map[Int32, ValueType],
  csubst : Map[Int32, Captures],
) -> BlockType {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result, effects) => {
      // Names are unique symbols, so shadowing should NOT take place; we still
      // subtract to be safe.
      let vsubst_local = shadowed(vsubst, tparams)
      let csubst_local = shadowed(csubst, capture_ids(cparams))
      FunctionType(
        tparams,
        cparams,
        // technically, in the source, cparams are not bound in value arguments
        vparams.map(t => substitute_value_type_with(t, vsubst_local, csubst)),
        bparams.map(t => {
          substitute_block_type_with(t, vsubst_local, csubst_local)
        }),
        substitute_value_type_with(result, vsubst_local, csubst_local),
        Effects::new(
          effects
          .to_list()
          .map(e => substitute_block_type_with(e, vsubst, csubst)),
        ),
      )
    }
    InterfaceType(sym, targs) =>
      InterfaceType(
        sym,
        targs.map(t => substitute_value_type_with(t, vsubst, csubst)),
      )
  }
}

///|
pub fn substitute_value_type(
  tpe : ValueType,
  subst : Substitution,
) -> ValueType {
  substitute_value_type_with(tpe, subst.vtypes, subst.captures)
}

///|
pub fn substitute_block_type(
  tpe : BlockType,
  subst : Substitution,
) -> BlockType {
  substitute_block_type_with(tpe, subst.vtypes, subst.captures)
}

///|
pub fn substitute_captures(capt : Captures, subst : Substitution) -> Captures {
  substitute_captures_with(capt, subst.captures)
}

// ---------------------------------------------------------------------------
// Tree substitution
// ---------------------------------------------------------------------------

///|
fn check_arity(
  actual : Int32,
  expected : Int32,
  what : String,
) -> Unit raise EffektError {
  if actual != expected {
    raise EffektError::Internal(
      "Wrong number of \{what}: expected \{expected}, got \{actual}",
    )
  }
}

///|
/// The captures of a block, as far as they are annotated. Upstream infers them
/// with `Type.inferCapt`; this port only has annotations, and treats every
/// non-variable block as pure.
pub fn block_captures(b : Block) -> Captures {
  match b {
    BlockVar(bv) => bv.annotated_capt
    _ => Captures::empty()
  }
}

///|
/// Starting point for inlining: substitutes `(tparams, vparams, bparams)` for
/// the given arguments in the body of the block.
pub fn substitute_block_lit_call(
  block : BlockLit,
  targs : Array[ValueType],
  vargs : Array[Expr],
  bargs : Array[Block],
) -> Stmt raise EffektError {
  check_arity(targs.length(), block.tparams.length(), "type arguments")
  check_arity(bargs.length(), block.cparams.length(), "capture arguments")
  check_arity(bargs.length(), block.bparams.length(), "block arguments")
  check_arity(vargs.length(), block.vparams.length(), "value arguments")
  let tsubst : Map[Int32, ValueType] = Map([])
  for i = 0; i < block.tparams.length(); i = i + 1 {
    tsubst.set(block.tparams[i].uid(), targs[i])
  }
  let csubst : Map[Int32, Captures] = Map([])
  for i = 0; i < block.cparams.length(); i = i + 1 {
    csubst.set(block.cparams[i].uid(), block_captures(bargs[i]))
  }
  let vsubst : Map[Int32, Expr] = Map([])
  for i = 0; i < block.vparams.length(); i = i + 1 {
    vsubst.set(block.vparams[i].id.uid(), vargs[i])
  }
  let bsubst : Map[Int32, Block] = Map([])
  for i = 0; i < block.bparams.length(); i = i + 1 {
    bsubst.set(block.bparams[i].id.uid(), bargs[i])
  }
  substitute_stmt(block.body, Substitution::new(tsubst, csubst, vsubst, bsubst))
}

///|
/// Substitutes the id of a region/reference, which must always be a variable.
pub fn substitute_as_var(
  id : Sym,
  subst : Substitution,
) -> Sym raise EffektError {
  match subst.blocks.get(id.uid()) {
    Some(BlockVar(bv)) => bv.id
    Some(_) => raise EffektError::Internal("Regions should always be variables")
    None => id
  }
}

///|
/// Substitutes a block variable. If the substitution maps it to a block, that
/// block must be a variable (this is what upstream's `asInstanceOf` assumes).
pub fn substitute_block_var(
  bv : BlockVar,
  subst : Substitution,
) -> BlockVar raise EffektError {
  match subst.blocks.get(bv.id.uid()) {
    Some(BlockVar(replacement)) => replacement
    Some(_) =>
      raise EffektError::Internal(
        "Should never substitute a concrete block for an FFI function.",
      )
    None =>
      BlockVar::new(
        bv.id,
        substitute_block_type(bv.annotated_tpe, subst),
        substitute_captures(bv.annotated_capt, subst),
      )
  }
}

///|
pub fn substitute_stmt(
  s : Stmt,
  subst : Substitution,
) -> Stmt raise EffektError {
  match s {
    Def(id, block, body) =>
      Def(
        id,
        substitute_block(block, subst.shadow_blocks([id])),
        substitute_stmt(body, subst.shadow_blocks([id])),
      )
    Let(id, binding, body) =>
      Let(
        id,
        substitute_expr(binding, subst),
        substitute_stmt(body, subst.shadow_values([id])),
      )
    ImpureApp(id, callee, targs, vargs, bargs, body) =>
      ImpureApp(
        id,
        substitute_block_var(callee, subst),
        targs.map(t => substitute_value_type(t, subst)),
        vargs.map(e => substitute_expr(e, subst)),
        bargs.map(b => substitute_block(b, subst)),
        substitute_stmt(body, subst.shadow_values([id])),
      )
    Return(expr) => Return(substitute_expr(expr, subst))
    Val(id, binding, body) =>
      Val(
        id,
        substitute_stmt(binding, subst),
        substitute_stmt(body, subst.shadow_values([id])),
      )
    App(callee, targs, vargs, bargs) =>
      App(
        substitute_block(callee, subst),
        targs.map(t => substitute_value_type(t, subst)),
        vargs.map(e => substitute_expr(e, subst)),
        bargs.map(b => substitute_block(b, subst)),
      )
    Invoke(callee, method, method_tpe, targs, vargs, bargs) =>
      Invoke(
        substitute_block(callee, subst),
        method,
        substitute_block_type(method_tpe, subst),
        targs.map(t => substitute_value_type(t, subst)),
        vargs.map(e => substitute_expr(e, subst)),
        bargs.map(b => substitute_block(b, subst)),
      )
    If(cond, thn, els) =>
      If(
        substitute_expr(cond, subst),
        substitute_stmt(thn, subst),
        substitute_stmt(els, subst),
      )
    Match(scrutinee, tpe, clauses, default) =>
      Match(
        substitute_expr(scrutinee, subst),
        substitute_value_type(tpe, subst),
        clauses.map(c => Clause::new(c.tag, substitute_block_lit(c.body, subst))),
        match default {
          Some(body) => Some(substitute_stmt(body, subst))
          None => None
        },
      )
    Alloc(id, init, region, body) =>
      Alloc(
        id,
        substitute_expr(init, subst),
        substitute_as_var(region, subst),
        substitute_stmt(body, subst.shadow_blocks([id])),
      )
    Var(ref_id, init, capture, body) =>
      Var(
        ref_id,
        substitute_expr(init, subst),
        capture,
        substitute_stmt(body, subst.shadow_blocks([ref_id])),
      )
    Get(id, tpe, ref_id, capt, body) =>
      Get(
        id,
        substitute_value_type(tpe, subst),
        substitute_as_var(ref_id, subst),
        substitute_captures(capt, subst),
        substitute_stmt(body, subst.shadow_blocks([id])),
      )
    Put(ref_id, capt, value, body) =>
      Put(
        substitute_as_var(ref_id, subst),
        substitute_captures(capt, subst),
        substitute_expr(value, subst),
        substitute_stmt(body, subst),
      )
    // We annotate the answer type here since it needs to be the union of
    // body.tpe and all shifts.
    Reset(body) => Reset(substitute_block_lit(body, subst))
    Shift(prompt, k, body) => {
      // the resumption must not be substituted in the body of the shift
      let after = substitute_stmt(body, subst.shadow_blocks([k.id]))
      Shift(
        substitute_block_var(prompt, subst),
        substitute_block_param(k, subst),
        after,
      )
    }
    Resume(k, body) =>
      Resume(substitute_block_var(k, subst), substitute_stmt(body, subst))
    Region(body) => Region(substitute_block_lit(body, subst))
    Hole(tpe, span) => Hole(substitute_value_type(tpe, subst), span)
  }
}

///|
pub fn substitute_block_lit(
  b : BlockLit,
  subst : Substitution,
) -> BlockLit raise EffektError {
  let shadowed_typelevel = subst
    .shadow_types(b.tparams)
    .shadow_captures(b.cparams)
  BlockLit::new(
    b.tparams,
    b.cparams,
    b.vparams.map(p => substitute_value_param(p, shadowed_typelevel)),
    b.bparams.map(p => substitute_block_param(p, shadowed_typelevel)),
    substitute_stmt(
      b.body,
      shadowed_typelevel.shadow_params(b.vparams, b.bparams),
    ),
  )
}

///|
pub fn substitute_block(
  b : Block,
  subst : Substitution,
) -> Block raise EffektError {
  match b {
    BlockVar(bv) =>
      match subst.blocks.get(bv.id.uid()) {
        Some(replacement) => replacement
        None =>
          BlockVar(
            BlockVar::new(
              bv.id,
              substitute_block_type(bv.annotated_tpe, subst),
              substitute_captures(bv.annotated_capt, subst),
            ),
          )
      }
    BlockLit(lit) => BlockLit(substitute_block_lit(lit, subst))
    Unbox(pure) => Unbox(substitute_expr(pure, subst))
    New(implementation) => New(substitute_implementation(implementation, subst))
  }
}

///|
pub fn substitute_expr(
  e : Expr,
  subst : Substitution,
) -> Expr raise EffektError {
  match e {
    ValueVar(id, annotated_tpe) =>
      match subst.values.get(id.uid()) {
        Some(replacement) => replacement
        None => ValueVar(id, substitute_value_type(annotated_tpe, subst))
      }
    Literal(value, annotated_tpe) =>
      Literal(value, substitute_value_type(annotated_tpe, subst))
    Make(data, tag, targs, vargs) =>
      Make(
        data,
        tag,
        targs.map(t => substitute_value_type(t, subst)),
        vargs.map(x => substitute_expr(x, subst)),
      )
    PureApp(callee, targs, vargs) =>
      PureApp(
        substitute_block_var(callee, subst),
        targs.map(t => substitute_value_type(t, subst)),
        vargs.map(x => substitute_expr(x, subst)),
      )
    Box(b, annotated_capture) =>
      Box(
        substitute_block(b, subst),
        substitute_captures(annotated_capture, subst),
      )
  }
}

///|
pub fn substitute_implementation(
  implementation : Implementation,
  subst : Substitution,
) -> Implementation raise EffektError {
  Implementation::new(
    substitute_block_type(implementation.interface, subst),
    implementation.operations.map(op => substitute_operation(op, subst)),
  )
}

///|
pub fn substitute_operation(
  op : Operation,
  subst : Substitution,
) -> Operation raise EffektError {
  let shadowed_typelevel = subst
    .shadow_types(op.tparams)
    .shadow_captures(op.cparams)
  Operation::new(
    op.name,
    op.tparams,
    op.cparams,
    op.vparams.map(p => substitute_value_param(p, shadowed_typelevel)),
    op.bparams.map(p => substitute_block_param(p, shadowed_typelevel)),
    substitute_stmt(
      op.body,
      shadowed_typelevel.shadow_params(op.vparams, op.bparams),
    ),
  )
}

///|
pub fn substitute_value_param(
  p : ValueParam,
  subst : Substitution,
) -> ValueParam {
  ValueParam::new(p.id, substitute_value_type(p.tpe, subst))
}

///|
pub fn substitute_block_param(
  p : BlockParam,
  subst : Substitution,
) -> BlockParam {
  BlockParam::new(
    p.id,
    substitute_block_type(p.tpe, subst),
    substitute_captures(p.capt, subst),
  )
}

///|
pub fn substitute_binding(
  binding : Binding,
  subst : Substitution,
) -> Binding raise EffektError {
  match binding {
    BindingVal(id, b) => BindingVal(id, substitute_stmt(b, subst))
    BindingLet(id, b) => BindingLet(id, substitute_expr(b, subst))
    BindingImpureApp(id, callee, targs, vargs, bargs) =>
      BindingImpureApp(
        id,
        substitute_block_var(callee, subst),
        targs.map(t => substitute_value_type(t, subst)),
        vargs.map(e => substitute_expr(e, subst)),
        bargs.map(b => substitute_block(b, subst)),
      )
    BindingDef(id, b) =>
      BindingDef(id, substitute_block(b, subst.shadow_blocks([id])))
    BindingAlloc(id, init, region) =>
      BindingAlloc(
        id,
        substitute_expr(init, subst),
        substitute_as_var(region, subst),
      )
    BindingVar(ref_id, init, capture) =>
      BindingVar(ref_id, substitute_expr(init, subst), capture)
    BindingGet(id, annotated_tpe, ref_id, annotated_capt) =>
      BindingGet(
        id,
        substitute_value_type(annotated_tpe, subst),
        substitute_as_var(ref_id, subst),
        substitute_captures(annotated_capt, subst),
      )
    BindingPut(ref_id, annotated_capt, value) =>
      BindingPut(
        substitute_as_var(ref_id, subst),
        substitute_captures(annotated_capt, subst),
        substitute_expr(value, subst),
      )
  }
}
