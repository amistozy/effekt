// Free variables of core trees.
//
// Mirrors `effekt/core/Tree.scala` (`Free` and `object freeVariables`).
//
// Upstream uses `DB[ValueType]` / `DB[(BlockType, Captures)]` keyed by symbol.
// MoonBit's `Map` needs `Hash + Eq` on keys, so we key by the (globally unique)
// `Sym.uid()` and store the symbol inside the value. Membership tests are O(1)
// and no `Hash` instance for `Sym` is required.

///|
/// A free value variable together with its (inferred) type.
pub(all) struct FreeValue {
  id : Sym
  tpe : ValueType
}

///|
/// A free block variable together with its type and captures.
pub(all) struct FreeBlock {
  id : Sym
  tpe : BlockType
  capt : Captures
}

///|
/// The free variables of a core tree, split into values and blocks.
pub(all) struct Free {
  /// uid -> value
  values : Map[Int32, FreeValue]
  /// uid -> block
  blocks : Map[Int32, FreeBlock]
}

///|
pub fn Free::empty() -> Free {
  { values: Map([]), blocks: Map([]), }
}

///|
pub fn Free::value(id : Sym, tpe : ValueType) -> Free {
  let values : Map[Int32, FreeValue] = Map([])
  values.set(id.uid(), { id, tpe, })
  { values, blocks: Map([]), }
}

///|
pub fn Free::block(id : Sym, tpe : BlockType, capt : Captures) -> Free {
  let blocks : Map[Int32, FreeBlock] = Map([])
  blocks.set(id.uid(), { id, tpe, capt, })
  { values: Map([]), blocks, }
}

///|
pub fn Free::is_empty(self : Free) -> Bool {
  self.values.length() == 0 && self.blocks.length() == 0
}

///|
/// Whether `id` occurs free. Prefer this to `free_ids().contains(id)`.
pub fn Free::contains(self : Free, id : Sym) -> Bool {
  self.values.contains(id.uid()) || self.blocks.contains(id.uid())
}

///|
/// All free ids, values and blocks together.
pub fn Free::free_ids(self : Free) -> Array[Sym] {
  let out : Array[Sym] = []
  for _, v in self.values {
    out.push(v.id)
  }
  for _, b in self.blocks {
    out.push(b.id)
  }
  out
}

///|
/// All free values.
pub fn Free::free_values(self : Free) -> Array[FreeValue] {
  let out : Array[FreeValue] = []
  for _, v in self.values {
    out.push(v)
  }
  out
}

///|
/// All free blocks.
pub fn Free::free_blocks(self : Free) -> Array[FreeBlock] {
  let out : Array[FreeBlock] = []
  for _, b in self.blocks {
    out.push(b)
  }
  out
}

///|
/// Removes the given value variables from the free set.
pub fn Free::without_values(self : Free, ids : Array[Sym]) -> Free {
  let values = self.values.copy()
  for id in ids {
    values.remove(id.uid())
  }
  { values, blocks: self.blocks, }
}

///|
/// Removes the given block variables from the free set.
pub fn Free::without_blocks(self : Free, ids : Array[Sym]) -> Free {
  let blocks = self.blocks.copy()
  for id in ids {
    blocks.remove(id.uid())
  }
  { values: self.values, blocks, }
}

///|
/// Removes a single value variable. Upstream additionally takes the type of the
/// variable; the removal does not need it.
pub fn Free::remove_value(self : Free, id : Sym) -> Free {
  self.without_values([id])
}

///|
/// Removes a single block variable. Upstream additionally takes type and
/// captures; the removal does not need them.
pub fn Free::remove_block(self : Free, id : Sym) -> Free {
  self.without_blocks([id])
}

///|
pub fn Free::without(
  self : Free,
  bound_values : Array[ValueParam],
  bound_blocks : Array[BlockParam],
) -> Free {
  self
  .without_values(bound_values.map(p => p.id))
  .without_blocks(bound_blocks.map(p => p.id))
}

///|
/// Upstream merges with `unionWith(free1, free2, (_, tpe2) => tpe2)`: on a
/// conflict the right-hand side wins.
pub fn Free::union(self : Free, other : Free) -> Free {
  let values = self.values.copy()
  for k, v in other.values {
    values.set(k, v)
  }
  let blocks = self.blocks.copy()
  for k, b in other.blocks {
    blocks.set(k, b)
  }
  { values, blocks, }
}

///|
/// The capture set `{ c }`.
pub fn capture_set(c : Sym) -> Captures {
  @symbols.CaptureSetOf([c])
}

// ---------------------------------------------------------------------------
// freeVariables
// ---------------------------------------------------------------------------

///|
fn[T] free_all(xs : Array[T], f : (T) -> Free) -> Free {
  let mut acc = Free::empty()
  for x in xs {
    acc = acc.union(f(x))
  }
  acc
}

///|
fn free_opt(s : Stmt?) -> Free {
  match s {
    Some(s) => s.free()
    None => Free::empty()
  }
}

///|
pub fn Stmt::free(self : Stmt) -> Free {
  match self {
    Def(id, block, body) =>
      // recursive: the block can refer to itself
      body.free().remove_block(id).union(block.free().remove_block(id))
    Let(id, binding, body) => body.free().remove_value(id).union(binding.free())
    ImpureApp(id, callee, _, vargs, bargs, body) =>
      Free::block(callee.id, callee.annotated_tpe, callee.annotated_capt)
      .union(free_all(vargs, e => e.free()))
      .union(free_all(bargs, b => b.free()))
      .union(body.free().remove_value(id))
    Return(expr) => expr.free()
    Val(id, binding, body) => body.free().remove_value(id).union(binding.free())
    App(callee, _, vargs, bargs) =>
      callee
      .free()
      .union(free_all(vargs, e => e.free()))
      .union(free_all(bargs, b => b.free()))
    Invoke(callee, _, _, _, vargs, bargs) =>
      callee
      .free()
      .union(free_all(vargs, e => e.free()))
      .union(free_all(bargs, b => b.free()))
    If(cond, thn, els) => cond.free().union(thn.free()).union(els.free())
    Match(scrutinee, _, clauses, default) =>
      scrutinee
      .free()
      .union(free_all(clauses, c => c.free()))
      .union(free_opt(default))
    Region(body) => body.free()
    Alloc(id, init, region, body) =>
      init
      .free()
      .union(Free::block(region, t_region(), capture_set(region)))
      .union(body.free().remove_block(id))
    Var(ref, init, _, body) => init.free().union(body.free().remove_block(ref))
    Get(id, annotated_tpe, ref, annotated_capt, body) =>
      Free::block(ref, t_state(annotated_tpe), annotated_capt).union(
        body.free().remove_value(id),
      )
    Put(ref, annotated_capt, value, body) =>
      Free::block(ref, t_state(expr_type_hint(value)), annotated_capt)
      .union(value.free())
      .union(body.free())
    Reset(body) => body.free()
    Shift(prompt, k, body) =>
      body
      .free()
      .remove_block(k.id)
      .union(
        Free::block(prompt.id, prompt.annotated_tpe, prompt.annotated_capt),
      )
    Resume(k, body) =>
      body.free().union(Free::block(k.id, k.annotated_tpe, k.annotated_capt))
    Hole(_, _) => Free::empty()
  }
}

///|
pub fn Expr::free(self : Expr) -> Free {
  match self {
    ValueVar(id, annotated_tpe) => Free::value(id, annotated_tpe)
    Literal(_, _) => Free::empty()
    PureApp(callee, _, vargs) =>
      free_all(vargs, e => e.free()).union(
        Free::block(callee.id, callee.annotated_tpe, callee.annotated_capt),
      )
    Make(_, _, _, vargs) => free_all(vargs, e => e.free())
    Box(b, _) => b.free()
  }
}

///|
pub fn Block::free(self : Block) -> Free {
  match self {
    BlockVar(bv) => Free::block(bv.id, bv.annotated_tpe, bv.annotated_capt)
    BlockLit(lit) => lit.body.free().without(lit.vparams, lit.bparams)
    Unbox(pure) => pure.free()
    New(implementation) => implementation.free()
  }
}

///|
pub fn BlockLit::free(self : BlockLit) -> Free {
  self.body.free().without(self.vparams, self.bparams)
}

///|
pub fn Clause::free(self : Clause) -> Free {
  self.body.free()
}

///|
pub fn Implementation::free(self : Implementation) -> Free {
  free_all(self.operations, op => op.free())
}

///|
pub fn Operation::free(self : Operation) -> Free {
  self.body.free().without(self.vparams, self.bparams)
}

///|
pub fn Toplevel::free(self : Toplevel) -> Free {
  match self {
    ToplevelDef(_, block) => block.free()
    ToplevelVal(_, binding) => binding.free()
  }
}

///|
/// The free variables of a whole module: the union over all definitions and
/// over the splices of all extern bodies.
pub fn free_var_module(m : ModuleDecl) -> Free {
  let mut acc = free_all(m.definitions, t => t.free())
  for e in m.externs {
    match e {
      ExternDef(_, _, _, _, vparams, bparams, _, _, body) =>
        acc = acc.union(free_var_extern_body(body).without(vparams, bparams))
      _ => ()
    }
  }
  acc
}

///|
pub fn free_var_extern_body(body : ExternBody[Expr]) -> Free {
  match body {
    StringExternBody(_, contents) => free_all(contents.args, e => e.free())
    Unsupported(_) => Free::empty()
  }
}
