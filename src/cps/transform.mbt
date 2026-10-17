// The source-to-CPS transformation.
//
// Mirrors `effekt/cps/Transformer.scala`.
//
// Deviations from the Scala original (documented on purpose):
//   * the implicit context (`TransformationContext ?=>`) is passed explicitly;
//   * `Continuation.Static` carries a closure, exactly as upstream — the only
//     difference is that a `Static` continuation in upstream reuses the *name*
//     of its hint for the reified continuation parameter (`Id(hint)` compares
//     equal to `hint`), whereas here every `reify` mints a fresh symbol with
//     that name;
//   * `reifyAt(tpe)` ignores the value type. This port does not include core
//     type inference (`core/Type.scala` is not ported), so the type of an
//     `App` / `Invoke` / `Shift` / `Resume` statement is not available.
//     Upstream only inspects it to answer "is this `Nothing`?", in which case
//     it passes `undefined` as the continuation; since such a call never
//     returns, reifying instead is semantics-preserving (just bigger output).

///|
/// A fresh value symbol with the given name.
///
/// Upstream `core.Id(name)` mints an `Id` that is compared by name; here
/// symbols are compared by `uid`, so every call mints a genuinely fresh symbol.
fn fresh_sym(name : String) -> Sym {
  @symbols.Sym::value_param(@symbols.Name::local_(name), None, Span::missing())
}

///|
/// A fresh symbol with the same name as `hint` (upstream: `Id(hint)`).
fn fresh_like(hint : Sym) -> Sym {
  fresh_sym(hint.name().name)
}

// ---------------------------------------------------------------------------
// Continuations
// ---------------------------------------------------------------------------

///|
/// A continuation, either already a variable or a piece of code that is only
/// materialised (reified) when needed.
priv enum Continuation {
  Dynamic(Sym)
  Static(Sym, (Expr, Sym) -> Stmt raise EffektError)
}

///|
/// `k(arg, ks)`: jump to the continuation, or inline its body.
fn Continuation::apply(
  self : Continuation,
  arg : Expr,
  ks : Sym,
) -> Stmt raise EffektError {
  match self {
    Dynamic(id) => Jump(id, [arg], MetaCont::new(ks))
    Static(_, k) => k(arg, ks)
  }
}

///|
/// Materialise the continuation as a `ContLam`.
fn Continuation::reify(self : Continuation) -> Cont raise EffektError {
  match self {
    Dynamic(id) => ContVar(id)
    Static(hint, k) => {
      let param = fresh_like(hint)
      let ks = fresh_sym("ks")
      ContLam(ContLam::new([param], ks, k(ValueVar(param), ks)))
    }
  }
}

///|
/// `reifyAt(tpe)`: see the note at the top of the file — the type is ignored.
fn Continuation::reify_at(
  self : Continuation,
  tpe : ValueType?,
) -> Cont raise EffektError {
  let _ = tpe
  self.reify()
}

///|
/// Do not create a join point for continuations roughly of the size of a
/// return continuation (upstream: `size <= 5`).
fn with_joinpoint(
  k : Continuation,
  body : (Continuation) -> Stmt raise EffektError,
) -> Stmt raise EffektError {
  match k {
    Dynamic(_) => body(k)
    Static(_, _) => {
      let name = fresh_sym("k")
      match k.reify() {
        ContLam(reified) =>
          if reified.body.size() <= 5 {
            body(k)
          } else {
            LetCont(name, reified, body(Dynamic(name)))
          }
        _ =>
          internal_error("Reifying a static continuation must yield a lambda")
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Transformation context
// ---------------------------------------------------------------------------

///|
/// Maps dealiased core variables to the CPS expressions / blocks they stand
/// for. Upstream this is an implicit parameter.
///
/// Upstream uses immutable maps and copies on every binding; MoonBit maps are
/// mutable, so `bind_*` copies the map before extending it (the copy is what
/// implements shadowing).
priv struct TransformationContext {
  values : Map[Int32, Expr]
  blocks : Map[Int32, Block]
}

///|
fn TransformationContext::empty() -> TransformationContext {
  { values: Map([]), blocks: Map([]), }
}

///|
fn TransformationContext::lookup_value(
  self : TransformationContext,
  id : Sym,
) -> Expr {
  match self.values.get(id.uid()) {
    Some(value) => value
    None => ValueVar(id)
  }
}

///|
fn TransformationContext::lookup_block(
  self : TransformationContext,
  id : Sym,
) -> Block {
  match self.blocks.get(id.uid()) {
    Some(block) => block
    None => BlockVar(id)
  }
}

///|
fn TransformationContext::bind_value(
  self : TransformationContext,
  id : Sym,
  value : Expr,
) -> TransformationContext {
  let values = self.values.copy()
  values.set(id.uid(), value)
  { values, blocks: self.blocks, }
}

///|
fn TransformationContext::bind_block(
  self : TransformationContext,
  id : Sym,
  block : Block,
) -> TransformationContext {
  let blocks = self.blocks.copy()
  blocks.set(id.uid(), block)
  { values: self.values, blocks, }
}

// ---------------------------------------------------------------------------
// Toplevel
// ---------------------------------------------------------------------------

///|
/// Translates a core module into the CPS representation.
pub fn transform(module_ : @core.ModuleDecl) -> ModuleDecl raise EffektError {
  let ctx = TransformationContext::empty()
  let externs : Array[Extern] = []
  for e in module_.externs {
    externs.push(transform_extern(e, ctx))
  }
  let definitions : Array[ToplevelDefinition] = []
  for d in module_.definitions {
    definitions.push(transform_toplevel(d, ctx))
  }
  ModuleDecl::new(
    module_.path,
    module_.includes,
    module_.declarations,
    externs,
    definitions,
    module_.exports,
  )
}

///|
fn transform_toplevel(
  definition : @core.Toplevel,
  ctx : TransformationContext,
) -> ToplevelDefinition raise EffektError {
  match definition {
    @core.ToplevelDef(id, block) => ToplevelDef(id, transform_block(block, ctx))
    @core.ToplevelVal(id, stmt) => {
      let ks = fresh_sym("ks")
      let k = fresh_sym("k")
      ToplevelVal(id, ks, k, transform_stmt(stmt, ks, Dynamic(k), ctx))
    }
  }
}

// ---------------------------------------------------------------------------
// Externs
// ---------------------------------------------------------------------------

///|
fn transform_extern(
  extern_def : @core.Extern,
  ctx : TransformationContext,
) -> Extern raise EffektError {
  match extern_def {
    @core.ExternDef(
      id,
      _qualified_signature,
      _tparams,
      _cparams,
      vparams,
      bparams,
      _ret,
      annotated_capture,
      body
    ) => {
      let vps : Array[Sym] = []
      for p in vparams {
        vps.push(p.id)
      }
      let bps : Array[Sym] = []
      for p in bparams {
        bps.push(p.id)
      }
      let is_async = annotated_capture
        .to_array()
        .any(c => sym_eq(c, @symbols.async_capture()))
      ExternDef(id, vps, bps, is_async, transform_extern_body(body, ctx))
    }
    @core.ExternInclude(feature_flag, contents) =>
      ExternInclude(feature_flag, contents)
    @core.ExternData(id, tparams, body) =>
      ExternData(id, tparams, transform_extern_body(body, ctx))
    @core.ExternInterface(id, tparams, body) =>
      ExternInterface(id, tparams, transform_extern_body(body, ctx))
  }
}

///|
fn transform_extern_body(
  body : @core.ExternBody[@core.Expr],
  ctx : TransformationContext,
) -> ExternBody[Expr] raise EffektError {
  match body {
    @core.StringExternBody(feature_flag, template) =>
      StringExternBody(
        feature_flag,
        template.map_raise(arg => transform_expr(arg, ctx)),
      )
    @core.Unsupported(err) => Unsupported(err)
  }
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
fn transform_stmt(
  stmt : @core.Stmt,
  ks : Sym,
  k : Continuation,
  ctx : TransformationContext,
) -> Stmt raise EffektError {
  match stmt {
    // dealiasing
    @core.Def(id, binding, body) =>
      match binding {
        @core.BlockVar(block_var) =>
          transform_stmt(
            body,
            ks,
            k,
            ctx.bind_block(id, ctx.lookup_block(block_var.id)),
          )
        _ =>
          LetDef(
            id,
            transform_block(binding, ctx),
            transform_stmt(body, ks, k, ctx),
          )
      }

    // dealiasing
    @core.Let(id, binding, body) =>
      match binding {
        @core.ValueVar(value_var, _) =>
          transform_stmt(
            body,
            ks,
            k,
            ctx.bind_value(id, ctx.lookup_value(value_var)),
          )
        _ =>
          LetExpr(
            id,
            transform_expr(binding, ctx),
            transform_stmt(body, ks, k, ctx),
          )
      }
    @core.ImpureApp(id, callee, _targs, vargs, bargs, body) =>
      match transform_block(@core.BlockVar(callee), ctx) {
        BlockVar(f) =>
          ImpureApp(
            id,
            f,
            vargs.map(e => transform_expr(e, ctx)),
            bargs.map(b => transform_block(b, ctx)),
            transform_stmt(body, ks, k, ctx),
          )
        _ => internal_error("The callee of an ImpureApp should be a variable")
      }
    @core.Return(value) => k.apply(transform_expr(value, ctx), ks)
    @core.Val(id, rhs, body) =>
      transform_stmt(
        rhs,
        ks,
        Static(id, (value, ks2) => {
          transform_stmt(body, ks2, k, ctx.bind_value(id, value))
        }),
        ctx,
      )
    @core.App(callee, _targs, vargs, bargs) =>
      App(
        transform_block(callee, ctx),
        vargs.map(e => transform_expr(e, ctx)),
        bargs.map(b => transform_block(b, ctx)),
        MetaCont::new(ks),
        k.reify_at(None),
      )
    @core.Invoke(callee, method_, _tpe, _targs, vargs, bargs) =>
      Invoke(
        transform_block(callee, ctx),
        method_,
        vargs.map(e => transform_expr(e, ctx)),
        bargs.map(b => transform_block(b, ctx)),
        MetaCont::new(ks),
        k.reify_at(None),
      )
    @core.If(cond, thn, els) =>
      with_joinpoint(k, k2 => {
        If(
          transform_expr(cond, ctx),
          transform_stmt(thn, ks, k2, ctx),
          transform_stmt(els, ks, k2, ctx),
        )
      })
    @core.Match(scrutinee, _tpe, clauses, default) =>
      match (clauses, default) {
        ([clause], None) =>
          Match(
            transform_expr(scrutinee, ctx),
            [transform_clause(clause, ks, k, ctx)],
            None,
          )
        _ =>
          with_joinpoint(k, k2 => {
            let translated : Array[Clause] = []
            for clause in clauses {
              translated.push(transform_clause(clause, ks, k2, ctx))
            }
            let translated_default = match default {
              Some(body) => Some(transform_stmt(body, ks, k2, ctx))
              None => None
            }
            Match(
              transform_expr(scrutinee, ctx),
              translated,
              translated_default,
            )
          })
      }
    @core.Reset(block_lit) =>
      match block_lit.bparams {
        [prompt] => {
          let ks2 = fresh_sym("ks")
          let k2 = fresh_sym("k")
          Reset(
            BlockLit::new(
              [],
              [prompt.id],
              ks2,
              k2,
              transform_stmt(block_lit.body, ks2, Dynamic(k2), ctx),
            ),
            MetaCont::new(ks),
            k.reify(),
          )
        }
        _ => internal_error("Reset should bind exactly one prompt")
      }

    // Only unidirectional, yet.
    @core.Shift(prompt, resume_, body) => {
      let ks2 = fresh_sym("ks")
      let k2 = fresh_sym("k")
      let translated_body = BlockLit::new(
        [],
        [resume_.id],
        ks2,
        k2,
        transform_stmt(body, ks2, Dynamic(k2), ctx),
      )
      Shift(prompt.id, translated_body, MetaCont::new(ks), k.reify_at(None))
    }
    @core.Resume(cont, body) => {
      let ks2 = fresh_sym("ks")
      let k2 = fresh_sym("k")
      Resume(
        cont.id,
        BlockLit::new(
          [],
          [],
          ks2,
          k2,
          transform_stmt(body, ks2, Dynamic(k2), ctx),
        ),
        MetaCont::new(ks),
        k.reify_at(None),
      )
    }
    @core.Hole(_tpe, span) => Hole(span)
    @core.Region(block_lit) =>
      match block_lit.bparams {
        [region] =>
          Region(
            region.id,
            MetaCont::new(ks),
            transform_stmt(
              block_lit.body,
              ks,
              Static(fresh_sym("tmp"), (x, ks2) => {
                Dealloc(region.id, k.apply(x, ks2))
              }),
              ctx,
            ),
          )
        _ => internal_error("Region should bind exactly one region")
      }
    @core.Alloc(id, init, region, body) =>
      Alloc(
        id,
        transform_expr(init, ctx),
        region,
        transform_stmt(body, ks, k, ctx),
      )
    @core.Var(id, init, _capture, body) =>
      Var(
        id,
        transform_expr(init, ctx),
        MetaCont::new(ks),
        transform_stmt(
          body,
          ks,
          Static(fresh_sym("tmp"), (x, ks2) => Dealloc(id, k.apply(x, ks2))),
          ctx,
        ),
      )
    @core.Get(id, _tpe, ref_, _capt, body) =>
      Get(ref_, id, transform_stmt(body, ks, k, ctx))
    @core.Put(ref_, _capt, value, body) =>
      Put(ref_, transform_expr(value, ctx), transform_stmt(body, ks, k, ctx))
  }
}

///|
fn transform_clause(
  clause : @core.Clause,
  ks : Sym,
  k : Continuation,
  ctx : TransformationContext,
) -> Clause raise EffektError {
  let vparams : Array[Sym] = []
  for p in clause.body.vparams {
    vparams.push(p.id)
  }
  // The constructor tag of a core clause is remembered in the clause's
  // parameter list; see `clause_with_tag` in `prelude.mbt`.
  clause_with_tag(
    vparams,
    clause.tag,
    transform_stmt(clause.body.body, ks, k, ctx),
  )
}

// ---------------------------------------------------------------------------
// Implementations and operations
// ---------------------------------------------------------------------------

///|
fn transform_impl(
  implementation : @core.Implementation,
  ctx : TransformationContext,
) -> Implementation raise EffektError {
  let operations : Array[Operation] = []
  for op in implementation.operations {
    operations.push(transform_op(op, ctx))
  }
  Implementation::new(implementation.interface, operations)
}

///|
fn transform_op(
  op : @core.Operation,
  ctx : TransformationContext,
) -> Operation raise EffektError {
  let ks = fresh_sym("ks")
  let k = fresh_sym("k")
  let vparams : Array[Sym] = []
  for p in op.vparams {
    vparams.push(p.id)
  }
  let bparams : Array[Sym] = []
  for p in op.bparams {
    bparams.push(p.id)
  }
  Operation::new(
    op.name,
    vparams,
    bparams,
    ks,
    k,
    transform_stmt(op.body, ks, Dynamic(k), ctx),
  )
}

// ---------------------------------------------------------------------------
// Expressions and blocks
// ---------------------------------------------------------------------------

///|
fn transform_expr(
  pure : @core.Expr,
  ctx : TransformationContext,
) -> Expr raise EffektError {
  match pure {
    @core.ValueVar(id, _annotated_type) => ctx.lookup_value(id)
    @core.Literal(value, annotated_type) => Literal(value, annotated_type)
    @core.PureApp(block_var, _targs, vargs) =>
      match transform_block(@core.BlockVar(block_var), ctx) {
        BlockVar(id) => PureApp(id, vargs.map(e => transform_expr(e, ctx)))
        _ => internal_error("The callee of a PureApp should be a variable")
      }
    @core.Make(data, tag, _targs, vargs) =>
      Make(data, tag, vargs.map(e => transform_expr(e, ctx)))
    @core.Box(block, _annotated_capture) => Box(transform_block(block, ctx))
  }
}

///|
fn transform_block_lit(
  block : @core.BlockLit,
  ctx : TransformationContext,
) -> BlockLit raise EffektError {
  let ks = fresh_sym("ks")
  let k = fresh_sym("k")
  let vparams : Array[Sym] = []
  for p in block.vparams {
    vparams.push(p.id)
  }
  let bparams : Array[Sym] = []
  for p in block.bparams {
    bparams.push(p.id)
  }
  BlockLit::new(
    vparams,
    bparams,
    ks,
    k,
    transform_stmt(block.body, ks, Dynamic(k), ctx),
  )
}

///|
fn transform_block(
  block : @core.Block,
  ctx : TransformationContext,
) -> Block raise EffektError {
  match block {
    @core.BlockVar(block_var) => ctx.lookup_block(block_var.id)
    @core.BlockLit(lit) => BlockLit(transform_block_lit(lit, ctx))
    @core.Unbox(pure) => Unbox(transform_expr(pure, ctx))
    @core.New(implementation) => New(transform_impl(implementation, ctx))
  }
}
