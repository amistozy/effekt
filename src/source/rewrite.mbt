// Generic bottom-up structural rewriting of the syntax tree.
//
// This replaces kiama's `Tree.Rewrite` / `structuralVisit` from upstream: a
// set of optional hooks is applied to every node *after* its children have
// been rewritten.

///|
/// The rewriting hooks. A hook returns `None` to leave the node unchanged.
pub(all) struct Hooks {
  expr : ((Context, Term) -> Term? raise EffektError)?
  stmt : ((Context, Stmt) -> Stmt? raise EffektError)?
  defn : ((Context, Def) -> Def? raise EffektError)?
}

///|
pub fn Hooks::none() -> Hooks {
  { expr: None, stmt: None, defn: None, }
}

///|
fn apply_expr(hooks : Hooks, ctx : Context, t : Term) -> Term raise EffektError {
  match hooks.expr {
    None => t
    Some(f) =>
      match f(ctx, t) {
        None => t
        Some(t2) => t2
      }
  }
}

///|
fn apply_stmt(hooks : Hooks, ctx : Context, s : Stmt) -> Stmt raise EffektError {
  match hooks.stmt {
    None => s
    Some(f) =>
      match f(ctx, s) {
        None => s
        Some(s2) => s2
      }
  }
}

///|
fn apply_def(hooks : Hooks, ctx : Context, d : Def) -> Def raise EffektError {
  match hooks.defn {
    None => d
    Some(f) =>
      match f(ctx, d) {
        None => d
        Some(d2) => d2
      }
  }
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

///|
pub fn rewrite_module(
  m : ModuleDecl,
  ctx : Context,
  hooks : Hooks,
) -> ModuleDecl raise EffektError {
  let defs = m.defs.map(d => rewrite_def(d, ctx, hooks))
  { ..m, defs, }
}

///|
pub fn rewrite_def(
  d : Def,
  ctx : Context,
  hooks : Hooks,
) -> Def raise EffektError {
  let kind = match d.kind {
    FunDef(id, tparams, vparams, bparams, captures, ret, body) =>
      FunDef(
        id,
        tparams,
        vparams,
        bparams,
        captures,
        ret,
        rewrite_stmt(body, ctx, hooks),
      )
    ValDef(id, annot, binding) =>
      ValDef(id, annot, rewrite_stmt(binding, ctx, hooks))
    RegDef(id, annot, region, binding) =>
      RegDef(id, annot, region, rewrite_stmt(binding, ctx, hooks))
    VarDef(id, annot, binding) =>
      VarDef(id, annot, rewrite_stmt(binding, ctx, hooks))
    DefDef(id, captures, annot, block) =>
      DefDef(id, captures, annot, rewrite_term(block, ctx, hooks))
    NamespaceDef(id, defs) =>
      NamespaceDef(id, defs.map(x => rewrite_def(x, ctx, hooks)))
    InterfaceDef(id, tparams, ops) =>
      InterfaceDef(
        id,
        tparams,
        ops.map(op => rewrite_operation(op, ctx, hooks)),
      )
    DataDef(id, tparams, ctors) => DataDef(id, tparams, ctors)
    RecordDef(id, tparams, fields) => RecordDef(id, tparams, fields)
    TypeDef(id, tparams, tpe) =>
      TypeDef(id, tparams, rewrite_type(tpe, ctx, hooks))
    EffectDef(id, tparams, effs) =>
      EffectDef(id, tparams, rewrite_effects(effs, ctx, hooks))
    ExternType(id, tparams, bodies) =>
      ExternType(
        id,
        tparams,
        bodies.map(b => rewrite_extern_body(b, ctx, hooks)),
      )
    ExternDef(id, tparams, vparams, bparams, captures, ret, bodies) =>
      ExternDef(
        id,
        tparams,
        vparams,
        bparams,
        captures,
        rewrite_type(ret, ctx, hooks),
        bodies.map(b => rewrite_extern_body(b, ctx, hooks)),
      )
    ExternResource(id, tpe) => ExternResource(id, rewrite_type(tpe, ctx, hooks))
    ExternInterface(id, tparams, bodies) =>
      ExternInterface(
        id,
        tparams,
        bodies.map(b => rewrite_extern_body(b, ctx, hooks)),
      )
    ExternInclude(flag, path, contents) => ExternInclude(flag, path, contents)
  }
  let d2 = { ..d, kind, }
  apply_def(hooks, ctx, d2)
}

///|
fn rewrite_operation(
  op : Operation,
  ctx : Context,
  hooks : Hooks,
) -> Operation raise EffektError {
  {
    ..op,
    ret: rewrite_type(op.ret, ctx, hooks),
    vparams: op.vparams.map(p => rewrite_value_param(p, ctx, hooks)),
    bparams: op.bparams.map(p => rewrite_block_param(p, ctx, hooks)),
  }
}

///|
fn rewrite_value_param(
  p : ValueParam,
  ctx : Context,
  hooks : Hooks,
) -> ValueParam raise EffektError {
  match p.tpe {
    None => p
    Some(t) => { ..p, tpe: Some(rewrite_type(t, ctx, hooks)), }
  }
}

///|
fn rewrite_block_param(
  p : BlockParam,
  ctx : Context,
  hooks : Hooks,
) -> BlockParam raise EffektError {
  match p.tpe {
    None => p
    Some(t) => { ..p, tpe: Some(rewrite_type(t, ctx, hooks)), }
  }
}

///|
pub fn rewrite_extern_body(
  b : ExternBody,
  ctx : Context,
  hooks : Hooks,
) -> ExternBody raise EffektError {
  match b {
    StringExternBody(flag, template) =>
      StringExternBody(
        flag,
        template.map_raise(t => rewrite_term(t, ctx, hooks)),
      )
    EffektExternBody(flag, body) =>
      EffektExternBody(flag, rewrite_stmt(body, ctx, hooks))
    Unsupported(msg) => Unsupported(msg)
  }
}

///|
pub fn rewrite_stmt(
  s : Stmt,
  ctx : Context,
  hooks : Hooks,
) -> Stmt raise EffektError {
  let kind = match s.kind {
    DefStmt(d, rest) =>
      DefStmt(rewrite_def(d, ctx, hooks), rewrite_stmt(rest, ctx, hooks))
    ExprStmt(t, rest) =>
      ExprStmt(rewrite_term(t, ctx, hooks), rewrite_stmt(rest, ctx, hooks))
    Return(t) => Return(rewrite_term(t, ctx, hooks))
    BlockStmt(inner) => BlockStmt(rewrite_stmt(inner, ctx, hooks))
  }
  apply_stmt(hooks, ctx, { ..s, kind, })
}

///|
pub fn rewrite_term(
  t : Term,
  ctx : Context,
  hooks : Hooks,
) -> Term raise EffektError {
  let kind = match t.kind {
    Var(id) => Var(id)
    Assign(id, value) => Assign(id, rewrite_term(value, ctx, hooks))
    Literal(v, ty) => Literal(v, ty)
    Hole(id, template) =>
      Hole(id, template.map_raise(s => rewrite_stmt(s, ctx, hooks)))
    Box(captures, body) => Box(captures, rewrite_term(body, ctx, hooks))
    Unbox(body) => Unbox(rewrite_term(body, ctx, hooks))
    Select(receiver, id) => Select(rewrite_term(receiver, ctx, hooks), id)
    Do(id, targs, vargs, bargs) =>
      Do(
        id,
        targs.map(x => rewrite_type(x, ctx, hooks)),
        vargs.map(a => rewrite_value_arg(a, ctx, hooks)),
        bargs.map(b => rewrite_term(b, ctx, hooks)),
      )
    Call(target, targs, vargs, bargs) =>
      Call(
        rewrite_call_target(target, ctx, hooks),
        targs.map(x => rewrite_type(x, ctx, hooks)),
        vargs.map(a => rewrite_value_arg(a, ctx, hooks)),
        bargs.map(b => rewrite_term(b, ctx, hooks)),
      )
    MethodCall(receiver, id, targs, vargs, bargs) =>
      MethodCall(
        rewrite_term(receiver, ctx, hooks),
        id,
        targs.map(x => rewrite_type(x, ctx, hooks)),
        vargs.map(a => rewrite_value_arg(a, ctx, hooks)),
        bargs.map(b => rewrite_term(b, ctx, hooks)),
      )
    If(guards, thn, els) =>
      If(
        guards.map(g => rewrite_guard(g, ctx, hooks)),
        rewrite_stmt(thn, ctx, hooks),
        rewrite_stmt(els, ctx, hooks),
      )
    While(guards, body, default) =>
      While(
        guards.map(g => rewrite_guard(g, ctx, hooks)),
        rewrite_stmt(body, ctx, hooks),
        match default {
          None => None
          Some(d) => Some(rewrite_stmt(d, ctx, hooks))
        },
      )
    Match(scrutinees, clauses, default) =>
      Match(
        scrutinees.map(x => rewrite_term(x, ctx, hooks)),
        clauses.map(c => rewrite_clause(c, ctx, hooks)),
        match default {
          None => None
          Some(d) => Some(rewrite_stmt(d, ctx, hooks))
        },
      )
    TryHandle(prog, handlers) =>
      TryHandle(
        rewrite_stmt(prog, ctx, hooks),
        handlers.map(h => rewrite_handler(h, ctx, hooks)),
      )
    Region(id, body) => Region(id, rewrite_stmt(body, ctx, hooks))
    BlockLiteral(tparams, vparams, bparams, body) =>
      BlockLiteral(
        tparams,
        vparams.map(p => rewrite_value_param(p, ctx, hooks)),
        bparams.map(p => rewrite_block_param(p, ctx, hooks)),
        rewrite_stmt(body, ctx, hooks),
      )
    New(implementation) =>
      New(rewrite_implementation(implementation, ctx, hooks))
  }
  apply_expr(hooks, ctx, { ..t, kind, })
}

///|
fn rewrite_call_target(
  target : CallTarget,
  ctx : Context,
  hooks : Hooks,
) -> CallTarget raise EffektError {
  match target {
    IdTarget(id) => IdTarget(id)
    ExprTarget(t) => ExprTarget(rewrite_term(t, ctx, hooks))
  }
}

///|
pub fn rewrite_value_arg(
  a : ValueArg,
  ctx : Context,
  hooks : Hooks,
) -> ValueArg raise EffektError {
  { ..a, value: rewrite_term(a.value, ctx, hooks), }
}

///|
fn rewrite_guard(
  g : MatchGuard,
  ctx : Context,
  hooks : Hooks,
) -> MatchGuard raise EffektError {
  let kind = match g.kind {
    BooleanGuard(t) => BooleanGuard(rewrite_term(t, ctx, hooks))
    PatternGuard(t, p) =>
      PatternGuard(rewrite_term(t, ctx, hooks), rewrite_pattern(p, ctx, hooks))
  }
  { ..g, kind, }
}

///|
fn rewrite_pattern(
  p : MatchPattern,
  ctx : Context,
  hooks : Hooks,
) -> MatchPattern raise EffektError {
  let kind = match p.kind {
    AnyPattern(id) => AnyPattern(id)
    TagPattern(id, ps) =>
      TagPattern(id, ps.map(x => rewrite_pattern(x, ctx, hooks)))
    IgnorePattern => IgnorePattern
    LiteralPattern(v, ty) => LiteralPattern(v, ty)
    MultiPattern(ps) =>
      MultiPattern(ps.map(x => rewrite_pattern(x, ctx, hooks)))
  }
  { ..p, kind, }
}

///|
fn rewrite_clause(
  c : MatchClause,
  ctx : Context,
  hooks : Hooks,
) -> MatchClause raise EffektError {
  {
    ..c,
    pattern: rewrite_pattern(c.pattern, ctx, hooks),
    guards: c.guards.map(g => rewrite_guard(g, ctx, hooks)),
    body: rewrite_stmt(c.body, ctx, hooks),
  }
}

///|
pub fn rewrite_handler(
  h : Handler,
  ctx : Context,
  hooks : Hooks,
) -> Handler raise EffektError {
  {
    ..h,
    capability: match h.capability {
      None => None
      Some(p) => Some(rewrite_block_param(p, ctx, hooks))
    },
    implementation: rewrite_implementation(h.implementation, ctx, hooks),
  }
}

///|
pub fn rewrite_implementation(
  i : Implementation,
  ctx : Context,
  hooks : Hooks,
) -> Implementation raise EffektError {
  {
    ..i,
    interface: rewrite_type(i.interface, ctx, hooks),
    clauses: i.clauses.map(c => rewrite_op_clause(c, ctx, hooks)),
  }
}

///|
pub fn rewrite_op_clause(
  c : OpClause,
  ctx : Context,
  hooks : Hooks,
) -> OpClause raise EffektError {
  {
    ..c,
    vparams: c.vparams.map(p => rewrite_value_param(p, ctx, hooks)),
    bparams: c.bparams.map(p => rewrite_block_param(p, ctx, hooks)),
    ret: match c.ret {
      None => None
      Some(t) => Some(rewrite_type(t, ctx, hooks))
    },
    body: rewrite_stmt(c.body, ctx, hooks),
  }
}

///|
pub fn rewrite_effects(
  e : EffectsTree,
  ctx : Context,
  hooks : Hooks,
) -> EffectsTree raise EffektError {
  { ..e, effs: e.effs.map(t => rewrite_type(t, ctx, hooks)), }
}

///|
pub fn rewrite_type(
  t : TypeTree,
  ctx : Context,
  hooks : Hooks,
) -> TypeTree raise EffektError {
  let kind = match t.kind {
    TypeRef(id, args) => TypeRef(id, args.map(a => rewrite_type(a, ctx, hooks)))
    ValueTypeTree(ty) => ValueTypeTree(ty)
    BlockTypeTree(ty) => BlockTypeTree(ty)
    BoxedType(inner, captures) =>
      BoxedType(
        rewrite_type(inner, ctx, hooks),
        rewrite_capture_set(captures, ctx, hooks),
      )
    FunctionType(tparams, vparams, bparams, result, effects) =>
      FunctionType(
        tparams,
        vparams.map(a => rewrite_type(a, ctx, hooks)),
        bparams.map(pair => {
          match pair {
            (id, bt) =>
              match id {
                None => (None, rewrite_type(bt, ctx, hooks))
                Some(i) => (Some(i), rewrite_type(bt, ctx, hooks))
              }
          }
        }),
        rewrite_type(result, ctx, hooks),
        rewrite_effects(effects, ctx, hooks),
      )
    Effectful(inner, effects) =>
      Effectful(
        rewrite_type(inner, ctx, hooks),
        rewrite_effects(effects, ctx, hooks),
      )
  }
  { ..t, kind, }
}

///|
pub fn rewrite_capture_set(
  c : CaptureSetTree,
  ctx : Context,
  hooks : Hooks,
) -> CaptureSetTree {
  let _ = ctx
  let _ = hooks
  c
}
