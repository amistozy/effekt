// Translating a typed program into explicit capability-passing style.
//
// Mirrors `effekt/source/ExplicitCapabilities.scala`. After this phase
//
//   - there are no `Do` nodes left (they become method calls on a capability),
//   - `l.foo(x)` where `foo` is a field is desugared to `l.foo`,
//   - every function / block literal / operation clause binds one block
//     parameter per effect it performs, and every call site passes the
//     corresponding capabilities.
//
// The type checker is responsible for filling in the annotations that this
// phase consumes (see `Context.bound_capabilities_of` etc.).

///|
pub fn explicit_capabilities(
  module_ : ModuleDecl,
  ctx : Context,
) -> ModuleDecl raise EffektError {
  let hooks : Hooks = {
    expr: Some(capabilities_expr),
    stmt: None,
    defn: Some((ctx, d) => capabilities_def(ctx, d)),
  }
  rewrite_module(module_, ctx, hooks)
}

///|
fn capabilities_expr(ctx : Context, t : Term) -> Term? raise EffektError {
  match t.kind {
    // An effect call: dispatch on the inferred capability.
    Do(id, _targs, vargs, bargs) => {
      let extra_v = ctx.implicit_value_args_of(t.uid)
      let extra_b = ctx.implicit_block_args_of(t.uid)
      let value_args = vargs + extra_v.map(a => ValueArg::unnamed(a))
      let block_args = bargs + extra_b
      let receiver = match ctx.capability_receiver_of(t.uid) {
        Some(cap) => reference_to_capability(cap, ctx)
        None => mk_term(Span::missing(), Var(id))
      }
      let capability_args = ctx
        .capability_arguments_of(t.uid)
        .map(cap => reference_to_capability(cap, ctx))
      let type_args = ctx
        .type_arguments_of(t.uid)
        .map(e => mk_type(Span::missing(), ValueTypeTree(e)))
      Some(
        mk_term(
          t.span.synthesized(),
          MethodCall(
            receiver,
            id,
            type_args,
            value_args,
            block_args + capability_args,
          ),
        ),
      )
    }

    // `f(receiver)` where `f` is a field selector becomes a selection.
    //
    // This arm must be guarded on the callee actually being a `Field`:
    // upstream does the same (`case c @ Call(fun: IdTarget, ...) if
    // fun.definition.isInstanceOf[Field]`). Without the guard it swallows every
    // named call, and the general `Call` arm below — the one that inserts the
    // capability arguments — would never run.
    Call(IdTarget(fun), _targs, vargs, bargs) if is_field_call(
        ctx, fun, vargs, bargs,
      ) => Some(mk_term(t.span.synthesized(), Select(vargs[0].value, fun)))
    MethodCall(receiver, id, _targs, vargs, bargs) => {
      let extra_v = ctx.implicit_value_args_of(t.uid)
      let extra_b = ctx.implicit_block_args_of(t.uid)
      let value_args = vargs + extra_v.map(a => ValueArg::unnamed(a))
      let block_args = bargs + extra_b
      let capability_args = ctx
        .capability_arguments_of(t.uid)
        .map(cap => reference_to_capability(cap, ctx))
      let type_args = ctx
        .type_arguments_of(t.uid)
        .map(e => mk_type(Span::missing(), ValueTypeTree(e)))
      Some(
        mk_term(
          t.span,
          MethodCall(
            receiver,
            id,
            type_args,
            value_args,
            block_args + capability_args,
          ),
        ),
      )
    }
    Call(target, _targs, vargs, bargs) => {
      let extra_v = ctx.implicit_value_args_of(t.uid)
      let extra_b = ctx.implicit_block_args_of(t.uid)
      let value_args = vargs + extra_v.map(a => ValueArg::unnamed(a))
      let block_args = bargs + extra_b
      let capability_args = ctx
        .capability_arguments_of(t.uid)
        .map(cap => reference_to_capability(cap, ctx))
      let type_args = ctx
        .type_arguments_of(t.uid)
        .map(e => mk_type(Span::missing(), ValueTypeTree(e)))
      Some(
        mk_term(
          t.span,
          Call(target, type_args, value_args, block_args + capability_args),
        ),
      )
    }
    TryHandle(prog, handlers) => {
      let capabilities = ctx.bound_capabilities_of(t.uid)
      if capabilities.length() != handlers.length() {
        ctx.panic(
          "expected as many capabilities as handlers in try/handle, got \{capabilities.length()} and \{handlers.length()}",
        )
      }
      let new_handlers : Array[Handler] = []
      for i = 0; i < handlers.length(); i = i + 1 {
        let h = handlers[i]
        let cap = capabilities[i]
        new_handlers.push({
          ..h,
          capability: Some(definition_for_capability(cap, ctx)),
          implementation: rewrite_implementation(
            h.implementation,
            ctx,
            capability_hooks(),
          ),
        })
      }
      Some(mk_term(t.span, TryHandle(prog, new_handlers)))
    }
    New(implementation) => {
      let clauses : Array[OpClause] = []
      for c in implementation.clauses {
        let caps = ctx
          .bound_capabilities_of(c.uid)
          .map(cap => definition_for_capability(cap, ctx))
        let c2 = { ..c, bparams: c.bparams + caps, }
        ctx.copy_annotations(c.uid, c2.uid)
        clauses.push(rewrite_op_clause(c2, ctx, capability_hooks()))
      }
      let impl2 = { ..implementation, clauses, }
      ctx.copy_annotations(implementation.uid, impl2.uid)
      Some(mk_term(t.span, New(impl2)))
    }
    BlockLiteral(tparams, vparams, bparams, body) => {
      let caps = ctx
        .bound_capabilities_of(t.uid)
        .map(cap => definition_for_capability(cap, ctx))
      Some(
        mk_term(t.span, BlockLiteral(tparams, vparams, bparams + caps, body)),
      )
    }
    _ => None
  }
}

///|
/// Is this call really a field selection in disguise, i.e. `f(receiver)` where
/// `f` resolved to a `Field` symbol? Upstream guards its corresponding case the
/// same way (`fun.definition.isInstanceOf[Field]`).
fn is_field_call(
  ctx : Context,
  fun : IdRef,
  vargs : Array[ValueArg],
  bargs : Array[Term],
) -> Bool {
  if vargs.length() != 1 || bargs.length() != 0 {
    return false
  }
  match ctx.symbol_of(fun.uid) {
    Some(Field(_)) => true
    _ => false
  }
}

///|
/// Hooks used when descending into handler implementations, where the
/// capabilities bound by the enclosing `try` are already in scope.
fn capability_hooks() -> Hooks {
  {
    expr: Some(capabilities_expr),
    stmt: None,
    defn: Some((ctx, d) => capabilities_def(ctx, d)),
  }
}

///|
fn capabilities_def(ctx : Context, d : Def) -> Def? {
  match d.kind {
    FunDef(id, tparams, vparams, bparams, captures, ret, body) => {
      let caps = ctx
        .bound_capabilities_of(d.uid)
        .map(cap => definition_for_capability(cap, ctx))
      let d2 = copy_def_kind(
        d,
        FunDef(id, tparams, vparams, bparams + caps, captures, ret, body),
        ctx,
      )
      Some(d2)
    }
    _ => None
  }
}

///|
fn copy_def_kind(from : Def, kind : DefKind, ctx : Context) -> Def {
  let to = mk_def(from.span, from.info, kind)
  ctx.copy_annotations(from.uid, to.uid)
  to
}

///|
/// A term referencing a capability bound in the environment.
pub fn reference_to_capability(cap : Sym, ctx : Context) -> Term {
  let id = IdRef::new(cap.name().name, Span::missing())
  ctx.assign_symbol(id.uid, cap)
  let t = mk_term(Span::missing(), Var(id))
  match cap {
    BlockParam(bp) =>
      match bp.tpe {
        Some(bt) => ctx.assign_block_type(t.uid, bt)
        None => ()
      }
    _ => ()
  }
  t
}

///|
/// A block parameter binding the given capability symbol.
pub fn definition_for_capability(cap : Sym, ctx : Context) -> BlockParam {
  let id = IdDef::new(cap.name().name, Span::missing())
  ctx.assign_symbol(id.uid, cap)
  let tpe = match cap {
    BlockParam(bp) => bp.tpe
    _ => None
  }
  {
    id,
    tpe: match tpe {
      None => None
      Some(t) => Some(mk_type(Span::missing(), BlockTypeTree(t)))
    },
    is_implicit: false,
  }
}
