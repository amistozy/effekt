// Turns a local mutable reference that does not escape into an ordinary value:
// the local definitions that use it take its current value as an extra parameter
// and return its new value as an extra result.
//
// Mirrors `effekt/core/optimizer/ReferencesToParameters.scala`. A reference is
// eliminated when every use is a `get`/`put` (or a call to a definition that only
// does that), so the state can be threaded through instead of living in a cell.

// ---------------------------------------------------------------------------
// Dependencies between a reference and the local definitions around it
// ---------------------------------------------------------------------------

///|
/// What a local definition, prompt or continuation refers to: a definition and a
/// prompt their body, a continuation the prompt it is captured up to.
///
/// One bound in the handler of a shift only uses the reference if the
/// continuation of that shift does.
priv struct Dependency {
  id : Sym
  free : Map[Int32, Sym]
  handler : Sym?
}

///|
/// Whether `ids` and `free` share a symbol.
fn mentions_any(free : Map[Int32, Sym], ids : Map[Int32, Sym]) -> Bool {
  let mut found = false
  for uid, _ in ids {
    if free.contains(uid) {
      found = true
    }
  }
  found
}

///|
/// Whether `free` contains the reference or one of the definitions that use it.
fn mentions(ref : Sym, uses : Map[Int32, Sym], free : Free) -> Bool {
  free.contains(ref) || mentions_any(sym_set(free.free_ids()), uses)
}

///|
/// The local definitions, prompts and continuations in `s` that use `ref`,
/// directly or through one that does.
fn uses_of(ref : Sym, s : Stmt) -> Map[Int32, Sym] {
  let dependencies : Map[Int32, Dependency] = Map([])
  dependencies_in(s, None, dependencies)
  let uses : Map[Int32, Sym] = Map([])
  let mut changed = true
  while changed {
    changed = false
    for uid, dep in dependencies {
      let depends = dep.free.contains(ref.uid()) || mentions_any(dep.free, uses)
      let handler_used = match dep.handler {
        Some(handler) => uses.contains(handler.uid())
        None => true
      }
      if depends && handler_used && !uses.contains(uid) {
        uses.set(uid, dep.id)
        changed = true
      }
    }
  }
  uses
}

///|
/// Collects what every local definition, prompt and continuation of `s` refers to
/// (upstream `dependenciesIn`), under the shift whose handler binds it.
fn dependencies_in(
  s : Stmt,
  handler : Sym?,
  out : Map[Int32, Dependency],
) -> Unit {
  match s {
    Def(id, Block::BlockLit(lit), body) => {
      out.set(id.uid(), { id, free: sym_set(lit.free().free_ids()), handler, })
      dependencies_in(lit.body, handler, out)
      dependencies_in(body, handler, out)
    }
    Reset(lit) if lit.bparams.length() == 1 => {
      let prompt = lit.bparams[0].id
      out.set(prompt.uid(), {
        id: prompt,
        free: sym_set(lit.free().free_ids()),
        handler,
      })
      dependencies_in(lit.body, handler, out)
    }
    Shift(prompt, k, body) => {
      out.set(k.id.uid(), { id: k.id, free: sym_set([prompt.id]), handler, })
      dependencies_in(body, Some(k.id), out)
    }
    Resume(_, body) => dependencies_in(body, None, out)
    // the congruence
    Def(_, block, body) => {
      dependencies_in_block(block, handler, out)
      dependencies_in(body, handler, out)
    }
    Let(_, binding, body) => {
      dependencies_in_expr(binding, handler, out)
      dependencies_in(body, handler, out)
    }
    ImpureApp(_, _, _, vargs, bargs, body) => {
      for v in vargs {
        dependencies_in_expr(v, handler, out)
      }
      for b in bargs {
        dependencies_in_block(b, handler, out)
      }
      dependencies_in(body, handler, out)
    }
    Return(exprs) =>
      for e in exprs {
        dependencies_in_expr(e, handler, out)
      }
    Val(_, binding, body) => {
      dependencies_in(binding, handler, out)
      dependencies_in(body, handler, out)
    }
    App(callee, _, vargs, bargs) => {
      dependencies_in_block(callee, handler, out)
      for v in vargs {
        dependencies_in_expr(v, handler, out)
      }
      for b in bargs {
        dependencies_in_block(b, handler, out)
      }
    }
    Invoke(callee, _, _, _, vargs, bargs) => {
      dependencies_in_block(callee, handler, out)
      for v in vargs {
        dependencies_in_expr(v, handler, out)
      }
      for b in bargs {
        dependencies_in_block(b, handler, out)
      }
    }
    If(cond, thn, els) => {
      dependencies_in_expr(cond, handler, out)
      dependencies_in(thn, handler, out)
      dependencies_in(els, handler, out)
    }
    Match(scrutinee, _, clauses, default) => {
      dependencies_in_expr(scrutinee, handler, out)
      for clause in clauses {
        dependencies_in(clause.body.body, handler, out)
      }
      match default {
        Some(body) => dependencies_in(body, handler, out)
        None => ()
      }
    }
    Region(lit) => dependencies_in(lit.body, handler, out)
    Alloc(_, init, _, body) => {
      dependencies_in_expr(init, handler, out)
      dependencies_in(body, handler, out)
    }
    Var(_, init, _, body) => {
      dependencies_in_expr(init, handler, out)
      dependencies_in(body, handler, out)
    }
    Get(_, _, _, _, body) => dependencies_in(body, handler, out)
    Put(_, _, value, body) => {
      dependencies_in_expr(value, handler, out)
      dependencies_in(body, handler, out)
    }
    Reset(lit) => dependencies_in(lit.body, handler, out)
    Hole(_, _) => ()
  }
}

///|
fn dependencies_in_block(
  b : Block,
  handler : Sym?,
  out : Map[Int32, Dependency],
) -> Unit {
  match b {
    BlockVar(_) => ()
    BlockLit(lit) => dependencies_in(lit.body, handler, out)
    Unbox(e) => dependencies_in_expr(e, handler, out)
    New(implementation) =>
      for op in implementation.operations {
        dependencies_in(op.body, handler, out)
      }
  }
}

///|
fn dependencies_in_expr(
  e : Expr,
  handler : Sym?,
  out : Map[Int32, Dependency],
) -> Unit {
  match e {
    ValueVar(_, _) | Literal(_, _) => ()
    PureApp(_, _, vargs) =>
      for v in vargs {
        dependencies_in_expr(v, handler, out)
      }
    Make(_, _, _, vargs) =>
      for v in vargs {
        dependencies_in_expr(v, handler, out)
      }
    Box(b, _) => dependencies_in_block(b, handler, out)
  }
}

// ---------------------------------------------------------------------------
// Escaping
// ---------------------------------------------------------------------------

///|
/// Whether the reference escapes from `body`: it, or one of the definitions that
/// use it, occurs other than in a `get` and a `put`, as the callee of a call, or
/// as a definition — for example as an argument, in a closure, or under a
/// `reset`.
fn escapes_ref(
  ref : Sym,
  uses : Map[Int32, Sym],
  body : Stmt,
  outside : Free,
) -> Bool raise EffektError {
  escaping_ref_stmt(ref, uses, outside, body)
}

///|
fn escaping_ref_stmt(
  ref : Sym,
  uses : Map[Int32, Sym],
  outside : Free,
  s : Stmt,
) -> Bool raise EffektError {
  match s {
    Def(id, Block::BlockLit(lit), rest) =>
      if uses.contains(id.uid()) {
        escaping_ref_stmt(ref, uses, outside, lit.body) ||
        escaping_ref_stmt(ref, uses, outside, rest)
      } else {
        mentions(ref, uses, lit.free()) ||
        escaping_ref_stmt(ref, uses, outside, rest)
      }
    Def(_, block, rest) =>
      mentions(ref, uses, block.free()) ||
      escaping_ref_stmt(ref, uses, outside, rest)
    Let(_, binding, rest) =>
      mentions(ref, uses, binding.free()) ||
      escaping_ref_stmt(ref, uses, outside, rest)
    ImpureApp(_, _, _, vargs, bargs, rest) =>
      mentions(ref, uses, s.free()) ||
      vargs.any(v => mentions(ref, uses, v.free())) ||
      bargs.any(b => mentions(ref, uses, b.free())) ||
      escaping_ref_stmt(ref, uses, outside, rest)
    Return(exprs) => exprs.any(e => mentions(ref, uses, e.free()))
    Val(_, binding, rest) =>
      escaping_ref_stmt(ref, uses, outside, binding) ||
      escaping_ref_stmt(ref, uses, outside, rest)
    App(Block::BlockVar(callee), _, vargs, bargs) =>
      if uses.contains(callee.id.uid()) {
        vargs.any(v => mentions(ref, uses, v.free())) ||
        bargs.any(b => mentions(ref, uses, b.free()))
      } else {
        mentions(ref, uses, s.free())
      }
    If(cond, thn, els) =>
      mentions(ref, uses, cond.free()) ||
      escaping_ref_stmt(ref, uses, outside, thn) ||
      escaping_ref_stmt(ref, uses, outside, els)
    Match(scrutinee, _, clauses, default) =>
      mentions(ref, uses, scrutinee.free()) ||
      clauses.any(clause => {
        escaping_ref_stmt(ref, uses, outside, clause.body.body)
      }) ||
      (match default {
        Some(body) => escaping_ref_stmt(ref, uses, outside, body)
        None => false
      })
    Var(_, init, _, rest) =>
      mentions(ref, uses, init.free()) ||
      escaping_ref_stmt(ref, uses, outside, rest)
    Alloc(_, init, _, rest) =>
      mentions(ref, uses, init.free()) ||
      escaping_ref_stmt(ref, uses, outside, rest)
    Get(_, _, _, _, rest) => escaping_ref_stmt(ref, uses, outside, rest)
    Put(_, _, value, rest) =>
      mentions(ref, uses, value.free()) ||
      escaping_ref_stmt(ref, uses, outside, rest)
    Hole(_, _) => false
    Reset(lit) =>
      if lit.bparams.length() == 1 && uses.contains(lit.bparams[0].id.uid()) {
        escaping_ref_stmt(ref, uses, outside, lit.body)
      } else {
        mentions(ref, uses, s.free())
      }
    Shift(prompt, k_param, body) =>
      if uses.contains(prompt.id.uid()) {
        escaping_ref_stmt(ref, uses, outside, body)
      } else {
        match k_param.tpe {
          ResumeType(result, _) =>
            if mentions(ref, uses, s.free()) {
              let captured = { shift: s, k: k_param.id, result, }
              !outside.contains(prompt.id) ||
              !captured.resumes_only() ||
              mentions(
                ref,
                uses,
                captured.replace_resumptions(_ => Return([])).free(),
              ) ||
              resumed_statements(k_param.id, body).any(resumed => {
                escaping_ref_stmt(ref, uses, outside, resumed)
              })
            } else {
              false
            }
          _ => mentions(ref, uses, s.free())
        }
      }
    Resume(callee, body) =>
      if uses.contains(callee.id.uid()) {
        escaping_ref_stmt(ref, uses, outside, body)
      } else {
        mentions(ref, uses, s.free())
      }
    other => mentions(ref, uses, other.free())
  }
}

// ---------------------------------------------------------------------------
// Removing the capture of the eliminated reference
// ---------------------------------------------------------------------------

///|
/// Removes `capture` from every capture set in `s`.
fn remove_capture(capture : Sym, s : Stmt) -> Stmt raise EffektError {
  Rewrite::Rewrite(
    None,
    None,
    Some(capt => capt.diff(CaptureSetOf([capture]))),
    None,
  ).rewrite_stmt(s)
}

// ---------------------------------------------------------------------------
// Threading the state through
// ---------------------------------------------------------------------------

///|
/// The types of the definition that uses the reference, with the state as extra
/// parameter and extra result.
fn extended(
  callee : BlockVar,
  state_type : ValueType,
) -> BlockVar raise EffektError {
  match callee.annotated_tpe {
    FunctionType(tparams, cparams, vparams, bparams, result) =>
      {
        ..callee,
        annotated_tpe: FunctionType(
          tparams,
          cparams,
          vparams + [state_type],
          bparams,
          result + [state_type],
        ),
      }
    other =>
      raise EffektError::Internal(
        "Local definition without function type: \{callee.id.name().name} is a \{other}",
      )
  }
}

///|
/// `val r = s; return r, current` for a statement that does not return the state
/// itself.
fn and_return(s : Stmt, current : Expr) -> Stmt raise EffektError {
  let result_types = s.infer_type()
  let results : Array[Sym] = result_types.map(_ => Sym::id(Name::local("r")))
  let returns : Array[Expr] = []
  for i = 0; i < results.length(); i = i + 1 {
    returns.push(Expr::ValueVar(results[i], result_types[i]))
  }
  returns.push(current)
  Val(results, s, Return(returns))
}

///|
/// `val r, state = s; return r` where `tpe` are the types of `r`.
fn drop_state(s : Stmt, tpe : Array[ValueType], ref : Sym) -> Stmt {
  let results : Array[Sym] = tpe.map(_ => Sym::id(Name::local("r")))
  let returns : Array[Expr] = []
  for i = 0; i < results.length(); i = i + 1 {
    returns.push(Expr::ValueVar(results[i], tpe[i]))
  }
  Val(results + [Sym::id(ref.name())], s, Return(returns))
}

///|
/// `s` with the current value of the reference passed explicitly; every
/// transformed statement returns it as an extra result (upstream
/// `Transformation.go`).
fn thread_state(
  ref : Sym,
  state_type : ValueType,
  uses : Map[Int32, Sym],
  s : Stmt,
  current : Expr,
) -> Stmt raise EffektError {
  match s {
    Def(id, Block::BlockLit(lit), rest) =>
      if uses.contains(id.uid()) {
        let param = ValueParam(Sym::id(ref.name()), state_type)
        let body = thread_state(
          ref,
          state_type,
          uses,
          lit.body,
          Expr::ValueVar(param.id, state_type),
        )
        let lit = BlockLit::BlockLit(
          lit.tparams,
          lit.cparams,
          lit.vparams + [param],
          lit.bparams,
          body,
        )
        Def(
          id,
          Block::BlockLit(lit),
          thread_state(ref, state_type, uses, rest, current),
        )
      } else {
        Def(
          id,
          Block::BlockLit(lit),
          thread_state(ref, state_type, uses, rest, current),
        )
      }
    Def(id, block, rest) =>
      Def(id, block, thread_state(ref, state_type, uses, rest, current))
    Let(id, binding, rest) =>
      Let(id, binding, thread_state(ref, state_type, uses, rest, current))
    ImpureApp(id, callee, targs, vargs, bargs, rest) =>
      ImpureApp(
        id,
        callee,
        targs,
        vargs,
        bargs,
        thread_state(ref, state_type, uses, rest, current),
      )
    Return(exprs) => Return(exprs + [current])
    Val(ids, binding, rest) =>
      if mentions(ref, uses, binding.free()) {
        let next = Sym::id(ref.name())
        Val(
          ids + [next],
          thread_state(ref, state_type, uses, binding, current),
          thread_state(
            ref,
            state_type,
            uses,
            rest,
            Expr::ValueVar(next, state_type),
          ),
        )
      } else {
        Val(ids, binding, thread_state(ref, state_type, uses, rest, current))
      }
    App(Block::BlockVar(callee), targs, vargs, bargs) =>
      if uses.contains(callee.id.uid()) {
        App(
          Block::BlockVar(extended(callee, state_type)),
          targs,
          vargs + [current],
          bargs,
        )
      } else {
        and_return(s, current)
      }
    If(cond, thn, els) =>
      If(
        cond,
        thread_state(ref, state_type, uses, thn, current),
        thread_state(ref, state_type, uses, els, current),
      )
    Match(scrutinee, tpe, clauses, default) =>
      Match(
        scrutinee,
        tpe + [state_type],
        clauses.map(clause => {
          Clause(clause.tag, {
            ..clause.body,
            body: thread_state(ref, state_type, uses, clause.body.body, current),
          })
        }),
        match default {
          Some(body) => Some(thread_state(ref, state_type, uses, body, current))
          None => None
        },
      )
    Var(other, init, capture, rest) =>
      Var(
        other,
        init,
        capture,
        thread_state(ref, state_type, uses, rest, current),
      )
    Alloc(id, init, region, rest) =>
      Alloc(
        id,
        init,
        region,
        thread_state(ref, state_type, uses, rest, current),
      )
    Get(id, tpe, other, capt, rest) =>
      if other.uid() == ref.uid() {
        Let(id, current, thread_state(ref, state_type, uses, rest, current))
      } else {
        Get(
          id,
          tpe,
          other,
          capt,
          thread_state(ref, state_type, uses, rest, current),
        )
      }
    Put(other, capt, value, rest) =>
      if other.uid() == ref.uid() {
        let next = Sym::id(ref.name())
        Let(
          next,
          value,
          thread_state(
            ref,
            state_type,
            uses,
            rest,
            Expr::ValueVar(next, state_type),
          ),
        )
      } else {
        Put(
          other,
          capt,
          value,
          thread_state(ref, state_type, uses, rest, current),
        )
      }
    Hole(tpe, span) => Hole(tpe + [state_type], span)
    Reset(lit) =>
      if lit.bparams.length() == 1 && uses.contains(lit.bparams[0].id.uid()) {
        let param = lit.bparams[0]
        match param.tpe {
          PromptType(answer) => {
            let retyped = { ..param, tpe: PromptType(answer + [state_type]), }
            let body = thread_state(ref, state_type, uses, lit.body, current)
            Reset(
              BlockLit::BlockLit(
                lit.tparams,
                lit.cparams,
                lit.vparams,
                [retyped],
                body,
              ),
            )
          }
          _ => and_return(s, current)
        }
      } else {
        and_return(s, current)
      }
    Shift(prompt, k_param, body) =>
      match k_param.tpe {
        ResumeType(result, answer) =>
          if uses.contains(prompt.id.uid()) {
            let prompt_var = {
              ..prompt,
              annotated_tpe: PromptType(answer + [state_type]),
            }
            let k_tpe = ResumeType(result + [state_type], answer + [state_type])
            let k_param = { ..k_param, tpe: k_tpe, }
            Shift(
              prompt_var,
              k_param,
              thread_state(ref, state_type, uses, body, current),
            )
          } else if mentions(ref, uses, s.free()) {
            let retyped = {
              ..k_param,
              tpe: ResumeType(result + [state_type], answer),
            }
            let captured = { shift: s, k: k_param.id, result, }
            Shift(
              prompt,
              retyped,
              captured.replace_resumptions(resumed => {
                Resume(
                  BlockVar::BlockVar(retyped.id, retyped.tpe, retyped.capt),
                  thread_state(ref, state_type, uses, resumed, current),
                )
              }),
            )
          } else {
            and_return(s, current)
          }
        _ => and_return(s, current)
      }
    Resume(callee, body) =>
      match callee.annotated_tpe {
        ResumeType(result, answer) =>
          if uses.contains(callee.id.uid()) {
            Resume(
              {
                ..callee,
                annotated_tpe: ResumeType(
                  result + [state_type],
                  answer + [state_type],
                ),
              },
              thread_state(ref, state_type, uses, body, current),
            )
          } else {
            and_return(s, current)
          }
        _ => and_return(s, current)
      }
    other => and_return(other, current)
  }
}

///|
/// Replaces `var ref = init; body` by passing the current value of the reference
/// to the definitions that use it (upstream `eliminate`).
fn eliminate(
  ref : Sym,
  init : Expr,
  capture : Sym,
  uses : Map[Int32, Sym],
  body : Stmt,
) -> Stmt? raise EffektError {
  let state_type = init.infer_type()
  let initial = Sym::id(ref.name())
  let threaded = thread_state(
    ref,
    state_type,
    uses,
    body,
    Expr::ValueVar(initial, state_type),
  )
  // Every use of the reference has to be threaded: a use the transformation does
  // not know how to thread would be left behind, referring to a reference that no
  // longer exists. Upstream rules that out in `escapes`; this check keeps the
  // reference (i.e. skips the optimization) rather than miscompiling when the
  // coarser capture sets or the `unknown_*` annotations of this port let a use
  // through.
  if threaded.free().contains(ref) {
    return None
  }
  let dropped = drop_state(threaded, body.infer_type(), ref)
  Some(remove_capture(capture, Let(initial, init, dropped)))
}

///|
/// `ReferencesToParameters.transform` (upstream
/// `core/optimizer/ReferencesToParameters.scala`).
pub fn references_to_parameters(
  module : ModuleDecl,
) -> ModuleDecl raise EffektError {
  let rewrite = Rewrite::Rewrite(
    Some((rewrite, s) => {
      match s {
        Var(ref, init, capture, body) => {
          let rewritten_init = rewrite.rewrite_expr(init)
          let rewritten_body = rewrite.rewrite_stmt(body)
          let uses = uses_of(ref, rewritten_body)
          if escapes_ref(ref, uses, rewritten_body, rewritten_body.free()) {
            Some(Var(ref, rewritten_init, capture, rewritten_body))
          } else {
            match
              eliminate(ref, rewritten_init, capture, uses, rewritten_body) {
              Some(eliminated) => Some(eliminated)
              None => Some(Var(ref, rewritten_init, capture, rewritten_body))
            }
          }
        }
        _ => None
      }
    }),
    None,
    None,
    None,
  )
  rewrite.rewrite_module(module)
}
