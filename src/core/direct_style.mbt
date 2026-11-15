// Direct style: turns a binding that returns into a join point.
//
// Mirrors `effekt/core/optimizer/DirectStyle.scala`:
//
//     val x = { ... return 42 }; stmt2
//   =>
//     def l(x) = stmt2;
//     ... l(42)
//
// The binding does not push a frame that the answer pops — it returns — so the
// statement after it can be run where the `return` stands. Afterwards the inliner
// sees the call instead of a continuation.

///|
/// Whether `s` ends in a `return` (or a hole) on every path: nothing is pushed
/// and no control effect intervenes.
fn stmt_can_be_direct(s : Stmt) -> Bool {
  match s {
    Return(_) | Hole(_, _) => true
    // non-tail calls
    App(_, _, _, _) | Invoke(_, _, _, _, _, _) => false
    // control effects
    Reset(_) | Region(_) | Resume(_, _) | Shift(_, _, _) => false
    // congruences
    Def(_, _, body) => stmt_can_be_direct(body)
    Let(_, _, body) => stmt_can_be_direct(body)
    ImpureApp(_, _, _, _, _, body) => stmt_can_be_direct(body)
    Val(_, _, body) => stmt_can_be_direct(body)
    If(_, thn, els) => stmt_can_be_direct(thn) && stmt_can_be_direct(els)
    Match(_, _, clauses, default) =>
      clauses.all(clause => stmt_can_be_direct(clause.body.body)) &&
      (match default {
        Some(body) => stmt_can_be_direct(body)
        None => true
      })
    Alloc(_, _, _, body) => stmt_can_be_direct(body)
    Var(_, _, _, body) => stmt_can_be_direct(body)
    Get(_, _, _, _, body) => stmt_can_be_direct(body)
    Put(_, _, _, body) => stmt_can_be_direct(body)
  }
}

///|
/// The results of the join point `label` (upstream `returnType`).
///
/// Some rewrites change the answer type of a `match` or a hole to the type the
/// join point is called with, which is its result.
fn joinpoint_results(label : BlockVar) -> Array[ValueType] raise EffektError {
  match label.annotated_tpe {
    FunctionType(_, _, _, _, result) => result
    _ => raise EffektError::Internal("Join points need to have a function type")
  }
}

///|
/// `s` with every `return` replaced by a jump to `label` (upstream
/// `toDirectStyle`).
fn to_direct_style(s : Stmt, label : BlockVar) -> Stmt raise EffektError {
  match s {
    Return(exprs) => App(Block::BlockVar(label), [], exprs, [])
    // non-tail calls and control effects are not direct style
    App(_, _, _, _) | Invoke(_, _, _, _, _, _) => s
    Reset(_) | Resume(_, _) | Shift(_, _, _) | Region(_) => s
    // congruences
    Def(id, block, body) => Def(id, block, to_direct_style(body, label))
    Let(id, binding, body) => Let(id, binding, to_direct_style(body, label))
    ImpureApp(id, callee, targs, vargs, bargs, body) =>
      ImpureApp(id, callee, targs, vargs, bargs, to_direct_style(body, label))
    Val(ids, binding, body) => Val(ids, binding, to_direct_style(body, label))
    If(cond, thn, els) =>
      If(cond, to_direct_style(thn, label), to_direct_style(els, label))
    Match(scrutinee, _, clauses, default) =>
      Match(
        scrutinee,
        joinpoint_results(label),
        clauses.map(clause => {
          Clause(clause.tag, {
            ..clause.body,
            body: to_direct_style(clause.body.body, label),
          })
        }),
        match default {
          Some(body) => Some(to_direct_style(body, label))
          None => None
        },
      )
    Hole(_, span) => Hole(joinpoint_results(label), span)
    Alloc(id, init, region, body) =>
      Alloc(id, init, region, to_direct_style(body, label))
    Var(ref, init, capture, body) =>
      Var(ref, init, capture, to_direct_style(body, label))
    Get(id, tpe, ref, capt, body) =>
      Get(id, tpe, ref, capt, to_direct_style(body, label))
    Put(ref, capt, value, body) =>
      Put(ref, capt, value, to_direct_style(body, label))
  }
}

///|
/// `DirectStyle` (upstream `core/optimizer/DirectStyle.scala`).
pub fn direct_style(module : ModuleDecl) -> ModuleDecl raise EffektError {
  let rewrite = Rewrite(
    Some((rewrite, s) => {
      match s {
        Val(ids, binding, body) => {
          let rewritten_binding = rewrite.rewrite_stmt(binding)
          let rewritten_body = rewrite.rewrite_stmt(body)
          if stmt_can_be_direct(rewritten_binding) {
            let l = Sym::tmp_block("l")
            let result_types = rewritten_binding.infer_type()
            let vparams : Array[ValueParam] = []
            // upstream zips the ids with the results, which truncates
            for i in 0..<ids.length().min(result_types.length()) {
              vparams.push(ValueParam(ids[i], result_types[i]))
            }
            let joinpoint = BlockLit::BlockLit(
              [],
              [],
              vparams,
              [],
              rewritten_body,
            )
            let label = BlockVar::BlockVar(
              l,
              joinpoint.infer_type(),
              joinpoint.infer_capt(),
            )
            Some(
              Def(
                l,
                Block::BlockLit(joinpoint),
                to_direct_style(rewritten_binding, label),
              ),
            )
          } else {
            Some(Val(ids, rewritten_binding, rewritten_body))
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
