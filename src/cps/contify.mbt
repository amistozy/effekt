// Contification.
//
// Mirrors `effekt/cps/Contify.scala`: a `let`-bound block literal that is only
// ever *called* (never used as a value) and that always returns to the same
// continuation `k2` is turned into a `let`-bound continuation, and its call
// sites are turned into jumps.
//
// Deviation from the Scala original (documented on purpose): upstream compares
// continuations structurally (`Set[Cont]`), which includes the *body* of a
// `ContLam`. Here two `ContLam`s are conservatively considered distinct, so
// the `returnsTo` set can only be too big, never too small: fewer blocks are
// contified, none is contified wrongly.
//
// The `rewrite*` family raises `EffektError` because substitution can fail
// (upstream calls `INTERNAL_ERROR`, which aborts compilation).

///|
/// How a block is used inside a statement.
///
/// Contification needs two facts about the block:
///   1. `returns_to`: the continuations that calls to the block return to;
///   2. `used_as_value`: whether it occurs anywhere that is not the callee of a
///      call — passed as a block argument, boxed, or the receiver of an
///      `Invoke`.
priv struct Occurrences {
  returns_to : Array[Cont]
  used_as_value : Bool
}

///|
fn Occurrences::none() -> Occurrences {
  { returns_to: [], used_as_value: false, }
}

///|
fn Occurrences::used() -> Occurrences {
  { returns_to: [], used_as_value: true, }
}

///|
fn Occurrences::call(k : Cont) -> Occurrences {
  { returns_to: [k], used_as_value: false, }
}

///|
/// Conservative equality on continuations: `ContLam`s are never equal.
fn cont_equal(a : Cont, b : Cont) -> Bool {
  match (a, b) {
    (ContVar(x), ContVar(y)) => x.uid() == y.uid()
    (Abort, Abort) => true
    _ => false
  }
}

///|
fn Occurrences::combine(self : Occurrences, other : Occurrences) -> Occurrences {
  let returns_to = self.returns_to.copy()
  for k in other.returns_to {
    if !returns_to.any(x => cont_equal(x, k)) {
      returns_to.push(k)
    }
  }
  { returns_to, used_as_value: self.used_as_value || other.used_as_value, }
}

///|
fn[T] all_occurrences(xs : Array[T], f : (T) -> Occurrences) -> Occurrences {
  let mut acc = Occurrences::none()
  for x in xs {
    acc = f(x).combine(acc)
  }
  acc
}

// ---------------------------------------------------------------------------
// Occurrences
// ---------------------------------------------------------------------------

///|
fn occurrences_stmt(id : Sym, s : Stmt) -> Occurrences {
  match s {
    App(callee, vargs, bargs, _ks, k) => {
      // the callee position is a call; anything else, including the callee when
      // it is not us, is an ordinary occurrence
      let self = match callee {
        BlockVar(id2) if id.uid() == id2.uid() => Occurrences::call(k)
        other => occurrences_block(id, other)
      }
      self
      .combine(all_occurrences(vargs, e => occurrences_expr(id, e)))
      .combine(all_occurrences(bargs, b => occurrences_block(id, b)))
      .combine(occurrences_cont(id, k))
    }
    Invoke(callee, _method, vargs, bargs, _ks, k) =>
      // the receiver of an invoke is a value use: you cannot jump to it
      occurrences_block(id, callee)
      .combine(all_occurrences(vargs, e => occurrences_expr(id, e)))
      .combine(all_occurrences(bargs, b => occurrences_block(id, b)))
      .combine(occurrences_cont(id, k))
    If(cond, thn, els) =>
      occurrences_expr(id, cond)
      .combine(occurrences_stmt(id, thn))
      .combine(occurrences_stmt(id, els))
    Match(scrutinee, clauses, default) =>
      occurrences_expr(id, scrutinee)
      .combine(all_occurrences(clauses, c => occurrences_stmt(id, c.body)))
      .combine(
        match default {
          Some(body) => occurrences_stmt(id, body)
          None => Occurrences::none()
        },
      )
    LetDef(_id2, binding, body) =>
      occurrences_block(id, binding).combine(occurrences_stmt(id, body))
    LetExpr(_id2, binding, body) =>
      occurrences_expr(id, binding).combine(occurrences_stmt(id, body))
    LetCont(_id2, binding, body) =>
      occurrences_cont_lam(id, binding).combine(occurrences_stmt(id, body))
    ImpureApp(_id2, _callee, vargs, bargs, body) =>
      all_occurrences(vargs, e => occurrences_expr(id, e))
      .combine(all_occurrences(bargs, b => occurrences_block(id, b)))
      .combine(occurrences_stmt(id, body))
    Region(_id2, _ks, body) => occurrences_stmt(id, body)
    Alloc(_id2, init, _region, body) =>
      occurrences_expr(id, init).combine(occurrences_stmt(id, body))
    Var(_id2, init, _ks, body) =>
      occurrences_expr(id, init).combine(occurrences_stmt(id, body))
    Dealloc(_ref, body) => occurrences_stmt(id, body)
    Get(_ref, _id2, body) => occurrences_stmt(id, body)
    Put(_ref, value, body) =>
      occurrences_expr(id, value).combine(occurrences_stmt(id, body))
    Reset(prog, _ks, k) =>
      occurrences_block_lit(id, prog).combine(occurrences_cont(id, k))
    Shift(_prompt, body, _ks, k) =>
      occurrences_block_lit(id, body).combine(occurrences_cont(id, k))
    Resume(_r, body, _ks, k) =>
      occurrences_block_lit(id, body).combine(occurrences_cont(id, k))
    Jump(_k, vargs, _ks) => all_occurrences(vargs, e => occurrences_expr(id, e))
    Hole(_span) => Occurrences::none()
  }
}

///|
fn occurrences_block(id : Sym, b : Block) -> Occurrences {
  match b {
    BlockVar(id2) =>
      if id.uid() == id2.uid() {
        Occurrences::used()
      } else {
        Occurrences::none()
      }
    BlockLit(lit) => occurrences_stmt(id, lit.body)
    Unbox(pure) => occurrences_expr(id, pure)
    New(implementation) => occurrences_impl(id, implementation)
  }
}

///|
fn occurrences_block_lit(id : Sym, b : BlockLit) -> Occurrences {
  occurrences_stmt(id, b.body)
}

///|
fn occurrences_impl(id : Sym, implementation : Implementation) -> Occurrences {
  all_occurrences(implementation.operations, op => occurrences_stmt(id, op.body))
}

///|
fn occurrences_expr(id : Sym, e : Expr) -> Occurrences {
  match e {
    ValueVar(_) => Occurrences::none()
    Literal(_, _) => Occurrences::none()
    PureApp(_id2, vargs) => all_occurrences(vargs, x => occurrences_expr(id, x))
    Make(_data, _tag, vargs) =>
      all_occurrences(vargs, x => occurrences_expr(id, x))
    Box(b) => occurrences_block(id, b)
  }
}

///|
fn occurrences_cont(id : Sym, k : Cont) -> Occurrences {
  match k {
    ContVar(_) => Occurrences::none()
    ContLam(lam) => occurrences_stmt(id, lam.body)
    Abort => Occurrences::none()
  }
}

///|
fn occurrences_cont_lam(id : Sym, lam : ContLam) -> Occurrences {
  occurrences_stmt(id, lam.body)
}

// ---------------------------------------------------------------------------
// Contify: turning calls into jumps
// ---------------------------------------------------------------------------

///|
fn contify_in_stmt(id : Sym, s : Stmt) -> Stmt {
  match s {
    App(BlockVar(callee), vargs, [], ks, _k) if callee.uid() == id.uid() =>
      Jump(id, vargs, ks)
    // Congruences
    App(callee, vargs, bargs, ks, k) =>
      App(
        contify_in_block(id, callee),
        vargs.map(e => contify_in_expr(id, e)),
        bargs.map(b => contify_in_block(id, b)),
        ks,
        contify_in_cont(id, k),
      )
    Invoke(callee, method, vargs, bargs, ks, k) =>
      Invoke(
        contify_in_block(id, callee),
        method,
        vargs.map(e => contify_in_expr(id, e)),
        bargs.map(b => contify_in_block(id, b)),
        ks,
        contify_in_cont(id, k),
      )
    If(cond, thn, els) =>
      If(
        contify_in_expr(id, cond),
        contify_in_stmt(id, thn),
        contify_in_stmt(id, els),
      )
    Match(scrutinee, clauses, default) => {
      let translated : Array[Clause] = []
      for clause in clauses {
        translated.push(
          Clause::new(clause.vparams, contify_in_stmt(id, clause.body)),
        )
      }
      Match(
        contify_in_expr(id, scrutinee),
        translated,
        match default {
          Some(body) => Some(contify_in_stmt(id, body))
          None => None
        },
      )
    }
    LetDef(id2, binding, body) =>
      LetDef(id2, contify_in_block(id, binding), contify_in_stmt(id, body))
    LetExpr(id2, binding, body) =>
      LetExpr(id2, contify_in_expr(id, binding), contify_in_stmt(id, body))
    LetCont(id2, binding, body) =>
      LetCont(id2, contify_in_cont_lam(id, binding), contify_in_stmt(id, body))
    ImpureApp(id2, callee, vargs, bargs, body) =>
      ImpureApp(
        id2,
        callee,
        vargs.map(e => contify_in_expr(id, e)),
        bargs.map(b => contify_in_block(id, b)),
        contify_in_stmt(id, body),
      )
    Region(id2, ks, body) => Region(id2, ks, contify_in_stmt(id, body))
    Alloc(id2, init, region, body) =>
      Alloc(id2, contify_in_expr(id, init), region, contify_in_stmt(id, body))
    Var(id2, init, ks, body) =>
      Var(id2, contify_in_expr(id, init), ks, contify_in_stmt(id, body))
    Dealloc(ref, body) => Dealloc(ref, contify_in_stmt(id, body))
    Get(ref, id2, body) => Get(ref, id2, contify_in_stmt(id, body))
    Put(ref, value, body) =>
      Put(ref, contify_in_expr(id, value), contify_in_stmt(id, body))
    Reset(prog, ks, k) =>
      Reset(contify_in_block_lit(id, prog), ks, contify_in_cont(id, k))
    Shift(prompt, body, ks, k) =>
      Shift(prompt, contify_in_block_lit(id, body), ks, contify_in_cont(id, k))
    Resume(r, body, ks, k) =>
      Resume(r, contify_in_block_lit(id, body), ks, contify_in_cont(id, k))
    other => other
  }
}

///|
fn contify_in_block(id : Sym, b : Block) -> Block {
  match b {
    BlockVar(_) => b
    BlockLit(lit) =>
      BlockLit(
        BlockLit::new(
          lit.vparams,
          lit.bparams,
          lit.ks,
          lit.k,
          contify_in_stmt(id, lit.body),
        ),
      )
    Unbox(pure) => Unbox(contify_in_expr(id, pure))
    New(implementation) => New(contify_in_impl(id, implementation))
  }
}

///|
fn contify_in_block_lit(id : Sym, b : BlockLit) -> BlockLit {
  BlockLit::new(b.vparams, b.bparams, b.ks, b.k, contify_in_stmt(id, b.body))
}

///|
fn contify_in_impl(id : Sym, implementation : Implementation) -> Implementation {
  let operations : Array[Operation] = []
  for op in implementation.operations {
    operations.push(
      Operation::new(
        op.name,
        op.vparams,
        op.bparams,
        op.ks,
        op.k,
        contify_in_stmt(id, op.body),
      ),
    )
  }
  Implementation::new(implementation.interface, operations)
}

///|
fn contify_in_expr(id : Sym, e : Expr) -> Expr {
  match e {
    ValueVar(_) => e
    Literal(_, _) => e
    PureApp(id2, vargs) => PureApp(id2, vargs.map(x => contify_in_expr(id, x)))
    Make(data, tag, vargs) =>
      Make(data, tag, vargs.map(x => contify_in_expr(id, x)))
    Box(b) => Box(contify_in_block(id, b))
  }
}

///|
fn contify_in_cont(id : Sym, k : Cont) -> Cont {
  match k {
    ContVar(_) => k
    ContLam(lam) => ContLam(contify_in_cont_lam(id, lam))
    Abort => k
  }
}

///|
fn contify_in_cont_lam(id : Sym, lam : ContLam) -> ContLam {
  ContLam::new(lam.results, lam.ks, contify_in_stmt(id, lam.body))
}

// ---------------------------------------------------------------------------
// Rewriting
// ---------------------------------------------------------------------------

///|
fn rewrite_stmt(s : Stmt) -> Stmt raise EffektError {
  match s {
    LetDef(id, binding, rest) =>
      match binding {
        BlockLit(lit) if lit.bparams.length() == 0 => {
          let rewritten_body = rewrite_stmt(lit.body)
          let rewritten_rest = rewrite_stmt(rest)
          let in_body = occurrences_stmt(id, rewritten_body)
          let in_rest = occurrences_stmt(id, rewritten_rest)

          let returns_unique = in_rest.returns_to.length() == 1
          let is_recursive = in_body.returns_to.length() > 0
          // a block that is also used as a value cannot become a continuation
          let escapes = in_rest.used_as_value || in_body.used_as_value
          let contifiable = returns_unique && !is_recursive && !escapes

          // This is problematic:
          //
          //   function l(k1) { ... k1 ... }
          //   function loop(k2) { ... l(k2) ... }
          //
          // we cannot simply specialize l to k2 since it is not lexically in
          // scope. We approximate whether k is in scope by checking whether it
          // is free in `rest`.
          let rest_free = rewritten_rest.free()

          let head = if in_rest.returns_to.length() > 0 {
            Some(in_rest.returns_to[0])
          } else {
            None
          }
          match head {
            Some(ContVar(k2)) if contifiable =>
              if rest_free.contains(k2) {
                let conts : Map[Int32, Cont] = Map([])
                conts.set(lit.k.uid(), ContVar(k2))
                let subst = Substitution::new(Map([]), Map([]), conts, Map([]))
                LetCont(
                  id,
                  ContLam::new(
                    lit.vparams,
                    lit.ks,
                    substitute_stmt(rewritten_body, subst),
                  ),
                  contify_in_stmt(id, rewritten_rest),
                )
              } else {
                LetDef(
                  id,
                  BlockLit(
                    BlockLit::new(
                      lit.vparams,
                      lit.bparams,
                      lit.ks,
                      lit.k,
                      rewritten_body,
                    ),
                  ),
                  rewritten_rest,
                )
              }
            _ =>
              LetDef(
                id,
                BlockLit(
                  BlockLit::new(
                    lit.vparams,
                    lit.bparams,
                    lit.ks,
                    lit.k,
                    rewritten_body,
                  ),
                ),
                rewritten_rest,
              )
          }
        }
        _ => LetDef(id, rewrite_block(binding), rewrite_stmt(rest))
      }
    // Congruences
    Jump(k, vargs, ks) => Jump(k, vargs.map(e => rewrite_expr(e)), ks)
    App(callee, vargs, bargs, ks, k) =>
      App(
        rewrite_block(callee),
        vargs.map(e => rewrite_expr(e)),
        bargs.map(b => rewrite_block(b)),
        ks,
        rewrite_cont(k),
      )
    Invoke(callee, method, vargs, bargs, ks, k) =>
      Invoke(
        rewrite_block(callee),
        method,
        vargs.map(e => rewrite_expr(e)),
        bargs.map(b => rewrite_block(b)),
        ks,
        rewrite_cont(k),
      )
    If(cond, thn, els) =>
      If(rewrite_expr(cond), rewrite_stmt(thn), rewrite_stmt(els))
    Match(scrutinee, clauses, default) => {
      let translated : Array[Clause] = []
      for clause in clauses {
        translated.push(rewrite_clause(clause))
      }
      Match(
        rewrite_expr(scrutinee),
        translated,
        match default {
          Some(body) => Some(rewrite_stmt(body))
          None => None
        },
      )
    }
    LetExpr(id, binding, body) =>
      LetExpr(id, rewrite_expr(binding), rewrite_stmt(body))
    LetCont(id, binding, body) =>
      LetCont(id, rewrite_cont_lam(binding), rewrite_stmt(body))
    ImpureApp(id, callee, vargs, bargs, body) =>
      ImpureApp(
        id,
        callee,
        vargs.map(e => rewrite_expr(e)),
        bargs.map(b => rewrite_block(b)),
        rewrite_stmt(body),
      )
    Region(id, ks, body) => Region(id, ks, rewrite_stmt(body))
    Alloc(id, init, region, body) =>
      Alloc(id, rewrite_expr(init), region, rewrite_stmt(body))
    Var(id, init, ks, body) =>
      Var(id, rewrite_expr(init), ks, rewrite_stmt(body))
    Dealloc(ref, body) => Dealloc(ref, rewrite_stmt(body))
    Get(ref, id, body) => Get(ref, id, rewrite_stmt(body))
    Put(ref, value, body) => Put(ref, rewrite_expr(value), rewrite_stmt(body))
    Reset(prog, ks, k) => Reset(rewrite_block_lit(prog), ks, rewrite_cont(k))
    Shift(prompt, body, ks, k) =>
      Shift(prompt, rewrite_block_lit(body), ks, rewrite_cont(k))
    Resume(r, body, ks, k) =>
      Resume(r, rewrite_block_lit(body), ks, rewrite_cont(k))
    Hole(span) => Hole(span)
  }
}

///|
fn rewrite_clause(clause : Clause) -> Clause raise EffektError {
  Clause::new(clause.vparams, rewrite_stmt(clause.body))
}

///|
fn rewrite_expr(e : Expr) -> Expr raise EffektError {
  match e {
    ValueVar(_) => e
    Literal(_, _) => e
    PureApp(id, vargs) => PureApp(id, vargs.map(x => rewrite_expr(x)))
    Make(data, tag, vargs) => Make(data, tag, vargs.map(x => rewrite_expr(x)))
    Box(b) => Box(rewrite_block(b))
  }
}

///|
fn rewrite_block(b : Block) -> Block raise EffektError {
  match b {
    BlockVar(_) => b
    BlockLit(lit) =>
      BlockLit(
        BlockLit::new(
          lit.vparams,
          lit.bparams,
          lit.ks,
          lit.k,
          rewrite_stmt(lit.body),
        ),
      )
    Unbox(pure) => Unbox(rewrite_expr(pure))
    New(implementation) => New(rewrite_impl(implementation))
  }
}

///|
fn rewrite_block_lit(b : BlockLit) -> BlockLit raise EffektError {
  BlockLit::new(b.vparams, b.bparams, b.ks, b.k, rewrite_stmt(b.body))
}

///|
fn rewrite_impl(
  implementation : Implementation,
) -> Implementation raise EffektError {
  let operations : Array[Operation] = []
  for op in implementation.operations {
    operations.push(
      Operation::new(
        op.name,
        op.vparams,
        op.bparams,
        op.ks,
        op.k,
        rewrite_stmt(op.body),
      ),
    )
  }
  Implementation::new(implementation.interface, operations)
}

///|
fn rewrite_cont(k : Cont) -> Cont raise EffektError {
  match k {
    ContVar(_) => k
    ContLam(lam) => ContLam(rewrite_cont_lam(lam))
    Abort => k
  }
}

///|
fn rewrite_cont_lam(lam : ContLam) -> ContLam raise EffektError {
  ContLam::new(lam.results, lam.ks, rewrite_stmt(lam.body))
}

///|
fn rewrite_extern(extern_def : Extern) -> Extern raise EffektError {
  match extern_def {
    ExternDef(id, vparams, bparams, is_async, body) =>
      ExternDef(id, vparams, bparams, is_async, rewrite_extern_body(body))
    ExternData(id, tparams, body) => ExternData(id, tparams, body)
    ExternInterface(id, tparams, body) => ExternInterface(id, tparams, body)
    ExternInclude(feature_flag, contents) =>
      ExternInclude(feature_flag, contents)
  }
}

///|
fn rewrite_extern_body(
  body : ExternBody[Expr],
) -> ExternBody[Expr] raise EffektError {
  match body {
    StringExternBody(feature_flag, template) =>
      StringExternBody(
        feature_flag,
        Template::new(template.strings, template.args.map(a => rewrite_expr(a))),
      )
    Unsupported(err) => Unsupported(err)
  }
}

///|
fn rewrite_toplevel(
  definition : ToplevelDefinition,
) -> ToplevelDefinition raise EffektError {
  match definition {
    ToplevelDef(id, block) => ToplevelDef(id, rewrite_block(block))
    ToplevelVal(id, ks, k, binding) =>
      ToplevelVal(id, ks, k, rewrite_stmt(binding))
    ToplevelLet(id, binding) => ToplevelLet(id, rewrite_expr(binding))
  }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

///|
/// Rewrites a CPS module, contifying calls where possible.
pub fn contify(module : ModuleDecl) -> ModuleDecl raise EffektError {
  let externs : Array[Extern] = []
  for e in module.externs {
    externs.push(rewrite_extern(e))
  }
  let definitions : Array[ToplevelDefinition] = []
  for d in module.definitions {
    definitions.push(rewrite_toplevel(d))
  }
  ModuleDecl::new(
    module.path,
    module.includes,
    module.declarations,
    externs,
    definitions,
    module.exports,
  )
}
