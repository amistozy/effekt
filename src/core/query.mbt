// Looking for a statement anywhere in a tree.
//
// Upstream uses kiama's `Tree.Query` for the two questions the inlining policy
// asks ("does inlining this body move a scope into a prompt?", "does a block
// argument shift into an enclosing prompt?"), which visits every subtree. These
// helpers do the same, explicitly.

///|
/// Whether any statement in `s` (or in a block that an expression of `s` boxes)
/// satisfies the predicate.
fn stmt_any(s : Stmt, p : (Stmt) -> Bool) -> Bool {
  if p(s) {
    return true
  }
  match s {
    Def(_, block, body) => block_any(block, p) || stmt_any(body, p)
    Let(_, binding, body) => expr_any(binding, p) || stmt_any(body, p)
    ImpureApp(_, _, _, vargs, bargs, body) =>
      exprs_any(vargs, p) || blocks_any(bargs, p) || stmt_any(body, p)
    Return(exprs) => exprs_any(exprs, p)
    Val(_, binding, body) => stmt_any(binding, p) || stmt_any(body, p)
    App(callee, _, vargs, bargs) =>
      block_any(callee, p) || exprs_any(vargs, p) || blocks_any(bargs, p)
    Invoke(callee, _, _, _, vargs, bargs) =>
      block_any(callee, p) || exprs_any(vargs, p) || blocks_any(bargs, p)
    If(cond, thn, els) =>
      expr_any(cond, p) || stmt_any(thn, p) || stmt_any(els, p)
    Match(scrutinee, _, clauses, default) =>
      expr_any(scrutinee, p) ||
      clauses.any(clause => block_lit_any(clause.body, p)) ||
      (match default {
        Some(d) => stmt_any(d, p)
        None => false
      })
    Region(body) => block_lit_any(body, p)
    Alloc(_, init, _, body) => expr_any(init, p) || stmt_any(body, p)
    Var(_, init, _, body) => expr_any(init, p) || stmt_any(body, p)
    Get(_, _, _, _, body) => stmt_any(body, p)
    Put(_, _, value, body) => expr_any(value, p) || stmt_any(body, p)
    Reset(body) => block_lit_any(body, p)
    Shift(_, _, body) => stmt_any(body, p)
    Resume(_, body) => stmt_any(body, p)
    Hole(_, _) => false
  }
}

///|
fn block_any(b : Block, p : (Stmt) -> Bool) -> Bool {
  match b {
    BlockVar(_) => false
    BlockLit(lit) => block_lit_any(lit, p)
    Unbox(expr) => expr_any(expr, p)
    New(implementation) => any_stmt_in_implementation(implementation, p)
  }
}

///|
fn block_lit_any(lit : BlockLit, p : (Stmt) -> Bool) -> Bool {
  stmt_any(lit.body, p)
}

///|
fn blocks_any(blocks : Array[Block], p : (Stmt) -> Bool) -> Bool {
  blocks.any(b => block_any(b, p))
}

///|
/// A pure expression only contains a statement through `box`.
fn expr_any(e : Expr, p : (Stmt) -> Bool) -> Bool {
  match e {
    ValueVar(_, _) | Literal(_, _) => false
    PureApp(_, _, vargs) => exprs_any(vargs, p)
    Make(_, _, _, vargs) => exprs_any(vargs, p)
    Box(b, _) => block_any(b, p)
  }
}

///|
fn exprs_any(exprs : Array[Expr], p : (Stmt) -> Bool) -> Bool {
  exprs.any(e => expr_any(e, p))
}

///|
fn any_stmt_in_implementation(
  implementation : Implementation,
  p : (Stmt) -> Bool,
) -> Bool {
  implementation.operations.any(op => stmt_any(op.body, p))
}
