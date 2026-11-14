// The number of nodes of a core tree, used by the inlining heuristics.
//
// Mirrors `object sizes` in `effekt/core/Tree.scala`. Note that a definition
// counts as `block + body + 1` and every statement adds one for itself, so the
// numbers are comparable with upstream's `--max-inline-size` threshold.

///|
fn[T] size_all(xs : Array[T], f : (T) -> Int32) -> Int32 {
  let mut acc = 0
  for x in xs {
    acc = acc + f(x)
  }
  acc
}

///|
fn size_opt(s : Stmt?) -> Int32 {
  match s {
    Some(s) => s.size()
    None => 0
  }
}

///|
fn Stmt::size(self : Stmt) -> Int32 {
  match self {
    Def(_, block, body) => block.size() + body.size() + 1
    Let(_, binding, body) => binding.size() + body.size() + 1
    ImpureApp(_, _, _, vargs, bargs, body) =>
      size_all(vargs, e => e.size()) +
      size_all(bargs, b => b.size()) +
      body.size() +
      1
    Return(exprs) => size_all(exprs, e => e.size()) + 1
    Val(_, binding, body) => binding.size() + body.size() + 1
    App(callee, _, vargs, bargs) =>
      callee.size() +
      size_all(vargs, e => e.size()) +
      size_all(bargs, b => b.size()) +
      1
    Invoke(callee, _, _, _, vargs, bargs) =>
      callee.size() +
      size_all(vargs, e => e.size()) +
      size_all(bargs, b => b.size()) +
      1
    If(cond, thn, els) => cond.size() + thn.size() + els.size() + 1
    Match(scrutinee, _, clauses, default) =>
      scrutinee.size() +
      size_all(clauses, c => c.body.size()) +
      size_opt(default) +
      1
    Region(body) => body.size() + 1
    Alloc(_, init, _, body) => init.size() + body.size() + 1
    Var(_, init, _, body) => init.size() + body.size() + 1
    Get(_, _, _, _, body) => body.size() + 1
    Put(_, _, value, body) => value.size() + body.size() + 1
    Reset(body) => body.size() + 1
    Shift(_, _, body) => body.size() + 1
    Resume(_, body) => body.size() + 1
    Hole(_, _) => 1
  }
}

///|
fn Expr::size(self : Expr) -> Int32 {
  match self {
    ValueVar(_, _) => 1
    Literal(_, _) => 1
    PureApp(_, _, vargs) => size_all(vargs, e => e.size()) + 1
    Make(_, _, _, vargs) => size_all(vargs, e => e.size()) + 1
    Box(b, _) => b.size() + 1
  }
}

///|
fn Block::size(self : Block) -> Int32 {
  match self {
    BlockVar(_) => 1
    BlockLit(lit) => lit.body.size() + 1
    Unbox(pure) => pure.size() + 1
    New(implementation) => implementation.size() + 1
  }
}

///|
fn BlockLit::size(self : BlockLit) -> Int32 {
  self.body.size() + 1
}

///|
fn Implementation::size(self : Implementation) -> Int32 {
  size_all(self.operations, op => op.size()) + 1
}

///|
fn Operation::size(self : Operation) -> Int32 {
  self.body.size() + 1
}
