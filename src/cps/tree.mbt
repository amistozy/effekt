// Tree structure of programs in the CPS representation.
//
// Mirrors `effekt/cps/Tree.scala`. As in core, symbols (`@symbols.Sym`) are the
// names and identity is by `uid`.

///|
/// A module declaration; the path should be an Effekt include path, not a
/// system dependent file path.
pub(all) struct ModuleDecl {
  path : String
  includes : Array[String]
  declarations : Array[Declaration]
  externs : Array[Extern]
  definitions : Array[ToplevelDefinition]
  exports : Array[Sym]
}

///|
pub fn ModuleDecl::new(
  path : String,
  includes : Array[String],
  declarations : Array[Declaration],
  externs : Array[Extern],
  definitions : Array[ToplevelDefinition],
  exports : Array[Sym],
) -> ModuleDecl {
  { path, includes, declarations, externs, definitions, exports, }
}

///|
pub(all) enum ToplevelDefinition {
  ToplevelDef(Sym, Block)
  /// This is a let-run: `val id = ks(k, binding)`.
  ToplevelVal(Sym, Sym, Sym, Stmt)
  ToplevelLet(Sym, Expr)
}

///|
pub fn ToplevelDefinition::id(self : ToplevelDefinition) -> Sym {
  match self {
    ToplevelDef(id, _) => id
    ToplevelVal(id, _, _, _) => id
    ToplevelLet(id, _) => id
  }
}

// ---------------------------------------------------------------------------
// FFI external definitions
// ---------------------------------------------------------------------------

///|
pub(all) enum Extern {
  ExternDef(Sym, Array[Sym], Array[Sym], Bool, ExternBody[Expr])
  ExternData(Sym, Array[Sym], ExternBody[Expr])
  ExternInterface(Sym, Array[Sym], ExternBody[Expr])
  ExternInclude(FeatureFlag, String)
}

///|
pub(all) enum ExternBody[T] {
  StringExternBody(FeatureFlag, Template[T])
  Unsupported(EffektError)
}

///|
pub fn[T] ExternBody::flag(self : ExternBody[T]) -> FeatureFlag {
  match self {
    StringExternBody(flag, _) => flag
    Unsupported(_) => Default
  }
}

///|
pub fn[T] ExternBody::is_supported_by(
  self : ExternBody[T],
  name : String,
) -> Bool {
  match self {
    StringExternBody(flag, _) => flag.matches(name)
    Unsupported(_) => false
  }
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

///|
pub(all) enum Expr {
  ValueVar(Sym)
  Literal(LiteralValue, ValueType)
  /// Pure FFI calls. Invariant: the block is pure.
  PureApp(Sym, Array[Expr])
  Make(Sym, Sym, Array[Expr])
  Box(Block)
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

///|
pub(all) enum Block {
  BlockVar(Sym)
  BlockLit(BlockLit)
  Unbox(Expr)
  New(Implementation)
}

///|
pub(all) struct BlockLit {
  vparams : Array[Sym]
  bparams : Array[Sym]
  /// The meta continuation of this block.
  ks : Sym
  /// The continuation of this block.
  k : Sym
  body : Stmt
}

///|
pub fn BlockLit::new(
  vparams : Array[Sym],
  bparams : Array[Sym],
  ks : Sym,
  k : Sym,
  body : Stmt,
) -> BlockLit {
  { vparams, bparams, ks, k, body, }
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
pub(all) enum Stmt {
  Jump(Sym, Array[Expr], MetaCont)
  App(Block, Array[Expr], Array[Block], MetaCont, Cont)
  Invoke(Block, Sym, Array[Expr], Array[Block], MetaCont, Cont)
  // Local control flow
  If(Expr, Stmt, Stmt)
  Match(Expr, Array[Clause], Stmt?)
  LetDef(Sym, Block, Stmt)
  LetExpr(Sym, Expr, Stmt)
  LetCont(Sym, ContLam, Stmt)
  ImpureApp(Sym, Sym, Array[Expr], Array[Block], Stmt)
  // Regions
  Region(Sym, MetaCont, Stmt)
  Alloc(Sym, Expr, Sym, Stmt)
  /// Creates a fresh state handler to model local (backtrackable) state:
  /// `val id = ks.fresh(init); body`.
  Var(Sym, Expr, MetaCont, Stmt)
  /// `dealloc(ref); body`
  Dealloc(Sym, Stmt)
  /// `val id = !ref; body`
  Get(Sym, Sym, Stmt)
  Put(Sym, Expr, Stmt)
  /// `reset( { (p, ks, k) => STMT }, ks, k)`
  Reset(BlockLit, MetaCont, Cont)
  /// `shift(p, { (resume, ks, k) => STMT }, ks, k)`
  Shift(Sym, BlockLit, MetaCont, Cont)
  /// `resume(r, (ks, k) => STMT, ks, k)`
  Resume(Sym, BlockLit, MetaCont, Cont)
  // Others
  Hole(Span)
}

///|
pub(all) struct Clause {
  vparams : Array[Sym]
  body : Stmt
}

///|
pub fn Clause::new(vparams : Array[Sym], body : Stmt) -> Clause {
  { vparams, body, }
}

///|
pub(all) enum Cont {
  ContVar(Sym)
  ContLam(ContLam)
  Abort
}

///|
pub(all) struct ContLam {
  results : Array[Sym]
  ks : Sym
  body : Stmt
}

///|
pub fn ContLam::new(results : Array[Sym], ks : Sym, body : Stmt) -> ContLam {
  { results, ks, body, }
}

///|
pub(all) struct MetaCont {
  id : Sym
}

///|
pub fn MetaCont::new(id : Sym) -> MetaCont {
  { id, }
}

///|
pub(all) struct Implementation {
  interface : BlockType
  operations : Array[Operation]
}

///|
pub fn Implementation::new(
  interface : BlockType,
  operations : Array[Operation],
) -> Implementation {
  { interface, operations, }
}

///|
pub(all) struct Operation {
  name : Sym
  vparams : Array[Sym]
  bparams : Array[Sym]
  ks : Sym
  k : Sym
  body : Stmt
}

///|
pub fn Operation::new(
  name : Sym,
  vparams : Array[Sym],
  bparams : Array[Sym],
  ks : Sym,
  k : Sym,
  body : Stmt,
) -> Operation {
  { name, vparams, bparams, ks, k, body, }
}

///|
pub(all) struct Def {
  id : Sym
  block : Block
}

///|
pub fn Def::new(id : Sym, block : Block) -> Def {
  { id, block, }
}

// ---------------------------------------------------------------------------
// Sizes (used by inlining heuristics)
// ---------------------------------------------------------------------------

///|
fn[T] size_all(xs : Array[T], f : (T) -> Int32) -> Int32 {
  let mut acc = 0
  for x in xs {
    acc = acc + f(x)
  }
  acc
}

///|
fn size_opt(x : Stmt?) -> Int32 {
  match x {
    Some(s) => s.size()
    None => 0
  }
}

///|
pub fn Expr::size(self : Expr) -> Int32 {
  match self {
    ValueVar(_) => 1
    Literal(_, _) => 1
    PureApp(_, vargs) => size_all(vargs, e => e.size()) + 1
    Make(_, _, vargs) => size_all(vargs, e => e.size()) + 1
    Box(b) => b.size() + 1
  }
}

///|
pub fn Block::size(self : Block) -> Int32 {
  match self {
    BlockVar(_) => 1
    BlockLit(lit) => lit.body.size() + 1
    Unbox(pure) => pure.size() + 1
    New(implementation) => implementation.size() + 1
  }
}

///|
pub fn Stmt::size(self : Stmt) -> Int32 {
  match self {
    Jump(_, vargs, ks) => size_all(vargs, e => e.size()) + ks.size() + 1
    App(callee, vargs, bargs, ks, k) =>
      callee.size() +
      size_all(vargs, e => e.size()) +
      size_all(bargs, b => b.size()) +
      ks.size() +
      k.size() +
      1
    Invoke(callee, _, vargs, bargs, ks, k) =>
      callee.size() +
      size_all(vargs, e => e.size()) +
      size_all(bargs, b => b.size()) +
      ks.size() +
      k.size() +
      1
    If(cond, thn, els) => cond.size() + thn.size() + els.size() + 1
    Match(scrutinee, clauses, default) =>
      scrutinee.size() +
      size_all(clauses, c => c.size()) +
      size_opt(default) +
      1
    LetDef(_, binding, body) => binding.size() + body.size() + 1
    LetExpr(_, binding, body) => binding.size() + body.size() + 1
    LetCont(_, binding, body) => binding.size() + body.size() + 1
    ImpureApp(_, _, vargs, bargs, body) =>
      size_all(vargs, e => e.size()) +
      size_all(bargs, b => b.size()) +
      body.size() +
      1
    Region(_, ks, body) => ks.size() + body.size() + 1
    Alloc(_, init, _, body) => init.size() + body.size() + 1
    Var(_, init, ks, body) => init.size() + ks.size() + body.size() + 1
    Dealloc(_, body) => body.size() + 1
    Get(_, _, body) => body.size() + 1
    Put(_, value, body) => value.size() + body.size() + 1
    Reset(prog, ks, k) => prog.size() + ks.size() + k.size() + 1
    Shift(_, body, ks, k) => body.size() + ks.size() + k.size() + 1
    Resume(_, body, ks, k) => body.size() + ks.size() + k.size() + 1
    Hole(_) => 1
  }
}

///|
pub fn BlockLit::size(self : BlockLit) -> Int32 {
  self.body.size() + 1
}

///|
pub fn Clause::size(self : Clause) -> Int32 {
  self.body.size() + 1
}

///|
pub fn Cont::size(self : Cont) -> Int32 {
  match self {
    ContVar(_) => 1
    ContLam(lam) => lam.size() + 1
    Abort => 1
  }
}

///|
pub fn ContLam::size(self : ContLam) -> Int32 {
  self.body.size() + 1
}

///|
pub fn MetaCont::size(self : MetaCont) -> Int32 {
  1
}

///|
pub fn Implementation::size(self : Implementation) -> Int32 {
  size_all(self.operations, op => op.size()) + 1
}

///|
pub fn Operation::size(self : Operation) -> Int32 {
  self.body.size() + 1
}

///|
pub fn Def::size(self : Def) -> Int32 {
  self.block.size() + 1
}

///|
pub fn ModuleDecl::size(self : ModuleDecl) -> Int32 {
  let mut acc = 0
  for d in self.definitions {
    match d {
      ToplevelDef(_, block) => acc = acc + block.size()
      ToplevelVal(_, _, _, binding) => acc = acc + binding.size()
      ToplevelLet(_, binding) => acc = acc + binding.size()
    }
  }
  acc
}

// ---------------------------------------------------------------------------
// Variables (free variables)
// ---------------------------------------------------------------------------

///|
/// A set of variables.
///
/// Upstream this is `Set[Id]`; MoonBit maps need `Hash + Eq` on their keys, so
/// we key by `Sym.uid()`. The `value` / `block` / `cont` / `meta` constructors
/// are all the same set, exactly as upstream, and only serve as documentation.
pub(all) struct Variables {
  ids : Map[Int32, Sym]
}

///|
pub fn Variables::empty() -> Variables {
  { ids: Map([]), }
}

///|
fn Variables::of(id : Sym) -> Variables {
  let ids : Map[Int32, Sym] = Map([])
  ids.set(id.uid(), id)
  { ids, }
}

///|
pub fn Variables::value(id : Sym) -> Variables {
  Variables::of(id)
}

///|
pub fn Variables::block(id : Sym) -> Variables {
  Variables::of(id)
}

///|
pub fn Variables::cont(id : Sym) -> Variables {
  Variables::of(id)
}

///|
pub fn Variables::meta(id : Sym) -> Variables {
  Variables::of(id)
}

///|
pub fn Variables::is_empty(self : Variables) -> Bool {
  self.ids.length() == 0
}

///|
pub fn Variables::length(self : Variables) -> Int32 {
  self.ids.length()
}

///|
pub fn Variables::contains(self : Variables, id : Sym) -> Bool {
  self.ids.contains(id.uid())
}

///|
pub fn Variables::to_array(self : Variables) -> Array[Sym] {
  let out : Array[Sym] = []
  for _, v in self.ids {
    out.push(v)
  }
  out
}

///|
pub fn Variables::union(self : Variables, other : Variables) -> Variables {
  let ids = self.ids.copy()
  for k, v in other.ids {
    ids.set(k, v)
  }
  { ids, }
}

///|
/// Removes the given variables.
pub fn Variables::diff(self : Variables, ids : Array[Sym]) -> Variables {
  let out = self.ids.copy()
  for id in ids {
    out.remove(id.uid())
  }
  { ids: out, }
}

///|
fn[T] vars_all(xs : Array[T], f : (T) -> Variables) -> Variables {
  let mut acc = Variables::empty()
  for x in xs {
    acc = acc.union(f(x))
  }
  acc
}

///|
fn vars_opt(x : Stmt?) -> Variables {
  match x {
    Some(s) => s.free()
    None => Variables::empty()
  }
}

///|
pub fn Expr::free(self : Expr) -> Variables {
  match self {
    ValueVar(id) => Variables::value(id)
    Literal(_, _) => Variables::empty()
    PureApp(id, vargs) =>
      Variables::block(id).union(vars_all(vargs, e => e.free()))
    Make(_, _, vargs) => vars_all(vargs, e => e.free())
    Box(b) => b.free()
  }
}

///|
pub fn Block::free(self : Block) -> Variables {
  match self {
    BlockVar(id) => Variables::block(id)
    BlockLit(lit) => lit.free()
    Unbox(pure) => pure.free()
    New(implementation) => implementation.free()
  }
}

///|
pub fn Implementation::free(self : Implementation) -> Variables {
  vars_all(self.operations, op => op.free())
}

///|
pub fn Operation::free(self : Operation) -> Variables {
  self.body
  .free()
  .diff(self.vparams)
  .diff(self.bparams)
  .diff([self.ks])
  .diff([self.k])
}

///|
pub fn BlockLit::free(self : BlockLit) -> Variables {
  self.body
  .free()
  .diff(self.vparams)
  .diff(self.bparams)
  .diff([self.ks])
  .diff([self.k])
}

///|
pub fn Stmt::free(self : Stmt) -> Variables {
  match self {
    Jump(k, vargs, ks) =>
      Variables::cont(k).union(vars_all(vargs, e => e.free())).union(ks.free())
    App(callee, vargs, bargs, ks, k) =>
      callee
      .free()
      .union(vars_all(vargs, e => e.free()))
      .union(vars_all(bargs, b => b.free()))
      .union(ks.free())
      .union(k.free())
    Invoke(callee, _, vargs, bargs, ks, k) =>
      callee
      .free()
      .union(vars_all(vargs, e => e.free()))
      .union(vars_all(bargs, b => b.free()))
      .union(ks.free())
      .union(k.free())
    If(cond, thn, els) => cond.free().union(thn.free()).union(els.free())
    Match(scrutinee, clauses, default) =>
      scrutinee
      .free()
      .union(vars_all(clauses, c => c.free()))
      .union(vars_opt(default))
    LetDef(id, binding, body) => binding.free().union(body.free()).diff([id])
    LetExpr(id, binding, body) => binding.free().union(body.free().diff([id]))
    LetCont(id, binding, body) => binding.free().union(body.free().diff([id]))
    ImpureApp(id, callee, vargs, bargs, body) =>
      Variables::block(callee)
      .union(vars_all(vargs, e => e.free()))
      .union(vars_all(bargs, b => b.free()))
      .union(body.free().diff([id]))
    Region(id, ks, body) => ks.free().union(body.free().diff([id]))
    Alloc(id, init, region, body) =>
      init.free().union(Variables::block(region)).union(body.free().diff([id]))
    Var(id, init, ks, body) =>
      init.free().union(ks.free()).union(body.free().diff([id]))
    Dealloc(reference, body) => Variables::block(reference).union(body.free())
    Get(reference, id, body) =>
      Variables::block(reference).union(body.free().diff([id]))
    Put(reference, value, body) =>
      Variables::block(reference).union(value.free()).union(body.free())
    Reset(prog, ks, k) => prog.free().union(ks.free()).union(k.free())
    Shift(prompt, body, ks, k) =>
      Variables::block(prompt)
      .union(body.free())
      .union(ks.free())
      .union(k.free())
    Resume(r, body, ks, k) =>
      Variables::block(r).union(body.free()).union(ks.free()).union(k.free())
    Hole(_) => Variables::empty()
  }
}

///|
pub fn Clause::free(self : Clause) -> Variables {
  self.body.free().diff(self.vparams)
}

///|
pub fn Def::free(self : Def) -> Variables {
  self.block.free().diff([self.id])
}

///|
pub fn MetaCont::free(self : MetaCont) -> Variables {
  Variables::meta(self.id)
}

///|
pub fn Cont::free(self : Cont) -> Variables {
  match self {
    ContVar(id) => Variables::cont(id)
    Abort => Variables::empty()
    ContLam(lam) => lam.free()
  }
}

///|
pub fn ContLam::free(self : ContLam) -> Variables {
  self.body.free().diff(self.results).diff([self.ks])
}

// ---------------------------------------------------------------------------
// Substitutions
// ---------------------------------------------------------------------------

///|
/// A simultaneous substitution on CPS trees.
///
/// Upstream keys the four maps by symbol; MoonBit maps need `Hash + Eq` on
/// their keys, so all maps are keyed by `Sym.uid()`. Shadowing copies the
/// affected map (MoonBit maps are mutable).
pub(all) struct Substitution {
  /// uid -> value
  values : Map[Int32, Expr]
  /// uid -> block
  blocks : Map[Int32, Block]
  /// uid -> continuation
  conts : Map[Int32, Cont]
  /// uid -> meta continuation
  metaconts : Map[Int32, MetaCont]
}

///|
pub fn Substitution::empty() -> Substitution {
  { values: Map([]), blocks: Map([]), conts: Map([]), metaconts: Map([]), }
}

///|
pub fn Substitution::new(
  values : Map[Int32, Expr],
  blocks : Map[Int32, Block],
  conts : Map[Int32, Cont],
  metaconts : Map[Int32, MetaCont],
) -> Substitution {
  { values, blocks, conts, metaconts, }
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
pub fn Substitution::shadow_values(
  self : Substitution,
  ids : Array[Sym],
) -> Substitution {
  {
    values: shadowed(self.values, ids),
    blocks: self.blocks,
    conts: self.conts,
    metaconts: self.metaconts,
  }
}

///|
pub fn Substitution::shadow_blocks(
  self : Substitution,
  ids : Array[Sym],
) -> Substitution {
  {
    values: self.values,
    blocks: shadowed(self.blocks, ids),
    conts: self.conts,
    metaconts: self.metaconts,
  }
}

///|
pub fn Substitution::shadow_conts(
  self : Substitution,
  ids : Array[Sym],
) -> Substitution {
  {
    values: self.values,
    blocks: self.blocks,
    conts: shadowed(self.conts, ids),
    metaconts: self.metaconts,
  }
}

///|
pub fn Substitution::shadow_metaconts(
  self : Substitution,
  ids : Array[Sym],
) -> Substitution {
  {
    values: self.values,
    blocks: self.blocks,
    conts: self.conts,
    metaconts: shadowed(self.metaconts, ids),
  }
}

///|
pub fn Substitution::shadow_params(
  self : Substitution,
  vparams : Array[Sym],
  bparams : Array[Sym],
) -> Substitution {
  self.shadow_values(vparams).shadow_blocks(bparams)
}

///|
pub fn substitute_as_block_var(
  id : Sym,
  subst : Substitution,
) -> Sym raise EffektError {
  match subst.blocks.get(id.uid()) {
    Some(BlockVar(x)) => x
    Some(_) => internal_error("References should always be variables")
    None => id
  }
}

///|
pub fn substitute_as_cont_var(
  id : Sym,
  subst : Substitution,
) -> Sym raise EffektError {
  match subst.conts.get(id.uid()) {
    Some(ContVar(x)) => x
    Some(_) =>
      internal_error("Continuation references should always be variables")
    None => id
  }
}

///|
pub fn substitute_meta_cont(ks : MetaCont, subst : Substitution) -> MetaCont {
  match subst.metaconts.get(ks.id.uid()) {
    Some(replacement) => replacement
    None => ks
  }
}

///|
pub fn substitute_expr(
  e : Expr,
  subst : Substitution,
) -> Expr raise EffektError {
  match e {
    ValueVar(id) =>
      match subst.values.get(id.uid()) {
        Some(replacement) => replacement
        None => ValueVar(id)
      }
    Literal(value, tpe) => Literal(value, tpe)
    Make(tpe, tag, vargs) =>
      Make(tpe, tag, vargs.map(x => substitute_expr(x, subst)))
    PureApp(id, vargs) => PureApp(id, vargs.map(x => substitute_expr(x, subst)))
    Box(b) => Box(substitute_block(b, subst))
  }
}

///|
pub fn substitute_block(
  b : Block,
  subst : Substitution,
) -> Block raise EffektError {
  match b {
    BlockVar(id) =>
      match subst.blocks.get(id.uid()) {
        Some(replacement) => replacement
        None => BlockVar(id)
      }
    BlockLit(lit) => BlockLit(substitute_block_lit(lit, subst))
    Unbox(pure) => Unbox(substitute_expr(pure, subst))
    New(implementation) => New(substitute_implementation(implementation, subst))
  }
}

///|
pub fn substitute_block_lit(
  b : BlockLit,
  subst : Substitution,
) -> BlockLit raise EffektError {
  BlockLit::new(
    b.vparams,
    b.bparams,
    b.ks,
    b.k,
    substitute_stmt(
      b.body,
      subst
      .shadow_params(b.vparams, b.bparams)
      .shadow_metaconts([b.ks])
      .shadow_conts([b.k]),
    ),
  )
}

///|
pub fn substitute_stmt(
  s : Stmt,
  subst : Substitution,
) -> Stmt raise EffektError {
  match s {
    Jump(k, vargs, ks) =>
      Jump(
        substitute_as_cont_var(k, subst),
        vargs.map(x => substitute_expr(x, subst)),
        substitute_meta_cont(ks, subst),
      )
    App(callee, vargs, bargs, ks, k) =>
      App(
        substitute_block(callee, subst),
        vargs.map(x => substitute_expr(x, subst)),
        bargs.map(b => substitute_block(b, subst)),
        substitute_meta_cont(ks, subst),
        substitute_cont(k, subst),
      )
    Invoke(callee, method, vargs, bargs, ks, k) =>
      Invoke(
        substitute_block(callee, subst),
        method,
        vargs.map(x => substitute_expr(x, subst)),
        bargs.map(b => substitute_block(b, subst)),
        substitute_meta_cont(ks, subst),
        substitute_cont(k, subst),
      )
    If(cond, thn, els) =>
      If(
        substitute_expr(cond, subst),
        substitute_stmt(thn, subst),
        substitute_stmt(els, subst),
      )
    Match(scrutinee, clauses, default) =>
      Match(
        substitute_expr(scrutinee, subst),
        clauses.map(c => substitute_clause(c, subst)),
        match default {
          Some(body) => Some(substitute_stmt(body, subst))
          None => None
        },
      )
    LetDef(id, binding, body) =>
      LetDef(
        id,
        substitute_block(binding, subst),
        substitute_stmt(body, subst.shadow_blocks([id])),
      )
    LetExpr(id, binding, body) =>
      LetExpr(
        id,
        substitute_expr(binding, subst),
        substitute_stmt(body, subst.shadow_values([id])),
      )
    LetCont(id, binding, body) =>
      LetCont(
        id,
        substitute_cont_lam(binding, subst),
        substitute_stmt(body, subst.shadow_conts([id])),
      )
    ImpureApp(id, callee, vargs, bargs, body) =>
      ImpureApp(
        id,
        callee,
        vargs.map(x => substitute_expr(x, subst)),
        bargs.map(b => substitute_block(b, subst)),
        substitute_stmt(body, subst.shadow_values([id])),
      )
    Region(id, ks, body) =>
      Region(
        id,
        substitute_meta_cont(ks, subst),
        substitute_stmt(body, subst.shadow_blocks([id])),
      )
    Alloc(id, init, region, body) =>
      Alloc(
        id,
        substitute_expr(init, subst),
        substitute_as_block_var(region, subst),
        substitute_stmt(body, subst.shadow_blocks([id])),
      )
    Var(id, init, ks, body) =>
      Var(
        id,
        substitute_expr(init, subst),
        substitute_meta_cont(ks, subst),
        substitute_stmt(body, subst.shadow_blocks([id])),
      )
    Dealloc(reference, body) =>
      Dealloc(
        substitute_as_block_var(reference, subst),
        substitute_stmt(body, subst),
      )
    Get(reference, id, body) =>
      Get(
        substitute_as_block_var(reference, subst),
        id,
        substitute_stmt(body, subst.shadow_values([id])),
      )
    Put(reference, value, body) =>
      Put(
        substitute_as_block_var(reference, subst),
        substitute_expr(value, subst),
        substitute_stmt(body, subst),
      )
    Reset(prog, ks, k) =>
      Reset(
        substitute_block_lit(prog, subst),
        substitute_meta_cont(ks, subst),
        substitute_cont(k, subst),
      )
    Shift(prompt, body, ks, k) =>
      Shift(
        substitute_as_block_var(prompt, subst),
        substitute_block_lit(body, subst),
        substitute_meta_cont(ks, subst),
        substitute_cont(k, subst),
      )
    Resume(r, body, ks, k) =>
      Resume(
        substitute_as_block_var(r, subst),
        substitute_block_lit(body, subst),
        substitute_meta_cont(ks, subst),
        substitute_cont(k, subst),
      )
    Hole(_) => s
  }
}

///|
pub fn substitute_implementation(
  implementation : Implementation,
  subst : Substitution,
) -> Implementation raise EffektError {
  Implementation::new(
    implementation.interface,
    implementation.operations.map(op => substitute_operation(op, subst)),
  )
}

///|
pub fn substitute_operation(
  op : Operation,
  subst : Substitution,
) -> Operation raise EffektError {
  Operation::new(
    op.name,
    op.vparams,
    op.bparams,
    op.ks,
    op.k,
    substitute_stmt(
      op.body,
      subst
      .shadow_params(op.vparams, op.bparams)
      .shadow_metaconts([op.ks])
      .shadow_conts([op.k]),
    ),
  )
}

///|
pub fn substitute_clause(
  clause : Clause,
  subst : Substitution,
) -> Clause raise EffektError {
  Clause::new(
    clause.vparams,
    substitute_stmt(clause.body, subst.shadow_values(clause.vparams)),
  )
}

///|
pub fn substitute_cont(
  k : Cont,
  subst : Substitution,
) -> Cont raise EffektError {
  match k {
    ContVar(id) =>
      match subst.conts.get(id.uid()) {
        Some(replacement) => replacement
        None => ContVar(id)
      }
    ContLam(lam) => ContLam(substitute_cont_lam(lam, subst))
    Abort => Abort
  }
}

///|
pub fn substitute_cont_lam(
  k : ContLam,
  subst : Substitution,
) -> ContLam raise EffektError {
  ContLam::new(
    k.results,
    k.ks,
    substitute_stmt(
      k.body,
      subst.shadow_values(k.results).shadow_metaconts([k.ks]),
    ),
  )
}
