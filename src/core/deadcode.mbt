// Dead code elimination on core modules.
//
// Mirrors `effekt/core/optimizer/Reachable.scala` (the reachability analysis)
// and `effekt/core/optimizer/Deadcode.scala` (the rewrite it drives). Upstream
// runs the pass on the aggregated module, before `core.Show` and before code
// generation:
//
//     allToCore(Core) andThen Aggregate andThen Deadcode andThen core.Show ...
//     (generator/js/JavaScript.scala:47)
//
// so unreachable definitions and externs never reach `js.TransformerCps`, which
// reports every extern whose body does not apply to the current backend
// (TransformerCps.scala:118). The llvm-only externs of
// `libraries/common/effekt.effekt` are exactly this shape and are dropped here.
//
// Upstream's `Deadcode` is a `core.Tree.TrampolinedRewrite`; this port has no
// generic rewriter, so the traversal is written out by hand, following the
// per-node cases of `TrampolinedRewrite` (Tree.scala:645-887). The
// `Trampoline` upstream is only a stack safety device and is not needed.
//
// Deviations from upstream, all of them also noted where they occur:
//
//   - `Usage.*`, `Usage.decrement` and `Reachable.usage`'s counterpart
//     `Usage.Many` bookkeeping for the optimizer are only used by the passes
//     that this port does not include (`Optimizer`, `Normalizer`, `Inlining`,
//     `StaticResumptions`), so `*` and `decrement` are omitted; `+` is needed
//     by the analysis itself.
//   - `Reachable` threads the definitions functionally (`using defs:
//     Definitions`); the port threads a mutable map instead, adding an entry
//     when entering a `Def` / `Let` and removing it on the way out (uids are
//     globally unique, so this cannot shadow anything).
//   - `Deadcode.isPureCall` / the `Stmt.Val` rule is **not** ported: it tests
//     the *capture sets* of the callee and of the block arguments, and
//     capture-set inference in this port is approximate (see `README.mbt.md`),
//     so a call that captures a region -- the recursive function of a `while`
//     loop, for instance -- can look pure and would be dropped together with
//     its effect. See [[Deadcode::rewrite_stmt]].
//   - `Reachable` reads `callee.tpe` of an `Invoke` and the type of every
//     block; only block *variables* carry an annotated type in this port, see
//     [[Reachable::process_block_tpe]].
//   - `Usage`, `Reachable` and `Deadcode` are not part of the public interface:
//     the only caller is the backend.

// ---------------------------------------------------------------------------
// Usage (Reachable.scala:211-245)
// ---------------------------------------------------------------------------

///|
/// How often a definition is used, the result of the reachability analysis.
priv enum Usage {
  Never
  Once
  Many
  Recursive
}

///|
/// Upstream's `Usage.+` (Reachable.scala:217): the usage of a definition that is
/// used by both operands.
///
/// MoonBit spells operator overloading as an implementation of the `Add` trait.
impl Add for Usage with fn add(self, other) {
  match (self, other) {
    (Never, other) => other
    (other, Never) => other
    (_, Recursive) => Recursive
    (Recursive, _) => Recursive
    (Once, Once) => Many
    (Many, Many) => Many
    (Many, Once) => Many
    (Once, Many) => Many
  }
}

// ---------------------------------------------------------------------------
// Definitions (Reachable.scala:15)
// ---------------------------------------------------------------------------

///|
/// What a symbol stands for while the analysis looks at it: upstream's
/// `Reachable.Definitions` value type.
priv enum Definition {
  DefBlock(Block)
  DefExpr(Expr)
  DefStmt(Stmt)
  DefExtern(Extern)
  DefDeclaration(Declaration)
  /// A property together with the interface declaration that declares it.
  DefProperty(Property, Declaration)
}

// ---------------------------------------------------------------------------
// The reachability analysis (Reachable.scala)
// ---------------------------------------------------------------------------

///|
/// The state of the analysis: the usage of every symbol seen so far, the
/// definitions of the module, the ids whose definition is currently being
/// processed (`stack`) and those that have been processed (`seen`).
priv struct Reachable {
  /// uid -> usage (upstream's `reachable`)
  reachable : Map[Int32, Usage]
  /// The ids whose definition is currently being processed (upstream's `stack`)
  stack : Array[Int32]
  /// The ids whose definition has already been processed (upstream's `seen`)
  seen : Map[Int32, Bool]
  /// uid -> definition (upstream's `defs`)
  defs : Map[Int32, Definition]
}

///|
/// The initial usage and *all* definitions of the module, mirroring
/// `Reachable.apply` (Reachable.scala:188).
///
/// Note that a `Property` is registered under its own id and that using it also
/// marks the enclosing interface as used (`process_definition`).
fn reachable_new(entrypoints : Array[Sym], m : ModuleDecl) -> Reachable {
  let defs : Map[Int32, Definition] = Map([])
  for d in m.definitions {
    match d {
      ToplevelDef(id, block) => defs.set(id.uid(), DefBlock(block))
      ToplevelVal(id, binding) => defs.set(id.uid(), DefStmt(binding))
    }
  }
  for d in m.declarations {
    defs.set(d.id().uid(), DefDeclaration(d))
    match d {
      DeclarationData(_, _, _) => ()
      DeclarationInterface(_, _, properties) =>
        for p in properties {
          defs.set(p.id.uid(), DefProperty(p, d))
        }
    }
  }
  for e in m.externs {
    match e {
      // only extern *definitions* have a body that can be reached
      ExternDef(id, _, _, _, _, _, _, _, _) => defs.set(id.uid(), DefExtern(e))
      _ => ()
    }
  }
  let reachable : Map[Int32, Usage] = Map([])
  for id in entrypoints {
    reachable.set(id.uid(), Recursive)
  }
  { reachable, stack: [], seen: Map([]), defs, }
}

///|
fn Reachable::update(self : Reachable, id : Sym, u : Usage) -> Unit {
  self.reachable.set(id.uid(), u)
}

///|
fn Reachable::usage(self : Reachable, id : Sym) -> Usage {
  match self.reachable.get(id.uid()) {
    Some(u) => u
    None => Never
  }
}

///|
/// Records a use of `id` and, the first time the id is seen, processes the
/// definition it stands for. Mirrors `Reachable.process(id)` (Reachable.scala:43).
fn Reachable::process_id(self : Reachable, id : Sym) -> Unit {
  let uid = id.uid()
  if self.stack.contains(uid) {
    self.update(id, Recursive)
    return
  }
  self.update(id, self.usage(id) + Once)
  if !self.seen.contains(uid) {
    self.seen.set(uid, true)
    match self.defs.get(uid) {
      Some(d) => self.process_definition(id, d)
      None => ()
    }
  }
}

///|
/// Processes the definition of an id that is on the stack of the analysis.
/// Mirrors `Reachable.processDefinition` (Reachable.scala:20).
fn Reachable::process_definition(
  self : Reachable,
  id : Sym,
  d : Definition,
) -> Unit {
  let uid = id.uid()
  if self.stack.contains(uid) {
    self.update(id, Recursive)
    return
  }
  self.seen.set(uid, true)
  match d {
    DefBlock(block) => {
      let before = self.stack.length()
      self.stack.push(uid)
      self.process_block(block)
      self.stack.truncate(before)
    }
    DefExpr(expr) => self.process_expr(expr)
    DefStmt(binding) => self.process_stmt(binding)
    DefExtern(definition) => self.process_extern(definition)
    DefDeclaration(decl) => self.process_declaration(decl)
    DefProperty(p, d) => {
      self.process_block_type(p.tpe)
      self.process_id(d.id())
    }
  }
}

// ---------------------------------------------------------------------------
// The tree traversal of the analysis
// ---------------------------------------------------------------------------

///|
/// `process(b: Block)` (Reachable.scala:57).
fn Reachable::process_block(self : Reachable, b : Block) -> Unit {
  match b {
    BlockVar(bv) => {
      self.process_block_type(bv.annotated_tpe)
      self.process_id(bv.id)
    }
    BlockLit(lit) => self.process_block_lit(lit)
    Unbox(expr) => self.process_expr(expr)
    New(implementation) => self.process_implementation(implementation)
  }
}

///|
/// `process(b: Block.BlockLit)` (Reachable.scala:61): the type parameters and
/// capture parameters are not processed.
fn Reachable::process_block_lit(self : Reachable, lit : BlockLit) -> Unit {
  for p in lit.vparams {
    self.process_value_type(p.tpe)
  }
  for p in lit.bparams {
    self.process_block_type(p.tpe)
  }
  self.process_stmt(lit.body)
}

///|
/// `process(callee.tpe)` of `Stmt.Invoke` (Reachable.scala:138).
///
/// Upstream reads the inferred type of the block; in this port only a block
/// *variable* records one, so the other cases approximate it by the types that
/// are available (the parameter types of a literal and the interface of a
/// `New`). Processing a type can only ever mark more definitions as used, so
/// the approximation keeps code rather than dropping it.
fn Reachable::process_block_tpe(self : Reachable, b : Block) -> Unit {
  match b {
    BlockVar(bv) => self.process_block_type(bv.annotated_tpe)
    BlockLit(lit) => {
      for p in lit.vparams {
        self.process_value_type(p.tpe)
      }
      for p in lit.bparams {
        self.process_block_type(p.tpe)
      }
    }
    Unbox(_) => ()
    New(implementation) => self.process_block_type(implementation.interface)
  }
}

///|
/// `process(e: Extern.Def)` (Reachable.scala:67): the type and capture
/// parameters are not processed.
fn Reachable::process_extern(self : Reachable, e : Extern) -> Unit {
  match e {
    ExternDef(_, _, _, _, vparams, bparams, ret, _, body) => {
      for p in vparams {
        self.process_value_type(p.tpe)
      }
      for p in bparams {
        self.process_block_type(p.tpe)
      }
      self.process_value_type(ret)
      match body {
        StringExternBody(_, contents) =>
          for arg in contents.args {
            self.process_expr(arg)
          }
        Unsupported(_) => ()
      }
    }
    _ => ()
  }
}

///|
/// `process(d: Declaration)` (Reachable.scala:83): the type parameters are not
/// processed.
fn Reachable::process_declaration(self : Reachable, d : Declaration) -> Unit {
  match d {
    DeclarationData(_, _, constructors) =>
      for c in constructors {
        for f in c.fields {
          self.process_value_type(f.tpe)
        }
      }
    DeclarationInterface(_, _, properties) =>
      for p in properties {
        self.process_block_type(p.tpe)
      }
  }
}

///|
/// `process(t: ValueType)` (Reachable.scala:98): a type *variable* is ignored
/// and the captures of a boxed type are not processed.
fn Reachable::process_value_type(self : Reachable, t : ValueType) -> Unit {
  match t {
    ValueTypeRef(_) => ()
    ValueTypeApp(name, targs) => {
      self.process_id(name)
      for targ in targs {
        self.process_value_type(targ)
      }
    }
    BoxedType(tpe, _) => self.process_block_type(tpe)
  }
}

///|
/// `process(t: BlockType)` (Reachable.scala:104): neither the type parameters
/// nor the capture parameters (the port's `effects`) are processed.
fn Reachable::process_block_type(self : Reachable, t : BlockType) -> Unit {
  match t {
    FunctionType(_, _, vparams, bparams, result, _) => {
      for p in vparams {
        self.process_value_type(p)
      }
      for p in bparams {
        self.process_block_type(p)
      }
      self.process_value_type(result)
    }
    InterfaceType(name, targs) => {
      self.process_id(name)
      for targ in targs {
        self.process_value_type(targ)
      }
    }
  }
}

///|
/// `process(s: Stmt)` (Reachable.scala:113).
fn Reachable::process_stmt(self : Reachable, s : Stmt) -> Unit {
  match s {
    Def(id, block, body) => {
      // Do NOT process `block` here, since this would mean the definition is
      // used (Reachable.scala:115). The entry is removed again on the way out:
      // uids are globally unique, so the surrounding scope cannot be shadowed.
      self.defs.set(id.uid(), DefBlock(block))
      self.process_stmt(body)
      self.defs.remove(id.uid())
    }
    Let(id, binding, body) => {
      // We would need to process the binding if it was impure, to keep it for
      // its side effects; however, the binding is guaranteed to be pure
      // (Reachable.scala:117).
      self.defs.set(id.uid(), DefExpr(binding))
      self.process_stmt(body)
      self.defs.remove(id.uid())
    }
    ImpureApp(_, callee, targs, vargs, bargs, body) => {
      self.process_block(BlockVar(callee))
      for targ in targs {
        self.process_value_type(targ)
      }
      for varg in vargs {
        self.process_expr(varg)
      }
      for barg in bargs {
        self.process_block(barg)
      }
      // TODO what to do here? (upstream does not add `id -> binding` either)
      self.process_stmt(body)
    }
    Return(expr) => self.process_expr(expr)
    Val(_, binding, body) => {
      self.process_stmt(binding)
      self.process_stmt(body)
    }
    App(callee, targs, vargs, bargs) => {
      self.process_block(callee)
      for targ in targs {
        self.process_value_type(targ)
      }
      for varg in vargs {
        self.process_expr(varg)
      }
      for barg in bargs {
        self.process_block(barg)
      }
    }
    Invoke(callee, method, method_tpe, targs, vargs, bargs) => {
      self.process_block(callee)
      self.process_block_tpe(callee)
      self.process_id(method)
      self.process_block_type(method_tpe)
      for targ in targs {
        self.process_value_type(targ)
      }
      for varg in vargs {
        self.process_expr(varg)
      }
      for barg in bargs {
        self.process_block(barg)
      }
    }
    If(cond, thn, els) => {
      self.process_expr(cond)
      self.process_stmt(thn)
      self.process_stmt(els)
    }
    Match(scrutinee, tpe, clauses, default) => {
      self.process_expr(scrutinee)
      self.process_value_type(tpe)
      // the *tag* of a clause is not processed: only the clause body is
      for clause in clauses {
        self.process_block_lit(clause.body)
      }
      match default {
        Some(body) => self.process_stmt(body)
        None => ()
      }
    }
    Alloc(_, init, region, body) => {
      self.process_expr(init)
      // the region is bound by this statement; it is a `BlockVar` in the tree
      self.process_id(region)
      self.process_stmt(body)
    }
    Var(_, init, _, body) => {
      self.process_expr(init)
      self.process_stmt(body)
    }
    Get(_, tpe, ref, _, body) => {
      self.process_id(ref)
      self.process_value_type(tpe)
      self.process_stmt(body)
    }
    Put(ref, _, value, body) => {
      self.process_id(ref)
      self.process_expr(value)
      self.process_stmt(body)
    }
    Reset(body) => self.process_block_lit(body)
    Shift(prompt, k, body) => {
      self.process_block(BlockVar(prompt))
      // `k` is a binding occurrence; only its type is looked at
      self.process_block_type(k.tpe)
      self.process_stmt(body)
    }
    Resume(k, body) => {
      self.process_block(BlockVar(k))
      self.process_stmt(body)
    }
    Region(body) => self.process_block_lit(body)
    Hole(tpe, _) => self.process_value_type(tpe)
  }
}

///|
/// `process(e: Expr)` (Reachable.scala:167).
fn Reachable::process_expr(self : Reachable, e : Expr) -> Unit {
  match e {
    ValueVar(id, annotated_tpe) => {
      self.process_id(id)
      self.process_value_type(annotated_tpe)
    }
    Literal(_, annotated_tpe) => self.process_value_type(annotated_tpe)
    PureApp(callee, targs, vargs) => {
      self.process_block(BlockVar(callee))
      for targ in targs {
        self.process_value_type(targ)
      }
      for varg in vargs {
        self.process_expr(varg)
      }
    }
    Make(data, tag, targs, vargs) => {
      self.process_id(data)
      self.process_id(tag)
      for targ in targs {
        self.process_value_type(targ)
      }
      for varg in vargs {
        self.process_expr(varg)
      }
    }
    Box(b, _) => self.process_block(b)
  }
}

///|
/// `process(i: Implementation)` (Reachable.scala:176): the name, type and
/// capture parameters of an operation are not processed.
fn Reachable::process_implementation(
  self : Reachable,
  i : Implementation,
) -> Unit {
  self.process_block_type(i.interface)
  for op in i.operations {
    for p in op.vparams {
      self.process_value_type(p.tpe)
    }
    for p in op.bparams {
      self.process_block_type(p.tpe)
    }
    self.process_stmt(op.body)
  }
}

// ---------------------------------------------------------------------------
// The rewrite (Deadcode.scala)
// ---------------------------------------------------------------------------

///|
/// The rewrite driven by the reachability analysis, mirroring `Deadcode`.
priv struct Deadcode {
  reachable : Map[Int32, Usage]
}

///|
/// `Deadcode.used` (Deadcode.scala:12).
fn Deadcode::used(self : Deadcode, id : Sym) -> Bool {
  match self.reachable.get(id.uid()) {
    Some(Never) | None => false
    Some(_) => true
  }
}

///|
/// `Deadcode.unused`.
fn Deadcode::unused(self : Deadcode, id : Sym) -> Bool {
  !self.used(id)
}

///|
/// `Deadcode.rewrite(m: ModuleDecl)` (Deadcode.scala:52): drops unused
/// declarations, unreachable externs and unreachable toplevel definitions.
///
/// `Extern.Include` is always kept; an extern with an unsupported body is kept
/// as long as it is used (and is then reported by the backend).
fn Deadcode::rewrite_module(self : Deadcode, m : ModuleDecl) -> ModuleDecl {
  // drop unused constructors and operations, and types
  let declarations : Array[Declaration] = []
  for d in m.declarations {
    if self.used(d.id()) {
      declarations.push(self.rewrite_declaration(d))
    }
  }
  // drop unreachable externs
  let externs : Array[Extern] = []
  for e in m.externs {
    match e {
      ExternDef(id, _, _, _, _, _, _, _, _) =>
        if self.used(id) {
          externs.push(e)
        }
      ExternInclude(_, _) => externs.push(e)
      ExternData(id, _, _) => if self.used(id) { externs.push(e) }
      ExternInterface(id, _, _) => if self.used(id) { externs.push(e) }
    }
  }
  // drop unreachable definitions
  let definitions : Array[Toplevel] = []
  for d in m.definitions {
    if self.used(d.id()) {
      definitions.push(self.rewrite_toplevel(d))
    }
  }
  ModuleDecl::new(
    m.path,
    m.includes,
    declarations,
    externs,
    definitions,
    m.exports,
  )
}

///|
/// `Deadcode.rewrite(d: Declaration)` (Deadcode.scala:71).
fn Deadcode::rewrite_declaration(
  self : Deadcode,
  d : Declaration,
) -> Declaration {
  match d {
    DeclarationData(id, tparams, constructors) => {
      let kept : Array[Constructor] = []
      for c in constructors {
        if self.used(c.id) {
          kept.push(c)
        }
      }
      DeclarationData(id, tparams, kept)
    }
    DeclarationInterface(id, tparams, properties) => {
      let kept : Array[Property] = []
      for p in properties {
        if self.used(p.id) {
          kept.push(p)
        }
      }
      DeclarationInterface(id, tparams, kept)
    }
  }
}

///|
/// `rewrite(d: Toplevel)` of `TrampolinedRewrite` (Tree.scala:817).
fn Deadcode::rewrite_toplevel(self : Deadcode, d : Toplevel) -> Toplevel {
  match d {
    ToplevelDef(id, block) => ToplevelDef(id, self.rewrite_block(block))
    ToplevelVal(id, binding) => ToplevelVal(id, self.rewrite_stmt(binding))
  }
}

///|
/// `Deadcode.rewrite(implementation: Implementation)` (Deadcode.scala:45): drops unused
/// operations. The interface type itself is not rewritten, like everywhere else
/// in this pass (the base rewriter is the identity on types).
fn Deadcode::rewrite_implementation(
  self : Deadcode,
  implementation : Implementation,
) -> Implementation {
  let operations : Array[Operation] = []
  for op in implementation.operations {
    if self.used(op.name) {
      operations.push(self.rewrite_operation(op))
    }
  }
  Implementation::new(implementation.interface, operations)
}

///|
/// `rewrite(o: Operation)` of `TrampolinedRewrite` (Tree.scala:793).
fn Deadcode::rewrite_operation(self : Deadcode, op : Operation) -> Operation {
  Operation::new(
    op.name,
    op.tparams,
    op.cparams,
    op.vparams,
    op.bparams,
    self.rewrite_stmt(op.body),
  )
}

///|
/// `rewrite(b: Block)` of `TrampolinedRewrite` (Tree.scala:778).
fn Deadcode::rewrite_block(self : Deadcode, b : Block) -> Block {
  match b {
    BlockVar(bv) => BlockVar(bv)
    BlockLit(lit) => BlockLit(self.rewrite_block_lit(lit))
    Unbox(pure) => Unbox(self.rewrite_expr(pure))
    New(implementation) => New(self.rewrite_implementation(implementation))
  }
}

///|
/// `rewrite(b: BlockLit)` of `TrampolinedRewrite` (Tree.scala:844).
fn Deadcode::rewrite_block_lit(self : Deadcode, lit : BlockLit) -> BlockLit {
  BlockLit::new(
    lit.tparams,
    lit.cparams,
    lit.vparams,
    lit.bparams,
    self.rewrite_stmt(lit.body),
  )
}

///|
/// `rewrite(e: Expr)` of `TrampolinedRewrite` (Tree.scala:647): `Deadcode` does
/// not override expressions, but the traversal still descends into them (a
/// `Box` can hold a block literal whose body is rewritten).
fn Deadcode::rewrite_expr(self : Deadcode, e : Expr) -> Expr {
  match e {
    ValueVar(id, annotated_tpe) => ValueVar(id, annotated_tpe)
    Literal(value, annotated_tpe) => Literal(value, annotated_tpe)
    PureApp(callee, targs, vargs) =>
      PureApp(callee, targs, vargs.map(v => self.rewrite_expr(v)))
    Make(data, tag, targs, vargs) =>
      Make(data, tag, targs, vargs.map(v => self.rewrite_expr(v)))
    Box(b, annotated_capture) => Box(self.rewrite_block(b), annotated_capture)
  }
}

///|
/// `Deadcode.rewrite(stmt: Stmt)` (Deadcode.scala:22) together with the cases of
/// `TrampolinedRewrite.rewrite(s: Stmt)` (Tree.scala:667) that `Deadcode` does
/// not override.
fn Deadcode::rewrite_stmt(self : Deadcode, s : Stmt) -> Stmt {
  match s {
    // Remove local unused definitions
    Def(id, block, body) =>
      if self.unused(id) {
        self.rewrite_stmt(body)
      } else {
        Def(id, self.rewrite_block(block), self.rewrite_stmt(body))
      }
    Let(id, binding, body) =>
      if self.unused(id) {
        self.rewrite_stmt(body)
      } else {
        Let(id, self.rewrite_expr(binding), self.rewrite_stmt(body))
      }

    // Upstream also removes a local unused `val` whose binding is a *pure* call
    // (`Deadcode.isPureCall`, Deadcode.scala:17-28). That rule is deliberately
    // not ported: it decides purity from the capture sets of the callee and of
    // the block arguments, and capture-set inference here is approximate, so
    // bindings that do capture a region are classified as pure and dropped --
    // a `while` loop is exactly this shape (its loop function captures the
    // mutable variables), and dropping the `val` that performs the call loses
    // the loop. The two rules above only look at *reachability* and are
    // therefore sound with approximate captures.
    Val(id, binding, body) =>
      Val(id, self.rewrite_stmt(binding), self.rewrite_stmt(body))

    // `Reset({ [cap]{p} => body })` with an unused prompt is the body
    Reset(body) => {
      let body2 = self.rewrite_block_lit(body)
      if body2.bparams.length() == 1 && self.unused(body2.bparams[0].id) {
        body2.body
      } else {
        Reset(body2)
      }
    }
    Match(scrutinee, tpe, clauses, default) => {
      let clauses2 : Array[Clause] = []
      for clause in clauses {
        if self.used(clause.tag) {
          clauses2.push(
            Clause::new(clause.tag, self.rewrite_block_lit(clause.body)),
          )
        }
      }
      let default2 = match default {
        Some(body) => Some(self.rewrite_stmt(body))
        None => None
      }
      Match(self.rewrite_expr(scrutinee), tpe, clauses2, default2)
    }

    // `case other => super.rewrite(other)`
    ImpureApp(id, callee, targs, vargs, bargs, body) =>
      ImpureApp(
        id,
        callee,
        targs,
        vargs.map(v => self.rewrite_expr(v)),
        bargs.map(b => self.rewrite_block(b)),
        self.rewrite_stmt(body),
      )
    Return(expr) => Return(self.rewrite_expr(expr))
    App(callee, targs, vargs, bargs) =>
      App(
        self.rewrite_block(callee),
        targs,
        vargs.map(v => self.rewrite_expr(v)),
        bargs.map(b => self.rewrite_block(b)),
      )
    Invoke(callee, method, method_tpe, targs, vargs, bargs) =>
      Invoke(
        self.rewrite_block(callee),
        method,
        method_tpe,
        targs,
        vargs.map(v => self.rewrite_expr(v)),
        bargs.map(b => self.rewrite_block(b)),
      )
    If(cond, thn, els) =>
      If(
        self.rewrite_expr(cond),
        self.rewrite_stmt(thn),
        self.rewrite_stmt(els),
      )
    Region(body) => Region(self.rewrite_block_lit(body))
    Alloc(id, init, region, body) =>
      Alloc(id, self.rewrite_expr(init), region, self.rewrite_stmt(body))
    Var(ref, init, capture, body) =>
      Var(ref, self.rewrite_expr(init), capture, self.rewrite_stmt(body))
    Get(id, annotated_tpe, ref, annotated_capt, body) =>
      Get(id, annotated_tpe, ref, annotated_capt, self.rewrite_stmt(body))
    Put(ref, annotated_capt, value, body) =>
      Put(
        ref,
        annotated_capt,
        self.rewrite_expr(value),
        self.rewrite_stmt(body),
      )
    Shift(prompt, k, body) => Shift(prompt, k, self.rewrite_stmt(body))
    Resume(k, body) => Resume(k, self.rewrite_stmt(body))
    Hole(tpe, span) => Hole(tpe, span)
  }
}

// ---------------------------------------------------------------------------
// The pass (Deadcode.scala:83)
// ---------------------------------------------------------------------------

///|
/// Removes the definitions and externs that are not reachable from the given
/// entry points, mirroring `Deadcode.remove` (Deadcode.scala:100).
///
/// The entry points themselves are always kept, and their usage is `Recursive`
/// from the start (Reachable.scala:202); pass `core.required_names` alongside
/// the entry point of the module to keep the names that `core.Show` needs.
pub fn deadcode(module : ModuleDecl, entrypoints : Array[Sym]) -> ModuleDecl {
  let analysis = reachable_new(entrypoints, module)
  for id in entrypoints {
    analysis.process_id(id)
  }
  let rewrite : Deadcode = { reachable: analysis.reachable, }
  rewrite.rewrite_module(module)
}
