// The normalizer: performs a step of computation when enough information is
// available.
//
// Mirrors `effekt/core/optimizer/Normalizer.scala`:
//
//     def foo(n: Int) = return n + 1
//     foo(42)
//   =>
//     def foo(n: Int) = return n + 1
//     return 42 + 1
//
// A cut is not removed when the definition is recursive or when inlining would
// exceed the size budget of the policy; a definition that is used exactly once
// is inlined regardless of the budget (see `InliningPolicy`).
//
// Differences from upstream, all of them because this port has no core type
// inference (`core/Type.scala`) and therefore no `tpe` on expressions and
// statements:
//
//   * `facts` (upstream's CSE: pure expressions that are known to equal a
//     simpler expression, keyed by *structural expression equality*) is not
//     ported. Knowledge about variables (`NormCtx.exprs`) is kept, which is
//     what folds `if`/`match` on a known scrutinee.
//   * `covers` and `selecting` need the scrutinee's data type, so a `match`
//     keeps its default and its clauses are normalized without knowing which
//     constructor the scrutinee has.
//   * the `Shift` rule of `normalizeVal` needs `BlockType.Resume`, which the
//     type language of this port does not have.
//   * join point parameters get `unknown_value_type()` (upstream uses the
//     inferred types of the branches) and a `Match` keeps the annotation it had.
//   * the "return the unit value" rule of `normalizeVal` checks that the bound
//     statement returns `()` syntactically instead of comparing result types.

// ---------------------------------------------------------------------------
// The inlining policy (InliningPolicy.scala)
// ---------------------------------------------------------------------------

///|
/// When to inline a call site.
pub(all) enum InliningPolicy {
  /// Inline a callee that is used exactly once, one with a known block argument,
  /// or one whose body is at most `threshold` nodes.
  Unique(Int32)
  /// `Unique`, with the used-once rule bounded by `once_limit` (`None` means
  /// unbounded) and with the "carries an operation to its handler" rule bounded
  /// by `carrying_limit`.
  Default(Int32, Int32?, Int32)
}

///|
/// The default policy, with upstream's flag defaults (`--max-inline-size 50`,
/// `--max-once-inline-size 5000`, `--max-carrying-inline-size 100`).
pub fn InliningPolicy::default() -> InliningPolicy {
  Default(50, Some(5000), 100)
}

///|
/// A callee together with the arguments at the call site.
priv struct CallSite {
  callee : BlockLit
  /// The block variable the callee was reached through, if any.
  bound_by : BlockVar?
  vargs : Array[Expr]
  bargs : Array[Block]
}

///|
fn CallSite::CallSite(
  callee : BlockLit,
  bound_by : BlockVar?,
  vargs : Array[Expr],
  bargs : Array[Block],
) -> CallSite {
  { callee, bound_by, vargs, bargs, }
}

// ---------------------------------------------------------------------------
// The context
// ---------------------------------------------------------------------------

///|
/// The environment of the current subtree: the blocks and expressions that are
/// known to denote something, and the prompts we are under.
priv struct NormCtx {
  /// uid -> block
  blocks : Map[Int32, Block]
  /// uid -> expression
  exprs : Map[Int32, Expr]
  /// The enclosing `Reset`s' prompts, innermost first.
  prompts : Array[Sym]
}

///|
fn NormCtx::empty(blocks : Map[Int32, Block]) -> NormCtx {
  { blocks, exprs: Map([]), prompts: [], }
}

///|
fn NormCtx::with_block(self : NormCtx, id : Sym, block : Block) -> NormCtx {
  let blocks = self.blocks.copy()
  blocks.set(id.uid(), block)
  { blocks, exprs: self.exprs, prompts: self.prompts, }
}

///|
fn NormCtx::with_expr(self : NormCtx, id : Sym, expr : Expr) -> NormCtx {
  let exprs = self.exprs.copy()
  exprs.set(id.uid(), expr)
  { blocks: self.blocks, exprs, prompts: self.prompts, }
}

///|
fn NormCtx::enter_prompt(self : NormCtx, prompt : Sym) -> NormCtx {
  { blocks: self.blocks, exprs: self.exprs, prompts: [prompt] + self.prompts, }
}

///|
/// Whether `id` is one of the enclosing prompts.
fn NormCtx::has_prompt(self : NormCtx, id : Sym) -> Bool {
  self.prompts.any(p => p.uid() == id.uid())
}

///|
/// A block that `active` has resolved: either it is known (`BlockLit`, `New`,
/// `Unbox`), together with the variable it was reached through, or it is stuck
/// on a variable.
priv enum NormBlock {
  Known(Block, BlockVar?)
  Unknown(BlockVar)
}

///|
fn NormBlock::dealiased(self : NormBlock) -> Block {
  match self {
    Known(b, _) => b
    Unknown(b) => BlockVar(b)
  }
}

///|
fn NormBlock::shared(self : NormBlock) -> Block {
  match self {
    Known(_, Some(bv)) => BlockVar(bv)
    Known(b, None) => b
    Unknown(b) => BlockVar(b)
  }
}

// ---------------------------------------------------------------------------
// The normalizer
// ---------------------------------------------------------------------------

///|
/// The state of one normalization run: the usage information (mutated while
/// inlining, which is how upstream keeps it up to date), the policy and the
/// declarations of the module.
priv struct Normalizer {
  /// uid -> usage
  usage : Map[Int32, Usage]
  policy : InliningPolicy
}

///|
/// Normalizes `module`; `entrypoints` are the symbols the reachability analysis
/// starts from (upstream: `Normalizer.normalize(entrypoints, m, policy)`).
pub fn normalize(
  module : ModuleDecl,
  entrypoints : Array[Sym],
  policy : InliningPolicy,
) -> ModuleDecl raise EffektError {
  let usage = reachable_usage(module, entrypoints)
  let blocks : Map[Int32, Block] = Map([])
  for d in module.definitions {
    match d {
      ToplevelDef(id, block) => blocks.set(id.uid(), block)
      ToplevelVal(_, _) => ()
    }
  }
  let normal : Normalizer = { usage, policy, }
  let mut ctx = NormCtx::empty(blocks)
  let definitions : Array[Toplevel] = []
  for d in module.definitions {
    match d {
      ToplevelDef(id, block) => {
        let normalized = normal.rewrite_block(block, ctx)
        ctx = ctx.with_block(id, normalized)
        definitions.push(ToplevelDef(id, normalized))
      }
      ToplevelVal(id, binding) => {
        let normalized = normal.rewrite_stmt(binding, ctx)
        match normalized {
          // a toplevel `val` that is just a value is an alias
          Return([expr]) => ctx = ctx.with_expr(id, expr)
          _ => ()
        }
        definitions.push(ToplevelVal(id, normalized))
      }
    }
  }
  ModuleDecl(
    module.path,
    module.includes,
    module.declarations,
    module.externs,
    definitions,
    module.exports,
  )
}

// ---------------------------------------------------------------------------
// Usage
// ---------------------------------------------------------------------------

///|
fn Normalizer::usage_of(self : Normalizer, id : Sym) -> Usage {
  match self.usage.get(id.uid()) {
    Some(usage) => usage
    None => Never
  }
}

///|
/// Upstream's `isRecursive`: without information a definition counts as
/// recursive, since reducing it might diverge.
fn Normalizer::is_recursive(self : Normalizer, id : Sym) -> Bool {
  match self.usage.get(id.uid()) {
    Some(usage) => usage == Recursive
    None => true
  }
}

///|
fn Normalizer::is_once(self : Normalizer, id : Sym) -> Bool {
  match self.usage.get(id.uid()) {
    Some(usage) => usage == Once
    None => false
  }
}

///|
fn Normalizer::is_unused(self : Normalizer, id : Sym) -> Bool {
  match self.usage.get(id.uid()) {
    Some(usage) => usage == Never
    None => true
  }
}

///|
fn Normalizer::copy_usage_one(self : Normalizer, to : Sym, from : Sym) -> Unit {
  match self.usage.get(from.uid()) {
    Some(usage) => self.usage.set(to.uid(), usage)
    None => ()
  }
}

///|
fn Normalizer::copy_usage(
  self : Normalizer,
  renamings : Map[Int32, Sym],
) -> Unit {
  for fresh, original in renamings {
    match self.usage.get(original.uid()) {
      Some(usage) => self.usage.set(fresh, usage)
      None => ()
    }
  }
}

// ---------------------------------------------------------------------------
// Knowledge
// ---------------------------------------------------------------------------

///|
/// The expression that `e` denotes, after normalizing it and resolving the
/// variables we know.
fn Normalizer::active_expr(
  self : Normalizer,
  e : Expr,
  ctx : NormCtx,
) -> Expr raise EffektError {
  match self.rewrite_expr(e, ctx) {
    ValueVar(id, _) as stuck =>
      match ctx.exprs.get(id.uid()) {
        Some(other) => other
        None => stuck
      }
    other => other
  }
}

///|
/// The block that `b` denotes, maximally dealiased. Depending on the call site
/// we want a redex (`BlockLit` / `New`), the outermost `Unbox`, or some sharing
/// (see `NormalizedBlock.shared`).
fn Normalizer::active_block(
  self : Normalizer,
  b : Block,
  ctx : NormCtx,
) -> NormBlock raise EffektError {
  match self.rewrite_block(b, ctx) {
    BlockLit(lit) => Known(BlockLit(lit), None)
    New(implementation) => Known(New(implementation), None)
    BlockVar(bv) =>
      match ctx.blocks.get(bv.id.uid()) {
        Some(known) =>
          match known {
            BlockLit(_) | New(_) | Unbox(_) => Known(known, Some(bv))
            _ => Unknown(bv)
          }
        None => Unknown(bv)
      }
    Unbox(expr) =>
      match self.active_expr(expr, ctx) {
        Box(inner, _) => self.active_block(inner, ctx)
        _ => Known(Unbox(expr), None)
      }
  }
}

///|
/// The block that `b` denotes, when it is known here *and* nothing else uses it:
/// this is what lets the normalizer resolve its operations and consume it
/// instead of copying it.
fn Normalizer::known_and_used_once(
  self : Normalizer,
  b : Block,
  ctx : NormCtx,
) -> Block? raise EffektError {
  match b {
    BlockVar(bv) =>
      if self.is_once(bv.id) {
        match self.active_block(BlockVar(bv), ctx) {
          Known(known, Some(_)) => Some(known)
          _ => None
        }
      } else {
        None
      }
    _ => None
  }
}

///|
/// Within a branch we know the value of the condition.
fn assuming(cond : Expr, value : Bool, ctx : NormCtx) -> NormCtx {
  match cond {
    // variables belong into the environment, which `active` consults
    ValueVar(id, tpe) => ctx.with_expr(id, Literal(LBool(value), tpe))
    _ => ctx
  }
}

// ---------------------------------------------------------------------------
// The policy
// ---------------------------------------------------------------------------

///|
fn has_known_block_arg(site : CallSite) -> Bool {
  site.bargs.any(b => {
    match b {
      BlockLit(_) | New(_) => true
      BlockVar(_) | Unbox(_) => false
    }
  })
}

///|
/// Whether normalizing `body` would *move* a scope (a `reset` or a `region`)
/// rather than copy computation.
fn installs_scope(body : Stmt) -> Bool {
  stmt_any(body, s => {
    match s {
      Reset(_) | Region(_) => true
      _ => false
    }
  })
}

///|
fn Normalizer::moves_a_scope_into_a_prompt(
  self : Normalizer,
  site : CallSite,
  ctx : NormCtx,
) -> Bool {
  let _ = self
  ctx.prompts.length() > 0 && installs_scope(site.callee.body)
}

///|
/// A callee used exactly once is inlined if it is at most `once_limit` nodes,
/// and only if inlining it does not move a scope into a prompt.
fn Normalizer::used_once(
  self : Normalizer,
  callee : BlockVar,
  site : CallSite,
  ctx : NormCtx,
  once_limit : Int32?,
) -> Bool {
  self.is_once(callee.id) &&
  (match once_limit {
    Some(limit) => site.callee.body.size() <= limit
    None => true
  }) &&
  !self.moves_a_scope_into_a_prompt(site, ctx)
}

///|
fn Normalizer::shifts_to_an_enclosing_prompt(
  self : Normalizer,
  implementation : Implementation,
  ctx : NormCtx,
) -> Bool {
  let _ = self
  let shifts = (s : Stmt) => {
    match s {
      Shift(prompt, _, _) => ctx.has_prompt(prompt.id)
      _ => false
    }
  }
  if any_stmt_in_implementation(implementation, shifts) {
    true
  } else {
    // a method that only tail-calls a known block is looked through
    implementation.operations.any(op => {
      match op.body {
        App(BlockVar(callee), _, _, _) =>
          match ctx.blocks.get(callee.id.uid()) {
            Some(BlockLit(jumped_to)) => block_lit_any(jumped_to, shifts)
            _ => false
          }
        _ => false
      }
    })
  }
}

///|
/// Whether the call carries an operation to the handler that serves it: the
/// cheapest and most valuable case for inlining.
fn Normalizer::carries_an_operation_to_its_handler(
  self : Normalizer,
  site : CallSite,
  ctx : NormCtx,
  carrying_limit : Int32,
) -> Bool raise EffektError {
  site.bargs.length() > 0 &&
  site.callee.body.size() <= carrying_limit &&
  any_raise(site.bargs, barg => {
    match self.known_and_used_once(barg, ctx) {
      Some(New(implementation)) =>
        self.shifts_to_an_enclosing_prompt(implementation, ctx)
      _ => false
    }
  }) &&
  !self.moves_a_scope_into_a_prompt(site, ctx)
}

///|
/// Does the body fit the budget this call site can afford?
fn Normalizer::affordable(
  self : Normalizer,
  site : CallSite,
  ctx : NormCtx,
  threshold : Int32,
) -> Bool raise EffektError {
  site.callee.body.size() <= threshold ||
  site.callee.body.size() <= threshold + self.discount(site, ctx)
}

///|
/// How much of the callee provably becomes dead once the arguments known *here*
/// are substituted. Conservative: under-counting only loses an inlining.
fn Normalizer::discount(
  self : Normalizer,
  site : CallSite,
  ctx : NormCtx,
) -> Int32 raise EffektError {
  let known : Array[(Sym, Expr)] = []
  let count = if site.callee.vparams.length() < site.vargs.length() {
    site.callee.vparams.length()
  } else {
    site.vargs.length()
  }
  for i = 0; i < count; i = i + 1 {
    let arg = self.active_expr(site.vargs[i], ctx)
    match arg {
      Literal(_, _) | Make(_, _, _, _) =>
        known.push((site.callee.vparams[i].id, arg))
      _ => ()
    }
  }
  if known.length() == 0 {
    0
  } else {
    dead_branches(known, site.callee.body)
  }
}

///|
/// The size of the branches that knowing the given values would delete.
fn dead_branches(known : Array[(Sym, Expr)], body : Stmt) -> Int32 {
  let mut acc = 0
  let mut current = body
  while true {
    match current {
      // a binder cannot select a branch, so pass through it
      Val(_, _, rest) => current = rest
      Let(_, _, rest) => current = rest
      ImpureApp(_, _, _, _, _, rest) => current = rest
      Def(_, _, rest) => current = rest
      Alloc(_, _, _, rest) => current = rest
      Var(_, _, _, rest) => current = rest
      Get(_, _, _, _, rest) => current = rest
      Put(_, _, _, rest) => current = rest
      If(cond, thn, els) =>
        match cond {
          ValueVar(id, _) =>
            match known_value(known, id) {
              Some(Literal(LBool(true), _)) => {
                acc = acc + els.size()
                current = thn
              }
              Some(Literal(LBool(false), _)) => {
                acc = acc + thn.size()
                current = els
              }
              _ => return acc
            }
          _ => return acc
        }
      Match(scrutinee, _, clauses, default) =>
        match scrutinee {
          ValueVar(id, _) =>
            match known_value(known, id) {
              Some(Make(_, tag, _, _)) => {
                let mut dead = 0
                let mut selected : Clause? = None
                for clause in clauses {
                  if clause.tag.uid() == tag.uid() {
                    selected = Some(clause)
                  } else {
                    dead = dead + clause.body.size()
                  }
                }
                match selected {
                  Some(clause) => {
                    acc = acc + dead
                    match default {
                      Some(d) => acc = acc + d.size()
                      None => ()
                    }
                    current = clause.body.body
                  }
                  None =>
                    match default {
                      Some(d) => {
                        acc = acc + dead
                        current = d
                      }
                      None => return acc + dead
                    }
                }
              }
              _ => return acc
            }
          _ => return acc
        }
      // past anything else we cannot see what dies
      _ => return acc
    }
  }
  acc
}

///|
fn known_value(known : Array[(Sym, Expr)], id : Sym) -> Expr? {
  for entry in known {
    let (sym, value) = entry
    if sym.uid() == id.uid() {
      return Some(value)
    }
  }
  None
}

///|
fn Normalizer::should_inline(
  self : Normalizer,
  site : CallSite,
  ctx : NormCtx,
) -> Bool raise EffektError {
  match self.policy {
    Unique(threshold) =>
      match site.bound_by {
        // an anonymous callee cannot be recursive (it has no name)
        None => site.bargs.any(b => b is BlockLit(_))
        Some(callee) =>
          !self.is_recursive(callee.id) &&
          (self.is_once(callee.id) || site.callee.body.size() <= threshold)
      }
    Default(threshold, once_limit, carrying_limit) =>
      match site.bound_by {
        None => has_known_block_arg(site)
        Some(callee) =>
          // 1) never inline recursive identifiers
          !self.is_recursive(callee.id) &&
          // 2) a callee used only once is tried first
          (
            self.used_once(callee, site, ctx, once_limit) ||
            // 3) or the call carries an operation to its handler
            self.carries_an_operation_to_its_handler(site, ctx, carrying_limit) ||
            // 4) otherwise inline if affordable
            self.affordable(site, ctx, threshold)
          )
      }
  }
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
fn Normalizer::rewrite_stmt(
  self : Normalizer,
  s : Stmt,
  ctx : NormCtx,
) -> Stmt raise EffektError {
  match s {
    // see #798 for context (it led to a stack overflow)
    Def(id, _, body) if self.is_unused(id) => self.rewrite_stmt(body, ctx)
    Def(id, block, body) =>
      match self.active_block(block, ctx) {
        Known(New(implementation), None) if !Block::New(implementation)
          .free()
          .contains(id) => {
          // def id = new Interface { op => body }; rest
          //   ==>
          // def <op> = body; ...; def id = new Interface { op => forward }; rest
          let lifted = implementation.operations.map(op => self.lift(op, id))
          let forwarding = New(
            Implementation(
              implementation.interface,
              lifted.map(entry => entry.2),
            ),
          )
          let mut inner = ctx.with_block(id, forwarding)
          for entry in lifted {
            let (method, literal, _) = entry
            inner = inner.with_block(method.id, BlockLit(literal))
          }
          let rest = self.rewrite_stmt(body, inner)
          let definitions : Array[Binding] = []
          let operations : Array[Operation] = []
          for i, entry in lifted {
            let (method, literal, forwarder) = entry
            if rest.free().contains(method.id) {
              definitions.push(BindingDef(method.id, BlockLit(literal)))
              operations.push(forwarder)
            } else {
              operations.push(implementation.operations[i])
            }
          }
          let forwarded = Def(
            id,
            New(Implementation(implementation.interface, operations)),
            rest,
          )
          bindings_to_stmt(definitions, forwarded)
        }
        normalized => {
          let dealiased = match block {
            BlockLit(_) | New(_) => normalized.dealiased()
            // a copy, so that the copy's binders cannot capture anything here
            BlockVar(_) | Unbox(_) => {
              let (copy, renamings) = rename_block(normalized.dealiased())
              self.copy_usage(renamings)
              copy
            }
          }
          Def(
            id,
            dealiased,
            self.rewrite_stmt(body, ctx.with_block(id, dealiased)),
          )
        }
      }
    Let(id, expr, body) =>
      self.normalize_let([(id, self.active_expr(expr, ctx))], body, ctx)
    ImpureApp(id, callee, targs, vargs, bargs, body) =>
      ImpureApp(
        id,
        callee,
        targs,
        vargs.map(arg => self.rewrite_expr(arg, ctx)),
        bargs.map(arg => self.rewrite_block(arg, ctx)),
        self.rewrite_stmt(body, ctx),
      )
    // Redexes
    App(callee, targs, vargs, bargs) =>
      match self.active_block(callee, ctx) {
        Known(BlockLit(lit), bound_by) if self.should_inline(
            CallSite::CallSite(lit, bound_by, vargs, bargs),
            ctx,
          ) => {
          // a block used more than once uses its free variables more than once
          let block_usage = match bound_by {
            Some(bv) => self.usage_of(bv.id)
            None => Once
          }
          if block_usage == Many {
            for v in lit.free().free_ids() {
              self.usage.set(v.uid(), self.usage_of(v).times(Many))
            }
          }
          self.reduce(
            lit,
            targs,
            vargs.map(arg => self.rewrite_expr(arg, ctx)),
            bargs.map(arg => self.rewrite_block(arg, ctx)),
            ctx,
          )
        }
        normalized =>
          App(
            normalized.shared(),
            targs,
            vargs.map(arg => self.rewrite_expr(arg, ctx)),
            bargs.map(arg => self.rewrite_block(arg, ctx)),
          )
      }
    Invoke(callee, method, method_tpe, targs, vargs, bargs) =>
      match self.active_block(callee, ctx) {
        Known(New(implementation), bound_by) =>
          match self.select_operation(implementation, method) {
            Some(jump) =>
              match jump.body {
                // an operation that only forwards to a lifted method
                App(_, _, _, _) =>
                  self.reduce(
                    jump,
                    targs,
                    vargs.map(arg => self.rewrite_expr(arg, ctx)),
                    bargs.map(arg => self.rewrite_block(arg, ctx)),
                    ctx,
                  )
                _ =>
                  if self.should_inline(
                      CallSite::CallSite(jump, bound_by, vargs, bargs),
                      ctx,
                    ) {
                    self.reduce(
                      jump,
                      targs,
                      vargs.map(arg => self.rewrite_expr(arg, ctx)),
                      bargs.map(arg => self.rewrite_block(arg, ctx)),
                      ctx,
                    )
                  } else {
                    Invoke(
                      Block::New(implementation),
                      method,
                      method_tpe,
                      targs,
                      vargs.map(arg => self.rewrite_expr(arg, ctx)),
                      bargs.map(arg => self.rewrite_block(arg, ctx)),
                    )
                  }
              }
            // upstream fails here; falling back keeps an invoke we cannot
            // resolve an invoke
            None =>
              Invoke(
                Block::New(implementation),
                method,
                method_tpe,
                targs,
                vargs.map(arg => self.rewrite_expr(arg, ctx)),
                bargs.map(arg => self.rewrite_block(arg, ctx)),
              )
          }
        normalized =>
          Invoke(
            normalized.shared(),
            method,
            method_tpe,
            targs,
            vargs.map(arg => self.rewrite_expr(arg, ctx)),
            bargs.map(arg => self.rewrite_block(arg, ctx)),
          )
      }
    // [[ sc match {} else { stmt } ]] = [[ stmt ]]
    Match(_, _, [], Some(default)) => self.rewrite_stmt(default, ctx)
    Match(scrutinee, tpe, clauses, default) =>
      match self.active_expr(scrutinee, ctx) {
        // [[ make tag(..) match { case tag => body; ... } ]] = [[ body ]] applied
        Make(_, tag, targs, vargs) => {
          let mut selected : BlockLit? = None
          for clause in clauses {
            if clause.tag.uid() == tag.uid() {
              selected = Some(clause.body)
            }
          }
          match selected {
            Some(clause) => {
              let result = self.reduce(
                clause,
                targs,
                map_raise(vargs, arg => self.rewrite_expr(arg, ctx)),
                [],
                ctx,
              )
              self.rewrite_stmt(result, ctx)
            }
            None =>
              match default {
                Some(d) => self.rewrite_stmt(d, ctx)
                None =>
                  self.normalize_match(scrutinee, tpe, clauses, default, ctx)
              }
          }
        }
        _ => self.normalize_match(scrutinee, tpe, clauses, default, ctx)
      }
    // [[ if (true) stmt1 else stmt2 ]] = [[ stmt1 ]]
    If(cond, thn, els) =>
      match self.active_expr(cond, ctx) {
        Literal(LBool(true), _) => self.rewrite_stmt(thn, ctx)
        Literal(LBool(false), _) => self.rewrite_stmt(els, ctx)
        _ => {
          let condition = self.rewrite_expr(cond, ctx)
          If(
            condition,
            self.rewrite_stmt(thn, assuming(condition, true, ctx)),
            self.rewrite_stmt(els, assuming(condition, false, ctx)),
          )
        }
      }
    Val(ids, binding, body) =>
      self.normalize_val(ids, self.rewrite_stmt(binding, ctx), body, ctx)
    // Congruences
    Reset(body) =>
      Reset(
        self.rewrite_block_lit(
          body,
          if body.bparams.length() > 0 {
            ctx.enter_prompt(body.bparams[0].id)
          } else {
            ctx
          },
        ),
      )
    Shift(prompt, k, body) => Shift(prompt, k, self.rewrite_stmt(body, ctx))
    Return(exprs) => Return(exprs.map(expr => self.rewrite_expr(expr, ctx)))
    Alloc(id, init, region, body) =>
      Alloc(
        id,
        self.rewrite_expr(init, ctx),
        region,
        self.rewrite_stmt(body, ctx),
      )
    Resume(k, body) => Resume(k, self.rewrite_stmt(body, ctx))
    Region(body) => Region(self.rewrite_block_lit(body, ctx))
    Var(ref, init, capture, body) =>
      Var(
        ref,
        self.rewrite_expr(init, ctx),
        capture,
        self.rewrite_stmt(body, ctx),
      )
    Get(id, tpe, ref, capt, body) =>
      Get(id, tpe, ref, capt, self.rewrite_stmt(body, ctx))
    Put(ref, capt, value, body) =>
      Put(
        ref,
        capt,
        self.rewrite_expr(value, ctx),
        self.rewrite_stmt(body, ctx),
      )
    Hole(_, _) => s
  }
}

///|
/// `let x = e; body`, with `e` already in normal form: an alias that is known
/// here is replaced by the expression it is known to equal.
fn Normalizer::normalize_let(
  self : Normalizer,
  bindings : Array[(Sym, Expr)],
  body : Stmt,
  ctx : NormCtx,
) -> Stmt raise EffektError {
  match bindings {
    [] => self.rewrite_stmt(body, ctx)
    [(id, expr), .. rest] => {
      let bound = expr
      Let(
        id,
        bound,
        self.normalize_let(rest.to_owned(), body, ctx.with_expr(id, bound)),
      )
    }
  }
}

// ---------------------------------------------------------------------------
// `val` (the join points and the commutations)
// ---------------------------------------------------------------------------

///|
/// `val k(ids) = body; f(k, ctx)` with a fresh `k`, or `f(k, ctx)` directly if
/// `body` only applies a variable to the ids (do not eta-expand variables).
fn Normalizer::joinpoint(
  self : Normalizer,
  ids : Array[Sym],
  tpe : ValueType,
  body : Stmt,
  f : (BlockVar, NormCtx) -> Stmt raise EffektError,
  ctx : NormCtx,
) -> Stmt raise EffektError {
  match body {
    App(BlockVar(k), [], vargs, []) =>
      if vargs.length() == ids.length() && variables_are(vargs, ids) {
        f(k, ctx)
      } else {
        self.make_joinpoint(ids, tpe, body, f, ctx)
      }
    _ => self.make_joinpoint(ids, tpe, body, f, ctx)
  }
}

///|
fn Normalizer::make_joinpoint(
  self : Normalizer,
  ids : Array[Sym],
  tpe : ValueType,
  body : Stmt,
  f : (BlockVar, NormCtx) -> Stmt raise EffektError,
  ctx : NormCtx,
) -> Stmt raise EffektError {
  let k = Sym::id(Name::local("k"))
  // the join point is created here, so the reachability analysis does not know
  // it: without recording it, the `def` below would look unused and be dropped
  self.usage.set(k.uid(), Many)
  let definition = BlockLit::new(
    [],
    [],
    ids.map(id => ValueParam::ValueParam(id, tpe)),
    [],
    body,
  )
  let kv = BlockVar::new(k, unknown_block_type(), Captures::empty())
  Def(k, BlockLit(definition), f(kv, ctx.with_block(k, BlockLit(definition))))
}

///|
/// Whether the given expressions are exactly the given variables, in order.
fn variables_are(exprs : Array[Expr], ids : Array[Sym]) -> Bool {
  if exprs.length() != ids.length() {
    return false
  }
  for i, expr in exprs {
    match expr {
      ValueVar(id, _) => if id.uid() != ids[i].uid() { return false }
      _ => return false
    }
  }
  true
}

///|
/// Fresh copies of the given ids (upstream: `Id(id.name)`).
fn fresh_ids(ids : Array[Sym]) -> Array[Sym] {
  ids.map(id => Sym::id(id.name()))
}

///|
/// Applies the given block variable to the given values.
fn jump(k : BlockVar, ids : Array[Sym], tpe : ValueType) -> Stmt {
  App(BlockVar(k), [], ids.map(id => ValueVar(id, tpe)), [])
}

///|
/// `val ids = binding; body`, where `binding` is already in normal form.
///
/// Commutes the bindings on the spine of `binding` and normalizes `body` exactly
/// once.
fn Normalizer::normalize_val(
  self : Normalizer,
  ids : Array[Sym],
  binding : Stmt,
  body : Stmt,
  ctx : NormCtx,
) -> Stmt raise EffektError {
  match binding {
    // [[ val x: A = sc match [A] { case k => body2 }; body: B ]]
    //   == sc match [B] { case k => [[ val x: A = body2; body: B ]] }
    Match(sc, tpe, [clause], None) => {
      let inner = self.normalize_val(ids, clause.body.body, body, ctx)
      Match(
        sc,
        tpe,
        [
          Clause(
            clause.tag,
            BlockLit::new(
              clause.body.tparams,
              clause.body.cparams,
              clause.body.vparams,
              clause.body.bparams,
              inner,
            ),
          ),
        ],
        None,
      )
    }
    // Join points, so that they can be inlined or garbage collected later:
    // [[ val x = if (cond) { thn } else { els }; body ]] =
    //   def k(x) = [[ body ]]
    //   if (cond) { [[ val x1 = thn; k(x1) ]] } else { [[ val x2 = els; k(x2) ]] }
    If(cond, thn, els) => {
      let tpe = stmt_type_hint(thn)
      self.joinpoint(
        ids,
        tpe,
        self.rewrite_stmt(body, ctx),
        (k, inner) => {
          let x1 = fresh_ids(ids)
          let x2 = fresh_ids(ids)
          If(
            cond,
            self.normalize_val(
              x1,
              thn,
              jump(k, x1, tpe),
              assuming(cond, true, inner),
            ),
            self.normalize_val(
              x2,
              els,
              jump(k, x2, tpe),
              assuming(cond, false, inner),
            ),
          )
        },
        ctx,
      )
    }
    // avoid dead join points on coercions
    Match(sc, tpe, [], None) => Match(sc, tpe, [], None)
    // [[ val id: A = sc match[A] { ... }; body : B ]] =
    //   def k(id: A): B = [[ body ]]
    //   sc match [B] { ... k() ... }
    Match(sc, tpe, clauses, default) => {
      let res = self.rewrite_stmt(body, ctx)
      let result_type = stmt_type_hint(res)
      self.joinpoint(
        ids,
        tpe,
        res,
        (k, inner) => {
          Match(
            sc,
            result_type,
            clauses.map(clause => {
              let x = fresh_ids(ids)
              let normalized = self.normalize_val(
                x,
                clause.body.body,
                jump(k, x, tpe),
                inner,
              )
              Clause(
                clause.tag,
                BlockLit::new(
                  clause.body.tparams,
                  clause.body.cparams,
                  clause.body.vparams,
                  clause.body.bparams,
                  normalized,
                ),
              )
            }),
            match default {
              Some(d) => {
                let x = fresh_ids(ids)
                Some(self.normalize_val(x, d, jump(k, x, tpe), inner))
              }
              None => None
            },
          )
        },
        ctx,
      )
    }
    // [[ val x = return e; s ]] = let x = [[ e ]]; [[ s ]]
    Return(exprs) => {
      let pairs : Array[(Sym, Expr)] = []
      for i, expr in exprs {
        if i < ids.length() {
          pairs.push((ids[i], expr))
        }
      }
      self.normalize_let(pairs, body, ctx)
    }
    // Commute `val` and bindings
    Def(id2, block2, body2) =>
      Def(
        id2,
        block2,
        self.normalize_val(ids, body2, body, ctx.with_block(id2, block2)),
      )
    Let(id2, binding2, body2) =>
      Let(
        id2,
        binding2,
        self.normalize_val(ids, body2, body, ctx.with_expr(id2, binding2)),
      )
    ImpureApp(id2, callee2, targs2, vargs2, bargs2, body2) =>
      ImpureApp(
        id2,
        callee2,
        targs2,
        vargs2,
        bargs2,
        self.normalize_val(ids, body2, body, ctx),
      )
    // Flatten vals: [[ val x = { val y = s1; s2 }; s3 ]] = val y = s1; val x = s2; s3
    Val(ids2, binding2, body2) =>
      Val(ids2, binding2, self.normalize_val(ids, body2, body, ctx))
    Alloc(id2, init2, region2, body2) =>
      Alloc(id2, init2, region2, self.normalize_val(ids, body2, body, ctx))
    Get(id2, tpe2, ref2, capt2, body2) =>
      Get(id2, tpe2, ref2, capt2, self.normalize_val(ids, body2, body, ctx))
    Put(ref2, capt2, value2, body2) =>
      Put(ref2, capt2, value2, self.normalize_val(ids, body2, body, ctx))
    other =>
      match self.rewrite_stmt(body, ctx) {
        // [[ val x = stmt; return x ]] = [[ stmt ]]
        Return(xs) if variables_are(xs, ids) => other
        // [[ val x: Unit = stmt; return () ]] = [[ stmt ]]
        Return(xs) if xs.all(is_unit_literal) && returns_unit(other) => other
        // [[ val x = stmt; body ]] = val x = [[ stmt ]]; [[ body ]]
        normalized_body => Val(ids, other, normalized_body)
      }
  }
}

// ---------------------------------------------------------------------------
// Blocks, expressions and implementations
// ---------------------------------------------------------------------------

///|
fn Normalizer::rewrite_block(
  self : Normalizer,
  b : Block,
  ctx : NormCtx,
) -> Block raise EffektError {
  match b {
    BlockVar(_) => b
    BlockLit(lit) => BlockLit(self.rewrite_block_lit(lit, ctx))
    // [[ unbox (box b) ]] = [[ b ]]
    Unbox(expr) =>
      match self.rewrite_expr(expr, ctx) {
        Box(inner, _) => inner
        p => Unbox(p)
      }
    New(implementation) => New(self.rewrite_implementation(implementation, ctx))
  }
}

///|
fn Normalizer::rewrite_block_lit(
  self : Normalizer,
  lit : BlockLit,
  ctx : NormCtx,
) -> BlockLit raise EffektError {
  BlockLit::new(
    lit.tparams,
    lit.cparams,
    lit.vparams,
    lit.bparams,
    self.rewrite_stmt(lit.body, ctx),
  )
}

///|
fn Normalizer::rewrite_implementation(
  self : Normalizer,
  implementation : Implementation,
  ctx : NormCtx,
) -> Implementation raise EffektError {
  Implementation(
    implementation.interface,
    implementation.operations.map(op => {
      Operation(
        op.name,
        op.tparams,
        op.cparams,
        op.vparams,
        op.bparams,
        self.rewrite_stmt(op.body, ctx),
      )
    }),
  )
}

///|
fn Normalizer::rewrite_expr(
  self : Normalizer,
  e : Expr,
  ctx : NormCtx,
) -> Expr raise EffektError {
  match e {
    // [[ box (unbox e) ]] = [[ e ]]
    Box(b, capt) =>
      match self.active_block(b, ctx) {
        Known(Unbox(p), _) => p
        normalized => Box(normalized.shared(), capt)
      }
    // congruences (upstream also shares these through Context.facts, see the
    // note at the top of the file)
    PureApp(f, targs, vargs) =>
      PureApp(f, targs, map_raise(vargs, arg => self.rewrite_expr(arg, ctx)))
    Make(data, tag, targs, vargs) =>
      Make(
        data,
        tag,
        targs,
        map_raise(vargs, arg => self.rewrite_expr(arg, ctx)),
      )
    // [[ x ]] = y  if `x` was bound to `y`
    ValueVar(id, _) =>
      match ctx.exprs.get(id.uid()) {
        Some(ValueVar(_, _) as other) => self.rewrite_expr(other, ctx)
        _ => e
      }
    Literal(_, _) => e
  }
}

// ---------------------------------------------------------------------------
// Beta reduction
// ---------------------------------------------------------------------------

///|
/// Inlines the block literal at a call site: binds the block arguments, freshens
/// the callee so that the copy cannot capture anything, substitutes and
/// normalizes the result.
fn Normalizer::reduce(
  self : Normalizer,
  b : BlockLit,
  targs : Array[ValueType],
  vargs : Array[Expr],
  bargs : Array[Block],
  ctx : NormCtx,
) -> Stmt raise EffektError {
  let bindings : Array[Binding] = []
  let bvars : Array[Block] = []
  for i, bparam in b.bparams {
    if i < bargs.length() {
      match bargs[i] {
        BlockVar(bv) => {
          // u1 + (u2 - 1)
          self.usage.set(
            bv.id.uid(),
            self.usage_of(bparam.id) + self.usage_of(bv.id).decrement(),
          )
          bvars.push(BlockVar(bv))
        }
        block => {
          let id = Sym::tmp_block("blockBinding")
          bindings.push(BindingDef(id, block))
          bvars.push(
            BlockVar(
              BlockVar::new(id, unknown_block_type(), block_captures(block)),
            ),
          )
          self.copy_usage_one(id, bparam.id)
        }
      }
    }
  }
  // The pattern matching compiler of this port does not always bind the
  // existential type parameters of a match clause, so the type arguments of the
  // call site can be more than the callee declares (upstream asserts that they
  // line up). Types are erased by the backends, so the arguments that do line up
  // are enough -- and a missing one is filled with the unknown type.
  let targs = adjust_type_args(targs, b.tparams.length())
  let (renamed, renamings) = rename_block_lit(b)
  self.copy_usage(renamings)
  let body = substitute_block_lit_call(renamed, targs, vargs, bvars)
  self.rewrite_stmt(bindings_to_stmt(bindings, body), ctx)
}

///|
/// Lifts an operation of an object into a method: a `BlockVar` for the method
/// and the block literal that is its body.
fn Normalizer::lift(
  self : Normalizer,
  operation : Operation,
  interface_id : Sym,
) -> (BlockVar, BlockLit, Operation) {
  let literal = BlockLit::new(
    operation.tparams,
    operation.cparams,
    operation.vparams,
    operation.bparams,
    operation.body,
  )
  let method = BlockVar::new(
    Sym::id(operation.name.name()),
    unknown_block_type(),
    Captures::empty(),
  )
  self.copy_usage_one(method.id, interface_id)
  let forwarder = self.forward(operation, method)
  (method, literal, forwarder)
}

///|
/// The operation that forwards to the lifted method.
fn Normalizer::forward(
  self : Normalizer,
  operation : Operation,
  method : BlockVar,
) -> Operation {
  let body = App(
    BlockVar(method),
    operation.tparams.map(t => ValueTypeRef(t)),
    operation.vparams.map(p => ValueVar(p.id, p.tpe)),
    operation.bparams.map(p => BlockVar(BlockVar::new(p.id, p.tpe, p.capt))),
  )
  let forwarding = Operation(
    operation.name,
    operation.tparams,
    operation.cparams,
    operation.vparams,
    operation.bparams,
    body,
  )
  let renamer = Renamer::Renamer()
  let renamed = renamer.rewrite_operation(forwarding)
  self.copy_usage(renamer.renamed)
  renamed
}

///|
/// The operation of `implementation` that is named `method`.
fn Normalizer::select_operation(
  self : Normalizer,
  implementation : Implementation,
  method : Sym,
) -> BlockLit? {
  let _ = self
  for op in implementation.operations {
    if op.name.uid() == method.uid() {
      return Some(
        BlockLit::new(op.tparams, op.cparams, op.vparams, op.bparams, op.body),
      )
    }
  }
  None
}

// ---------------------------------------------------------------------------
// Type hints
// ---------------------------------------------------------------------------

///|
/// The type of the value a statement returns, as far as it is syntactically
/// obvious. This port has no core type inference, so most statements yield the
/// unknown type; the hint is only used for the parameters of join points.
fn stmt_type_hint(s : Stmt) -> ValueType {
  match s {
    Return([expr]) => expr_type_hint(expr)
    _ => unknown_value_type()
  }
}

///|
fn is_unit_literal(e : Expr) -> Bool {
  match e {
    Literal(LUnit, _) => true
    _ => false
  }
}

///|
/// Whether the statement returns `()` on every path, which stands in for
/// "the statement's type is Unit".
fn returns_unit(s : Stmt) -> Bool {
  match s {
    Return(exprs) => exprs.all(is_unit_literal)
    If(_, thn, els) => returns_unit(thn) && returns_unit(els)
    Match(_, _, clauses, default) =>
      clauses.all(c => returns_unit(c.body.body)) &&
      (match default {
        Some(d) => returns_unit(d)
        None => true
      })
    Val(_, _, body) => returns_unit(body)
    Let(_, _, body) => returns_unit(body)
    Def(_, _, body) => returns_unit(body)
    ImpureApp(_, _, _, _, _, body) => returns_unit(body)
    Alloc(_, _, _, body) => returns_unit(body)
    Var(_, _, _, body) => returns_unit(body)
    Get(_, _, _, _, body) => returns_unit(body)
    Put(_, _, _, body) => returns_unit(body)
    _ => false
  }
}

///|
/// The congruence case of match: normalize the scrutinee, every clause and the
/// default. Upstream additionally records what is known about the scrutinee
/// inside each clause (selecting), which needs its data type.
fn Normalizer::normalize_match(
  self : Normalizer,
  scrutinee : Expr,
  tpe : ValueType,
  clauses : Array[Clause],
  default : Stmt?,
  ctx : NormCtx,
) -> Stmt raise EffektError {
  Match(
    self.rewrite_expr(scrutinee, ctx),
    tpe,
    map_raise(clauses, clause => {
      Clause(clause.tag, self.rewrite_block_lit(clause.body, ctx))
    }),
    match default {
      Some(d) => Some(self.rewrite_stmt(d, ctx))
      None => None
    },
  )
}

///|
/// The type arguments of a call site, truncated or padded to `count`: see the
/// note in `reduce`.
fn adjust_type_args(
  targs : Array[ValueType],
  count : Int32,
) -> Array[ValueType] {
  if targs.length() == count {
    return targs
  }
  let out : Array[ValueType] = []
  for i = 0; i < count; i = i + 1 {
    if i < targs.length() {
      out.push(targs[i])
    } else {
      out.push(unknown_value_type())
    }
  }
  out
}
