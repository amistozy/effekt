// Unbox inference.
//
// Mirrors `effekt/typer/UnboxInference.scala`. This phase runs *before* type
// checking (upstream: `Parser andThen Namer andThen UnboxInference andThen
// Typer`) and inserts explicit `Unbox` nodes where a block is used as a value.
//
// There are only a few constructors for blocks: identifiers, explicit unboxing,
// object literals and selection.

///|
pub struct Unboxer {
  ctx : Context
}

///|
/// Rewrites the module, inserting `Unbox` nodes where blocks are used as
/// values and `Unbox` nodes where values are used as blocks.
pub fn unbox_inference(
  module : ModuleDecl,
  context : Context,
) -> ModuleDecl raise EffektError {
  let u = { ctx: context, }
  u.rewrite_module(module)
}

///|
/// A 1:1 rewrite of an existing node *keeps its uid*: annotations are keyed by
/// uid in this port, so this is what upstream achieves by copying the
/// annotations from the source to the target tree (`inheritPosition` +
/// `copyAnnotations`). It also makes the pass idempotent and keeps every
/// annotation the type checker writes reachable through the node the caller
/// already holds.
fn Unboxer::visit_term(self : Unboxer, from : Term, kind : TermKind) -> Term {
  ignore(self)
  { uid: from.uid, span: from.span, kind, }
}

///|
fn Unboxer::visit_stmt(self : Unboxer, from : Stmt, kind : StmtKind) -> Stmt {
  ignore(self)
  { uid: from.uid, span: from.span, kind, }
}

///|
fn Unboxer::visit_def(self : Unboxer, from : Def, kind : DefKind) -> Def {
  ignore(self)
  { uid: from.uid, span: from.span, info: from.info, kind, }
}

///|
/// A *synthesized* wrapper (e.g. the `Unbox` inserted around a value that is
/// used as a block) is a new node and gets a fresh uid.
fn Unboxer::synthesized(self : Unboxer, span : Span, kind : TermKind) -> Term {
  ignore(self)
  mk_term(span, kind)
}

///|
fn Unboxer::error(self : Unboxer, span : Span, msg : String) -> Unit {
  self.ctx.error(span, msg)
}

///|
fn Unboxer::info(self : Unboxer, msg : String) -> Unit {
  self.ctx.info(msg)
}

///|
fn Unboxer::symbol_of(self : Unboxer, uid : Int32) -> Sym? {
  self.ctx.symbol_of(uid)
}

// ---------------------------------------------------------------------------
// The rewriting
// ---------------------------------------------------------------------------

///|
fn Unboxer::rewrite_module(
  self : Unboxer,
  m : ModuleDecl,
) -> ModuleDecl raise EffektError {
  let defs : Array[Def] = []
  for d in m.defs {
    defs.push(self.rewrite_def(d))
  }
  { ..m, defs, }
}

///|
fn Unboxer::rewrite_as_block(
  self : Unboxer,
  e : Term,
) -> Term raise EffektError {
  match e.kind {
    @source.TermKind::Var(id) =>
      match self.symbol_of(id.uid) {
        Some(s) =>
          if s.is_ref_binder() || s.is_value_symbol() {
            self.synthesized(e.span, @source.TermKind::Unbox(e))
          } else {
            e
          }
        None => e
      }
    @source.TermKind::Unbox(inner) =>
      self.visit_term(e, @source.TermKind::Unbox(self.rewrite_as_expr(inner)))
    @source.TermKind::New(implementation) =>
      self.visit_term(
        e,
        @source.TermKind::New(self.rewrite_impl(implementation)),
      )
    @source.TermKind::BlockLiteral(tparams, vparams, bparams, body) =>
      self.visit_term(
        e,
        @source.TermKind::BlockLiteral(
          tparams,
          vparams,
          bparams,
          self.rewrite_stmt(body),
        ),
      )
    _ =>
      self.synthesized(e.span, @source.TermKind::Unbox(self.rewrite_as_expr(e)))
  }
}

///|
fn Unboxer::rewrite_as_expr(self : Unboxer, e : Term) -> Term raise EffektError {
  match e.kind {
    @source.TermKind::Unbox(inner) => self.rewrite_as_expr(inner)
    @source.TermKind::Var(id) =>
      match self.symbol_of(id.uid) {
        Some(s) =>
          if s.is_ref_binder() || s.is_value_symbol() {
            e
          } else {
            // heuristic for a specific misunderstanding
            match s {
              @symbols.Sym::UserFunction(f) =>
                if f.vparams.length() == 0 && f.bparams.length() == 0 {
                  self.info(
                    "Did you mean to call the function using `\{id.name}()`?",
                  )
                }
              @symbols.Sym::ResumeParam(_) =>
                self.info("Did you mean to resume using `resume(...)`?")
              _ => ()
            }
            self.error(
              e.span,
              "Expected a value, but \{id.name} is a computation. Use `box \{id.name}` to pass it as a value instead",
            )
            e
          }
        None => e
      }
    @source.TermKind::New(_) => {
      self.error(
        e.span,
        "Expected a value, but `new` creates a computation (an object instance). Use `box new ... { ... }` to pass it as a value instead",
      )
      self.rewrite_as_block(e)
    }
    @source.TermKind::BlockLiteral(_, vparams, _, _) => {
      let names : Array[String] = vparams.map(p => p.id.name)
      self.error(
        e.span,
        "Expected a value, but block (function) literals are computations. Use `box { (\{names.join(", ")}) => ... }` to pass it as a value instead",
      )
      self.rewrite_as_block(e)
    }
    @source.TermKind::Literal(_, _) => e
    @source.TermKind::Assign(id, expr) =>
      self.visit_term(
        e,
        @source.TermKind::Assign(id, self.rewrite_as_expr(expr)),
      )
    @source.TermKind::If(guards, thn, els) =>
      self.visit_term(
        e,
        @source.TermKind::If(
          guards.map(g => self.rewrite_guard(g)),
          self.rewrite_stmt(thn),
          self.rewrite_stmt(els),
        ),
      )
    @source.TermKind::While(guards, body, default) =>
      self.visit_term(
        e,
        @source.TermKind::While(
          guards.map(g => self.rewrite_guard(g)),
          self.rewrite_stmt(body),
          match default {
            Some(d) => Some(self.rewrite_stmt(d))
            None => None
          },
        ),
      )
    @source.TermKind::Match(scs, clauses, default) =>
      self.visit_term(
        e,
        @source.TermKind::Match(
          scs.map(sc => self.rewrite_as_expr(sc)),
          clauses.map(c => self.rewrite_clause(c)),
          match default {
            Some(d) => Some(self.rewrite_stmt(d))
            None => None
          },
        ),
      )
    @source.TermKind::Select(recv, name) =>
      match self.symbol_of(name.uid) {
        Some(@symbols.Sym::Field(_)) =>
          self.visit_term(
            e,
            @source.TermKind::Select(self.rewrite_as_expr(recv), name),
          )
        _ => {
          self.error(e.span, "selection on blocks not supported yet.")
          e
        }
      }
    @source.TermKind::Do(id, targs, vargs, bargs) =>
      self.visit_term(
        e,
        @source.TermKind::Do(
          id,
          targs,
          vargs.map(a => self.rewrite_arg(a)),
          bargs.map(b => self.rewrite_as_block(b)),
        ),
      )
    @source.TermKind::Call(target, targs, vargs, bargs) =>
      self.visit_term(
        e,
        @source.TermKind::Call(
          self.rewrite_target(target),
          targs,
          vargs.map(a => self.rewrite_arg(a)),
          bargs.map(b => self.rewrite_as_block(b)),
        ),
      )
    @source.TermKind::MethodCall(receiver, id, targs, vargs, bargs) => {
      let vargs_transformed = vargs.map(a => self.rewrite_arg(a))
      let bargs_transformed = bargs.map(b => self.rewrite_as_block(b))
      let has_methods = match self.symbol_of(id.uid) {
        Some(@symbols.Sym::CallTarget(ct)) => {
          let mut found = false
          for scope in ct.symbols {
            for s in scope {
              if s.is_operation() {
                found = true
              }
            }
          }
          found
        }
        Some(s) => s.is_operation()
        None => false
      }
      if has_methods {
        // true method call on an interface: the receiver is the object
        self.visit_term(
          e,
          @source.TermKind::MethodCall(
            self.rewrite_as_block(receiver),
            id,
            targs,
            vargs_transformed,
            bargs_transformed,
          ),
        )
      } else if !self.is_block_like(receiver) {
        // value-UFCS: the receiver becomes the first value argument
        let first = ValueArg::unnamed(self.rewrite_as_expr(receiver))
        self.visit_term(
          e,
          @source.TermKind::Call(
            @source.CallTarget::IdTarget(id),
            targs,
            [first] + vargs_transformed,
            bargs_transformed,
          ),
        )
      } else {
        // block-UFCS: the receiver becomes the first block argument
        let first = self.rewrite_as_block(receiver)
        self.visit_term(
          e,
          @source.TermKind::Call(
            @source.CallTarget::IdTarget(id),
            targs,
            vargs_transformed,
            [first] + bargs_transformed,
          ),
        )
      }
    }
    @source.TermKind::TryHandle(prog, handlers) =>
      self.visit_term(
        e,
        @source.TermKind::TryHandle(
          self.rewrite_stmt(prog),
          handlers.map(h => self.rewrite_handler(h)),
        ),
      )
    @source.TermKind::Region(id, body) =>
      self.visit_term(e, @source.TermKind::Region(id, self.rewrite_stmt(body)))
    @source.TermKind::Hole(id, template) =>
      self.visit_term(
        e,
        @source.TermKind::Hole(id, {
          strings: template.strings,
          args: template.args.map(a => self.rewrite_stmt(a)),
        }),
      )
    @source.TermKind::Box(c, b) =>
      self.visit_term(e, @source.TermKind::Box(c, self.rewrite_as_block(b)))
  }
}

///|
fn Unboxer::rewrite_arg(
  self : Unboxer,
  a : ValueArg,
) -> ValueArg raise EffektError {
  { ..a, value: self.rewrite_as_expr(a.value), }
}

///|
fn Unboxer::rewrite_target(
  self : Unboxer,
  t : CallTarget,
) -> CallTarget raise EffektError {
  match t {
    @source.CallTarget::ExprTarget(receiver) =>
      @source.CallTarget::ExprTarget(self.rewrite_as_block(receiver))
    @source.CallTarget::IdTarget(id) =>
      match self.symbol_of(id.uid) {
        Some(s) =>
          if s.is_ref_binder() || s.is_value_symbol() {
            let v = mk_term(id.span, @source.TermKind::Var(id))
            @source.CallTarget::ExprTarget(
              self.visit_term(v, @source.TermKind::Unbox(v)),
            )
          } else {
            t
          }
        None => t
      }
  }
}

///|
fn Unboxer::rewrite_def(self : Unboxer, d : Def) -> Def raise EffektError {
  match d.kind {
    @source.DefKind::FunDef(id, tparams, vparams, bparams, captures, ret, body) =>
      self.visit_def(
        d,
        @source.DefKind::FunDef(
          id,
          tparams,
          vparams,
          bparams,
          captures,
          ret,
          self.rewrite_stmt(body),
        ),
      )
    @source.DefKind::ValDef(id, annot, binding) =>
      self.visit_def(
        d,
        @source.DefKind::ValDef(id, annot, self.rewrite_stmt(binding)),
      )
    @source.DefKind::RegDef(id, annot, region, binding) =>
      self.visit_def(
        d,
        @source.DefKind::RegDef(id, annot, region, self.rewrite_stmt(binding)),
      )
    @source.DefKind::VarDef(id, annot, binding) =>
      self.visit_def(
        d,
        @source.DefKind::VarDef(id, annot, self.rewrite_stmt(binding)),
      )
    @source.DefKind::DefDef(id, captures, annot, binding) =>
      self.visit_def(
        d,
        @source.DefKind::DefDef(
          id,
          captures,
          annot,
          self.rewrite_as_block(binding),
        ),
      )
    @source.DefKind::NamespaceDef(id, defs) =>
      self.visit_def(
        d,
        @source.DefKind::NamespaceDef(
          id,
          defs.map(inner => self.rewrite_def(inner)),
        ),
      )
    _ => d
  }
}

///|
fn Unboxer::rewrite_stmt(self : Unboxer, s : Stmt) -> Stmt raise EffektError {
  match s.kind {
    @source.StmtKind::DefStmt(d, rest) =>
      self.visit_stmt(
        s,
        @source.StmtKind::DefStmt(self.rewrite_def(d), self.rewrite_stmt(rest)),
      )
    @source.StmtKind::ExprStmt(e, rest) =>
      self.visit_stmt(
        s,
        @source.StmtKind::ExprStmt(
          self.rewrite_as_expr(e),
          self.rewrite_stmt(rest),
        ),
      )
    @source.StmtKind::Return(e) =>
      self.visit_stmt(s, @source.StmtKind::Return(self.rewrite_as_expr(e)))
    @source.StmtKind::BlockStmt(inner) =>
      self.visit_stmt(s, @source.StmtKind::BlockStmt(self.rewrite_stmt(inner)))
  }
}

///|
fn Unboxer::rewrite_handler(
  self : Unboxer,
  h : Handler,
) -> Handler raise EffektError {
  let implementation = self.rewrite_impl(h.implementation)
  { ..h, implementation, }
}

///|
fn Unboxer::rewrite_impl(
  self : Unboxer,
  i : Implementation,
) -> Implementation raise EffektError {
  { ..i, clauses: i.clauses.map(c => self.rewrite_op_clause(c)), }
}

///|
fn Unboxer::rewrite_op_clause(
  self : Unboxer,
  c : OpClause,
) -> OpClause raise EffektError {
  { ..c, body: self.rewrite_stmt(c.body), }
}

///|
fn Unboxer::rewrite_clause(
  self : Unboxer,
  c : MatchClause,
) -> MatchClause raise EffektError {
  {
    ..c,
    guards: c.guards.map(g => self.rewrite_guard(g)),
    body: self.rewrite_stmt(c.body),
  }
}

///|
fn Unboxer::rewrite_guard(
  self : Unboxer,
  g : MatchGuard,
) -> MatchGuard raise EffektError {
  match g.kind {
    @source.GuardKind::BooleanGuard(cond) =>
      {
        ..g,
        kind: @source.GuardKind::BooleanGuard(self.rewrite_as_expr(cond)),
      }
    @source.GuardKind::PatternGuard(scrutinee, pattern) =>
      {
        ..g,
        kind: @source.GuardKind::PatternGuard(
          self.rewrite_as_expr(scrutinee),
          pattern,
        ),
      }
  }
}

///|
/// Determines whether a term is inherently a block (computation) based on its
/// syntactic form and its definition.
///
/// Mutable variables (`VarBinder`, `RegBinder`) are treated as values, block
/// literals are treated as values for the purposes of UFCS.
fn Unboxer::is_block_like(self : Unboxer, e : Term) -> Bool {
  match e.kind {
    @source.TermKind::Var(id) =>
      match self.symbol_of(id.uid) {
        Some(s) => if s.is_ref_binder() { false } else { s.is_block_symbol() }
        None => false
      }
    @source.TermKind::Unbox(_) => true
    @source.TermKind::New(_) => true
    @source.TermKind::BlockLiteral(_, _, _, _) => false
    _ => false
  }
}
