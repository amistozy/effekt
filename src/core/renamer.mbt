// Freshens the bound names of a core term.
//
// Mirrors `effekt/core/Renamer.scala`. The optimizer uses it to make a *copy* of
// a block before inlining it (so that the copy's binders cannot capture
// anything of the call site) and to freshen the callee it reduces.
//
// `renamed` maps every fresh symbol to the one it was generated for: the
// normalizer copies the usage information along that map, so that the copy is
// considered as often used as its original. Free variables are left untouched.

///|
priv struct Renamer {
  /// The renamings currently in scope: bound symbol -> its fresh variant.
  scope : Map[Int32, Sym]
  /// Every renaming ever performed: fresh symbol -> the symbol it replaces.
  renamed : Map[Int32, Sym]
}

///|
fn Renamer::Renamer() -> Renamer {
  { scope: Map([]), renamed: Map([]), }
}

///|
/// The fresh variant of `id`, or `id` itself if it is free.
fn Renamer::rewrite_id(self : Renamer, id : Sym) -> Sym {
  match self.scope.get(id.uid()) {
    Some(fresh) => fresh
    None => id
  }
}

///|
/// Runs `f` with every symbol of `ids` bound to a fresh copy of itself. The
/// previous scope is restored afterwards, also when `f` fails.
fn[T] Renamer::with_bindings(
  self : Renamer,
  ids : Array[Sym],
  f : () -> T,
) -> T {
  let shadowed : Array[(Int32, Sym?)] = []
  for id in ids {
    shadowed.push((id.uid(), self.scope.get(id.uid())))
    let fresh = Sym::id(id.name())
    self.scope.set(id.uid(), fresh)
    self.renamed.set(fresh.uid(), id)
  }
  defer (for entry in shadowed {
    match entry {
      (uid, Some(previous)) => self.scope.set(uid, previous)
      (uid, None) => {
        let _ = self.scope.remove(uid)
      }
    }
  })
  f()
}

// ---------------------------------------------------------------------------
// Rewriting
// ---------------------------------------------------------------------------

///|
fn Renamer::rewrite_stmt(self : Renamer, s : Stmt) -> Stmt {
  match s {
    // can be recursive
    Def(id, block, body) =>
      self.with_bindings([id], () => {
        Def(
          self.rewrite_id(id),
          self.rewrite_block(block),
          self.rewrite_stmt(body),
        )
      })
    Let(id, binding, body) => {
      let resolved_binding = self.rewrite_expr(binding)
      self.with_bindings([id], () => {
        Let(self.rewrite_id(id), resolved_binding, self.rewrite_stmt(body))
      })
    }
    ImpureApp(id, callee, targs, vargs, bargs, body) => {
      let resolved_callee = self.rewrite_block_var(callee)
      let resolved_targs = targs.map(t => self.rewrite_value_type(t))
      let resolved_vargs = vargs.map(e => self.rewrite_expr(e))
      let resolved_bargs = bargs.map(b => self.rewrite_block(b))
      self.with_bindings([id], () => {
        ImpureApp(
          self.rewrite_id(id),
          resolved_callee,
          resolved_targs,
          resolved_vargs,
          resolved_bargs,
          self.rewrite_stmt(body),
        )
      })
    }
    Val(ids, binding, body) => {
      let resolved_binding = self.rewrite_stmt(binding)
      self.with_bindings(ids, () => {
        Val(
          ids.map(id => self.rewrite_id(id)),
          resolved_binding,
          self.rewrite_stmt(body),
        )
      })
    }
    Alloc(id, init, region, body) => {
      let resolved_init = self.rewrite_expr(init)
      let resolved_region = self.rewrite_id(region)
      self.with_bindings([id], () => {
        Alloc(
          self.rewrite_id(id),
          resolved_init,
          resolved_region,
          self.rewrite_stmt(body),
        )
      })
    }
    Var(ref, init, capture, body) => {
      let resolved_init = self.rewrite_expr(init)
      let resolved_capture = self.rewrite_id(capture)
      self.with_bindings([ref], () => {
        Var(
          self.rewrite_id(ref),
          resolved_init,
          resolved_capture,
          self.rewrite_stmt(body),
        )
      })
    }
    Get(id, tpe, ref, capt, body) => {
      let resolved_ref = self.rewrite_id(ref)
      let resolved_capt = self.rewrite_captures(capt)
      self.with_bindings([id], () => {
        Get(
          self.rewrite_id(id),
          self.rewrite_value_type(tpe),
          resolved_ref,
          resolved_capt,
          self.rewrite_stmt(body),
        )
      })
    }
    Shift(prompt, k, body) => {
      let resolved_prompt = self.rewrite_block_var(prompt)
      self.with_bindings([k.id], () => {
        Shift(
          resolved_prompt,
          self.rewrite_block_param(k),
          self.rewrite_stmt(body),
        )
      })
    }
    // congruences (upstream: `Tree.Rewrite`'s default cases)
    Return(exprs) => Return(exprs.map(e => self.rewrite_expr(e)))
    App(callee, targs, vargs, bargs) =>
      App(
        self.rewrite_block(callee),
        targs.map(t => self.rewrite_value_type(t)),
        vargs.map(e => self.rewrite_expr(e)),
        bargs.map(b => self.rewrite_block(b)),
      )
    Invoke(callee, method, method_tpe, targs, vargs, bargs) =>
      Invoke(
        self.rewrite_block(callee),
        self.rewrite_id(method),
        self.rewrite_block_type(method_tpe),
        targs.map(t => self.rewrite_value_type(t)),
        vargs.map(e => self.rewrite_expr(e)),
        bargs.map(b => self.rewrite_block(b)),
      )
    If(cond, thn, els) =>
      If(
        self.rewrite_expr(cond),
        self.rewrite_stmt(thn),
        self.rewrite_stmt(els),
      )
    Match(scrutinee, tpe, clauses, default) =>
      Match(
        self.rewrite_expr(scrutinee),
        tpe.map(t => self.rewrite_value_type(t)),
        clauses.map(clause => {
          Clause(
            self.rewrite_id(clause.tag),
            self.rewrite_block_lit(clause.body),
          )
        }),
        match default {
          Some(body) => Some(self.rewrite_stmt(body))
          None => None
        },
      )
    Region(body) => Region(self.rewrite_block_lit(body))
    Put(ref, capt, value, body) =>
      Put(
        self.rewrite_id(ref),
        self.rewrite_captures(capt),
        self.rewrite_expr(value),
        self.rewrite_stmt(body),
      )
    Reset(body) => Reset(self.rewrite_block_lit(body))
    Resume(k, body) =>
      Resume(self.rewrite_block_var(k), self.rewrite_stmt(body))
    Hole(tpe, span) => Hole(tpe.map(t => self.rewrite_value_type(t)), span)
  }
}

///|
fn Renamer::rewrite_block(self : Renamer, b : Block) -> Block {
  match b {
    BlockVar(bv) => BlockVar(self.rewrite_block_var(bv))
    BlockLit(lit) => BlockLit(self.rewrite_block_lit(lit))
    Unbox(e) => Unbox(self.rewrite_expr(e))
    New(implementation) => New(self.rewrite_implementation(implementation))
  }
}

///|
fn Renamer::rewrite_block_lit(self : Renamer, b : BlockLit) -> BlockLit {
  let ids = b.tparams + b.cparams
  let ids = ids + b.vparams.map(p => p.id)
  let ids = ids + b.bparams.map(p => p.id)
  self.with_bindings(ids, () => {
    BlockLit::new(
      b.tparams.map(id => self.rewrite_id(id)),
      b.cparams.map(id => self.rewrite_id(id)),
      b.vparams.map(p => self.rewrite_value_param(p)),
      b.bparams.map(p => self.rewrite_block_param(p)),
      self.rewrite_stmt(b.body),
    )
  })
}

///|
fn Renamer::rewrite_block_var(self : Renamer, bv : BlockVar) -> BlockVar {
  BlockVar::new(
    self.rewrite_id(bv.id),
    self.rewrite_block_type(bv.annotated_tpe),
    self.rewrite_captures(bv.annotated_capt),
  )
}

///|
fn Renamer::rewrite_implementation(
  self : Renamer,
  implementation : Implementation,
) -> Implementation {
  Implementation(
    self.rewrite_block_type(implementation.interface),
    implementation.operations.map(op => self.rewrite_operation(op)),
  )
}

///|
fn Renamer::rewrite_operation(self : Renamer, op : Operation) -> Operation {
  let ids = op.tparams + op.cparams
  let ids = ids + op.vparams.map(p => p.id)
  let ids = ids + op.bparams.map(p => p.id)
  self.with_bindings(ids, () => {
    Operation(
      self.rewrite_id(op.name),
      op.tparams.map(id => self.rewrite_id(id)),
      op.cparams.map(id => self.rewrite_id(id)),
      op.vparams.map(p => self.rewrite_value_param(p)),
      op.bparams.map(p => self.rewrite_block_param(p)),
      self.rewrite_stmt(op.body),
    )
  })
}

///|
fn Renamer::rewrite_value_param(self : Renamer, p : ValueParam) -> ValueParam {
  ValueParam::ValueParam(self.rewrite_id(p.id), self.rewrite_value_type(p.tpe))
}

///|
fn Renamer::rewrite_block_param(self : Renamer, p : BlockParam) -> BlockParam {
  BlockParam::BlockParam(
    self.rewrite_id(p.id),
    self.rewrite_block_type(p.tpe),
    self.rewrite_captures(p.capt),
  )
}

// ---------------------------------------------------------------------------
// Expressions and types
// ---------------------------------------------------------------------------

///|
fn Renamer::rewrite_expr(self : Renamer, e : Expr) -> Expr {
  match e {
    ValueVar(id, tpe) =>
      ValueVar(self.rewrite_id(id), self.rewrite_value_type(tpe))
    Literal(value, tpe) => Literal(value, self.rewrite_value_type(tpe))
    PureApp(f, targs, vargs) =>
      PureApp(
        self.rewrite_block_var(f),
        targs.map(t => self.rewrite_value_type(t)),
        vargs.map(v => self.rewrite_expr(v)),
      )
    Make(data, tag, targs, vargs) =>
      Make(
        self.rewrite_value_type(data),
        self.rewrite_id(tag),
        targs.map(t => self.rewrite_value_type(t)),
        vargs.map(v => self.rewrite_expr(v)),
      )
    Box(b, capt) => Box(self.rewrite_block(b), self.rewrite_captures(capt))
  }
}

///|
fn Renamer::rewrite_value_type(self : Renamer, tpe : ValueType) -> ValueType {
  match tpe {
    ValueVar(name) => ValueVar(self.rewrite_id(name))
    ValueData(name, targs) =>
      ValueData(
        self.rewrite_id(name),
        targs.map(t => self.rewrite_value_type(t)),
      )
    ValueBoxed(block, capt) =>
      ValueBoxed(self.rewrite_block_type(block), self.rewrite_captures(capt))
  }
}

///|
fn Renamer::rewrite_block_type(self : Renamer, tpe : BlockType) -> BlockType {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result) =>
      FunctionType(
        tparams.map(id => self.rewrite_id(id)),
        cparams.map(c => self.rewrite_captures(c)),
        vparams.map(t => self.rewrite_value_type(t)),
        bparams.map(t => self.rewrite_block_type(t)),
        result.map(t => self.rewrite_value_type(t)),
      )
    InterfaceType(name, targs) =>
      InterfaceType(
        self.rewrite_id(name),
        targs.map(t => self.rewrite_value_type(t)),
      )
    PromptType(answer) =>
      PromptType(answer.map(t => self.rewrite_value_type(t)))
    ResumeType(result, answer) =>
      ResumeType(
        result.map(t => self.rewrite_value_type(t)),
        answer.map(t => self.rewrite_value_type(t)),
      )
  }
}

///|
fn Renamer::rewrite_captures(self : Renamer, capt : Captures) -> Captures {
  match capt {
    CaptureSetOf(ids) => CaptureSetOf(ids.map(id => self.rewrite_id(id)))
    CaptVar(id) => CaptVar(self.rewrite_id(id))
  }
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

///|
/// Freshens a block and returns it together with the fresh symbols it introduced
/// (fresh symbol -> the symbol it replaces), mirroring `Renamer.rename(b)`.
pub fn rename_block(block : Block) -> (Block, Map[Int32, Sym]) {
  let renamer = Renamer::Renamer()
  let renamed = renamer.rewrite_block(block)
  (renamed, renamer.renamed)
}

///|
/// Freshens a block literal, see `rename_block`.
pub fn rename_block_lit(block : BlockLit) -> (BlockLit, Map[Int32, Sym]) {
  let renamer = Renamer::Renamer()
  let renamed = renamer.rewrite_block_lit(block)
  (renamed, renamer.renamed)
}
