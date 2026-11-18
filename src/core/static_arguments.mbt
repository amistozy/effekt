// The static argument transformation (upstream
// `core/optimizer/StaticArguments.scala`).
//
// When a recursive definition passes an argument unchanged in every recursive
// call, that argument is static: the definition is split into a wrapper that
// takes all arguments and a worker that takes only the others, so the recursive
// calls stop passing the static ones:
//
//   def foo(a, b, c) = if a == b then println(c) else foo(a - 2, b - 1, c)
//   ==>
//   def foo(a, b, c) =
//     def foo_worker(a, b) = if a == b then println(c) else foo_worker(a - 2, b - 1)
//     foo_worker(a, b)
//
// A parameter also counts as static when the body never reads it ("vacuously
// static" upstream). The translation only applies when *all* type parameters are
// static, since the worker's type arguments are the ones the recursive calls
// pass.
//
// The worker's result type is the type of the body. Upstream keeps the list of
// result types; the port's function types have a single result, so a body with
// several results has no core type and `single` raises (see `type.mbt`).

///|
/// Which parameters of a recursive definition are static (upstream `IsStatic`).
priv struct IsStatic {
  types : Array[Bool]
  values : Array[Bool]
  blocks : Array[Bool]
}

///|
/// Upstream `hasStatics`: all type parameters must be static, and at least one
/// value or block parameter.
fn IsStatic::allows_the_translation(self : IsStatic) -> Bool {
  self.types.all(x => x) && (self.values.any(x => x) || self.blocks.any(x => x))
}

///|
/// The arguments whose parameter is not static (upstream `dropStatic`); `zip`
/// truncates, as upstream's does.
fn[T] drop_static(static : ArrayView[Bool], args : ArrayView[T]) -> Array[T] {
  static.zip(args).filter_map(pair => if pair.0 { None } else { Some(pair.1) })
}

///|
/// The arguments whose parameter is static (upstream `selectStatic`).
fn[T] select_static(static : ArrayView[Bool], args : ArrayView[T]) -> Array[T] {
  static.zip(args).filter_map(pair => if pair.0 { Some(pair.1) } else { None })
}

///|
/// Whether every recursive call leaves parameter `i` alone. An *empty* list of
/// calls counts as "not unchanged", which keeps the translation off; every call
/// also has to pass at least `i + 1` arguments of that kind.
fn[T] unchanged_in(
  calls : ArrayView[Array[T]],
  i : Int32,
  kind : String,
  is_unchanged : (T) -> Bool,
) -> Bool raise EffektError {
  for args in calls {
    if i >= args.length() {
      raise EffektError::Internal(
        "A recursive call passes too few \{kind} arguments.",
      )
    }
  }
  !calls.is_empty() && calls.all(args => is_unchanged(args[i]))
}

///|
/// Which of the definition's parameters the recursive calls (and the body)
/// leave alone.
fn is_static(found : RecursiveFunction) -> IsStatic raise EffektError {
  let lit = found.definition
  let free = lit.body.free()
  let types = lit.tparams.mapi((i, param) => {
    unchanged_in(found.targs, i, "type", arg => {
      arg is ValueVar(other) && param == other
    })
  })
  let values = lit.vparams.mapi((i, param) => {
    let unchanged = unchanged_in(found.vargs, i, "value", arg => {
      arg is ValueVar(other, _) && param.id == other
    })
    unchanged || !free.contains(param.id)
  })
  let blocks = lit.bparams.mapi((i, param) => {
    let unchanged = unchanged_in(found.bargs, i, "block", arg => {
      arg is BlockVar(other) && param.id == other.id
    })
    unchanged || !free.contains(param.id)
  })
  { types, values, blocks, }
}

///|
/// The context of the rewrite (upstream `StaticArgumentsContext`).
priv struct StaticArguments {
  /// uid of a definition -> which of its parameters are static.
  statics : Map[Int32, IsStatic]
  /// uid of a definition -> the variable referring to its worker.
  workers : Map[Int32, Block]
  /// The definitions whose bodies are currently being rewritten; a call to one
  /// of them is a recursive call and goes to the worker.
  stack : Array[Sym]
}

///|
fn[T] StaticArguments::enter_function(
  self : StaticArguments,
  id : Sym,
  f : () -> T raise EffektError,
) -> T raise EffektError {
  self.stack.push(id)
  defer ignore(self.stack.pop())
  f()
}

///|
fn StaticArguments::within(self : StaticArguments, id : Sym) -> Bool {
  self.stack.contains(id)
}

///|
fn StaticArguments::has_statics(self : StaticArguments, id : Sym) -> Bool {
  match self.statics.get(id.uid()) {
    Some(is_static) => is_static.allows_the_translation()
    None => false
  }
}

///|
fn StaticArguments::statics_of(
  self : StaticArguments,
  id : Sym,
) -> IsStatic raise EffektError {
  match self.statics.get(id.uid()) {
    Some(is_static) => is_static
    None =>
      raise EffektError::Internal(
        "No static-argument analysis for \{id.name().name}.",
      )
  }
}

///|
fn StaticArguments::worker_of(
  self : StaticArguments,
  id : Sym,
) -> Block raise EffektError {
  match self.workers.get(id.uid()) {
    Some(worker) => worker
    None =>
      raise EffektError::Internal(
        "No worker has been created for \{id.name().name}.",
      )
  }
}

///|
/// Wraps the definition in a new one, abstracting the static parameters along
/// the way (upstream `wrapDefinition`).
fn StaticArguments::wrap_definition(
  self : StaticArguments,
  id : Sym,
  lit : BlockLit,
) -> BlockLit raise EffektError {
  let flags = self.statics_of(id)
  let static_t = flags.types
  let static_v = flags.values
  let static_b = flags.blocks
  if !static_t.all(x => x) {
    raise EffektError::Internal(
      "Can only apply the static arguments translation when all type arguments are static.",
    )
  }
  let worker_type = BlockType::FunctionType(
    drop_static(static_t, lit.tparams),
    // the capture parameters of the static block parameters are dropped
    drop_static(static_b, lit.cparams).map(c => Captures::CaptureSetOf([c])),
    drop_static(static_v, lit.vparams).map(p => p.tpe),
    drop_static(static_b, lit.bparams).map(p => p.tpe),
    lit.body.infer_type(),
  ) // Fresh parameters for the wrapper and its call to the worker. Only the
  // non-static ones are freshened, so that the static ones keep their names and
  // the worker closes over exactly those.
  let fresh_cparams = lit.cparams.mapi((i, param) => {
    if static_b[i] {
      param
    } else {
      Sym::id(param.name())
    }
  })
  let fresh_vparams = lit.vparams.mapi((i, param) => {
    if static_v[i] {
      param
    } else {
      ValueParam(Sym::id(param.id.name()), param.tpe)
    }
  })
  let fresh_bparams = lit.bparams.mapi((i, param) => {
    if static_b[i] {
      param
    } else {
      BlockParam(
        Sym::id(param.id.name()),
        param.tpe,
        CaptureSetOf([fresh_cparams[i]]),
      )
    }
  })
  // The worker closes over the static block arguments of the wrapper.
  let new_captures = select_static(static_b, fresh_cparams).fold(
    init=Block::BlockLit(lit).infer_capt(),
    (acc, c) => acc.union(capture_set(c)),
  )
  let worker_id = Sym::id(id.name().rename(original => "\{original}_worker"))
  let worker_var = BlockVar::BlockVar(worker_id, worker_type, new_captures)
  self.workers.set(id.uid(), Block::BlockVar(worker_var))
  let worker_body = self.enter_function(id, () => self.rewrite_stmt(lit.body))
  BlockLit::BlockLit(
    lit.tparams,
    fresh_cparams,
    fresh_vparams,
    fresh_bparams,
    Def(
      worker_id,
      Block::BlockLit(
        BlockLit::BlockLit(
          drop_static(static_t, lit.tparams),
          drop_static(static_b, lit.cparams),
          drop_static(static_v, lit.vparams),
          drop_static(static_b, lit.bparams),
          worker_body,
        ),
      ),
      App(
        Block::BlockVar(worker_var),
        drop_static(static_t, lit.tparams.map(t => ValueVar(t))),
        drop_static(static_v, fresh_vparams.map(p => ValueVar(p.id, p.tpe))),
        drop_static(
          static_b,
          fresh_bparams.map(b => {
            Block::BlockVar(BlockVar::BlockVar(b.id, b.tpe, b.capt))
          }),
        ),
      ),
    ),
  )
}

///|
fn StaticArguments::rewrite_toplevel(
  self : StaticArguments,
  toplevel : Toplevel,
) -> Toplevel raise EffektError {
  match toplevel {
    ToplevelDef(id, Block::BlockLit(lit)) if self.has_statics(id) =>
      ToplevelDef(id, Block::BlockLit(self.wrap_definition(id, lit)))
    ToplevelDef(id, block) => ToplevelDef(id, self.rewrite_block(block))
    ToplevelVal(id, binding) => ToplevelVal(id, self.rewrite_stmt(binding))
  }
}

///|
fn StaticArguments::rewrite_stmt(
  self : StaticArguments,
  stmt : Stmt,
) -> Stmt raise EffektError {
  match stmt {
    Def(id, Block::BlockLit(lit), body) if self.has_statics(id) =>
      Def(
        id,
        Block::BlockLit(self.wrap_definition(id, lit)),
        self.rewrite_stmt(body),
      )
    // A recursive call goes to the worker, without the static arguments.
    App(Block::BlockVar(callee), targs, vargs, bargs) if self.has_statics(
        callee.id,
      ) &&
      self.within(callee.id) => {
      let is_static = self.statics_of(callee.id)
      App(
        self.worker_of(callee.id),
        drop_static(is_static.types, targs),
        drop_static(is_static.values, vargs).map(e => self.rewrite_expr(e)),
        drop_static(is_static.blocks, bargs).map(b => self.rewrite_block(b)),
      )
    }
    Def(id, block, body) =>
      Def(id, self.rewrite_block(block), self.rewrite_stmt(body))
    Let(id, binding, body) =>
      Let(id, self.rewrite_expr(binding), self.rewrite_stmt(body))
    ImpureApp(id, callee, targs, vargs, bargs, body) =>
      ImpureApp(
        id,
        callee,
        targs,
        vargs.map(e => self.rewrite_expr(e)),
        bargs.map(b => self.rewrite_block(b)),
        self.rewrite_stmt(body),
      )
    Return(exprs) => Return(exprs.map(e => self.rewrite_expr(e)))
    Val(ids, binding, body) =>
      Val(ids, self.rewrite_stmt(binding), self.rewrite_stmt(body))
    App(callee, targs, vargs, bargs) =>
      App(
        self.rewrite_block(callee),
        targs,
        vargs.map(e => self.rewrite_expr(e)),
        bargs.map(b => self.rewrite_block(b)),
      )
    Invoke(callee, method, method_tpe, targs, vargs, bargs) =>
      Invoke(
        self.rewrite_block(callee),
        method,
        method_tpe,
        targs,
        vargs.map(e => self.rewrite_expr(e)),
        bargs.map(b => self.rewrite_block(b)),
      )
    If(cond, thn, els) =>
      If(
        self.rewrite_expr(cond),
        self.rewrite_stmt(thn),
        self.rewrite_stmt(els),
      )
    Match(scrutinee, annotated, clauses, default) =>
      Match(
        self.rewrite_expr(scrutinee),
        annotated,
        clauses.map(clause => {
          Clause(clause.tag, self.rewrite_block_lit(clause.body))
        }),
        default.map(body => self.rewrite_stmt(body)),
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
    Reset(body) => Reset(self.rewrite_block_lit(body))
    Shift(prompt, k, body) => Shift(prompt, k, self.rewrite_stmt(body))
    Resume(k, body) => Resume(k, self.rewrite_stmt(body))
    Hole(_, _) => stmt
  }
}

///|
fn StaticArguments::rewrite_block_lit(
  self : StaticArguments,
  lit : BlockLit,
) -> BlockLit raise EffektError {
  BlockLit::BlockLit(
    lit.tparams,
    lit.cparams,
    lit.vparams,
    lit.bparams,
    self.rewrite_stmt(lit.body),
  )
}

///|
fn StaticArguments::rewrite_block(
  self : StaticArguments,
  block : Block,
) -> Block raise EffektError {
  match block {
    BlockVar(_) => block
    BlockLit(lit) => Block::BlockLit(self.rewrite_block_lit(lit))
    Unbox(pure) => Unbox(self.rewrite_expr(pure))
    New(implementation) =>
      Block::New(self.rewrite_implementation(implementation))
  }
}

///|
fn StaticArguments::rewrite_expr(
  self : StaticArguments,
  expr : Expr,
) -> Expr raise EffektError {
  match expr {
    ValueVar(_, _) | Literal(_, _) => expr
    PureApp(callee, targs, vargs) =>
      PureApp(callee, targs, vargs.map(e => self.rewrite_expr(e)))
    Make(data, tag, targs, vargs) =>
      Make(data, tag, targs, vargs.map(e => self.rewrite_expr(e)))
    Box(block, captures) => Box(self.rewrite_block(block), captures)
  }
}

///|
fn StaticArguments::rewrite_implementation(
  self : StaticArguments,
  implementation : Implementation,
) -> Implementation raise EffektError {
  Implementation(
    implementation.interface,
    implementation.operations.map(op => self.rewrite_operation(op)),
  )
}

///|
fn StaticArguments::rewrite_operation(
  self : StaticArguments,
  operation : Operation,
) -> Operation raise EffektError {
  Operation(
    operation.name,
    operation.tparams,
    operation.cparams,
    operation.vparams,
    operation.bparams,
    self.rewrite_stmt(operation.body),
  )
}

///|
/// The static argument transformation (upstream `StaticArguments.transform`,
/// which also takes the entry point and ignores it).
pub fn static_arguments(module : ModuleDecl) -> ModuleDecl raise EffektError {
  let recursive = recursive_functions(module)
  let statics : Map[Int32, IsStatic] = Map([])
  for uid, found in recursive {
    statics.set(uid, is_static(found))
  }
  let rewriter : StaticArguments = { statics, workers: Map([]), stack: [], }
  let definitions = module.definitions.map(t => rewriter.rewrite_toplevel(t))
  { ..module, definitions, }
}
