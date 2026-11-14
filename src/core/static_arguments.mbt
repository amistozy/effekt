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
/// The arguments whose parameter is not static (upstream `dropStatic`). `zip`
/// truncates, as upstream's does.
fn[T] drop_static(static : Array[Bool], args : Array[T]) -> Array[T] {
  let out : Array[T] = []
  let n = if static.length() < args.length() {
    static.length()
  } else {
    args.length()
  }
  for i = 0; i < n; i = i + 1 {
    if !static[i] {
      out.push(args[i])
    }
  }
  out
}

///|
/// The arguments whose parameter is static (upstream `selectStatic`).
fn[T] select_static(static : Array[Bool], args : Array[T]) -> Array[T] {
  let out : Array[T] = []
  let n = if static.length() < args.length() {
    static.length()
  } else {
    args.length()
  }
  for i = 0; i < n; i = i + 1 {
    if static[i] {
      out.push(args[i])
    }
  }
  out
}

///|
/// Which of the definition's parameters the recursive calls (and the body)
/// leave alone.
fn is_static(found : RecursiveFunction) -> IsStatic raise EffektError {
  let lit = found.definition
  let free = lit.body.free()
  let types : Array[Bool] = []
  for i = 0; i < lit.tparams.length(); i = i + 1 {
    let param = lit.tparams[i]
    let mut unchanged = found.targs.length() > 0
    for args in found.targs {
      if i >= args.length() {
        raise EffektError::Internal(
          "A recursive call passes too few type arguments.",
        )
      }
      match args[i] {
        ValueTypeRef(other) => if !(param == other) { unchanged = false }
        _ => unchanged = false
      }
    }
    types.push(unchanged)
  }
  let values : Array[Bool] = []
  for i = 0; i < lit.vparams.length(); i = i + 1 {
    let param = lit.vparams[i]
    let mut unchanged = found.vargs.length() > 0
    for args in found.vargs {
      if i >= args.length() {
        raise EffektError::Internal(
          "A recursive call passes too few value arguments.",
        )
      }
      match args[i] {
        ValueVar(other, _) => if !(param.id == other) { unchanged = false }
        _ => unchanged = false
      }
    }
    values.push(unchanged || !free.contains(param.id))
  }
  let blocks : Array[Bool] = []
  for i = 0; i < lit.bparams.length(); i = i + 1 {
    let param = lit.bparams[i]
    let mut unchanged = found.bargs.length() > 0
    for args in found.bargs {
      if i >= args.length() {
        raise EffektError::Internal(
          "A recursive call passes too few block arguments.",
        )
      }
      match args[i] {
        BlockVar(other) => if !(param.id == other.id) { unchanged = false }
        _ => unchanged = false
      }
    }
    blocks.push(unchanged || !free.contains(param.id))
  }
  { types, values, blocks, }
}

///|
/// The type of the worker: the parameters of the definition that are not
/// static, and the type of its body (upstream `blockLit.returnType`).
fn worker_type_of(
  lit : BlockLit,
  flags : IsStatic,
) -> BlockType raise EffektError {
  FunctionType(
    drop_static(flags.types, lit.tparams),
    // the capture parameters of the static block parameters are dropped
    drop_static(flags.blocks, lit.cparams).map(c => CaptureSetOf([c])),
    drop_static(flags.values, lit.vparams).map(p => p.tpe),
    drop_static(flags.blocks, lit.bparams).map(p => p.tpe),
    single(lit.body.infer_type()),
    Effects::empty(),
  )
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
  defer {
    let _ = self.stack.pop()
  }
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
  let worker_type = worker_type_of(lit, flags)
  // Fresh parameters for the wrapper and its call to the worker. Only the
  // non-static ones are freshened, so that the static ones keep their names and
  // the worker closes over exactly those.
  let fresh_cparams : Array[Sym] = []
  for i = 0; i < lit.cparams.length(); i = i + 1 {
    let param = lit.cparams[i]
    if static_b[i] {
      fresh_cparams.push(param)
    } else {
      fresh_cparams.push(Sym::id(param.name()))
    }
  }
  let fresh_vparams : Array[ValueParam] = []
  for i = 0; i < lit.vparams.length(); i = i + 1 {
    let param = lit.vparams[i]
    if static_v[i] {
      fresh_vparams.push(param)
    } else {
      fresh_vparams.push(ValueParam(Sym::id(param.id.name()), param.tpe))
    }
  }
  let fresh_bparams : Array[BlockParam] = []
  for i = 0; i < lit.bparams.length(); i = i + 1 {
    let param = lit.bparams[i]
    if static_b[i] {
      fresh_bparams.push(param)
    } else {
      fresh_bparams.push(
        BlockParam(
          Sym::id(param.id.name()),
          param.tpe,
          CaptureSetOf([fresh_cparams[i]]),
        ),
      )
    }
  }
  // The worker closes over the static block arguments of the wrapper.
  let mut new_captures = Block::BlockLit(lit).infer_capt()
  for c in select_static(static_b, fresh_cparams) {
    new_captures = new_captures.union(CaptureSetOf([c]))
  }
  let worker_id = Sym::id(id.name().rename(original => "\{original}_worker"))
  let worker_var = BlockVar::new(worker_id, worker_type, new_captures)
  self.workers.set(id.uid(), Block::BlockVar(worker_var))
  let worker_body = self.enter_function(id, () => self.rewrite_stmt(lit.body))
  BlockLit::new(
    lit.tparams,
    fresh_cparams,
    fresh_vparams,
    fresh_bparams,
    Def(
      worker_id,
      Block::BlockLit(
        BlockLit::new(
          drop_static(static_t, lit.tparams),
          drop_static(static_b, lit.cparams),
          drop_static(static_v, lit.vparams),
          drop_static(static_b, lit.bparams),
          worker_body,
        ),
      ),
      App(
        Block::BlockVar(worker_var),
        drop_static(static_t, lit.tparams.map(t => ValueTypeRef(t))),
        drop_static(static_v, fresh_vparams.map(p => ValueVar(p.id, p.tpe))),
        drop_static(
          static_b,
          fresh_bparams.map(b => {
            Block::BlockVar(BlockVar::new(b.id, b.tpe, b.capt))
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
        match default {
          Some(body) => Some(self.rewrite_stmt(body))
          None => None
        },
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
  BlockLit::new(
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
