// The definitions that call themselves, together with the arguments of those
// calls (upstream `core/Recursive.scala`).
//
// A call counts as recursive when the callee is on the stack, i.e. when the call
// is inside the body of a `def` that (lexically) encloses the call: self
// recursion and calls to an enclosing definition. Two mutually recursive
// top-level definitions are not detected — upstream behaves the same, and
// `StaticArguments` only needs the self-recursive case.
//
// Upstream stores the argument lists of the calls in `mutable.Set`s, which
// `StaticArguments` only ever `forall`s over: duplicates cannot change the
// result, so the port appends to arrays instead of deduplicating.

///|
/// A definition that is called recursively, with the arguments of every call.
priv struct RecursiveFunction {
  definition : BlockLit
  /// The type arguments of each recursive call (upstream `targs`).
  targs : Array[Array[ValueType]]
  /// The value arguments of each recursive call (upstream `vargs`).
  vargs : Array[Array[Expr]]
  /// The block arguments of each recursive call (upstream `bargs`).
  bargs : Array[Array[Block]]
}

///|
fn RecursiveFunction::RecursiveFunction(
  definition : BlockLit,
) -> RecursiveFunction {
  { definition, targs: [], vargs: [], bargs: [], }
}

///|
priv struct RecursiveAnalysis {
  /// uid -> the function found for the definition with that binder.
  definitions : Map[Int32, RecursiveFunction]
  /// The binders whose bodies are currently being traversed.
  stack : Array[Sym]
}

///|
fn RecursiveAnalysis::enter(self : RecursiveAnalysis, id : Sym) -> Unit {
  self.stack.push(id)
}

///|
fn RecursiveAnalysis::leave(self : RecursiveAnalysis) -> Unit {
  let _ = self.stack.pop()
}

///|
fn RecursiveAnalysis::within(self : RecursiveAnalysis, id : Sym) -> Bool {
  self.stack.contains(id)
}

///|
fn RecursiveAnalysis::record_definition(
  self : RecursiveAnalysis,
  id : Sym,
  definition : BlockLit,
) -> Unit raise EffektError {
  if self.definitions.contains(id.uid()) {
    raise EffektError::Internal(
      "The definition \{id.name().name} is registered twice.",
    )
  }
  self.definitions.set(
    id.uid(),
    RecursiveFunction::RecursiveFunction(definition),
  )
}

///|
fn RecursiveAnalysis::record_call(
  self : RecursiveAnalysis,
  id : Sym,
  targs : Array[ValueType],
  vargs : Array[Expr],
  bargs : Array[Block],
) -> Unit raise EffektError {
  match self.definitions.get(id.uid()) {
    Some(found) => {
      found.targs.push(targs)
      found.vargs.push(vargs)
      found.bargs.push(bargs)
    }
    None =>
      raise EffektError::Internal(
        "The recursive call to \{id.name().name} has no definition.",
      )
  }
}

///|
fn RecursiveAnalysis::process_toplevel(
  self : RecursiveAnalysis,
  toplevel : Toplevel,
) -> Unit raise EffektError {
  match toplevel {
    ToplevelDef(id, block) => self.process_definition(id, block)
    ToplevelVal(_, binding) => self.process_stmt(binding)
  }
}

///|
/// A block binder is registered and its body traversed with the binder on the
/// stack, so that calls inside it are recognised as recursive.
fn RecursiveAnalysis::process_definition(
  self : RecursiveAnalysis,
  id : Sym,
  block : Block,
) -> Unit raise EffektError {
  match block {
    BlockLit(lit) => {
      self.record_definition(id, lit)
      self.enter(id)
      self.process_block(block)
      self.leave()
    }
    _ => self.process_block(block)
  }
}

///|
fn RecursiveAnalysis::process_block(
  self : RecursiveAnalysis,
  block : Block,
) -> Unit raise EffektError {
  match block {
    BlockVar(_) => ()
    BlockLit(lit) => self.process_stmt(lit.body)
    Unbox(pure) => self.process_expr(pure)
    New(implementation) => self.process_implementation(implementation)
  }
}

///|
fn RecursiveAnalysis::process_stmt(
  self : RecursiveAnalysis,
  stmt : Stmt,
) -> Unit raise EffektError {
  match stmt {
    Def(id, block, body) => {
      self.process_definition(id, block)
      self.process_stmt(body)
    }
    Let(_, binding, body) => {
      self.process_expr(binding)
      self.process_stmt(body)
    }
    ImpureApp(_, _, _, vargs, bargs, body) => {
      for e in vargs {
        self.process_expr(e)
      }
      for b in bargs {
        self.process_block(b)
      }
      self.process_stmt(body)
    }
    Return(exprs) =>
      for e in exprs {
        self.process_expr(e)
      }
    Val(_, binding, body) => {
      self.process_stmt(binding)
      self.process_stmt(body)
    }
    App(callee, targs, vargs, bargs) => {
      self.process_block(callee)
      for e in vargs {
        self.process_expr(e)
      }
      for b in bargs {
        self.process_block(b)
      }
      match callee {
        BlockVar(bv) =>
          if self.within(bv.id) {
            self.record_call(bv.id, targs, vargs, bargs)
          }
        _ => ()
      }
    }
    Invoke(callee, _, _, _, vargs, bargs) => {
      self.process_block(callee)
      for e in vargs {
        self.process_expr(e)
      }
      for b in bargs {
        self.process_block(b)
      }
    }
    If(cond, thn, els) => {
      self.process_expr(cond)
      self.process_stmt(thn)
      self.process_stmt(els)
    }
    Match(scrutinee, _, clauses, default) => {
      self.process_expr(scrutinee)
      for clause in clauses {
        self.process_stmt(clause.body.body)
      }
      match default {
        Some(body) => self.process_stmt(body)
        None => ()
      }
    }
    Alloc(_, init, _, body) => {
      self.process_expr(init)
      self.process_stmt(body)
    }
    Var(_, init, _, body) => {
      self.process_expr(init)
      self.process_stmt(body)
    }
    Get(_, _, _, _, body) => self.process_stmt(body)
    Put(_, _, value, body) => {
      self.process_expr(value)
      self.process_stmt(body)
    }
    Reset(body) => self.process_stmt(body.body)
    Shift(_, _, body) => self.process_stmt(body)
    Resume(_, body) => self.process_stmt(body)
    Region(body) => self.process_stmt(body.body)
    Hole(_, _) => ()
  }
}

///|
fn RecursiveAnalysis::process_expr(
  self : RecursiveAnalysis,
  expr : Expr,
) -> Unit raise EffektError {
  match expr {
    ValueVar(_, _) => ()
    Literal(_, _) => ()
    PureApp(_, _, vargs) =>
      for e in vargs {
        self.process_expr(e)
      }
    Make(_, _, _, vargs) =>
      for e in vargs {
        self.process_expr(e)
      }
    Box(block, _) => self.process_block(block)
  }
}

///|
fn RecursiveAnalysis::process_implementation(
  self : RecursiveAnalysis,
  implementation : Implementation,
) -> Unit raise EffektError {
  for operation in implementation.operations {
    self.process_stmt(operation.body)
  }
}

///|
fn RecursiveAnalysis::process_module(
  self : RecursiveAnalysis,
  module : ModuleDecl,
) -> Unit raise EffektError {
  for toplevel in module.definitions {
    self.process_toplevel(toplevel)
  }
}

///|
/// Every definition that is called recursively, keyed by the uid of its binder.
fn recursive_functions(
  module : ModuleDecl,
) -> Map[Int32, RecursiveFunction] raise EffektError {
  let analysis : RecursiveAnalysis = { definitions: Map([]), stack: [], }
  analysis.process_module(module)
  analysis.definitions
}
