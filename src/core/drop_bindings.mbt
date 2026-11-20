// Dropping (inlining) unique value bindings (upstream
// `core/optimizer/DropBindings.scala`).
//
//   let x = 42
//   let y = x + 1
//   let z = y * 2
//   z
//   ==>
//   (42 + 1) * 2
//
// Upstream says this improves the performance for JS on some benchmarks (mostly
// `match_options`, `sum_range` and `parsing_dollars`). A binding is dropped only
// if its use is at most as often as the binding itself. `Once` in the
// reachability analysis means exactly one reference in the reachable program;
// on top of that a reference inside a *called* block does not count, because it
// is one reference per call of that block. Without the second rule a loop would
// recompute the value on every iteration:
//
//   let n = size(arr)
//   def go(i) = if (i < n) { ...; go(i + 1) } else { ... }
//
// The phase runs after the optimizer and *unconditionally*: unlike
// `Optimizer.optimize`, upstream's `DropBindings` does not consult
// `Context.config.optimize()`, so `--no-optimize` still drops bindings.
//
// The definitions are threaded through the rewrite (upstream's `DropContext` is
// the `using` context of a `Tree.Rewrite`): the `Let` is removed and its
// single use is replaced by the (already rewritten) binding. Ids are globally
// unique, so the map cannot be shadowed; the entry is dropped again when the
// body it scopes over has been rewritten.

///|
/// The context of the rewrite (upstream `DropContext`).
priv struct DropBindings {
  /// uid -> how often the symbol is referenced (upstream `DropContext.usage`,
  /// the result of the reachability analysis).
  usage : Map[Int32, Usage]
  /// uid -> whether the symbol is referenced inside a called block (upstream
  /// `DropContext.usedInCalledBlock`).
  called : Map[Int32, Bool]
  /// uid -> the expression a dropped binding stands for (upstream
  /// `DropContext.definitions`).
  definitions : Map[Int32, Expr]
}

///|
/// `DropBindings.usedOnce`.
fn DropBindings::used_once(self : DropBindings, id : Sym) -> Bool {
  self.usage.get(id.uid()) is Some(Once)
}

///|
/// `DropBindings.droppable`: used once, and not inside a block that is called.
fn DropBindings::droppable(self : DropBindings, id : Sym) -> Bool {
  self.used_once(id) && !self.called.contains(id.uid())
}

///|
/// Drops the unique value bindings of `module` (upstream `DropBindings.apply`);
/// `entrypoints` is the module's `main`.
pub fn drop_bindings(
  module : ModuleDecl,
  entrypoints : ArrayView[Sym],
) -> ModuleDecl raise EffektError {
  let state : DropBindings = {
    usage: reachable_usage(module, entrypoints),
    called: used_in_called_block(module),
    definitions: Map([]),
  }
  state.rewrite(module)
}

///|
/// The rewrite itself (upstream `DropBindings.dropping`).
fn DropBindings::rewrite(
  self : DropBindings,
  module : ModuleDecl,
) -> ModuleDecl raise EffektError {
  let rewrite : Rewrite = Rewrite(
    Some((rewrite, stmt) => {
      match stmt {
        Let(id, binding, body) if self.droppable(id) => {
          // The binding is rewritten in the context of the enclosing block, so
          // that a use of an outer dropped binding inside it is replaced first.
          let binding = rewrite.rewrite_expr(binding)
          self.definitions.set(id.uid(), binding)
          let body = rewrite.rewrite_stmt(body)
          self.definitions.remove(id.uid())
          Some(body)
        }
        _ => None
      }
    }),
    None,
    None,
    None,
    on_expr=(_rewrite, expr) => {
      match expr {
        // The definition is already rewritten; replacing it here (rather than
        // recursing) is what upstream's `rewrite(expr)` override does, and it
        // keeps a definition from being inlined into itself.
        ValueVar(id, _) if self.droppable(id) &&
          self.definitions.contains(id.uid()) =>
          Some(self.definitions.get(id.uid()).unwrap())
        _ => None
      }
    },
  )
  rewrite.rewrite_module(module)
}

// ---------------------------------------------------------------------------
// The variables used inside a called block (DropBindings.scala:70)
// ---------------------------------------------------------------------------

///|
/// The variables used inside a *called* block, plus every variable that is free
/// where it occurs (upstream `DropBindings.usedInCalledBlock`).
///
/// A block literal, an operation or a clause body may run once per call of the
/// block that receives it, so a reference inside one says nothing about how
/// often the enclosing `let` is evaluated. Only the let-bound variables of the
/// current block are excluded while they are in scope, which is upstream's
/// `lets` parameter: the query is started with an empty scope and reset for the
/// body of a block literal.
fn used_in_called_block(module : ModuleDecl) -> Map[Int32, Bool] {
  let out : Map[Int32, Bool] = Map([])
  // The scope at the toplevel is empty; a block literal starts a new one.
  let lets : Map[Int32, Bool] = Map([])
  for definition in module.definitions {
    match definition {
      ToplevelDef(_, block) => collect_block(block, lets, out)
      ToplevelVal(_, binding) => collect_stmt(binding, lets, out)
    }
  }
  for e in module.externs {
    if e is ExternDef(_, _, _, _, _, _, _, _, StringExternBody(_, template)) {
      for arg in template.args {
        collect_expr(arg, lets, out)
      }
    }
  }
  out
}

///|
/// `usedInCalledBlock.pure`: a value variable that is not let-bound where it
/// occurs. Block variables are not value variables and are not collected.
fn collect_expr(
  expr : Expr,
  lets : Map[Int32, Bool],
  out : Map[Int32, Bool],
) -> Unit {
  match expr {
    ValueVar(id, _) => if !lets.contains(id.uid()) { out.set(id.uid(), true) }
    Literal(_, _) => ()
    PureApp(_, _, args) =>
      for arg in args {
        collect_expr(arg, lets, out)
      }
    Make(_, _, _, args) =>
      for arg in args {
        collect_expr(arg, lets, out)
      }
    Box(block, _) => collect_block(block, lets, out)
  }
}

///|
/// `usedInCalledBlock.block`: the body of a block literal is queried in a fresh
/// scope — everything it references is captured by a block that is called.
fn collect_block(
  block : Block,
  lets : Map[Int32, Bool],
  out : Map[Int32, Bool],
) -> Unit {
  match block {
    BlockVar(_) => ()
    BlockLit(lit) => collect_stmt(lit.body, Map([]), out)
    Unbox(expr) => collect_expr(expr, lets, out)
    New(implementation) =>
      for operation in implementation.operations {
        collect_stmt(operation.body, Map([]), out)
      }
  }
}

///|
/// `usedInCalledBlock.stmt`.
fn collect_stmt(
  stmt : Stmt,
  lets : Map[Int32, Bool],
  out : Map[Int32, Bool],
) -> Unit {
  match stmt {
    Def(_, block, body) => {
      collect_block(block, lets, out)
      collect_stmt(body, lets, out)
    }
    Let(id, binding, body) => {
      collect_expr(binding, lets, out)
      lets.set(id.uid(), true)
      collect_stmt(body, lets, out)
      lets.remove(id.uid())
    }
    // An immediately applied block literal runs in place, so its body belongs to
    // the current scope rather than to a called block.
    App(BlockLit(lit), _, vargs, bargs) => {
      collect_stmt(lit.body, lets, out)
      for arg in vargs {
        collect_expr(arg, lets, out)
      }
      for arg in bargs {
        collect_block(arg, lets, out)
      }
    }
    App(callee, _, vargs, bargs) => {
      collect_block(callee, lets, out)
      for arg in vargs {
        collect_expr(arg, lets, out)
      }
      for arg in bargs {
        collect_block(arg, lets, out)
      }
    }
    Invoke(callee, _, _, _, vargs, bargs) => {
      collect_block(callee, lets, out)
      for arg in vargs {
        collect_expr(arg, lets, out)
      }
      for arg in bargs {
        collect_block(arg, lets, out)
      }
    }
    ImpureApp(_, _, _, vargs, bargs, body) => {
      for arg in vargs {
        collect_expr(arg, lets, out)
      }
      for arg in bargs {
        collect_block(arg, lets, out)
      }
      collect_stmt(body, lets, out)
    }
    Return(exprs) =>
      for expr in exprs {
        collect_expr(expr, lets, out)
      }
    Val(_, binding, body) => {
      collect_stmt(binding, lets, out)
      collect_stmt(body, lets, out)
    }
    If(cond, thn, els) => {
      collect_expr(cond, lets, out)
      collect_stmt(thn, lets, out)
      collect_stmt(els, lets, out)
    }
    Match(scrutinee, _, clauses, default) => {
      collect_expr(scrutinee, lets, out)
      // A clause runs once per match, so it stays in the current scope.
      for clause in clauses {
        collect_stmt(clause.body.body, lets, out)
      }
      if default is Some(body) {
        collect_stmt(body, lets, out)
      }
    }
    // `reset` and `region` bodies run once, in place.
    Region(lit) => collect_stmt(lit.body, lets, out)
    Reset(lit) => collect_stmt(lit.body, lets, out)
    Alloc(_, init, _, body) => {
      collect_expr(init, lets, out)
      collect_stmt(body, lets, out)
    }
    Var(_, init, _, body) => {
      collect_expr(init, lets, out)
      collect_stmt(body, lets, out)
    }
    Get(_, _, _, _, body) => collect_stmt(body, lets, out)
    Put(_, _, value, body) => {
      collect_expr(value, lets, out)
      collect_stmt(body, lets, out)
    }
    Shift(_, _, body) => collect_stmt(body, lets, out)
    Resume(_, body) => collect_stmt(body, lets, out)
    Hole(_, _) => ()
  }
}
