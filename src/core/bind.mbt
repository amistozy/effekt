// Bindings and the binding monad of the core representation.
//
// Mirrors the `Binding` / `Bind` part of `effekt/core/Tree.scala`. Bindings are
// not part of the tree, but are used by the transformations (inlining,
// normalization): every intrusive linked list (like `Val`) appears here in a
// non-intrusive form where the body / rest is left implicit.

///|
/// A binding, i.e. a statement with its "rest" (body) left implicit.
///
/// Invariant: all binding occurrences store the id separately from the
/// (implicit) body.
pub(all) enum Binding {
  BindingVal(Array[Sym], Stmt)
  BindingLet(Sym, Expr)
  BindingImpureApp(Sym, BlockVar, Array[ValueType], Array[Expr], Array[Block])
  BindingDef(Sym, Block)
  BindingAlloc(Sym, Expr, Sym)
  BindingVar(Sym, Expr, Sym)
  BindingGet(Sym, ValueType, Sym, Captures)
  BindingPut(Sym, Captures, Expr)
}

///|
/// Turns this binding into the corresponding statement with the given rest.
fn Binding::to_stmt(self : Binding, rest : Stmt) -> Stmt {
  match self {
    BindingVal(ids, binding) => Val(ids, binding, rest)
    BindingLet(id, binding) => Let(id, binding, rest)
    BindingImpureApp(id, callee, targs, vargs, bargs) =>
      ImpureApp(id, callee, targs, vargs, bargs, rest)
    BindingDef(id, binding) => Def(id, binding, rest)
    BindingAlloc(id, init, region) => Alloc(id, init, region, rest)
    BindingVar(ref, init, capture) => Var(ref, init, capture, rest)
    BindingGet(id, annotated_tpe, ref, annotated_capt) =>
      Get(id, annotated_tpe, ref, annotated_capt, rest)
    BindingPut(ref, annotated_capt, value) =>
      Put(ref, annotated_capt, value, rest)
  }
}

///|
/// The name of a binding constructor, for error messages.
fn Binding::kind_name(self : Binding) -> String {
  match self {
    BindingVal(_, _) => "Val"
    BindingLet(_, _) => "Let"
    BindingImpureApp(_, _, _, _, _) => "ImpureApp"
    BindingDef(_, _) => "Def"
    BindingAlloc(_, _, _) => "Alloc"
    BindingVar(_, _, _) => "Var"
    BindingGet(_, _, _, _) => "Get"
    BindingPut(_, _, _) => "Put"
  }
}

///|
/// Turns a binding that has been emitted at the toplevel into a `Toplevel`
/// definition. Mirrors `Binding.toToplevel`, which is only defined for value
/// and block definitions (upstream leaves the other cases as `???`).
fn Binding::to_toplevel(self : Binding) -> Toplevel raise EffektError {
  match self {
    BindingVal([id], binding) => ToplevelVal(id, binding)
    BindingVal(_, _) =>
      raise EffektError::Internal(
        "Binding.Val with more than one pattern is not allowed on the toplevel.",
      )
    BindingDef(id, binding) => ToplevelDef(id, binding)
    _ =>
      raise EffektError::Internal(
        "Binding.\{self.kind_name()} is not allowed on the toplevel.",
      )
  }
}

///|
/// Prefixes `body` with the given bindings.
fn bindings_to_stmt(bindings : ArrayView[Binding], body : Stmt) -> Stmt {
  bindings.rev_fold(init=body, (acc, b) => b.to_stmt(acc))
}

///|
/// The binding monad: a value together with the bindings that have to be
/// emitted before it can be used.
pub(all) struct Bind[A] {
  value : A
  bindings : Array[Binding]
}

///|
pub fn[A] Bind::pure(value : A) -> Bind[A] {
  { value, bindings: [], }
}

///|
pub fn[A] Bind::run(self : Bind[A], f : (A) -> Stmt) -> Stmt {
  bindings_to_stmt(self.bindings, f(self.value))
}

///|
pub fn[A, B] Bind::map(self : Bind[A], f : (A) -> B) -> Bind[B] {
  { value: f(self.value), bindings: self.bindings, }
}

///|
pub fn[A, B] Bind::flat_map(self : Bind[A], f : (A) -> Bind[B]) -> Bind[B] {
  let other = f(self.value)
  { value: other.value, bindings: self.bindings + other.bindings, }
}

///|
pub fn Bind::delimit(b : Bind[Stmt]) -> Stmt {
  b.run(a => a)
}

///|
/// The type of an expression bound to a temporary (upstream `Type.inferType`,
/// `e.tpe`): the annotation of a value or literal, the data type of a `Make`,
/// the instantiated result of a pure application, the boxed type of a block.
/// Inference can fail on the placeholder types the port writes where upstream
/// always has a real type, so it degrades to the unknown type.
fn expr_type_hint(e : Expr) -> ValueType {
  e.infer_type() catch {
    _ => unknown_value_type()
  }
}

///|
/// The type of a statement bound to a temporary: upstream `Type.single(s.tpe)`.
fn stmt_type_hint(s : Stmt) -> ValueType {
  single(s.infer_type()) catch {
    _ => unknown_value_type()
  }
}

///|
/// `Type.bindingType` for an impure application: the result type of the callee,
/// instantiated with the type arguments of the call and the captures of its
/// block arguments.
fn impure_app_type(
  callee : BlockVar,
  targs : ArrayView[ValueType],
  bargs : ArrayView[Block],
) -> ValueType {
  let cargs = bargs.map(b => b.infer_capt_or_empty())
  single(instantiated_results(callee.annotated_tpe, targs, cargs)) catch {
    _ => unknown_value_type()
  }
}

///|
/// Binds an expression to a fresh temporary.
fn Bind::bind_expr(expr : Expr) -> Bind[Expr] {
  let id = Sym::tmp_value("tmp")
  {
    value: ValueVar(id, expr_type_hint(expr)),
    bindings: [BindingLet(id, expr)],
  }
}

///|
/// Binds a block to a fresh temporary.
pub fn Bind::bind_block(block : Block) -> Bind[Block] {
  let id = Sym::tmp_block("tmp")
  let bv = BlockVar::BlockVar(
    id,
    block.infer_type_or_unknown(),
    block.infer_capt_or_empty(),
  )
  { value: BlockVar(bv), bindings: [BindingDef(id, block)], }
}

///|
pub fn[S, T] Bind::traverse(
  l : ArrayView[S],
  f : (S) -> Bind[T],
) -> Bind[Array[T]] {
  let values : Array[T] = []
  let bindings : Array[Binding] = []
  for x in l {
    let b = f(x)
    values.push(b.value)
    bindings.append(b.bindings)
  }
  { value: values, bindings, }
}
