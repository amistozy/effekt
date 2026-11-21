// Arity raising: type-directed unboxing of records, after monomorphization
// (upstream `core/ArityRaising.scala`).
//
// A value of a flat record type R with constructor C(T₁, …, Tₙ) is represented by
// its components, and arrays and references of records become records of arrays
// and references:
//
//   ⟦R⟧    = ⟦T₁⟧ ++ … ++ ⟦Tₙ⟧      if R is flat
//   ⟦A[T]⟧ = ⟦T⟧ map (U => A[U])     if A ∈ {Array, Ref} and A[T] is not frozen
//   ⟦T⟧    = [T]                     otherwise
//
// The representation is global: parameters, results (multiple returns), fields of
// all data types, function types, prompts, continuations and local state are
// translated pointwise. Only externs see the original representation; at extern
// calls records are packed (`make`) and opened (`match`). The normalizer removes
// the remaining matches on known constructors.
//
// A record type R is *flat* if
//   - it has exactly one constructor with at least one field,
//   - it is not recursive,
//   - some match scrutinizes a value of type R (otherwise flattening can only add
//     packing),
//   - it does not occur in a function type at an extern boundary (which would
//     require eta).
//
// A container type A[T] is *frozen* if it occurs at an extern boundary that is not
// componentwise. Containers nested in frozen types are frozen as well.
//
// Upstream runs `BindSubexpressions` first, because the transformation needs
// every subexpression it translates to be a value or bound to one.
//
// Upstream's analysis traverses the module with the reflective `visitAll`; the
// `visit_*` functions below are that traversal written out. Like `visitAll` they
// also see the *types* of the tree, which is where the extern boundaries and the
// interface arguments come from.

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

///|
/// All value types occurring in a value type, including the type itself
/// (upstream `ArityRaising.occurrences`).
fn type_occurrences(tpe : ValueType) -> Array[ValueType] {
  match tpe {
    ValueVar(_) => [tpe]
    ValueData(_, targs) => [tpe] + block_type_occurrences_of(targs)
    ValueBoxed(block, _) => [tpe] + block_type_occurrences(block)
  }
}

///|
/// `type_occurrences` on a list of value types (upstream `targs.flatMap(occurrences)`).
fn block_type_occurrences_of(targs : ArrayView[ValueType]) -> Array[ValueType] {
  targs.map(t => type_occurrences(t)).flatten()
}

///|
/// All value types occurring in a block type (upstream `ArityRaising.occurrences`
/// on `BlockType`).
fn block_type_occurrences(tpe : BlockType) -> Array[ValueType] {
  match tpe {
    FunctionType(_, _, vparams, bparams, result) =>
      vparams.map(t => type_occurrences(t)).flatten() +
      result.map(t => type_occurrences(t)).flatten() +
      bparams.map(b => block_type_occurrences(b)).flatten()
    InterfaceType(_, targs) => block_type_occurrences_of(targs)
    PromptType(answer) => block_type_occurrences_of(answer)
    ResumeType(result, answer) =>
      block_type_occurrences_of(result) + block_type_occurrences_of(answer)
  }
}

///|
/// The value types occurring inside function types (upstream
/// `ArityRaising.underFunctions`).
fn under_functions(tpe : ValueType) -> Array[ValueType] {
  type_occurrences(tpe)
  .filter_map(occurrence => {
    match occurrence {
      ValueBoxed(block, _) => Some(block_type_occurrences(block))
      _ => None
    }
  })
  .flatten()
}

///|
/// Whether the type variable `t` occurs in `tpe` (upstream
/// `ArityRaising.mentions`).
fn type_mentions(tpe : ValueType, t : Sym) -> Bool {
  type_occurrences(tpe).contains(ValueVar(t))
}

///|
/// `T` directly under a container, i.e. `A[T]` with `A` in {`Array`, `Ref`}
/// (upstream `componentwise`'s `underContainer`).
fn is_under_container(
  tpe : ValueType,
  t : Sym,
  containers : Array[Sym],
) -> Bool {
  match tpe {
    ValueData(a, targs) =>
      targs.length() == 1 && containers.contains(a) && targs[0] == ValueVar(t)
    _ => false
  }
}

///|
/// The elements of `xs` without duplicates, keeping the first occurrence.
fn dedup_types(xs : Array[ValueType]) -> Array[ValueType] {
  let out : Array[ValueType] = []
  for x in xs {
    if !out.contains(x) {
      out.push(x)
    }
  }
  out
}

///|
/// The elements of `xs` without duplicates, keeping the first occurrence.
fn dedup_ids(xs : Array[Sym]) -> Array[Sym] {
  let out : Array[Sym] = []
  for x in xs {
    if !out.contains(x) {
      out.push(x)
    }
  }
  out
}

// ---------------------------------------------------------------------------
// The analysis
// ---------------------------------------------------------------------------

///|
/// The type-level part of an extern definition: what the analysis and the
/// rewriting need to instantiate the signature at a call site.
priv struct ExternSig {
  tparams : Array[Sym]
  cparams : Array[Sym]
  vparams : Array[ValueType]
  bparams : Array[BlockType]
  ret : ValueType
}

///|
/// A call to an extern (upstream `ArityRaising.CallSite`).
priv struct ExternCallSite {
  f : ExternSig
  targs : Array[ValueType]
  /// Whether the call is in control position (a `Stmt.App`). Such a call hands
  /// the result back through a continuation, so its result is not a boundary.
  control : Bool
}

///|
/// The module-wide analysis (upstream's `callSites`, `interfaceArguments` and
/// `matched`, collected by `visitAll`).
priv struct ArAnalysis {
  /// uid -> the signature of the extern.
  externs : Map[Int32, ExternSig]
  call_sites : Array[ExternCallSite]
  interface_arguments : Array[ValueType]
  matched : Array[ValueType]
}

///|
/// The signatures of the module's externs, keyed by uid.
fn extern_signatures(module : ModuleDecl) -> Map[Int32, ExternSig] {
  let out : Map[Int32, ExternSig] = Map([])
  for e in module.externs {
    match e {
      ExternDef(id, _, tparams, cparams, vparams, bparams, ret, _, _) =>
        out.set(id.uid(), {
          tparams,
          cparams,
          vparams: vparams.map(p => p.tpe),
          bparams: bparams.map(p => p.tpe),
          ret,
        })
      _ => ()
    }
  }
  out
}

///|
/// `f` instantiated with the type arguments of a call (upstream
/// `ArityRaising.signature`). The capture arguments are the extern's own capture
/// parameters, i.e. the identity substitution.
fn extern_signature(
  f : ExternSig,
  targs : ArrayView[ValueType],
) -> BlockType raise EffektError {
  let tpe = FunctionType(
    f.tparams,
    f.cparams.map(c => CaptureSetOf([c])),
    f.vparams,
    f.bparams,
    [f.ret],
  )
  instantiate(tpe, targs, f.cparams.map(c => CaptureSetOf([c])))
}

///|
/// The types at the boundary of an extern call; block parameters count as
/// (boxed) functions (upstream `ArityRaising.boundary`).
fn boundary(site : ExternCallSite) -> Array[ValueType] raise EffektError {
  match extern_signature(site.f, site.targs) {
    FunctionType(_, _, vparams, bparams, result) =>
      vparams + result + bparams.map(b => ValueBoxed(b, Captures::empty()))
    _ =>
      raise EffektError::Internal(
        "Extern signature is not a function type: \{site.f.ret}",
      )
  }
}

///|
/// An extern `f[T]` is componentwise if it has no block parameters, and `T` only
/// occurs bare or directly under a container, at least once under a container. By
/// parametricity such an extern commutes with unzipping `A[(T₁, …, Tₙ)]` into
/// `(A[T₁], …, A[Tₙ])`; it is then called once per component. Externs that
/// mention `T` only bare (like `genericEquals[T](x: T, y: T)`) may inspect their
/// arguments and are not componentwise.
fn is_componentwise(f : ExternSig, containers : Array[Sym]) -> Bool {
  if f.tparams.length() != 1 || !f.bparams.is_empty() {
    return false
  }
  let t = f.tparams[0]
  let tpes = [f.ret] + f.vparams
  let allowed = tpes.all(tpe => {
    tpe == ValueVar(t) ||
    is_under_container(tpe, t, containers) ||
    !type_mentions(tpe, t)
  })
  allowed && tpes.any(tpe => is_under_container(tpe, t, containers))
}

///|
/// The element type, if the call can be translated componentwise (upstream
/// `componentwiseElement`).
fn componentwise_element(
  f : ExternSig,
  targs : ArrayView[ValueType],
  containers : Array[Sym],
  frozen : Array[ValueType],
) -> ValueType? {
  if targs.length() != 1 || !is_componentwise(f, containers) {
    return None
  }
  let u = targs[0]
  let instances : Array[ValueType] = []
  for tpe in [f.ret] + f.vparams {
    match tpe {
      ValueData(a, targs) =>
        if targs.length() == 1 && containers.contains(a) {
          match targs[0] {
            ValueVar(_) => instances.push(ValueData(a, [u]))
            _ => ()
          }
        }
      _ => ()
    }
  }
  if instances.any(i => frozen.contains(i)) {
    None
  } else {
    Some(u)
  }
}

///|
/// Collects the module-wide analysis (upstream's `visitAll(m.definitions)`).
fn analyse(module : ModuleDecl) -> ArAnalysis raise EffektError {
  let analysis : ArAnalysis = {
    externs: extern_signatures(module),
    call_sites: [],
    interface_arguments: [],
    matched: [],
  }
  for definition in module.definitions {
    match definition {
      ToplevelDef(_, block) => analysis.visit_block(block)
      ToplevelVal(_, binding) => analysis.visit_stmt(binding)
    }
  }
  analysis
}

///|
fn ArAnalysis::visit_block(
  self : ArAnalysis,
  block : Block,
) -> Unit raise EffektError {
  match block {
    BlockVar(bv) => self.visit_block_type(bv.annotated_tpe)
    BlockLit(lit) => self.visit_block_lit(lit)
    Unbox(e) => self.visit_expr(e)
    New(implementation) => {
      self.visit_block_type(implementation.interface)
      for operation in implementation.operations {
        self.visit_operation(operation)
      }
    }
  }
}

///|
fn ArAnalysis::visit_block_lit(
  self : ArAnalysis,
  lit : BlockLit,
) -> Unit raise EffektError {
  for p in lit.vparams {
    self.visit_value_type(p.tpe)
  }
  for p in lit.bparams {
    self.visit_block_type(p.tpe)
  }
  self.visit_stmt(lit.body)
}

///|
fn ArAnalysis::visit_operation(
  self : ArAnalysis,
  operation : Operation,
) -> Unit raise EffektError {
  for p in operation.vparams {
    self.visit_value_type(p.tpe)
  }
  for p in operation.bparams {
    self.visit_block_type(p.tpe)
  }
  self.visit_stmt(operation.body)
}

///|
fn ArAnalysis::visit_stmt(
  self : ArAnalysis,
  s : Stmt,
) -> Unit raise EffektError {
  match s {
    Def(_, block, body) => {
      self.visit_block(block)
      self.visit_stmt(body)
    }
    Let(_, binding, body) => {
      self.visit_expr(binding)
      self.visit_stmt(body)
    }
    ImpureApp(_, callee, targs, vargs, bargs, body) => {
      match self.externs.get(callee.id.uid()) {
        Some(f) => self.call_sites.push({ f, targs, control: false, })
        None => ()
      }
      self.visit_block_type(callee.annotated_tpe)
      for t in targs {
        self.visit_value_type(t)
      }
      for e in vargs {
        self.visit_expr(e)
      }
      for b in bargs {
        self.visit_block(b)
      }
      self.visit_stmt(body)
    }
    Return(exprs) =>
      for e in exprs {
        self.visit_expr(e)
      }
    Val(_, binding, body) => {
      self.visit_stmt(binding)
      self.visit_stmt(body)
    }
    App(callee, targs, vargs, bargs) => {
      match callee {
        BlockVar(bv) =>
          match self.externs.get(bv.id.uid()) {
            Some(f) => self.call_sites.push({ f, targs, control: true, })
            None => ()
          }
        _ => ()
      }
      self.visit_block(callee)
      for t in targs {
        self.visit_value_type(t)
      }
      for e in vargs {
        self.visit_expr(e)
      }
      for b in bargs {
        self.visit_block(b)
      }
    }
    Invoke(callee, _, method_tpe, targs, vargs, bargs) => {
      self.visit_block(callee)
      self.visit_block_type(method_tpe)
      for t in targs {
        self.visit_value_type(t)
      }
      for e in vargs {
        self.visit_expr(e)
      }
      for b in bargs {
        self.visit_block(b)
      }
    }
    If(cond, thn, els) => {
      self.visit_expr(cond)
      self.visit_stmt(thn)
      self.visit_stmt(els)
    }
    Match(scrutinee, tpes, clauses, default) => {
      self.matched.push(scrutinee.infer_type())
      self.visit_expr(scrutinee)
      for t in tpes {
        self.visit_value_type(t)
      }
      for clause in clauses {
        self.visit_block_lit(clause.body)
      }
      match default {
        Some(body) => self.visit_stmt(body)
        None => ()
      }
    }
    Region(lit) => self.visit_block_lit(lit)
    Alloc(_, init, _, body) => {
      self.visit_expr(init)
      self.visit_stmt(body)
    }
    Var(_, init, _, body) => {
      self.visit_expr(init)
      self.visit_stmt(body)
    }
    Get(_, tpe, _, _, body) => {
      self.visit_value_type(tpe)
      self.visit_stmt(body)
    }
    Put(_, _, value, body) => {
      self.visit_expr(value)
      self.visit_stmt(body)
    }
    Reset(lit) => self.visit_block_lit(lit)
    Shift(prompt, k, body) => {
      self.visit_block_type(prompt.annotated_tpe)
      self.visit_block_type(k.tpe)
      self.visit_stmt(body)
    }
    Resume(k, body) => {
      self.visit_block_type(k.annotated_tpe)
      self.visit_stmt(body)
    }
    Hole(tpes, _) =>
      for t in tpes {
        self.visit_value_type(t)
      }
  }
}

///|
fn ArAnalysis::visit_expr(
  self : ArAnalysis,
  e : Expr,
) -> Unit raise EffektError {
  match e {
    ValueVar(_, tpe) => self.visit_value_type(tpe)
    Literal(_, tpe) => self.visit_value_type(tpe)
    PureApp(callee, targs, vargs) => {
      match self.externs.get(callee.id.uid()) {
        Some(f) => self.call_sites.push({ f, targs, control: false, })
        None => ()
      }
      self.visit_block_type(callee.annotated_tpe)
      for t in targs {
        self.visit_value_type(t)
      }
      for e in vargs {
        self.visit_expr(e)
      }
    }
    Make(data, _, targs, vargs) => {
      self.visit_value_type(data)
      for t in targs {
        self.visit_value_type(t)
      }
      for e in vargs {
        self.visit_expr(e)
      }
    }
    Box(b, _) => self.visit_block(b)
  }
}

///|
fn ArAnalysis::visit_value_type(
  self : ArAnalysis,
  tpe : ValueType,
) -> Unit raise EffektError {
  match tpe {
    ValueVar(_) => ()
    ValueData(_, targs) =>
      for t in targs {
        self.visit_value_type(t)
      }
    ValueBoxed(b, _) => self.visit_block_type(b)
  }
}

///|
fn ArAnalysis::visit_block_type(
  self : ArAnalysis,
  tpe : BlockType,
) -> Unit raise EffektError {
  match tpe {
    FunctionType(_, _, vparams, bparams, result) => {
      for t in vparams {
        self.visit_value_type(t)
      }
      for b in bparams {
        self.visit_block_type(b)
      }
      for t in result {
        self.visit_value_type(t)
      }
    }
    InterfaceType(_, targs) => {
      for t in targs {
        self.interface_arguments.push(t)
      }
      for t in targs {
        self.visit_value_type(t)
      }
    }
    PromptType(answer) =>
      for t in answer {
        self.visit_value_type(t)
      }
    ResumeType(result, answer) => {
      for t in result {
        self.visit_value_type(t)
      }
      for t in answer {
        self.visit_value_type(t)
      }
    }
  }
}

// ---------------------------------------------------------------------------
// The environment
// ---------------------------------------------------------------------------

///|
/// The translation environment (upstream `Raise.Env`): the value variables that
/// have been split into components, and the references that have been split into
/// one reference per component.
priv struct Env {
  /// uid -> the components a value variable stands for.
  values : Map[Int32, Array[Expr]]
  /// uid -> the references a split reference stands for.
  refs : Map[Int32, Array[Sym]]
}

///|
fn Env::empty() -> Env {
  { values: Map([]), refs: Map([]), }
}

///|
fn Env::bound_value(self : Env, id : Sym) -> Array[Expr]? {
  self.values.get(id.uid())
}

///|
fn Env::bound_ref(self : Env, id : Sym) -> Array[Sym]? {
  self.refs.get(id.uid())
}

///|
/// `env + (id -> exprs)` (upstream `Env.bind` on a list of expressions).
fn Env::bind_exprs(self : Env, id : Sym, exprs : Array[Expr]) -> Env {
  let values = self.values.copy()
  values.set(id.uid(), exprs)
  { values, refs: self.refs, }
}

///|
/// `env + (id -> components)` (upstream `Env.bind`).
fn Env::bind_value(self : Env, id : Sym, params : ArrayView[ValueParam]) -> Env {
  self.bind_exprs(id, params.map(p => ValueVar(p.id, p.tpe)))
}

///|
/// Binds each of the `ids` to the components of the corresponding parameter list
/// (upstream `Env.bind(ids, params)`).
fn Env::bind_values(
  self : Env,
  ids : ArrayView[Sym],
  params : ArrayView[Array[ValueParam]],
) -> Env {
  let mut env = self
  for i in 0..<ids.length() {
    env = env.bind_value(ids[i], params[i])
  }
  env
}

///|
/// `env + (id -> refs)` (upstream `Env.bindRef`).
fn Env::bind_ref(self : Env, id : Sym, refs : Array[Sym]) -> Env {
  let bound = self.refs.copy()
  bound.set(id.uid(), refs)
  { values: self.values, refs: bound, }
}

///|
/// Binds the state parameters to their components (upstream `Env.bindRefs`): a
/// `State[T]` block parameter is split into one `State[Tᵢ]` per component, all
/// other parameters are left alone.
fn Env::bind_refs(
  self : Env,
  bparams : ArrayView[BlockParam],
  components : ArrayView[Array[BlockParam]],
) -> Env {
  let mut env = self
  for i in 0..<bparams.length() {
    if i < components.length() && t_state_extract(bparams[i].tpe) is Some(_) {
      env = env.bind_ref(bparams[i].id, components[i].map(p => p.id))
    }
  }
  env
}

// ---------------------------------------------------------------------------
// The transformation
// ---------------------------------------------------------------------------

///|
/// The state of one arity-raising run: the module's externs, the containers, the
/// frozen types, the record constructors and the flat types (upstream the fields
/// of `Raise`).
priv struct Raise {
  externs : Map[Int32, ExternSig]
  containers : Array[Sym]
  frozen : Array[ValueType]
  /// uid -> the (single) constructor of a record type.
  records : Map[Int32, Constructor]
  flat : Array[Sym]
  toplevel : Env
}

///|
/// The constructor of a record type; only called for flat types, i.e. types that
/// the analysis has put into `records`.
/// The (single) constructor of a record type. Only flat types are asked for
/// their constructor, and those are exactly the types with an entry in `records`.
fn Raise::record_unchecked(self : Raise, id : Sym) -> Constructor {
  self.records.get(id.uid()).unwrap()
}

///|
fn Raise::extern_of(self : Raise, id : Sym) -> ExternSig raise EffektError {
  match self.externs.get(id.uid()) {
    Some(f) => f
    None => raise EffektError::Internal("Call of \{id}, which is not an extern")
  }
}

///|
/// `A[T]` with `A` in {`Array`, `Ref`} (upstream `isContainer`).
fn Raise::is_container(self : Raise, tpe : ValueType) -> Bool {
  match tpe {
    ValueData(a, targs) => targs.length() == 1 && self.containers.contains(a)
    _ => false
  }
}

///|
fn Raise::is_flat(self : Raise, tpe : ValueType) -> Bool {
  match tpe {
    ValueData(id, targs) => targs.is_empty() && self.flat.contains(id)
    _ => false
  }
}

///|
/// The representation of a value type (upstream `Raise.repr`).
fn Raise::repr_value(self : Raise, tpe : ValueType) -> Array[ValueType] {
  match tpe {
    ValueData(id, targs) =>
      if targs.is_empty() && self.flat.contains(id) {
        self.record_unchecked(id).fields
        .map(f => self.repr_value(f.tpe))
        .flatten()
      } else if self.is_container(tpe) && !self.frozen.contains(tpe) {
        self.repr_value(targs[0]).map(u => ValueData(id, [u]))
      } else {
        [tpe]
      }
    ValueBoxed(block, capt) => [ValueBoxed(self.repr_block_type(block), capt)]
    other => [other]
  }
}

///|
/// The representation of a block type (upstream `Raise.repr` on `BlockType`).
fn Raise::repr_block_type(self : Raise, tpe : BlockType) -> BlockType {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result) => {
      let components = bparams.map(b => self.reprs(b))
      FunctionType(
        tparams,
        captures_sets(cparams, components),
        repr_values(self, vparams),
        components.flatten(),
        repr_values(self, result),
      )
    }
    // An interface keeps its type (upstream: `case BlockType.Interface(_, _) =>
    // tpe`); which instantiations exist is the business of the callee, and the
    // type arguments are frozen.
    InterfaceType(_, _) => tpe
    PromptType(answer) => PromptType(repr_values(self, answer))
    ResumeType(result, answer) =>
      ResumeType(repr_values(self, result), repr_values(self, answer))
  }
}

///|
/// `es.flatMap(repr)` (upstream `repr` on a list).
fn repr_values(raiser : Raise, tpes : ArrayView[ValueType]) -> Array[ValueType] {
  tpes.map(t => raiser.repr_value(t)).flatten()
}

///|
/// The representation of a block type as a list: a `State[T]` becomes one
/// `State[Tᵢ]` per component of `T` (upstream `Raise.reprs`).
fn Raise::reprs(self : Raise, tpe : BlockType) -> Array[BlockType] {
  match t_state_extract(tpe) {
    Some(t) => self.repr_value(t).map(u => t_state(u))
    None => [self.repr_block_type(tpe)]
  }
}

///|
/// One capture per component (upstream `Raise.captures`): `cparams` and the block
/// parameters line up, and each block parameter that is split into `n` components
/// repeats its capture `n` times.
fn captures_sets(
  cparams : ArrayView[Captures],
  components : Array[Array[BlockType]],
) -> Array[Captures] {
  cparams.zip(components).map(pair => pair.1.map(_ => pair.0)).flatten()
}

///|
/// `captures_sets` for the id-valued capture parameters of a block literal or an
/// operation.
fn captures_ids(
  cparams : ArrayView[Sym],
  components : Array[Array[BlockParam]],
) -> Array[Sym] {
  cparams.zip(components).map(pair => pair.1.map(_ => pair.0)).flatten()
}

///|
/// A fresh symbol named after `id`, with `_<i>` appended.
fn suffixed_id(id : Sym, i : Int32) -> Sym {
  Sym::id(id.name().rename(n => "\{n}_\{i}"))
}

///|
/// The binders for a value of type `tpe` (upstream `Raise.binders`): one binder
/// with the original id if the representation is a single value, one `<name>_<i>`
/// per component otherwise.
fn Raise::binders(self : Raise, id : Sym, tpe : ValueType) -> Array[ValueParam] {
  let components = self.repr_value(tpe)
  if components.length() == 1 {
    [ValueParam(id, components[0])]
  } else {
    components.mapi((i, t) => ValueParam(suffixed_id(id, i), t))
  }
}

///|
/// The fields of a record type, pointwise (upstream `Raise.fields`).
fn Raise::fields(self : Raise, f : Field) -> Array[Field] {
  self.binders(f.id, f.tpe).map(p => Field(p.id, p.tpe))
}

///|
/// A short description of an expression, for internal error messages.
fn describe_expr(e : Expr) -> String {
  match e {
    ValueVar(id, tpe) => "\{id} : \{tpe}"
    Literal(_, tpe) => "a literal : \{tpe}"
    PureApp(callee, targs, _) =>
      "the pure call \{callee.id}[\{targs.map(t => "\{t}").join(", ")}]"
    Make(data, tag, _, vargs) =>
      "the constructor \{tag} of \{data} (\{vargs.map(x => describe_expr(x)).join("; ")})"
    Box(block, _) => "a boxed block \{block.infer_type_or_unknown()}"
  }
}

///|
/// The single component of an expression list (upstream `Raise.single`).
fn one_component(es : Array[Expr]) -> Expr raise EffektError {
  if es.length() == 1 {
    return es[0]
  }
  raise EffektError::Internal(
    "Expected a single component, but got \{es.length()}",
  )
}

///|
/// The original representation of a value, given its components (upstream
/// `Raise.pack`).
fn Raise::pack(
  self : Raise,
  tpe : ValueType,
  es : Array[Expr],
) -> Expr raise EffektError {
  if self.is_flat(tpe) {
    let data = match tpe {
      ValueData(id, _) => id
      _ => raise EffektError::Internal("A flat type is not a data type: \{tpe}")
    }
    Make(tpe, self.record_unchecked(data).id, [], es)
  } else {
    one_component(es)
  }
}

///|
/// The components of a value in the original representation (upstream
/// `Raise.open`): a flat record is opened with a match on its single constructor,
/// whose clause parameters are the components.
fn Raise::open(
  self : Raise,
  e : Expr,
  tpe : ValueType,
) -> Bind[Array[Expr]] raise EffektError {
  if !self.is_flat(tpe) {
    return Bind::pure([e])
  }
  let data = match tpe {
    ValueData(id, _) => id
    _ => raise EffektError::Internal("A flat type is not a data type: \{tpe}")
  }
  let ctor = self.record_unchecked(data)
  let params : Array[ValueParam] = []
  for f in ctor.fields {
    let field_id = Sym::id(f.id.name())
    params.append(self.binders(field_id, f.tpe))
  }
  // Upstream `params.map(p => ValueParam(Id(p.id), p.tpe))`: the bound results are
  // *fresh* symbols with the parameters' names. Sharing the symbols with the
  // clause's parameters would make the normalizer record `val x = x` for the
  // clause's `return x`, and its dealiasing would not terminate.
  let results = params.map(p => ValueParam(Sym::id(p.id.name()), p.tpe))
  let no_tparams : Array[Sym] = []
  let no_cparams : Array[Sym] = []
  let no_bparams : Array[BlockParam] = []
  let clause = BlockLit::BlockLit(
    no_tparams,
    no_cparams,
    params,
    no_bparams,
    Return(params.map(p => ValueVar(p.id, p.tpe))),
  )
  {
    value: results.map(p => ValueVar(p.id, p.tpe)),
    bindings: [
      BindingVal(
        results.map(p => p.id),
        Match(e, results.map(p => p.tpe), [Clause(ctor.id, clause)], None),
      ),
    ],
  }
}

///|
/// `let` bindings for the components (upstream `Raise.lets`).
fn component_lets(
  context : String,
  params : ArrayView[ValueParam],
  es : ArrayView[Expr],
  body : Stmt,
) -> Stmt raise EffektError {
  if params.length() != es.length() {
    let expected = params.map(p => "\{p.tpe}").join(", ")
    raise EffektError::Internal(
      "Wrong number of components in \{context}: expected \{params.length()} (\{expected}), got \{es.length()}",
    )
  }

  params
  .zip(es)
  .rev_fold(init=body, (rest, pair) => Let(pair.0.id, pair.1, rest))
}

///|
/// The references a split allocation stands for (upstream `Raise.references`).
fn component_refs(id : Sym, n : Int32) -> Array[Sym] {
  if n == 1 {
    [id]
  } else {
    Array::makei(n, i => suffixed_id(id, i))
  }
}

///|
/// The result type of an extern call (upstream `ArityRaising.result`).
fn extern_result(
  f : ExternSig,
  targs : ArrayView[ValueType],
) -> ValueType raise EffektError {
  match extern_signature(f, targs) {
    FunctionType(_, _, _, _, result) => single(result)
    _ =>
      raise EffektError::Internal(
        "Extern signature is not a function type: \{f.ret}",
      )
  }
}

// ---------------------------------------------------------------------------
// Bind combinators that may fail
// ---------------------------------------------------------------------------
//
// Upstream's `Bind` combinators take pure functions, because `Type.inferType` is
// total there. In this port the type inference can fail, so the combinators that
// are used with a raising function get a variant here instead of being changed
// in `bind.mbt`.

///|
/// `Bind::run` with a raising continuation.
fn[A] run_raise(
  b : Bind[A],
  f : (A) -> Stmt raise EffektError,
) -> Stmt raise EffektError {
  bindings_to_stmt(b.bindings, f(b.value))
}

///|
/// `Bind::map` with a raising function.
fn[A, B] map_raise(
  b : Bind[A],
  f : (A) -> B raise EffektError,
) -> Bind[B] raise EffektError {
  { value: f(b.value), bindings: b.bindings, }
}

///|
/// `Bind::flat_map` with a raising function.
fn[A, B] flat_map_raise(
  b : Bind[A],
  f : (A) -> Bind[B] raise EffektError,
) -> Bind[B] raise EffektError {
  let other = f(b.value)
  { value: other.value, bindings: b.bindings + other.bindings, }
}

///|
/// `Bind::traverse` with a raising function.
fn[S, T] traverse_raise(
  xs : ArrayView[S],
  f : (S) -> Bind[T] raise EffektError,
) -> Bind[Array[T]] raise EffektError {
  let values : Array[T] = []
  let bindings : Array[Binding] = []
  for x in xs {
    let b = f(x)
    values.push(b.value)
    bindings.append(b.bindings)
  }
  { value: values, bindings, }
}

///|
/// The first element, if any (upstream `calls.take(1)`).
fn[T] take_one(xs : Array[T]) -> Array[T] {
  if xs.is_empty() {
    []
  } else {
    [xs[0]]
  }
}

///|
/// The last element, if any (upstream `List(results.last)`).
fn[T] take_last(xs : Array[T]) -> Array[T] {
  if xs.is_empty() {
    []
  } else {
    [xs[xs.length() - 1]]
  }
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

///|
/// Translates an expression into its components (upstream `Raise.expr`).
fn Raise::expr(
  self : Raise,
  env : Env,
  e : Expr,
) -> Bind[Array[Expr]] raise EffektError {
  match e {
    ValueVar(id, tpe) =>
      match env.bound_value(id) {
        Some(es) => Bind::pure(es)
        // a toplevel value keeps the original representation
        None => self.open(e, tpe)
      }
    Literal(_, _) => Bind::pure([e])
    PureApp(callee, targs, vargs) => self.pure_call(env, callee, targs, vargs)
    Make(data, tag, targs, vargs) =>
      map_raise(self.exprs(env, vargs), es => {
        if self.is_flat(data) {
          es
        } else {
          [Make(data, tag, targs, es)]
        }
      })
    Box(block, capt) => Bind::pure([Box(self.block(env, block), capt)])
  }
}

///|
/// Translates a list of expressions, concatenating their components (upstream
/// `Raise.exprs`).
fn Raise::exprs(
  self : Raise,
  env : Env,
  es : ArrayView[Expr],
) -> Bind[Array[Expr]] raise EffektError {
  map_raise(traverse_raise(es, e => self.expr(env, e)), xs => xs.flatten())
}

///|
/// The arguments of an extern call, with the records among them packed
/// (upstream `Raise.packed`).
fn Raise::packed(
  self : Raise,
  env : Env,
  f : ExternSig,
  vargs : ArrayView[Expr],
) -> Bind[Array[Expr]] raise EffektError {
  let vparams = f.vparams
  map_raise(self.argument_components(env, vargs), args => {
    let out : Array[Expr] = []
    for i in 0..<args.length() {
      let tpe = if i < vparams.length() {
        vparams[i]
      } else {
        raise EffektError::Internal(
          "More arguments than value parameters in an extern call",
        )
      }
      out.push(self.pack(tpe, args[i]))
    }
    out
  })
}

///|
/// The arguments of the `j`-th componentwise call: the arguments whose parameter
/// mentions the type parameter contribute their `j`-th component, all others are
/// packed (upstream `Raise.componentArguments`).
fn Raise::component_arguments(
  self : Raise,
  f : ExternSig,
  args : ArrayView[Array[Expr]],
  n : Int32,
) -> Array[Array[Expr]] raise EffektError {
  let t = f.tparams[0]
  let out : Array[Array[Expr]] = []
  for j in 0..<n {
    let call : Array[Expr] = []
    for i in 0..<f.vparams.length() {
      let es = args[i]
      let p = f.vparams[i]
      if type_mentions(p, t) {
        if j >= es.length() {
          raise EffektError::Internal(
            "Argument of a componentwise extern call has too few components",
          )
        }
        call.push(es[j])
      } else {
        call.push(self.pack(p, es))
      }
    }
    out.push(call)
  }
  out
}

///|
/// The translated arguments, one component list per argument (upstream
/// `Bind.traverse(vargs)(expr)`).
fn Raise::argument_components(
  self : Raise,
  env : Env,
  vargs : ArrayView[Expr],
) -> Bind[Array[Array[Expr]]] raise EffektError {
  traverse_raise(vargs, e => self.expr(env, e))
}

///|
/// The componentwise translation of a pure extern call (upstream the first case
/// of `Raise.pureCall`).
fn Raise::componentwise_pure_call(
  self : Raise,
  env : Env,
  f : ExternSig,
  callee : BlockVar,
  vargs : ArrayView[Expr],
  u : ValueType,
) -> Bind[Array[Expr]] raise EffektError {
  let components = self.repr_value(u)
  map_raise(self.argument_components(env, vargs), args => {
    let arguments = self.component_arguments(f, args, components.length())
    let calls : Array[Expr] = []
    for j in 0..<components.length() {
      calls.push(PureApp(callee, [components[j]], arguments[j]))
    }
    // upstream `if mentions(f.ret, f.tparams.head) then calls else calls.take(1)`
    if type_mentions(f.ret, f.tparams[0]) {
      calls
    } else {
      take_one(calls)
    }
  })
}

///|
/// The componentwise translation of an impure extern call (upstream the first
/// case of `Raise.impureCall`).
fn Raise::componentwise_impure_call(
  self : Raise,
  env : Env,
  f : ExternSig,
  callee : BlockVar,
  vargs : ArrayView[Expr],
  u : ValueType,
) -> Bind[Array[Expr]] raise EffektError {
  let components = self.repr_value(u)
  flat_map_raise(self.argument_components(env, vargs), args => {
    let arguments = self.component_arguments(f, args, components.length())
    let calls : Array[Bind[Expr]] = []
    for j in 0..<components.length() {
      calls.push(Bind::bind_app(callee, [components[j]], arguments[j], []))
    }
    map_raise(traverse_raise(calls, b => b), results => {
      // upstream `if mentions(f.ret, f.tparams.head) then results else
      // List(results.last)` — the impure case keeps the *last* of the
      // per-component calls, the pure case above keeps the first
      if type_mentions(f.ret, f.tparams[0]) {
        results
      } else {
        take_last(results)
      }
    })
  })
}

///|
/// Translates a pure extern call (upstream `Raise.pureCall`).
fn Raise::pure_call(
  self : Raise,
  env : Env,
  callee : BlockVar,
  targs : ArrayView[ValueType],
  vargs : ArrayView[Expr],
) -> Bind[Array[Expr]] raise EffektError {
  let f = self.extern_of(callee.id)
  match componentwise_element(f, targs, self.containers, self.frozen) {
    Some(u) => self.componentwise_pure_call(env, f, callee, vargs, u)
    None =>
      flat_map_raise(self.packed(env, f, vargs), arguments => {
        let call = PureApp(callee, targs.to_owned(), arguments)
        self.open(call, extern_result(f, targs))
      })
  }
}

///|
/// Translates an impure extern call (upstream `Raise.impureCall`).
fn Raise::impure_call(
  self : Raise,
  env : Env,
  callee : BlockVar,
  targs : ArrayView[ValueType],
  vargs : ArrayView[Expr],
  bargs : ArrayView[Block],
) -> Bind[Array[Expr]] raise EffektError {
  let f = self.extern_of(callee.id)
  match componentwise_element(f, targs, self.containers, self.frozen) {
    Some(u) => self.componentwise_impure_call(env, f, callee, vargs, u)
    None =>
      flat_map_raise(self.packed(env, f, vargs), arguments => {
        let blocks : Array[Block] = []
        for b in bargs {
          blocks.push(self.block(env, b))
        }
        flat_map_raise(Bind::bind_app(callee, targs, arguments, blocks), v => {
          self.open(v, extern_result(f, targs))
        })
      })
  }
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
/// Translates a statement (upstream `Raise.stmt`).
fn Raise::stmt(self : Raise, env : Env, s : Stmt) -> Stmt raise EffektError {
  match s {
    Def(id, block, body) =>
      // `def id = <split reference>; body`: the definition is an alias for the
      // components of the reference, so it is dropped and the environment
      // remembers them.
      match block {
        BlockVar(bv) =>
          match env.bound_ref(bv.id) {
            Some(refs) => self.stmt(env.bind_ref(id, refs), body)
            None => Def(id, self.block(env, block), self.stmt(env, body))
          }
        _ => Def(id, self.block(env, block), self.stmt(env, body))
      }
    Let(id, e, body) =>
      run_raise(self.expr(env, e), es => {
        let params = self.binders(id, e.infer_type())
        component_lets(
          "let \{id} = \{describe_expr(e)}",
          params,
          es,
          self.stmt(env.bind_value(id, params), body),
        )
      })
    ImpureApp(id, callee, targs, vargs, bargs, body) =>
      run_raise(self.impure_call(env, callee, targs, vargs, bargs), es => {
        let tpe = extern_result(self.extern_of(callee.id), targs)
        let params = self.binders(id, tpe)
        component_lets(
          "call \{id}",
          params,
          es,
          self.stmt(env.bind_value(id, params), body),
        )
      })
    Return(exprs) => run_raise(self.exprs(env, exprs), es => Return(es))
    Val(ids, binding, body) => {
      let tpes = binding.infer_type()
      if tpes.length() != ids.length() {
        raise EffektError::Internal(
          "A val binds \{ids.length()} values, but its binding returns \{tpes.length()}",
        )
      }
      let params : Array[Array[ValueParam]] = []
      for i in 0..<ids.length() {
        params.push(self.binders(ids[i], tpes[i]))
      }
      let bound : Array[Sym] = []
      for components in params {
        for p in components {
          bound.push(p.id)
        }
      }
      Val(
        bound,
        self.stmt(env, binding),
        self.stmt(env.bind_values(ids, params), body),
      )
    }
    App(callee, targs, vargs, bargs) =>
      match callee {
        // a control call of an extern: the extern sees packed arguments, the
        // continuation the components of the original result
        BlockVar(bv) =>
          match self.externs.get(bv.id.uid()) {
            Some(f) =>
              run_raise(self.packed(env, f, vargs), arguments => {
                let tmp = Sym::id(Name::local("tmp"))
                let tpe = extern_result(f, targs)
                let blocks : Array[Block] = []
                for b in bargs {
                  blocks.push(self.block(env, b))
                }
                let opened = self.open(ValueVar(tmp, tpe), tpe)
                Val(
                  [tmp],
                  App(Block::BlockVar(bv), targs, arguments, blocks),
                  run_raise(opened, es => Return(es)),
                )
              })
            None => self.app_generic(env, callee, targs, vargs, bargs)
          }
        _ => self.app_generic(env, callee, targs, vargs, bargs)
      }
    Invoke(callee, method, method_tpe, targs, vargs, bargs) =>
      run_raise(self.exprs(env, vargs), vs => {
        let blocks : Array[Block] = []
        for b in bargs {
          for block in self.blocks(env, b) {
            blocks.push(block)
          }
        }
        Invoke(
          self.block(env, callee),
          method,
          self.repr_block_type(method_tpe),
          targs,
          vs,
          blocks,
        )
      })
    If(cond, thn, els) =>
      run_raise(self.expr(env, cond), cs => {
        If(one_component(cs), self.stmt(env, thn), self.stmt(env, els))
      })
    Match(scrutinee, tpes, clauses, default) => {
      let scrutinee_tpe = scrutinee.infer_type()
      let raised_tpes = repr_values(self, tpes)
      if self.is_flat(scrutinee_tpe) {
        // the scrutinee is already open: bind its components to the clause
        // parameters
        run_raise(self.expr(env, scrutinee), cs => {
          if clauses.length() == 1 {
            let lit = clauses[0].body
            let params : Array[Array[ValueParam]] = []
            for p in lit.vparams {
              params.push(self.binders(p.id, p.tpe))
            }
            let all : Array[ValueParam] = []
            for components in params {
              for p in components {
                all.push(p)
              }
            }
            component_lets(
              "val",
              all,
              cs,
              self.stmt(
                env.bind_values(lit.vparams.map(p => p.id), params),
                lit.body,
              ),
            )
          } else {
            match default {
              Some(body) => self.stmt(env, body)
              // an absurd match (no clauses, no default) keeps its scrutinee
              None => Match(self.pack(scrutinee_tpe, cs), raised_tpes, [], None)
            }
          }
        })
      } else {
        run_raise(self.expr(env, scrutinee), cs => {
          let raised_clauses : Array[Clause] = []
          for clause in clauses {
            raised_clauses.push(
              Clause(clause.tag, self.block_lit(env, clause.body)),
            )
          }
          let raised_default = match default {
            Some(body) => Some(self.stmt(env, body))
            None => None
          }
          Match(one_component(cs), raised_tpes, raised_clauses, raised_default)
        })
      }
    }
    Region(lit) => Region(self.block_lit(env, lit))
    Alloc(id, init, region, body) =>
      run_raise(self.expr(env, init), es => {
        let refs = component_refs(id, es.length())
        let rest = self.stmt(env.bind_ref(id, refs), body)
        refs
        .zip(es)
        .rev_fold(init=rest, (rest, pair) => Alloc(pair.0, pair.1, region, rest))
      })
    // all components share the capture of the original variable
    Var(ref, init, capture, body) =>
      run_raise(self.expr(env, init), es => {
        let refs = component_refs(ref, es.length())
        let rest = self.stmt(env.bind_ref(ref, refs), body)
        refs
        .zip(es)
        .rev_fold(init=rest, (rest, pair) => Var(pair.0, pair.1, capture, rest))
      })
    Get(id, tpe, ref, capt, body) => {
      let params = self.binders(id, tpe)
      let rest = self.stmt(env.bind_value(id, params), body)
      let refs = split_ref(ref, env)
      if refs.length() < params.length() {
        raise EffektError::Internal(
          "A get of \{ref} has more components than the reference",
        )
      }
      params
      .zip(refs)
      .rev_fold(init=rest, (rest, pair) => {
        Get(pair.0.id, pair.0.tpe, pair.1, capt, rest)
      })
    }
    Put(ref, capt, value, body) =>
      run_raise(self.expr(env, value), es => {
        let refs = split_ref(ref, env)
        let rest = self.stmt(env, body)
        refs
        .zip(es)
        .rev_fold(init=rest, (rest, pair) => Put(pair.0, capt, pair.1, rest))
      })
    Reset(lit) => Reset(self.block_lit(env, lit))
    Shift(prompt, k, body) =>
      Shift(self.block_var(prompt), self.block_param(k), self.stmt(env, body))
    Resume(k, body) => Resume(self.block_var(k), self.stmt(env, body))
    Hole(tpes, span) => Hole(repr_values(self, tpes), span)
  }
}

///|
/// A statement whose value is a call of a block (upstream the second half of
/// `Raise.stmt`'s `App` case).
fn Raise::app_generic(
  self : Raise,
  env : Env,
  callee : Block,
  targs : ArrayView[ValueType],
  vargs : ArrayView[Expr],
  bargs : ArrayView[Block],
) -> Stmt raise EffektError {
  run_raise(self.exprs(env, vargs), vs => {
    let blocks : Array[Block] = []
    for b in bargs {
      for block in self.blocks(env, b) {
        blocks.push(block)
      }
    }
    App(self.block(env, callee), targs.to_owned(), vs, blocks)
  })
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

///|
fn Raise::block(self : Raise, env : Env, b : Block) -> Block raise EffektError {
  match b {
    BlockVar(bv) => Block::BlockVar(self.block_var(bv))
    BlockLit(lit) => Block::BlockLit(self.block_lit(env, lit))
    Unbox(e) => {
      let translated = self.expr(env, e)
      if translated.bindings.is_empty() && translated.value.length() == 1 {
        Unbox(translated.value[0])
      } else {
        raise EffektError::Internal("Expected an atomic expression in unbox")
      }
    }
    New(implementation) => {
      let operations : Array[Operation] = []
      for operation in implementation.operations {
        operations.push(self.operation(env, operation))
      }
      New(Implementation(implementation.interface, operations))
    }
  }
}

///|
/// A block argument: a split reference contributes one argument per component
/// (upstream `Raise.blocks`).
fn Raise::blocks(
  self : Raise,
  env : Env,
  b : Block,
) -> Array[Block] raise EffektError {
  match b {
    BlockVar(bv) =>
      match env.bound_ref(bv.id) {
        Some(refs) =>
          // the references and the components line up; a shorter list of types
          // truncates, like upstream's `zip`
          refs
          .zip(self.reprs(bv.annotated_tpe))
          .map(pair => {
            Block::BlockVar(BlockVar(pair.0, pair.1, bv.annotated_capt))
          })
        None => [self.block(env, b)]
      }
    _ => [self.block(env, b)]
  }
}

///|
fn Raise::block_var(self : Raise, bv : BlockVar) -> BlockVar {
  if self.externs.contains(bv.id.uid()) {
    bv
  } else {
    BlockVar(bv.id, self.repr_block_type(bv.annotated_tpe), bv.annotated_capt)
  }
}

///|
fn Raise::block_param(self : Raise, p : BlockParam) -> BlockParam {
  BlockParam(p.id, self.repr_block_type(p.tpe), p.capt)
}

///|
/// A block parameter is split like its type: a `State[T]` becomes one parameter
/// per component of `T` (upstream `Raise.blockParams`).
fn Raise::block_params(self : Raise, p : BlockParam) -> Array[BlockParam] {
  let tpes = self.reprs(p.tpe)
  component_refs(p.id, tpes.length())
  .zip(tpes)
  .map(pair => BlockParam(pair.0, pair.1, p.capt))
}

///|
fn Raise::block_lit(
  self : Raise,
  env : Env,
  b : BlockLit,
) -> BlockLit raise EffektError {
  let params = b.vparams.map(p => self.binders(p.id, p.tpe))
  let components = b.bparams.map(p => self.block_params(p))
  let bound = env
    .bind_values(b.vparams.map(p => p.id), params)
    .bind_refs(b.bparams, components)
  BlockLit(
    b.tparams,
    captures_ids(b.cparams, components),
    params.flatten(),
    components.flatten(),
    self.stmt(bound, b.body),
  )
}

///|
fn Raise::operation(
  self : Raise,
  env : Env,
  operation : Operation,
) -> Operation raise EffektError {
  let params = operation.vparams.map(p => self.binders(p.id, p.tpe))
  let components = operation.bparams.map(p => self.block_params(p))
  let bound = env
    .bind_values(operation.vparams.map(p => p.id), params)
    .bind_refs(operation.bparams, components)
  Operation(
    operation.name,
    operation.tparams,
    captures_ids(operation.cparams, components),
    params.flatten(),
    components.flatten(),
    self.stmt(bound, operation.body),
  )
}

///|
/// The components of a split reference; every `alloc` / `var` binds its
/// components, so a missing entry is an internal error.
fn split_ref(id : Sym, env : Env) -> Array[Sym] raise EffektError {
  match env.bound_ref(id) {
    Some(refs) => refs
    None =>
      raise EffektError::Internal(
        "Reference \{id} is used before it is split into components",
      )
  }
}

// ---------------------------------------------------------------------------
// Module
// ---------------------------------------------------------------------------

///|
fn Raise::declaration(self : Raise, d : Declaration) -> Declaration {
  match d {
    DeclarationData(id, tparams, constructors) =>
      DeclarationData(
        id,
        tparams,
        constructors.map(c => {
          Constructor(
            c.id,
            c.tparams,
            c.fields.map(f => self.fields(f)).flatten(),
          )
        }),
      )
    DeclarationInterface(id, tparams, properties) =>
      DeclarationInterface(
        id,
        tparams,
        properties.map(p => Property(p.id, self.repr_block_type(p.tpe))),
      )
  }
}

///|
/// A toplevel value whose representation is a single value is translated as
/// such; a value with several components keeps the original representation and
/// is packed again (upstream `Raise.definition`).
fn Raise::definition(self : Raise, d : Toplevel) -> Toplevel raise EffektError {
  match d {
    ToplevelDef(id, block) => ToplevelDef(id, self.block(self.toplevel, block))
    ToplevelVal(id, binding) =>
      match self.toplevel.bound_value(id) {
        Some(_) => ToplevelVal(id, self.stmt(self.toplevel, binding))
        None => {
          let tpe = single(binding.infer_type())
          let params = self
            .repr_value(tpe)
            .map(t => ValueParam(Sym::id(id.name()), t))
          let ids = params.map(p => p.id)
          let components = params.map(p => Expr::ValueVar(p.id, p.tpe))
          ToplevelVal(
            id,
            Val(
              ids,
              self.stmt(self.toplevel, binding),
              Return([self.pack(tpe, components)]),
            ),
          )
        }
      }
  }
}

///|
fn Raise::module_of(
  self : Raise,
  module : ModuleDecl,
) -> ModuleDecl raise EffektError {
  let declarations : Array[Declaration] = []
  for d in module.declarations {
    declarations.push(self.declaration(d))
  }
  let definitions : Array[Toplevel] = []
  for d in module.definitions {
    definitions.push(self.definition(d))
  }
  ModuleDecl(
    module.path,
    module.includes,
    declarations,
    module.externs,
    definitions,
    module.exports,
  )
}

// ---------------------------------------------------------------------------
// The phase
// ---------------------------------------------------------------------------

///|
/// Arity raising on a module (upstream `ArityRaising.transform`): establish the
/// normal form, analyze the module, then rewrite it.
pub fn arity_raising(module : ModuleDecl) -> ModuleDecl raise EffektError {
  let module = bind_subexpressions(module)
  let analysis = analyse(module)
  // The only name-based step: the extern types of `array::Array` and `ref::Ref`.
  let containers : Array[Sym] = []
  for e in module.externs {
    match e {
      ExternData(id, tparams, _) =>
        if tparams.length() == 1 &&
          (id.name().name == "Array" || id.name().name == "Ref") {
          containers.push(id)
        }
      _ => ()
    }
  }
  // Frozen containers: those occurring at an extern boundary that is not
  // componentwise (they cannot be unzipped there), and those occurring in the
  // type arguments of an interface.
  let boundaries : Array[ValueType] = []
  for site in analysis.call_sites {
    if site.control || !is_componentwise(site.f, containers) {
      boundaries.append(boundary(site))
    }
  }
  boundaries.append(analysis.interface_arguments)
  let frozen : Array[ValueType] = []
  for tpe in boundaries {
    for occurrence in type_occurrences(tpe) {
      match occurrence {
        ValueData(a, targs) =>
          if targs.length() == 1 && containers.contains(a) {
            frozen.push(occurrence)
          }
        _ => ()
      }
    }
  }
  let frozen = dedup_types(frozen)
  let opaque : Array[ValueType] = []
  for site in analysis.call_sites {
    let componentwise = componentwise_element(
      site.f,
      site.targs,
      containers,
      frozen,
    )
    if site.control || componentwise is None {
      opaque.append(boundary(site))
    }
  }
  opaque.append(analysis.interface_arguments)
  // The record types: a single constructor with at least one field and no type
  // parameters of its own (upstream `Declaration.Data(id, Nil, List(c))`). The
  // port reaches arity raising *after* monomorphization (upstream runs `Mono`
  // later, in the backends), so every declaration here is monomorphic; the
  // condition keeps the transformation from unboxing a type it has no concrete
  // field types for.
  let records : Map[Int32, Constructor] = Map([])
  let record_list : Array[(Sym, Constructor)] = []
  let dependencies : Map[Int32, Array[Sym]] = Map([])
  for d in module.declarations {
    match d {
      DeclarationData(id, tparams, constructors) => {
        if tparams.is_empty() &&
          constructors.length() == 1 &&
          !constructors[0].fields.is_empty() {
          records.set(id.uid(), constructors[0])
          record_list.push((id, constructors[0]))
        }
        let depends : Array[Sym] = []
        for c in constructors {
          for f in c.fields {
            for occurrence in type_occurrences(f.tpe) {
              match occurrence {
                ValueData(other, _) => depends.push(other)
                _ => ()
              }
            }
          }
        }
        dependencies.set(id.uid(), dedup_ids(depends))
      }
      _ => ()
    }
  }
  let excluded : Array[Sym] = []
  for tpe in opaque {
    for occurrence in under_functions(tpe) {
      match occurrence {
        ValueData(id, _) => if !excluded.contains(id) { excluded.push(id) }
        _ => ()
      }
    }
  }
  let flat = flat_types(analysis, record_list, dependencies, excluded)

  let raiser : Raise = {
    externs: analysis.externs,
    containers,
    frozen,
    records,
    flat,
    toplevel: Env::empty(),
  }
  let toplevel = raiser.toplevel_env(module)
  let raiser = { ..raiser, toplevel, }
  let out = raiser.module_of(module)
  out
}

///|
/// The flat record types: a record that some match scrutinizes, that is not
/// recursive, and whose id does not occur under a function at an extern boundary
/// (upstream `flat`).
fn flat_types(
  analysis : ArAnalysis,
  records : ArrayView[(Sym, Constructor)],
  dependencies : Map[Int32, Array[Sym]],
  excluded : ArrayView[Sym],
) -> Array[Sym] {
  records.filter_map(pair => {
    let id = pair.0
    if !excluded.contains(id) &&
      analysis.matched.contains(ValueData(id, [])) &&
      !is_recursive(id, dependencies) {
      Some(id)
    } else {
      None
    }
  })
}

///|
/// Whether the data type (transitively) refers to itself (upstream `recursive`).
fn is_recursive(id : Sym, dependencies : Map[Int32, Array[Sym]]) -> Bool {
  let seen : Array[Sym] = []
  let stack : Array[Sym] = [id]
  while !stack.is_empty() {
    let next = stack.pop().unwrap()
    match dependencies.get(next.uid()) {
      Some(ds) =>
        for d in ds {
          if !seen.contains(d) {
            seen.push(d)
            stack.push(d)
          }
        }
      None => ()
    }
  }
  seen.contains(id)
}

///|
/// The environment of the toplevel definitions: a toplevel value whose
/// representation is a single value is translated, all others keep the original
/// representation (upstream `Raise.toplevel`).
fn Raise::toplevel_env(
  self : Raise,
  module : ModuleDecl,
) -> Env raise EffektError {
  let mut env = Env::empty()
  for d in module.definitions {
    match d {
      ToplevelVal(id, binding) => {
        let components = self.repr_value(single(binding.infer_type()))
        if components.length() == 1 {
          env = env.bind_exprs(id, [ValueVar(id, components[0])])
        }
      }
      _ => ()
    }
  }
  env
}
