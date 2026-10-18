// Structural `show` instances.
//
// Mirrors `effekt/core/Show.scala`. Walks a core module and replaces every call
// to the prelude's
//
//     extern def generated::show[R](value: R) at {}: String = js "undefined"
//
// with a call to a *structural* show definition that the compiler generates for
// the type argument of the call:
//
//     def show0(value: Int): String = { ret = showBuiltin(value); return ret }
//
// Generated definitions are cached per value type (`ShowContext`), builtin
// values are shown by the extern `showBuiltin` and the pieces of a constructor
// are concatenated with the extern `infixPlusPlus`:
//
//     def show1(value: List[Int]): String = value match {
//       case Nil()  => "Nil()"
//       case Cons(x, xs) => "Cons(" ++ show0(x) ++ ", " ++ show1(xs) ++ ")"
//     }
//
// Upstream this phase runs on the *aggregated* module, right after `Deadcode`:
//
//     Aggregate andThen Deadcode andThen core.Show andThen Optimizer andThen DropBindings
//
// `Deadcode` has to spare the three externs above (`requiredNames`); the
// backend passes them as entry points to `core.deadcode` (see `emit`).
//
// Deviations from upstream, all of them noted where they occur:
//
//   - The shown type is recovered from the *argument* of the call instead of
//     from its inferred type arguments, which do not survive
//     `ExplicitCapabilities` in this port (see `show_type_argument`), and the
//     universals of a constructor call are recovered from the fields and
//     arguments (the port's `Make` does not record them, see
//     `recover_make_type`).
//   - Calls are only rewritten when a structural instance can actually be
//     generated; a call whose type cannot be made out is left alone (and keeps
//     compiling to the extern's `undefined` body). Upstream aborts in several of
//     those cases, but it runs `Deadcode` first, which removes the unreachable
//     definitions that trigger them (see `showable_type`).
//   - Only *extern* functions named `show` are rewritten; upstream matches by
//     name only, which also catches e.g. `examples/minilib`'s
//     `def show(value: Int): String` (see `is_show_call`).
//   - The port has no warning sink, so `Context.warning` messages are dropped
//     (they concern degenerate cases only).
//   - Where upstream aborts with `Context.abort` we raise `EffektError::Fatal`,
//     for `Context.panic`/exceptions `EffektError::Internal`.
//   - The caches are keyed by a rendered key instead of by the value type
//     itself (see `value_type_key`).

///|
/// The name of the prelude's `show` extern (`generated::show`).
let show_function_name : String = "show"

///|
/// The name of the extern used to show builtin values.
let show_builtin_function_name : String = "showBuiltin"

///|
/// The name of the extern used to concatenate the generated pieces.
let show_string_concat_name : String = "infixPlusPlus"

///|
/// Names that `Deadcode` must preserve for this phase to work.
///
/// Mirrors `Show.requiredNames`; the backend passes the result to
/// `core.deadcode` as entry points (see `@backend.emit`). It is also used by the
/// tests to check the extern lookup.
pub fn required_names(module : ModuleDecl) -> Array[Sym] {
  let required : Array[String] = [
    show_function_name, show_builtin_function_name, show_string_concat_name,
  ]
  let out : Array[Sym] = []
  for e in module.externs {
    match e {
      ExternDef(id, _, _, _, _, _, _, _, _) =>
        if required.any(name => name == id.name().name) && !out.contains(id) {
          out.push(id)
        }
      _ => ()
    }
  }
  out
}

// ---------------------------------------------------------------------------
// Keys for the caches
// ---------------------------------------------------------------------------

///|
/// A structural key for a value type.
///
/// Upstream keys `showNames` and `showDefns` by `ValueType` itself, relying on
/// the structural equality of Scala case classes. MoonBit maps need a hashable
/// key and `show_core_value_type` is not injective (it prints the *names* of the
/// type constructors), so we render the type together with the uids of the
/// symbols it mentions.
///
/// NOTE: upstream compares capture sets and effect sets as *sets*; the rendered
/// key is order sensitive, which can at worst generate a duplicate definition
/// for types that are equal up to the order of their effects.
fn value_type_key(vt : ValueType) -> String {
  match vt {
    ValueTypeRef(id) => "'\{id.uid()}"
    ValueTypeApp(sym, targs) =>
      "@\{sym.uid()}[\{targs.map(value_type_key).join(",")}]"
    BoxedType(tpe, capt) =>
      "box(\{block_type_key(tpe)} at \{captures_key(capt)})"
  }
}

///|
fn captures_key(capt : Captures) -> String {
  match capt {
    CaptureSetOf(cs) => "{\{cs.map(s => s.uid().to_string()).join(",")}}"
    CaptVar(c) => "?\{c.uid()}"
  }
}

///|
fn block_type_key(tpe : BlockType) -> String {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result, effects) =>
      "fn[\{tparams.map(s => s.uid().to_string()).join(",")}]" +
      "\{cparams.map(captures_key).join(",")}(\{vparams.map(value_type_key).join(",")})" +
      "{\{bparams.map(block_type_key).join(",")}}:\{value_type_key(result)}/" +
      effects.effects.map(block_type_key).join(",")
    InterfaceType(ctor, targs) =>
      "iface@\{ctor.uid()}[\{targs.map(value_type_key).join(",")}]"
  }
}

// ---------------------------------------------------------------------------
// The state of the phase
// ---------------------------------------------------------------------------

///|
/// The state of a single run of the phase: the show instances generated so far
/// and the bindings collected for the statement currently being transformed.
///
/// Upstream's `ShowContext`.
pub(all) struct ShowContext {
  /// value type key -> the id of the generated show function
  show_names : Map[String, Sym]
  /// value type key -> the generated definition
  show_defns : Map[String, Toplevel]
  /// type parameter uid -> the value type it stands for
  tparam_lookup : Map[Int32, ValueType]
  /// The bindings emitted for the statement being transformed (upstream's
  /// `bindings` `ListBuffer`).
  mut bindings : Array[Binding]
}

///|
pub fn ShowContext::new() -> ShowContext {
  {
    show_names: Map([]),
    show_defns: Map([]),
    tparam_lookup: Map([]),
    bindings: [],
  }
}

///|
/// All show definitions generated so far (`getAllShowDef`).
fn ShowContext::all_show_defs(self : ShowContext) -> Array[Toplevel] {
  let out : Array[Toplevel] = []
  for _key, defn in self.show_defns {
    out.push(defn)
  }
  out
}

///|
/// Records a binding that has to be emitted before the current statement.
fn ShowContext::emit(self : ShowContext, id : Sym, stmt : Stmt) -> Unit {
  self.bindings.push(BindingVal(id, stmt))
}

///|
/// Runs `block` with a fresh binding list and returns the bindings it emitted
/// (the bindings pending before were *not* restored, see `with_bindings` and
/// `without_bindings`).
fn[T] ShowContext::scoped(
  self : ShowContext,
  block : () -> T raise EffektError,
) -> (T, Array[Binding]) raise EffektError {
  let pending = self.bindings
  self.bindings = []
  let result = block()
  (result, pending)
}

///|
/// Collects the bindings emitted while computing the statement and prefixes
/// them to it.
fn ShowContext::with_bindings(
  self : ShowContext,
  block : () -> Stmt raise EffektError,
) -> Stmt raise EffektError {
  let (transformed, pending) = self.scoped(block)
  bindings_to_stmt(pending, transformed)
}

///|
/// Collects the bindings emitted while computing `block` and prepends them to
/// the bindings of the enclosing scope.
fn[T] ShowContext::without_bindings(
  self : ShowContext,
  block : () -> T raise EffektError,
) -> T raise EffektError {
  let (result, pending) = self.scoped(block)
  self.bindings = pending
  result
}

///|
/// The counter behind the names of the generated definitions (`show0`, ...),
/// mirroring upstream's `freshShowCounter`.
let fresh_show_counter : Ref[Int32] = Ref(0)

///|
/// A fresh id for a generated show definition.
///
/// Upstream `freshShowId` uses a plain `Id`; since core ids are symbols that are
/// only compared by uid, a fresh temporary block symbol is used here.
fn fresh_show_id() -> Sym {
  let n = fresh_show_counter.val
  fresh_show_counter.val = n + 1
  Sym::tmp_block("\{show_function_name}\{n}")
}

// ---------------------------------------------------------------------------
// Lookups
// ---------------------------------------------------------------------------

///|
/// Is this a call to the prelude's `show` extern?
///
/// NOTE: upstream matches calls by *name* only (`bid.name.name == "show"`),
/// which also catches unrelated definitions that happen to be called `show`:
/// `examples/minilib/effekt.effekt` declares `def show(value: Int): String`,
/// and calls to it must not be replaced by a structural instance. We therefore
/// additionally require the callee to be an extern function.
fn is_show_call(block_var : BlockVar) -> Bool {
  if block_var.id.name().name != show_function_name {
    return false
  }
  match block_var.id {
    ExternFunction(_) => true
    _ => false
  }
}

///|
/// The value type of an expression, as far as it is annotated.
///
/// Upstream reads the type of everything from the typer; this port has no core
/// type inference (`src/core/tree.mbt`), so a value that the transformer had to
/// bind to a temporary carries the unknown (error) type.
fn shown_type_of(dctx : DeclarationContext, e : Expr) -> ValueType {
  match e {
    ValueVar(_, tpe) => tpe
    Literal(_, tpe) => tpe
    // The port's `Make` only stores the *existential* type arguments (upstream
    // stores `ValueType.Data(tpe, universals)`), so the universals are
    // recovered from the fields and the arguments.
    Make(data, tag, existentials, vargs) =>
      recover_make_type(dctx, data, tag, existentials, vargs)
    PureApp(block_var, _, _) =>
      match block_var.annotated_tpe {
        FunctionType(_, _, _, _, result, _) => result
        InterfaceType(_, _) => unknown_value_type()
      }
    Box(_, _) => unknown_value_type()
  }
}

///|
/// The type of a constructor call, with the universals of the data type
/// recovered from the types of the arguments.
///
/// If they cannot all be recovered the result is an under-applied type, which
/// [[is_showable]] rejects.
fn recover_make_type(
  dctx : DeclarationContext,
  data : Sym,
  tag : Sym,
  existentials : Array[ValueType],
  vargs : Array[Expr],
) -> ValueType {
  let tparams = match dctx.find_data(data) {
    Some(DeclarationData(_, tparams, _)) => tparams
    _ => []
  }
  let bindings : Map[Int32, ValueType] = Map([])
  match dctx.find_constructor(tag) {
    Some(constr) =>
      for i = 0; i < constr.fields.length() && i < vargs.length(); i = i + 1 {
        unify_type_hint(
          constr.fields[i].tpe,
          shown_type_of(dctx, vargs[i]),
          bindings,
        )
      }
    None => ()
  }
  let universals : Array[ValueType] = []
  let mut complete = true
  for tparam in tparams {
    match bindings.get(tparam.uid()) {
      Some(t) => universals.push(t)
      None => complete = false
    }
  }
  if complete {
    @symbols.ValueTypeApp(data, universals + existentials)
  } else {
    @symbols.ValueTypeApp(
      // not a well-formed application of `data`: `is_showable` rejects it
      data,
      [],
    )
  }
}

///|
/// Records `tpe := actual` for the type variables that `tpe` mentions, as far
/// as both types are known. This is *not* a unification: the first binding of a
/// variable wins and anything that does not line up is ignored.
fn unify_type_hint(
  tpe : ValueType,
  actual : ValueType,
  out : Map[Int32, ValueType],
) -> Unit {
  match (tpe, actual) {
    (ValueTypeRef(tparam), _) =>
      if !out.contains(tparam.uid()) {
        out.set(tparam.uid(), actual)
      }
    (ValueTypeApp(ctor1, targs1), ValueTypeApp(ctor2, targs2)) =>
      if ctor1.uid() == ctor2.uid() && targs1.length() == targs2.length() {
        for i = 0; i < targs1.length(); i = i + 1 {
          unify_type_hint(targs1[i], targs2[i], out)
        }
      }
    _ => ()
  }
}

///|
/// The builtin types that `generate_show_instance` has a case for.
fn showable_builtins() -> Array[String] {
  ["String", "Unit", "Int", "Char", "Byte", "Double", "Bool"]
}

///|
/// The type a call to `show` asks a structural instance for, i.e. upstream's
/// single type argument of the call, or `None` when the call is left alone
/// (see [[showable_type]]).
///
/// The inferred type arguments do not survive `ExplicitCapabilities`: it
/// rebuilds every call node with a fresh uid (`src/source/capabilities.mbt`),
/// while the annotation `Context.type_arguments_of` is keyed by uid (upstream
/// copies the annotations of a rewritten node: `Tree.Rewrite.visit` calls
/// `Context.copyAnnotations`). `core.transform` therefore sees calls without
/// type arguments, and since `show` has exactly one type parameter and one
/// value parameter of that very type, the type is recovered from the argument.
fn show_type_argument(
  dctx : DeclarationContext,
  targs : Array[ValueType],
  vargs : Array[Expr],
) -> ValueType? raise EffektError {
  if targs.length() == 1 {
    return showable_type(dctx, targs[0])
  }
  if targs.length() == 0 && vargs.length() == 1 {
    return showable_type(dctx, shown_type_of(dctx, vargs[0]))
  }
  raise EffektError::Fatal(
    "Expected targs for '\{show_function_name}' to have exactly one argument",
  )
}

///|
/// Is there a structural show instance for this type?
///
/// `None` means: leave the call to the `show` extern alone (it keeps compiling
/// to the prelude's `undefined` body). This happens for types whose structure
/// the port cannot make out:
///
///   - type variables, i.e. `show(value)` where `value: R` in a generic
///     function. Upstream aborts with "Too much type indirection over show"
///     only because it runs `Deadcode` first, and such definitions are usually
///     unreachable — the prelude's `inspect[R](value: R) = default {
///     println(show(value)) }` is exactly this shape. The port runs `Deadcode`
///     too (see `@backend.emit`), so this only happens if such a definition is
///     reachable after all.
///   - unknown types, i.e. the transformer could not annotate the shown
///     expression (see [[shown_type_of]]).
///   - data types that are not fully applied (see [[recover_make_type]]), and
///     types that are not data declarations at all, e.g. extern types. Upstream
///     aborts for the latter ("Extern type '...', does not have a manual show
///     implementation"); skipping keeps programs that compiled before
///     compiling.
fn showable_type(dctx : DeclarationContext, t : ValueType) -> ValueType? {
  if is_showable(dctx, t) {
    Some(t)
  } else {
    None
  }
}

///|
/// See [[showable_type]].
fn is_showable(dctx : DeclarationContext, t : ValueType) -> Bool {
  match t {
    ValueTypeRef(_) => false
    // A boxed block is shown as `"BOXED"` without looking at the type.
    BoxedType(_, _) => true
    ValueTypeApp(sym, targs) =>
      match builtin_type_name(t) {
        Some(name) => showable_builtins().contains(name)
        None =>
          if !targs.all(x => is_showable(dctx, x)) {
            false
          } else {
            match dctx.find_data(sym) {
              Some(DeclarationData(_, tparams, constructors)) =>
                tparams.length() == targs.length() && constructors.length() > 0
              _ => false
            }
          }
      }
  }
}

///|
/// A fresh show instance for the given value type, generating it when it does
/// not exist yet.
fn ShowContext::get_show_block_var(
  self : ShowContext,
  dctx : DeclarationContext,
  vt : ValueType,
) -> BlockVar raise EffektError {
  let key = value_type_key(vt)
  let show_id = match self.show_names.get(key) {
    Some(id) => id
    None =>
      match self.generate_show_instance(dctx, vt) {
        Some(defn) => defn.id()
        None =>
          match self.show_names.get(key) {
            Some(id) => id
            None =>
              raise EffektError::Fatal(
                "Could not generate show instance for '\{show_core_value_type(vt)}'",
              )
          }
      }
  }
  BlockVar::new(
    show_id,
    FunctionType([], [], [vt], [], t_string(), Effects::empty()),
    Captures::empty(),
  )
}

///|
/// Looks up an extern definition by name and parameter types.
///
/// Upstream `findExternDef`; the resulting block variable carries the signature
/// of the extern.
fn find_extern_def(
  dctx : DeclarationContext,
  name : String,
  vts : Array[ValueType],
) -> BlockVar raise EffektError {
  let rendered = vts.map(show_core_value_type).join(", ")
  match dctx.find_extern_def_by_name(name, vts) {
    Some(ExternDef(id, _, tparams, cparams, vparams, bparams, result, capt, _)) =>
      BlockVar::new(
        id,
        FunctionType(
          tparams,
          cparams.map(c => CaptureSetOf([c])),
          vparams.map(p => p.tpe),
          bparams.map(b => b.tpe),
          result,
          Effects::empty(),
        ),
        capt,
      )
    _ =>
      raise EffektError::Fatal(
        "Could not find show definition for [\{rendered}]",
      )
  }
}

///|
/// The `showBuiltin` extern for the given value type.
fn find_extern_show_def(
  dctx : DeclarationContext,
  value_type : ValueType,
) -> BlockVar raise EffektError {
  find_extern_def(dctx, show_builtin_function_name, [value_type])
}

// ---------------------------------------------------------------------------
// Generation
// ---------------------------------------------------------------------------

///|
/// The name of the builtin type a value type is, if it is one.
///
/// Upstream matches `Type.TString`, `Type.TInt`, ... which are the nullary
/// `ValueType.Data` of the builtin symbols.
fn builtin_type_name(vt : ValueType) -> String? {
  match vt {
    ValueTypeApp(sym, targs) =>
      if targs.length() == 0 {
        core_builtin_to_string(sym)
      } else {
        None
      }
    _ => None
  }
}

///|
/// Generates the show instance for the given value type, if there is one.
///
/// Mirrors `Show.generateShowInstance`; the generated definition (if any) is
/// also registered in the context.
fn ShowContext::generate_show_instance(
  self : ShowContext,
  dctx : DeclarationContext,
  vt : ValueType,
) -> Toplevel? raise EffektError {
  let show_id = fresh_show_id()
  self.show_names.set(value_type_key(vt), show_id)
  let param_id = Sym::tmp_value("value")
  let vparam = ValueParam::new(param_id, vt)
  let param_value_var = ValueVar(param_id, vt)

  let generate_def = (stmt : Stmt) => {
    let block = BlockLit(BlockLit::new([], [], [vparam], [], stmt))
    let defn = ToplevelDef(show_id, block)
    self.show_defns.set(value_type_key(vt), defn)
    defn
  }
  let generate_val_app_ret = (value_type : ValueType) => {
    let block_var = find_extern_show_def(dctx, value_type)
    let ret_id = Sym::tmp_value("ret")
    ImpureApp(
      ret_id,
      block_var,
      [],
      [param_value_var],
      [],
      Return(ValueVar(ret_id, t_string())),
    )
  }
  let generate_show = (value_type : ValueType) => {
    generate_def(generate_val_app_ret(value_type))
  }

  match builtin_type_name(vt) {
    // Strings are already strings.
    Some("String") => Some(generate_def(Return(param_value_var)))
    Some("Unit") =>
      Some(generate_def(Return(Literal(LString("()"), t_string()))))
    Some("Int") => Some(generate_show(t_int()))
    Some("Char") => Some(generate_show(t_char()))
    Some("Byte") => Some(generate_show(t_byte()))
    Some("Double") => Some(generate_show(t_double()))
    Some("Bool") =>
      Some(
        generate_def(
          If(
            param_value_var,
            Return(Literal(LString("true"), t_string())),
            Return(Literal(LString("false"), t_string())),
          ),
        ),
      )
    _ =>
      match vt {
        ValueTypeApp(name, targs) =>
          match dctx.find_data(name) {
            Some(data) => self.generate_show_instance_data(dctx, data, targs)
            None =>
              raise EffektError::Fatal(
                "Extern type '\{name.name().name}', does not have a manual show implementation",
              )
          }
        ValueTypeRef(name) => {
          // A type parameter: look up what it stands for. Note that upstream
          // only *generates* the instance for the looked-up type and does not
          // register it under the variable itself, so `getShowBlockVar` aborts
          // when the looked-up type already has an instance.
          let lookup = match self.tparam_lookup.get(name.uid()) {
            Some(t) => t
            None =>
              raise EffektError::Fatal(
                "Too much type indirection over show, cannot lookup '\{name.name().name}'",
              )
          }
          match self.show_names.get(value_type_key(lookup)) {
            Some(_) => None
            None => {
              let instance = self.generate_show_instance(dctx, lookup)
              match instance {
                Some(defn) => self.show_defns.set(value_type_key(vt), defn)
                None => ()
              }
              instance
            }
          }
        }
        BoxedType(_, _) =>
          // TODO: Handle this better, but honestly your fault for using this.
          // (upstream warns here; the port has no warning sink)
          Some(generate_def(Return(Literal(LString("BOXED"), t_string()))))
      }
  }
}

///|
/// Generates the show instance for a data type, if it has constructors.
///
/// Mirrors `Show.generateShowInstance(decl, targs)`.
fn ShowContext::generate_show_instance_data(
  self : ShowContext,
  dctx : DeclarationContext,
  decl : Declaration,
  targs : Array[ValueType],
) -> Toplevel? raise EffektError {
  match decl {
    DeclarationData(_, _, constructors) =>
      if constructors.length() == 0 {
        None
      } else {
        let fresh_id = fresh_show_id()
        let data_type = @symbols.ValueTypeApp(decl.id(), targs)
        self.show_names.set(value_type_key(data_type), fresh_id)
        let defn = self.generate_data_instance(dctx, decl, fresh_id, targs)
        self.show_defns.set(value_type_key(data_type), defn)
        Some(defn)
      }
    DeclarationInterface(_, _, _) => None
  }
}

///|
/// Generates the show instance of a data declaration: a function that matches
/// on the value and shows the constructor that was used.
///
/// Mirrors `Show.generateShowInstance(decl, id, targs)`.
fn ShowContext::generate_data_instance(
  self : ShowContext,
  dctx : DeclarationContext,
  decl : Declaration,
  id : Sym,
  targs : Array[ValueType],
) -> Toplevel raise EffektError {
  let (data_id, data_tparams, constructors) = match decl {
    DeclarationData(id, tparams, constructors) => (id, tparams, constructors)
    DeclarationInterface(_, _, _) =>
      raise EffektError::Internal(
        "Interfaces do not have structural show instances.",
      )
  }
  let value_id = Sym::tmp_value("value")

  // `ctx.tparamLookup ++= decl.tparams.zip(targs map lookupType)`: the
  // arguments are looked up *before* the new bindings are installed. (The
  // zip truncates to the shorter list, like upstream.)
  let looked_up = targs.map(t => self.lookup_type(t))
  let n = if data_tparams.length() < looked_up.length() {
    data_tparams.length()
  } else {
    looked_up.length()
  }
  for i = 0; i < n; i = i + 1 {
    self.tparam_lookup.set(data_tparams[i].uid(), looked_up[i])
  }

  let value_tpe = @symbols.ValueTypeApp(
    data_id,
    targs.map(t => self.lookup_type(t)),
  )
  let vparam = ValueParam::new(value_id, value_tpe)

  let constructor_vparams : Array[Array[ValueParam]] = []
  for constr in constructors {
    constructor_vparams.push(self.constructor_vparams(constr))
  }
  let clauses : Array[Clause] = []
  for i = 0; i < constructors.length(); i = i + 1 {
    clauses.push(
      self.constructor_clauses(dctx, constructors[i], constructor_vparams[i]),
    )
  }
  let match_stmt = Match(
    ValueVar(value_id, value_tpe),
    t_string(),
    clauses,
    None,
  )
  ToplevelDef(id, BlockLit(BlockLit::new([], [], [vparam], [], match_stmt)))
}

///|
/// The value parameters of the clause of a constructor: one per field, with the
/// field types looked up.
///
/// Mirrors `Show.constructorVparam`. Upstream *warns* when a field type is a
/// type variable that is not in `tparamLookup` and then throws; the port has no
/// warning sink and raises directly.
fn ShowContext::constructor_vparams(
  self : ShowContext,
  constr : Constructor,
) -> Array[ValueParam] raise EffektError {
  let out : Array[ValueParam] = []
  for field in constr.fields {
    let lookup = self.lookup_type(field.tpe)
    match lookup {
      ValueTypeApp(_, _) => out.push(ValueParam::new(field.id, lookup))
      ValueTypeRef(name) =>
        match self.tparam_lookup.get(name.uid()) {
          Some(t) => out.push(ValueParam::new(field.id, t))
          None =>
            raise EffektError::Internal(
              "Was not able to lookup var: \{name.name().name}",
            )
        }
      BoxedType(_, _) => out.push(ValueParam::new(field.id, lookup))
    }
  }
  out
}

///|
/// Substitutes the type parameters of the data type that is currently being
/// generated by the value types they stand for.
fn ShowContext::lookup_type(
  self : ShowContext,
  vt : ValueType,
) -> ValueType raise EffektError {
  match vt {
    ValueTypeApp(name, targs) =>
      ValueTypeApp(name, targs.map(t => self.lookup_type(t)))
    ValueTypeRef(name) =>
      match self.tparam_lookup.get(name.uid()) {
        Some(t) => t
        None =>
          raise EffektError::Internal(
            "Was not able to lookup type parameter '\{name.name().name}'",
          )
      }
    BoxedType(_, _) => vt
  }
}

///|
/// The clause showing one constructor, e.g.
/// `case Cons(x, xs) => return "Cons(" ++ show(x) ++ ", " ++ show(xs) ++ ")"`.
fn ShowContext::constructor_clauses(
  self : ShowContext,
  dctx : DeclarationContext,
  constr : Constructor,
  vparams : Array[ValueParam],
) -> Clause raise EffektError {
  Clause::new(
    constr.id,
    BlockLit::new([], [], vparams, [], self.constructor_stmt(dctx, constr)),
  )
}

///|
/// The body of a clause: binds every field to a temporary that holds its show
/// representation and returns the concatenation of all of them.
fn ShowContext::constructor_stmt(
  self : ShowContext,
  dctx : DeclarationContext,
  constr : Constructor,
) -> Stmt raise EffektError {
  let infix_concat = find_extern_def(dctx, show_string_concat_name, [
    t_string(),
    t_string(),
  ])
  let pure_fields : Array[(Sym, Stmt)] = []
  for field in constr.fields {
    pure_fields.push(self.field_pure(dctx, field))
  }
  let concatenated = PureApp(infix_concat, [], [
    Literal(LString("\{constr.id.name().name}("), t_string()),
    concat_pure(dctx, pure_fields),
  ])
  field_val_stmts(pure_fields, concatenated)
}

///|
/// Concatenates the shown fields, comma separated and closed by a parenthesis.
///
///     Literal("Just("), PureApp(show, x), Literal(", "), PureApp(show, y), Literal(")")
///       =>
///     PureApp(concat, List(Literal("Just("), PureApp(concat, List(PureApp(show, x),
///       PureApp(concat, List(Literal(", "), ...))))))
fn concat_pure(
  dctx : DeclarationContext,
  pures : Array[(Sym, Stmt)],
) -> Expr raise EffektError {
  let infix_concat = find_extern_def(dctx, show_string_concat_name, [
    t_string(),
    t_string(),
  ])
  if pures.length() == 0 {
    Literal(LString(")"), t_string())
  } else if pures.length() == 1 {
    PureApp(infix_concat, [], [
      ValueVar(pures[0].0, t_string()),
      Literal(LString(")"), t_string()),
    ])
  } else {
    PureApp(infix_concat, [], [
      ValueVar(pures[0].0, t_string()),
      PureApp(infix_concat, [], [
        Literal(LString(", "), t_string()),
        concat_pure(dctx, array_drop(pures, 1)),
      ]),
    ])
  }
}

///|
/// Binds every shown field with a `Val` and returns the concatenation.
fn field_val_stmts(
  pure_fields : Array[(Sym, Stmt)],
  concatenated : Expr,
) -> Stmt {
  if pure_fields.length() == 0 {
    Return(concatenated)
  } else {
    let (id, app) = pure_fields[0]
    Val(id, app, field_val_stmts(array_drop(pure_fields, 1), concatenated))
  }
}

///|
/// `(Id("field"), App(getShowBlockVar(paramTpe), List.empty, List(ValueVar(id, paramTpe)), List.empty))`
fn ShowContext::field_pure(
  self : ShowContext,
  dctx : DeclarationContext,
  field : Field,
) -> (Sym, Stmt) raise EffektError {
  let param_tpe = self.lookup_type(field.tpe)
  let app = App(
    BlockVar(self.get_show_block_var(dctx, param_tpe)),
    [],
    [ValueVar(field.id, param_tpe)],
    [],
  )
  (Sym::tmp_value("field"), app)
}

// ---------------------------------------------------------------------------
// The transformation
// ---------------------------------------------------------------------------

///|
/// Replaces calls to the prelude's `show` with compiler-generated structural
/// show definitions, mirroring `effekt/core/Show.scala`.
///
/// The generated definitions are appended to the definitions of the module,
/// exactly like upstream's `Toplevel.Def`s.
pub fn show_phase(module : ModuleDecl) -> ModuleDecl raise EffektError {
  let ctx = ShowContext::new()
  let dctx = DeclarationContext::new(module.declarations, module.externs)
  let definitions : Array[Toplevel] = []
  for d in module.definitions {
    definitions.push(ctx.transform_toplevel(dctx, d))
  }
  for defn in ctx.all_show_defs() {
    definitions.push(defn)
  }
  ModuleDecl::new(
    module.path,
    module.includes,
    module.declarations,
    module.externs,
    definitions,
    module.exports,
  )
}

///|
fn ShowContext::transform_toplevel(
  self : ShowContext,
  dctx : DeclarationContext,
  toplevel : Toplevel,
) -> Toplevel raise EffektError {
  match toplevel {
    ToplevelDef(id, block) => ToplevelDef(id, self.transform_block(dctx, block))
    ToplevelVal(id, binding) =>
      ToplevelVal(id, self.transform_stmt(dctx, binding))
  }
}

///|
fn ShowContext::transform_block(
  self : ShowContext,
  dctx : DeclarationContext,
  block : Block,
) -> Block raise EffektError {
  match block {
    BlockLit(lit) => BlockLit(self.transform_block_lit(dctx, lit))
    // `transform(b: BlockVar) = b`
    BlockVar(bv) => BlockVar(bv)
    New(implementation) =>
      New(self.transform_implementation(dctx, implementation))
    Unbox(pure) => Unbox(self.transform_expr(dctx, pure))
  }
}

///|
fn ShowContext::transform_implementation(
  self : ShowContext,
  dctx : DeclarationContext,
  implementation : Implementation,
) -> Implementation raise EffektError {
  let operations : Array[Operation] = []
  for op in implementation.operations {
    operations.push(self.transform_operation(dctx, op))
  }
  Implementation::new(implementation.interface, operations)
}

///|
fn ShowContext::transform_operation(
  self : ShowContext,
  dctx : DeclarationContext,
  operation : Operation,
) -> Operation raise EffektError {
  let body = self.without_bindings(() => {
    self.transform_stmt(dctx, operation.body)
  })
  Operation::new(
    operation.name,
    operation.tparams,
    operation.cparams,
    operation.vparams,
    operation.bparams,
    body,
  )
}

///|
fn ShowContext::transform_block_lit(
  self : ShowContext,
  dctx : DeclarationContext,
  lit : BlockLit,
) -> BlockLit raise EffektError {
  let body = self.without_bindings(() => self.transform_stmt(dctx, lit.body))
  BlockLit::new(lit.tparams, lit.cparams, lit.vparams, lit.bparams, body)
}

///|
fn ShowContext::transform_default(
  self : ShowContext,
  dctx : DeclarationContext,
  default : Stmt?,
) -> Stmt? raise EffektError {
  match default {
    None => None
    Some(value) => Some(self.transform_stmt(dctx, value))
  }
}

///|
fn ShowContext::transform_stmt(
  self : ShowContext,
  dctx : DeclarationContext,
  stmt : Stmt,
) -> Stmt raise EffektError {
  match stmt {
    // let x = show[R](value); body  ==>  val x = show0(value); body
    Let(id, PureApp(block_var, targs, vargs), body) => {
      let targ = if is_show_call(block_var) {
        show_type_argument(dctx, targs, vargs)
      } else {
        None
      }
      match targ {
        Some(targ) => {
          // We need to wrap here, because vargs might have been extern show
          // calls that are now not; this might happen everywhere we directly
          // transform an expression.
          let vargs_ = vargs.map(e => self.transform_expr(dctx, e))
          self.with_bindings(() => {
            Val(
              id,
              App(BlockVar(self.get_show_block_var(dctx, targ)), [], vargs_, []),
              self.transform_stmt(dctx, body),
            )
          })
        }
        None => {
          let binding_ = self.transform_expr(
            dctx,
            PureApp(block_var, targs, vargs),
          )
          self.with_bindings(() => {
            Let(id, binding_, self.transform_stmt(dctx, body))
          })
        }
      }
    }
    Let(id, binding, body) => {
      let binding_ = self.transform_expr(dctx, binding)
      self.with_bindings(() => {
        Let(id, binding_, self.transform_stmt(dctx, body))
      })
    }
    Return(expr) => {
      let expr_ = self.transform_expr(dctx, expr)
      self.with_bindings(() => Return(expr_))
    }
    // let x = show[R](value){...}; body  ==>  val x = show0(value){...}; body
    ImpureApp(id, block_var, targs, vargs, bargs, body) => {
      let targ = if is_show_call(block_var) {
        show_type_argument(dctx, targs, vargs)
      } else {
        None
      }
      match targ {
        Some(targ) => {
          let vargs_ = vargs.map(e => self.transform_expr(dctx, e))
          let bargs_ = bargs.map(b => self.transform_block(dctx, b))
          self.with_bindings(() => {
            Val(
              id,
              App(
                BlockVar(self.get_show_block_var(dctx, targ)),
                [],
                vargs_,
                bargs_,
              ),
              self.transform_stmt(dctx, body),
            )
          })
        }
        None => {
          let vargs_ = vargs.map(e => self.transform_expr(dctx, e))
          let bargs_ = bargs.map(b => self.transform_block(dctx, b))
          self.with_bindings(() => {
            ImpureApp(
              id,
              block_var,
              targs,
              vargs_,
              bargs_,
              self.transform_stmt(dctx, body),
            )
          })
        }
      }
    }
    Def(id, block, body) =>
      Def(
        id,
        self.transform_block(dctx, block),
        self.transform_stmt(dctx, body),
      )
    Val(id, binding, body) =>
      Val(
        id,
        self.transform_stmt(dctx, binding),
        self.transform_stmt(dctx, body),
      )
    App(callee, targs, vargs, bargs) => {
      let vargs_ = vargs.map(e => self.transform_expr(dctx, e))
      let bargs_ = bargs.map(b => self.transform_block(dctx, b))
      self.with_bindings(() => {
        App(self.transform_block(dctx, callee), targs, vargs_, bargs_)
      })
    }
    Invoke(callee, method, method_tpe, targs, vargs, bargs) => {
      let vargs_ = vargs.map(e => self.transform_expr(dctx, e))
      let bargs_ = bargs.map(b => self.transform_block(dctx, b))
      self.with_bindings(() => {
        Invoke(
          self.transform_block(dctx, callee),
          method,
          method_tpe,
          targs,
          vargs_,
          bargs_,
        )
      })
    }
    If(cond, thn, els) => {
      let cond_ = self.transform_expr(dctx, cond)
      self.with_bindings(() => {
        If(
          cond_,
          self.transform_stmt(dctx, thn),
          self.transform_stmt(dctx, els),
        )
      })
    }
    Match(scrutinee, match_tpe, clauses, default) => {
      let scrutinee_ = self.transform_expr(dctx, scrutinee)
      self.with_bindings(() => {
        let clauses_ : Array[Clause] = []
        for clause in clauses {
          clauses_.push(
            Clause::new(clause.tag, self.transform_block_lit(dctx, clause.body)),
          )
        }
        Match(
          scrutinee_,
          match_tpe,
          clauses_,
          self.transform_default(dctx, default),
        )
      })
    }
    Region(body) => Region(self.transform_block_lit(dctx, body))
    Alloc(id, init, region, body) => {
      let init_ = self.transform_expr(dctx, init)
      self.with_bindings(() => {
        Alloc(id, init_, region, self.transform_stmt(dctx, body))
      })
    }
    Var(ref, init, capture, body) => {
      let init_ = self.transform_expr(dctx, init)
      self.with_bindings(() => {
        Var(ref, init_, capture, self.transform_stmt(dctx, body))
      })
    }
    Get(id, annotated_tpe, ref, annotated_capt, body) =>
      Get(
        id,
        annotated_tpe,
        ref,
        annotated_capt,
        self.transform_stmt(dctx, body),
      )
    Put(ref, annotated_capt, value, body) => {
      let value_ = self.transform_expr(dctx, value)
      self.with_bindings(() => {
        Put(ref, annotated_capt, value_, self.transform_stmt(dctx, body))
      })
    }
    Reset(body) => Reset(self.transform_block_lit(dctx, body))
    Shift(prompt, k, body) => Shift(prompt, k, self.transform_stmt(dctx, body))
    Resume(k, body) => Resume(k, self.transform_stmt(dctx, body))
    Hole(tpe, span) => Hole(tpe, span)
  }
}

///|
fn ShowContext::transform_expr(
  self : ShowContext,
  dctx : DeclarationContext,
  expr : Expr,
) -> Expr raise EffektError {
  match expr {
    Make(data, tag, targs, vargs) =>
      Make(data, tag, targs, vargs.map(e => self.transform_expr(dctx, e)))
    // We are switching from an extern call to a normal call, so we need to wrap
    // the new call into a `Val`, store it and finally emit it before the
    // statement that called this; therefore we return the name of the `Val`.
    PureApp(block_var, targs, vargs) => {
      let targ = if is_show_call(block_var) {
        show_type_argument(dctx, targs, vargs)
      } else {
        None
      }
      match targ {
        Some(targ) => {
          let stmt = App(
            BlockVar(self.get_show_block_var(dctx, targ)),
            [],
            vargs.map(e => self.transform_expr(dctx, e)),
            [],
          )
          let let_id = Sym::tmp_value("showApp")
          self.emit(let_id, stmt)
          ValueVar(let_id, t_string())
        }
        None =>
          PureApp(
            block_var,
            targs,
            vargs.map(e => self.transform_expr(dctx, e)),
          )
      }
    }
    Literal(value, annotated_type) => Literal(value, annotated_type)
    ValueVar(id, annotated_type) => ValueVar(id, annotated_type)
    Box(block, annotated_capture) =>
      Box(self.transform_block(dctx, block), annotated_capture)
  }
}
