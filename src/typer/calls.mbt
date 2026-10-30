// Function and method calls, argument checking and overload resolution.
//
// Mirrors the corresponding parts of `effekt/Typer.scala`:
// `checkCallTo`, `checkOverloadedFunctionCall`, `checkOverloadedMethodCall`,
// `tryEach` and `assertArgsParamsAlign`.

///|
/// Is `name` the name of a tuple type/constructor (`Tuple2`, `Tuple3`, ...)?
/// Both the type and the literal are desugared to `effekt::TupleN`.
fn is_tuple_name(name : String) -> Bool {
  name.has_prefix("Tuple")
}

///|
/// Heuristics for the two ways of confusing a tuple with separate arguments
/// (upstream `Typer.checkCallTo`):
///
///   - `foo(x, y)` where `foo` takes a single tuple argument,
///   - `foo((x, y))` where `foo` takes two arguments.
///
/// Only hints are reported here; the arity error itself follows.
fn Typer::tuple_call_hint(
  self : Typer,
  call : CallLike,
  fun_vps : Array[ValueType],
  vargs : Array[ValueArg],
) -> Unit {
  if fun_vps.length() == 1 && vargs.length() > 1 {
    match self.st.u.prune_value(fun_vps[0]) {
      @symbols.ValueType::ValueTypeApp(ctor, args) =>
        if is_tuple_name(ctor.name().name) && args.length() == vargs.length() {
          self.ctx.info_at(
            call.span,
            "Did you mean to call \{call.name} with a single tuple argument instead of separate arguments?",
          )
        }
      _ => ()
    }
  } else if vargs.length() == 1 && fun_vps.length() > 1 {
    match vargs[0].value.kind {
      @source.TermKind::Call(@source.CallTarget::IdTarget(id), _, args, _) =>
        if is_tuple_name(id.name) && args.length() == fun_vps.length() {
          self.ctx.info_at(
            call.span,
            "Did you mean to call \{call.name} with \{args.length()} separate arguments instead of a tuple?",
          )
        }
      _ => ()
    }
  }
}

///|
/// Checks a call against a function type. This is the workhorse behind `Call`,
/// `Do` and `MethodCall`.
pub fn Typer::check_call_to(
  self : Typer,
  call : CallLike,
  tparams : Array[Sym],
  known_vps : Array[Sym],
  known_bps : Array[Sym],
  fun_tpe : BlockType,
  targs : Array[ValueType],
  vargs : Array[ValueArg],
  bargs : Array[Term],
  expected : ValueType?,
  scope : CapScope?,
) -> TyRes[ValueType] raise EffektError {
  ignore(scope)
  let callsite = self.st.current
  let span = call.span

  // (0) check that argument and parameter counts align
  let (fun_vps, fun_bps) = match self.st.u.prune_block(fun_tpe) {
    @symbols.BlockType::FunctionType(_, _, vps, bps, _, _) => (vps, bps)
    _ => self.abort(span, "Expected a function type in call to \{call.name}.")
  }
  if targs.length() > 0 && targs.length() != tparams.length() {
    self.abort(
      span,
      "Wrong number of type arguments to \{call.name}: expected \{tparams.length()}, but got \{targs.length()}",
    )
  }
  if !implicit_tail_matches(vargs.length(), fun_vps.length(), known_vps) {
    self.tuple_call_hint(call, fun_vps, vargs)
    self.abort(
      span,
      "Wrong number of arguments to \{call.name}: expected \{describe_args(0, fun_vps.length(), fun_bps.length())}, but got \{describe_args(targs.length(), vargs.length(), bargs.length())}.",
    )
  }
  if !implicit_tail_matches(bargs.length(), fun_bps.length(), known_bps) {
    self.abort(
      span,
      "Wrong number of arguments to \{call.name}: expected \{describe_args(0, fun_vps.length(), fun_bps.length())}, but got \{describe_args(targs.length(), vargs.length(), bargs.length())}.",
    )
  }

  // (1) instantiate the function type
  let (type_args, capt_args, inst) = self.instantiate_fresh(fun_tpe, tparams)

  // provided type arguments flow into the fresh unification variables
  if targs.length() > 0 {
    for i = 0; i < targs.length() && i < type_args.length(); i = i + 1 {
      self.match_expected(type_args[i], targs[i], None)
    }
  }

  // (2) check the return type against the expected type
  match expected {
    Some(exp) => self.match_expected(inst.ret, exp, Some(span))
    None => ()
  }

  // (3) named arguments must still be in the correct position
  for i = 0; i < vargs.length(); i = i + 1 {
    match vargs[i].name {
      Some(got) =>
        if i < known_vps.length() {
          let expected_name = known_vps[i].name().name
          if expected_name != got {
            self.error(
              span,
              "Unexpected name in named argument: got \{got}, but expected \{expected_name} in this position.",
            )
          }
        } else {
          self.error(
            span,
            "Unexpected named argument: got \{got}, but function call is not to a known function.",
          )
        }
      None => ()
    }
  }

  let mut effs = Effects::empty()

  // (4) check value arguments
  for i = 0; i < vargs.length(); i = i + 1 {
    let res = self.check_expr(vargs[i].value, Some(inst.vparams[i]))
    effs = eff_union(effs, res.effs)
  }

  // (5) check block arguments; the capture of the block argument flows into
  // the instantiated capture parameter.
  //
  // Upstream checks the block arguments whose expected type carries an effect
  // with type arguments *last*: capabilities can only be bound for fully known
  // effects, and the other arguments are what solves the type arguments — in
  // `for[A] { emit[A] } { (c: Char) => … }` the parameter annotation `Char`
  // makes the effect of the first argument `emit[Char]` concrete.
  //
  // Only the *explicit* block parameters are ordered here; the implicit ones
  // are generated below.
  let (without_effects, with_effects) = block_argument_order(
    inst.bparams[0:bargs.length()].to_owned(),
  )
  let order = without_effects + with_effects
  for i in order {
    let capt = capt_args[i]
    self.flows_into(capt, callsite, span)
    let res = self.flowing_into(capt, () => {
      self.check_expr_as_block(bargs[i], Some(inst.bparams[i]), None)
    })
    effs = eff_union(effs, res.effs)
  }

  // (5b) fill in the name-based implicit arguments for the parameters the
  // caller left out (upstream `GenerateImplicitArgs`). They are checked like
  // ordinary arguments and only recorded in the annotations; the call tree is
  // extended by `ExplicitCapabilities`.
  //
  // Generating an implicit argument can itself type check a call that needs
  // implicit arguments (`?myShow: A => String` applied to a `List[A]`), so the
  // generation is bounded. Without the bound, a recursive implicit whose type
  // is still an unsolved unification variable keeps solving `?A := List[?B]`
  // and the substitution chain grows without bound (upstream: the recursion
  // guard in `GenerateImplicitArgs`).
  let implicit_vargs : Array[Term] = []
  for i = vargs.length(); i < fun_vps.length(); i = i + 1 {
    self.st.implicit_depth = self.st.implicit_depth + 1
    if self.st.implicit_depth > 20 {
      self.abort(
        span,
        "Aborting recursive instantiation of the implicit argument \{known_vps[i].name().name}.",
      )
    }
    let term = self.implicit_value_term(call, known_vps[i], inst.vparams[i])
    let res = self.check_expr(term, Some(inst.vparams[i]))
    match inst.vparams[i] {
      @symbols.ValueType::BoxedType(_, capt) =>
        if capt.is_pure() && res.effs.non_empty() {
          self.abort(
            call.span,
            "Cannot instantiate the implicit argument \{call.name}: its type is pure, but the block that would be instantiated performs \{res.effs}.",
          )
        }
      _ => ()
    }
    effs = eff_union(effs, res.effs)
    implicit_vargs.push(term)
  }
  let implicit_bargs : Array[Term] = []
  for j = bargs.length(); j < fun_bps.length(); j = j + 1 {
    self.st.implicit_depth = self.st.implicit_depth + 1
    if self.st.implicit_depth > 20 {
      self.abort(
        span,
        "Aborting recursive instantiation of the implicit argument \{known_bps[j].name().name}.",
      )
    }
    let capt = capt_args[j]
    self.flows_into(capt, callsite, span)
    let term = self.implicit_block_arg_term(call, known_bps[j], inst.bparams[j])
    let res = self.flowing_into(capt, () => {
      self.check_expr_as_block(term, Some(inst.bparams[j]), None)
    })
    effs = eff_union(effs, res.effs)
    implicit_bargs.push(term)
  }
  if implicit_vargs.length() > 0 {
    self.st.ann.impl_vargs.set(call.uid, implicit_vargs)
  }
  if implicit_bargs.length() > 0 {
    self.st.ann.impl_bargs.set(call.uid, implicit_bargs)
  }
  self.st.implicit_depth = self.st.implicit_depth -
    (implicit_vargs.length() + implicit_bargs.length())

  // (6) the declared effects of the callee are effects of this call
  effs = eff_union(effs, inst.effs)

  // annotate the call node with the inferred type arguments
  self.st.ann.type_args.set(call.uid, type_args)

  // (7) find the capabilities for the effects of the callee
  let capabilities = canonical_order(inst.effs.distinct().effects).map(e => {
    self.capability_for(e, span)
  })
  self.st.ann.cap_args.set(call.uid, capabilities)

  let capt_params = capt_args[bargs.length() + implicit_bargs.length():].to_owned()
  for i = 0; i < capt_params.length() && i < capabilities.length(); i = i + 1 {
    self.flows_into(
      @symbols.Captures::CaptureSetOf([capture_of_capability(capabilities[i])]),
      capt_params[i],
      span,
    )
  }
  self.using_capture(
    @symbols.Captures::CaptureSetOf(
      capabilities.map(c => capture_of_capability(c)),
    ),
  )

  TyRes::new(inst.ret, effs)
}

///|
/// The order in which block arguments have to be checked: the indices whose
/// expected type carries an effect with type arguments go last (upstream
/// `checkCallTo`). Their capabilities can only be bound once those type
/// arguments are solved, and the earlier arguments are what solves them.
fn block_argument_order(bps : Array[BlockType]) -> (Array[Int32], Array[Int32]) {
  let without : Array[Int32] = []
  let with_effects : Array[Int32] = []
  for i = 0; i < bps.length(); i = i + 1 {
    let needs_concrete_effect = match bps[i] {
      @symbols.BlockType::FunctionType(_, _, _, _, _, effs) =>
        effs.effects.any(e => {
          match e {
            @symbols.BlockType::InterfaceType(_, args) => args.length() > 0
            _ => false
          }
        })
      _ => false
    }
    if needs_concrete_effect {
      with_effects.push(i)
    } else {
      without.push(i)
    }
  }
  (without, with_effects)
}

///|
fn describe_args(types : Int32, values : Int32, blocks : Int32) -> String {
  let parts : Array[String] = []
  if types > 0 {
    parts.push("\{types} type argument" + (if types == 1 { "" } else { "s" }))
  }
  if values > 0 {
    parts.push(
      "\{values} value argument" + (if values == 1 { "" } else { "s" }),
    )
  }
  if blocks > 0 {
    parts.push(
      "\{blocks} block argument" + (if blocks == 1 { "" } else { "s" }),
    )
  }
  if parts.length() == 0 {
    "no arguments"
  } else {
    parts.join(" and ")
  }
}

// ---------------------------------------------------------------------------
// Overload resolution
// ---------------------------------------------------------------------------

///|
/// Tries all candidates, each with its own copy of the typer state and with
/// diagnostics muted. Returns the successful attempts together with the state
/// they produced.
///
/// The verdict of an attempt is *local*: diagnostics recorded while checking
/// the arguments (which may contain nested overload resolutions, some of whose
/// candidates legitimately fail) must not mark the enclosing attempt as failed.
/// Upstream gets this for free because `Try` installs a fresh message buffer
/// per attempt and restores the outer one afterwards.
fn Typer::try_candidates(
  self : Typer,
  candidates : Array[Sym],
  run : (Sym) -> TyRes[ValueType] raise EffektError,
) -> (Array[(Sym, TyRes[ValueType], TyperState)], Array[(Sym, String)]) {
  let before = self.st.backup()
  let successes : Array[(Sym, TyRes[ValueType], TyperState)] = []
  let failures : Array[(Sym, String)] = []
  for c in candidates {
    self.st = before.backup()
    let muting_before = self.muting
    let error_before = self.muted_error
    let messages_before = self.muted_messages
    self.muting = true
    self.muted_error = false
    self.muted_messages = []
    let mut res : TyRes[ValueType]? = None
    let mut err = ""
    try {
      res = Some(run(c))
    } catch {
      EffektError::Fatal(m) => err = m
      EffektError::Internal(m) => err = m
    }
    let after = self.st.backup()
    // this attempt's own verdict and diagnostics
    let failed = self.muted_error
    let muted = self.muted_messages.copy()
    // restore the enclosing attempt's diagnostics
    self.muting = muting_before
    self.muted_error = error_before
    self.muted_messages = messages_before
    let recorded = if err != "" { err } else { muted.join("; ") }
    let final = if recorded == "" { "Type error" } else { recorded }
    match res {
      Some(r) =>
        if failed {
          failures.push((c, final))
        } else {
          successes.push((c, r, after))
        }
      None => failures.push((c, final))
    }
  }
  self.st = before
  (successes, failures)
}

///|
/// Can `provided` arguments be aligned with `total` parameters? This is the
/// case when the counts match, or when every left-out parameter is a
/// name-based implicit (`?name`) of a callee whose parameters are known.
fn implicit_tail_matches(
  provided : Int32,
  total : Int32,
  params : Array[Sym],
) -> Bool {
  if provided > total {
    return false
  }
  if provided == total {
    return true
  }
  if params.length() != total {
    return false
  }
  for i = provided; i < total; i = i + 1 {
    if !params[i].is_implicit() {
      return false
    }
  }
  true
}

///|
/// Checks a (potentially overloaded) function call.
pub fn Typer::check_overloaded_function_call(
  self : Typer,
  call : CallLike,
  id : IdRef,
  targs : Array[ValueType],
  vargs : Array[ValueArg],
  bargs : Array[Term],
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  let sym = self.symbol_of_id(id)
  let scopes : Array[Array[Sym]] = match sym {
    @symbols.Sym::CallTarget(ct) => ct.symbols
    _ =>
      if sym.is_block_symbol() {
        [[sym]]
      } else if sym.is_value_symbol() {
        self.abort(call.span, "Cannot call value \{sym.name().name}")
      } else {
        [[sym]]
      }
  }
  let all_failures : Array[(Sym, String)] = []
  for candidates in scopes {
    // a scope is a *set* of candidates (upstream `Bindings.terms` is a Set):
    // the same symbol can be bound under several paths of the same scope
    let (successes, failures) = self.try_candidates(dedup_syms(candidates), candidate => {
      let (fun_tpe, tparams, vps, bps) = self.find_function_type_for(candidate)
      self.check_call_to(
        call,
        tparams,
        vps,
        bps,
        fun_tpe,
        targs,
        vargs,
        bargs,
        expected,
        None,
      )
    })
    if successes.length() == 1 {
      let (found, res, state) = successes[0]
      self.st = state
      self.ctx.assign_symbol(id.uid, found)
      return res
    } else if successes.length() > 1 {
      // An implicit argument is instantiated by an eta-expanded call to a
      // function with the parameter's name. If several overloads type check,
      // the name is ambiguous — upstream reports exactly that instead of
      // choosing one (see `examples/neg/name-based-implicits`).
      if self.st.ann.implicit_calls.get(call.uid) is Some(_) {
        let names : Array[String] = successes.map(s => {
          let (sym, _, _) = s
          "\{sym.name().qualified_name()}"
        })
        self.abort(
          call.span,
          "Cannot instantiate the implicit argument \{call.name}: the overload is ambiguous. Could be: \{names.join(", ")}.",
        )
      }
      // Same scope, several candidates typecheck. Upstream reports an
      // ambiguity error here; we additionally prefer the *most specific*
      // candidates (those with the fewest type parameters), which is what a
      // reader expects for e.g. a monomorphic `show(Int)` competing with a
      // generic `show[R]` fallback (see `examples/minilib`). This can only
      // ever turn an error into a success, never the other way around.
      let best = self.most_specific(successes)
      if best.length() == 1 {
        let (found, res, state) = best[0]
        self.st = state
        self.ctx.assign_symbol(id.uid, found)
        return res
      }
      let names : Array[String] = best.map(s => {
        let (s, _, _) = s
        "\{self.lookup_block(s)}"
      })
      self.abort(
        call.span,
        "Ambiguous reference to \{call.name}. Could be: \{names.join(", ")}.",
      )
    }
    for f in failures {
      all_failures.push(f)
    }
  }
  match all_failures {
    [(_, msg)] => self.abort(call.span, msg)
    [] =>
      self.abort(
        call.span,
        "Cannot typecheck call to \{call.name}. Does a function/method with that name exist?",
      )
    _ => {
      // Report all failed candidates, like upstream's FailedOverloadError.
      let explanations : Array[String] = all_failures.map(f => {
        let (sym, msg) = f
        "  \{sym.name().qualified_name()}: \{msg}"
      })
      let message =
        $|Cannot typecheck call to \{call.name}. None of the \{all_failures.length()} overloads type check:
        $|\{explanations.join("\n")}
      self.abort(call.span, message)
    }
  }
}

///|
/// Of several successful candidates, the most specific ones: those that
/// instantiate the fewest type parameters (a monomorphic candidate wins over a
/// generic fallback).
fn Typer::most_specific(
  self : Typer,
  successes : Array[(Sym, TyRes[ValueType], TyperState)],
) -> Array[(Sym, TyRes[ValueType], TyperState)] {
  ignore(self)
  let mut best = 0
  let mut first = true
  for s in successes {
    let (sym, _, _) = s
    let n = match sym.as_callable() {
      Some(v) => v.tparams.length()
      None => 0
    }
    if first {
      best = n
      first = false
    } else if n < best {
      best = n
    }
  }
  successes.filter(s => {
    let (sym, _, _) = s
    let n = match sym.as_callable() {
      Some(v) => v.tparams.length()
      None => 0
    }
    n == best
  })
}

///|
/// The function type of a callable symbol, together with its type and block
/// parameters (which are needed to check named arguments).
pub fn Typer::find_function_type_for(
  self : Typer,
  sym : Sym,
) -> (BlockType, Array[Sym], Array[Sym], Array[Sym]) raise EffektError {
  let view = sym.as_callable()
  match view {
    None => {
      let tpe = self.lookup_block(sym)
      (tpe, [], [], [])
    }
    Some(v) => {
      let tpe = self.lookup_function_type(sym)
      (tpe, v.tparams, v.vparams, v.bparams)
    }
  }
}

///|
/// Checks a method call `receiver.id(...)`, which after unbox inference only
/// occurs for capabilities.
///
/// If the receiver is clearly not a computation, uniform function call syntax
/// was not desugared: the driver must type check the tree returned by
/// `unbox_inference` (upstream runs `Parser andThen Namer andThen
/// UnboxInference andThen Typer`).
pub fn Typer::check_overloaded_method_call(
  self : Typer,
  call_node : Term,
  receiver : Term,
  id : IdRef,
  targs : Array[ValueType],
  vargs : Array[ValueArg],
  bargs : Array[Term],
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  match receiver.kind {
    @source.TermKind::Var(recv_id) =>
      match self.symbol_of_id_opt(recv_id) {
        Some(s) =>
          if s.is_value_symbol() || s.is_ref_binder() {
            self.abort(
              receiver.span,
              "`\{recv_id.name}.\{id.name}` is uniform function call syntax on a value, which has to be desugared by `unbox_inference` before type checking (did the pipeline type check the tree returned by `unbox_inference`?).",
            )
          }
        None => ()
      }
    _ => ()
  }
  let sym = self.symbol_of_id(id)
  let methods : Array[Sym] = match sym {
    @symbols.Sym::CallTarget(ct) => {
      let out : Array[Sym] = []
      for scope in ct.symbols {
        for s in scope {
          if s.is_operation() {
            out.push(s)
          }
        }
      }
      out
    }
    _ =>
      if sym.is_operation() {
        [sym]
      } else {
        self.panic("Not a valid method: \{sym.name().name}")
      }
  }
  let recv = self.check_expr_as_block(receiver, None, None)
  let (iface_ctor, iface_args) = match self.st.u.prune_block(recv.tpe) {
    @symbols.BlockType::InterfaceType(ctor, args) => (ctor, args)
    _ =>
      self.abort(
        receiver.span,
        "Expected an interface type as receiver, but got \{recv.tpe}.",
      )
  }
  let candidates = methods.filter(m => {
    match operation_interface(m) {
      Some(ctor) => ctor == iface_ctor
      None => false
    }
  })
  if candidates.length() == 0 {
    self.abort(
      id.span,
      "Method \{id.name} not found for receiver of type \{recv.tpe}.",
    )
  }
  // manual type arguments have to be consistent with the receiver
  if targs.length() > 0 {
    for i = 0; i < targs.length() && i < iface_args.length(); i = i + 1 {
      self.match_expected(iface_args[i], targs[i], None)
    }
  }
  let call = { uid: call_node.uid, span: call_node.span, name: id.name, }
  for candidates_scope in [candidates] {
    let (successes, failures) = self.try_candidates(candidates_scope, candidate => {
      let (fun_tpe, tparams, vps, bps) = self.find_function_type_for(candidate)
      let synth = if targs.length() > 0 {
        targs
      } else {
        self.fill_in_type_arguments(tparams, iface_args)
      }
      self.check_call_to(
        call,
        tparams,
        vps,
        bps,
        fun_tpe,
        synth,
        vargs,
        bargs,
        expected,
        None,
      )
    })
    if successes.length() == 1 {
      let (found, res, state) = successes[0]
      self.st = state
      // Record the operation this method call resolved to: the namer resolves
      // an operation name to an overloaded `CallTarget`, and the backend needs
      // the concrete operation to build the `Invoke`.
      self.ctx.assign_symbol(id.uid, found)
      return TyRes::new(res.tpe, eff_union(res.effs, recv.effs))
    } else if successes.length() > 1 {
      self.abort(call.span, "Ambiguous method call to \{id.name}.")
    }
    match failures {
      [(_, msg)] => self.abort(call.span, msg)
      _ => ()
    }
  }
  self.abort(call.span, "Cannot typecheck method call to \{id.name}.")
}

///|
/// The first type arguments of a method come from the receiver's interface.
fn Typer::fill_in_type_arguments(
  self : Typer,
  tparams : Array[Sym],
  interface_args : Array[ValueType],
) -> Array[ValueType] {
  let out : Array[ValueType] = []
  for i = 0; i < tparams.length(); i = i + 1 {
    if i < interface_args.length() {
      out.push(interface_args[i])
    } else {
      out.push(
        @symbols.ValueType::ValueTypeRef(self.fresh_type_var(tparams[i])),
      )
    }
  }
  out
}

///|
fn operation_interface(op : Sym) -> Sym? {
  match op {
    @symbols.Sym::Operation(o) => Some(o.interface)
    _ => None
  }
}
