// Function and method calls, argument checking and overload resolution.
//
// Mirrors the corresponding parts of `effekt/Typer.scala`:
// `checkCallTo`, `checkOverloadedFunctionCall`, `checkOverloadedMethodCall`,
// `tryEach` and `assertArgsParamsAlign`.

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
  if vargs.length() != fun_vps.length() {
    self.abort(
      span,
      "Wrong number of arguments to \{call.name}: expected \{describe_args(0, fun_vps.length(), fun_bps.length())}, but got \{describe_args(targs.length(), vargs.length(), bargs.length())}.",
    )
  }
  if bargs.length() != fun_bps.length() {
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
  // the instantiated capture parameter
  for i = 0; i < bargs.length(); i = i + 1 {
    let capt = capt_args[i]
    self.flows_into(capt, callsite, span)
    let res = self.flowing_into(capt, () => {
      self.check_expr_as_block(bargs[i], Some(inst.bparams[i]), None)
    })
    effs = eff_union(effs, res.effs)
  }

  // (6) the declared effects of the callee are effects of this call
  effs = eff_union(effs, inst.effs)

  // annotate the call node with the inferred type arguments
  self.st.ann.type_args.set(call.uid, type_args)

  // (7) find the capabilities for the effects of the callee
  let capabilities = canonical_order(inst.effs.distinct().effects).map(e => {
    self.capability_for(e, span)
  })
  self.st.ann.cap_args.set(call.uid, capabilities)

  let capt_params = capt_args[bargs.length():].to_owned()
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
        show_block_type(self.lookup_block(s))
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
        "Expected an interface type as receiver, but got \{show_block_type(recv.tpe)}.",
      )
  }
  let candidates = methods.filter(m => {
    match operation_interface(m) {
      Some(ctor) => sym_eq(ctor, iface_ctor)
      None => false
    }
  })
  if candidates.length() == 0 {
    self.abort(
      id.span,
      "Method \{id.name} not found for receiver of type \{show_block_type(recv.tpe)}.",
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
