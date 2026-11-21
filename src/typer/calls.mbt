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
/// The hints are attached to the arity error that follows them (upstream's
/// `assertArgsParamsAlign` collects them in its `hints` block).
fn Typer::tuple_call_hints(
  self : Typer,
  call : CallLike,
  fun_vps : ArrayView[ValueType],
  vargs : ArrayView[ValueArg],
) -> Array[String] {
  let hints : Array[String] = []
  if fun_vps.length() == 1 && vargs.length() > 1 {
    if self.st.u.prune_value(fun_vps[0])
      is @symbols.ValueType::ValueTypeApp(ctor, args) &&
      is_tuple_name(ctor.name().name) &&
      args.length() == vargs.length() {
      hints.push(
        "Did you mean to call \{call.name} with a single tuple argument instead of separate arguments?",
      )
    }
  } else if vargs.length() == 1 && fun_vps.length() > 1 {
    if vargs[0].value.kind
      is @source.TermKind::Call(@source.CallTarget::IdTarget(id), _, args, _) &&
      is_tuple_name(id.name) &&
      args.length() == fun_vps.length() {
      hints.push(
        "Did you mean to call \{call.name} with \{args.length()} separate arguments instead of a tuple?",
      )
    }
  }
  hints
}

///|
/// Checks a call against a function type. This is the workhorse behind `Call`,
/// `Do` and `MethodCall`.
fn Typer::check_call_to(
  self : Typer,
  call : CallLike,
  known_vps : ArrayView[Sym],
  known_bps : ArrayView[Sym],
  fun_tpe : BlockType,
  targs : ArrayView[ValueType],
  vargs : ArrayView[ValueArg],
  bargs : ArrayView[Term],
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  let callsite = self.st.current
  let span = call.span
  let errors_before = self.muted_error

  // (0) check that argument and parameter counts align
  //
  // The type parameters come from the function type itself, not from the
  // callable: a block parameter has no callable view, but its type may still be
  // polymorphic (`{ f: [A](A) => Poly[A] }`), and upstream instantiates
  // `funTpe.tparams` in either case.
  let (fun_tparams, fun_vps, fun_bps) = match self.st.u.prune_block(fun_tpe) {
    @symbols.BlockType::FunctionType(tps, _, vps, bps, _, _) => (tps, vps, bps)
    _ => self.abort(span, "Expected a function type in call to \{call.name}.")
  }
  if !targs.is_empty() && targs.length() != fun_tparams.length() {
    self.abort(
      span,
      "Wrong number of type arguments, given \{targs.length()} but expected \{fun_tparams.length()}",
    )
  }
  let values_aligned = implicit_tail_matches(
    vargs.length(),
    fun_vps.length(),
    known_vps,
  )
  let blocks_aligned = implicit_tail_matches(
    bargs.length(),
    fun_bps.length(),
    known_bps,
  )
  if !values_aligned || !blocks_aligned {
    let hints = if !values_aligned {
      self.tuple_call_hints(call, fun_vps, vargs)
    } else {
      []
    }
    // Upstream's `assertArgsParamsAlign`: every *misaligned* kind is listed on
    // both sides, including a count of zero.
    let expected_parts : Array[String] = []
    let got_parts : Array[String] = []
    if !values_aligned {
      expected_parts.push(pluralized(fun_vps.length(), "value argument"))
      got_parts.push(pluralized(vargs.length(), "value argument"))
    }
    if !blocks_aligned {
      expected_parts.push(pluralized(fun_bps.length(), "block argument"))
      got_parts.push(pluralized(bargs.length(), "block argument"))
    }
    let mut msg = Message::error(
      span,
      "Wrong number of arguments to \{call.name}: expected \{format_args(expected_parts)}, but got \{format_args(got_parts)}",
    )
    for hint in hints {
      msg = msg.help(hint)
    }
    // Only when the *total* number of arguments is right is it likely that a
    // value was passed where a block is expected, or the other way around
    // (upstream: `values.delta + blocks.delta == 0`).
    let block_delta = bargs.length() - fun_bps.length()
    let value_delta = vargs.length() - fun_vps.length()
    if !values_aligned && !blocks_aligned && block_delta + value_delta == 0 {
      if block_delta > 0 {
        msg = msg.help(
          "Did you mean to pass \{pluralized(block_delta, "block argument")} as a value? e.g. box it using `box { ... }`",
        )
      } else if value_delta > 0 {
        msg = msg.help(
          "Did you mean to pass \{pluralized(value_delta, "value argument")} as a block (computation)?",
        )
      }
    }
    self.abort_message(msg)
  }

  // (1) instantiate the function type
  let (type_args, capt_args, inst) = self.instantiate_fresh(
    fun_tpe, fun_tparams,
  )

  // provided type arguments flow into the fresh unification variables
  if !targs.is_empty() {
    for i in 0..<targs.length().min(type_args.length()) {
      self.match_expected(type_args[i], targs[i], None)
    }
  }

  // (2) check the return type against the expected type
  if expected is Some(exp) {
    self.match_expected(inst.ret, exp, Some(span))
  }

  // (3) named arguments must still be in the correct position
  //
  // A name that belongs to *another* parameter of the same function is a
  // swap, and upstream adds a sentence saying that position still matters
  // (`examples/neg/named_args_wrong`).
  let vpnames : Array[String] = known_vps.map(p => p.name().name)
  for i in 0..<vargs.length() {
    if vargs[i].name is Some(got) {
      if i < known_vps.length() {
        let expected_name = known_vps[i].name().name
        if expected_name != got {
          if vpnames.contains(got) {
            self.error(
              span,
              "Unexpected name in named argument: got \{got}, but expected \{expected_name} in this position. Named arguments must still be in the correct position.",
            )
          } else {
            self.error(
              span,
              "Unexpected name in named argument: got \{got}, but expected \{expected_name}.",
            )
          }
        }
      } else {
        self.error(
          span,
          "Unexpected named argument: got \{got}, but function call is not to a known function.",
        )
      }
    }
  }

  let mut effs = Effects::empty()

  // (4) check value arguments
  //
  // An argument is expected to have the type of its *parameter*, which is an
  // expectation of its own: a handler clause's explanation of `resume` does not
  // apply inside one (upstream builds a fresh `Expected` for every argument).
  let saved_handler = self.handler_result
  self.handler_result = None
  defer {
    self.handler_result = saved_handler
  }
  for i in 0..<vargs.length() {
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
  // recursion is bounded (upstream: the recursion guard in
  // `GenerateImplicitArgs`, see `with_implicit_guard`). A candidate that has
  // already recorded a diagnostic does not get that far: the implicit search
  // below resolves the name against *all* overloads, so a rejected candidate
  // would instantiate the implicits of an overload that does not fit, and the
  // chain of instantiations of the same name grows exponentially with its
  // length (`examples/pos/overloading/implicit_same_size_chain`).
  self.reject_if_errors(errors_before)
  // Where the two argument lists are written: an implicit argument stands for
  // the list it would have been passed in, and its diagnostics point there
  // (upstream passes args.span / args.span to the generated tree).
  let (vargs_span, bargs_span) = @source.argument_spans_of(call.uid).unwrap_or(
    (call.span, call.span),
  )
  let implicit_vargs : Array[Term] = []
  for i in vargs.length()..<fun_vps.length() {
    let tpe = inst.vparams[i]
    let stencil : ImplicitStencil = {
      name: known_vps[i].name().name,
      kind: "value argument",
      index: i,
      explanation: implicit_explanation(known_vps[i].name().name, tpe),
    }
    let term = self.generate_implicit(call.span, stencil, "\{tpe}", () => {
      self.implicit_value_term(call, vargs_span, known_vps[i], tpe)
    })
    let res = self.check_implicit(vargs_span, stencil, "\{tpe}", () => {
      self.with_implicit_guard(
        stencil.name,
        value_type_size(self.st.u.prune_value(tpe)),
        () => self.check_expr(term, Some(tpe)),
      )
    })
    if tpe is @symbols.ValueType::BoxedType(_, capt) &&
      capt.is_pure() &&
      res.effs.non_empty() {
      self.abort(
        call.span,
        "Cannot instantiate the implicit argument \{call.name}: its type is pure, but the block that would be instantiated performs \{res.effs}.",
      )
    }
    effs = eff_union(effs, res.effs)
    implicit_vargs.push(term)
  }
  let implicit_bargs : Array[Term] = []
  for j in bargs.length()..<fun_bps.length() {
    let btpe = inst.bparams[j]
    let capt = capt_args[j]
    self.flows_into(capt, callsite, span)
    let stencil : ImplicitStencil = {
      name: known_bps[j].name().name,
      kind: "block argument",
      index: j,
      explanation: None,
    }
    let term = self.generate_implicit(call.span, stencil, "\{btpe}", () => {
      self.implicit_block_arg_term(call, bargs_span, known_bps[j], btpe)
    })
    let res = self.check_implicit(bargs_span, stencil, "\{btpe}", () => {
      self.with_implicit_guard(
        stencil.name,
        block_type_size(self.st.u.prune_block(btpe)),
        () => {
          self.flowing_into(capt, () => {
            self.check_expr_as_block(term, Some(btpe), None)
          })
        },
      )
    })
    effs = eff_union(effs, res.effs)
    implicit_bargs.push(term)
  }
  if !implicit_vargs.is_empty() {
    self.st.ann = {
      ..self.st.ann,
      impl_vargs: self.st.ann.impl_vargs.add(call.uid, implicit_vargs),
    }
  }
  if !implicit_bargs.is_empty() {
    self.st.ann = {
      ..self.st.ann,
      impl_bargs: self.st.ann.impl_bargs.add(call.uid, implicit_bargs),
    }
  }

  // (6) the declared effects of the callee are effects of this call
  effs = eff_union(effs, inst.effs)

  // annotate the call node with the inferred type arguments
  self.st.ann = {
    ..self.st.ann,
    type_args: self.st.ann.type_args.add(call.uid, type_args),
  }

  // (7) find the capabilities for the effects of the callee
  let capabilities = canonical_order(inst.effs.distinct().effects).map(e => {
    self.capability_for(e, span)
  })
  self.st.ann = {
    ..self.st.ann,
    cap_args: self.st.ann.cap_args.add(call.uid, capabilities),
  }

  let capt_params = capt_args[bargs.length() + implicit_bargs.length():].to_owned()
  for i in 0..<capt_params.length().min(capabilities.length()) {
    self.flows_into(
      @symbols.Captures::CaptureSetOf([capture_of_capability(capabilities[i])]),
      capt_params[i],
      span,
    )
  }
  self.using_capture(
    @symbols.Captures::CaptureSetOf(capabilities.map(capture_of_capability)),
  )

  TyRes(inst.ret, effs)
}

///|
/// The order in which block arguments have to be checked: the indices whose
/// expected type carries an effect with type arguments go last (upstream
/// `checkCallTo`). Their capabilities can only be bound once those type
/// arguments are solved, and the earlier arguments are what solves them.
fn block_argument_order(
  bps : ArrayView[BlockType],
) -> (Array[Int32], Array[Int32]) {
  let without : Array[Int32] = []
  let with_effects : Array[Int32] = []
  for i in 0..<bps.length() {
    let needs_concrete_effect = match bps[i] {
      @symbols.BlockType::FunctionType(_, _, _, _, _, effs) =>
        effs.effects.any(e => {
          match e {
            @symbols.BlockType::InterfaceType(_, args) => !args.is_empty()
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
/// `n` with its noun, pluralized the way upstream's `pluralized` does.
fn pluralized(n : Int32, singular : String) -> String {
  if n == 1 {
    "\{n} \{singular}"
  } else {
    "\{n} \{singular}s"
  }
}

///|
/// The arguments of a call, as in "expected 0 value arguments and 1 block
/// argument" (upstream `assertArgsParamsAlign`'s `formatArgs`). The parts are
/// already pluralized; the caller passes one per misaligned kind.
fn format_args(parts : ArrayView[String]) -> String {
  if parts.is_empty() {
    "no arguments"
  } else if parts.length() == 1 {
    parts[0]
  } else {
    let last = parts[parts.length() - 1]
    "\{parts[:parts.length() - 1].join(", ")} and \{last}"
  }
}

///|
fn describe_args(types : Int32, values : Int32, blocks : Int32) -> String {
  let parts : Array[String] = []
  if types > 0 {
    parts.push(pluralized(types, "type argument"))
  }
  if values > 0 {
    parts.push(pluralized(values, "value argument"))
  }
  if blocks > 0 {
    parts.push(pluralized(blocks, "block argument"))
  }
  if parts.is_empty() {
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
  candidates : ArrayView[Sym],
  /// Whether this is the only way to type check the call (one scope, one
  /// candidate). Upstream then calls checkCallTo directly instead of inside
  /// Try, so the hints of that candidate are reported even when it fails.
  alone : Bool,
  run : (Sym) -> TyRes[ValueType] raise EffektError,
) -> (
  Array[(Sym, TyRes[ValueType], TyperState, Array[(Span, String)])],
  Array[FailedCandidate],
) {
  // A single candidate in a single scope needs no backtracking: upstream calls
  // `checkCallTo` directly, and a candidate that fails is reported and aborted
  // by the caller, so the state it leaves behind is never read. The copies
  // below cover whole maps, and this is the common case for a call.
  let alone_single = alone && candidates.length() == 1
  let before = if alone_single { None } else { Some(self.st.backup()) }
  let successes : Array[
    (Sym, TyRes[ValueType], TyperState, Array[(Span, String)]),
  ] = []
  let failures : Array[FailedCandidate] = []
  for i, c in candidates {
    // Every candidate starts from the state the call was checked in; the first
    // one already does.
    if i > 0 {
      if before is Some(b) {
        self.st = b.backup()
      }
    }
    let ((res, err), failed, muted, infos, cut_off) = self.muted(() => {
      (Some(run(c)), "") catch {
        EffektError::Fatal(m) => (None, m)
        EffektError::Internal(m) => (None, m)
      }
    })
    match res {
      Some(r) =>
        if failed {
          failures.push({ sym: c, error: err, muted, undecided: cut_off, })
          if alone {
            self.replay_infos(infos)
          }
        } else {
          // Only a success has to keep the state for the caller; that of a
          // failed candidate is thrown away.
          let state = if alone_single { self.st } else { self.st.backup() }
          successes.push((c, r, state, infos))
        }
      None => {
        failures.push({ sym: c, error: err, muted, undecided: cut_off, })
        if alone {
          self.replay_infos(infos)
        }
      }
    }
  }
  if before is Some(b) {
    self.st = b
  }
  (successes, failures)
}

///|
/// Reports the hints of the overload candidate that was chosen.
fn Typer::replay_infos(self : Typer, infos : ArrayView[(Span, String)]) -> Unit {
  for (span, msg) in infos {
    self.ctx.info_at(span, msg)
  }
}

///|
/// Can `provided` arguments be aligned with `total` parameters? This is the
/// case when the counts match, or when every left-out parameter is a
/// name-based implicit (`?name`) of a callee whose parameters are known.
fn implicit_tail_matches(
  provided : Int32,
  total : Int32,
  params : ArrayView[Sym],
) -> Bool {
  guard provided <= total else { return false }
  guard provided != total else { return true }
  guard params.length() == total else { return false }
  for i in provided..<total {
    guard params[i].is_implicit() else { return false }
  }
  true
}

///|
/// Orders the candidates of one scope for the diagnostics of an overload
/// resolution.
///
/// Upstream keeps the candidates in a `Set[TermSymbol]`, whose iteration order
/// is the `hashCode` of the symbols — i.e. arbitrary, but deterministic. The
/// recorded corpus output lists them in the order a stable sort by qualified
/// name produces (`array::println` before `effekt::println`, `any::compare`
/// before `int::compare`), which leaves the overloads of one name in the order
/// they were defined.
fn candidates_in_order(candidates : ArrayView[Sym]) -> Array[Sym] {
  let key = (s : Sym) => s.name().qualified_name()
  let sorted = candidates.to_owned()
  // `String`'s own `Compare` orders by length first, which is not the order the
  // diagnostics need (`array::println` before `effekt::println`).
  sorted.mut_view().stable_sort_by((a, b) => key(a).lexical_compare(key(b)))
  sorted
}

///|
/// The candidates of one scope without the duplicates that a set-valued scope can
/// hold, in the order their diagnostics are reported in.
///
/// The single-candidate scope is by far the common one — it is the plain call —
/// and needs neither the dedup nor the sort, which would allocate two arrays and
/// a qualified name per call site just to hand the candidate back.
fn unique_candidates(candidates : Array[Sym]) -> Array[Sym] {
  if candidates.length() == 1 {
    candidates
  } else {
    candidates_in_order(dedup_syms(candidates))
  }
}

///|
/// Checks a (potentially overloaded) function call.
fn Typer::check_overloaded_function_call(
  self : Typer,
  call : CallLike,
  id : IdRef,
  targs : ArrayView[ValueType],
  vargs : ArrayView[ValueArg],
  bargs : ArrayView[Term],
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
  let all_failures : Array[FailedCandidate] = []
  for candidates in scopes {
    // a scope is a *set* of candidates (upstream `Bindings.terms` is a Set):
    // the same symbol can be bound under several paths of the same scope
    let unique = unique_candidates(candidates)
    let (successes, failures) = self.try_candidates(
      unique,
      scopes.length() == 1 && unique.length() == 1,
      candidate => {
        self.check_call_to_candidate(
          call, candidate, targs, vargs, bargs, expected,
        )
      },
    )
    if self.resolve_scope(id, successes, failures) is Some(res) {
      return res
    }
    all_failures.append(failures)
  }
  self.report_overload_failures(call, all_failures, NoExplanation)
}

///|
/// Resolves one scope of an overloaded call (upstream `resolveOverload`): a single
/// candidate that type checks wins unless a candidate whose implicit search was
/// cut off competes with it — that one could have worked, so the call cannot be
/// decided. Several candidates that type check are ambiguous. `None` means "try
/// the next scope".
fn Typer::resolve_scope(
  self : Typer,
  id : IdRef,
  successes : ArrayView[
    (Sym, TyRes[ValueType], TyperState, Array[(Span, String)]),
  ],
  failures : ArrayView[FailedCandidate],
) -> TyRes[ValueType]? raise EffektError {
  let undecided = failures.filter(f => f.undecided)
  if successes.length() == 1 && undecided.is_empty() {
    let (found, res, state, infos) = successes[0]
    self.st = state
    self.replay_infos(infos)
    self.assign_symbol(id.uid, found)
    return Some(res)
  }
  if successes.length() > 1 {
    // Same scope, several candidates typecheck: upstream reports an
    // ambiguity error here (`AmbiguousOverloadError`). That also covers the
    // eta-expanded call of an implicit argument whose name has several
    // overloads that would all type check (`qualified-error`).
    //
    // The diagnostic is placed at the *reference* (`Context.spanOf(id)`),
    // not at the call: `examples/neg/name-based-implicits/type-tag-complex`
    // underlines the 7 characters of `typeTag`, not `typeTag()`.
    self.abort_message(self.ambiguous_overload_message(id.span, successes))
  }
  if !undecided.is_empty() {
    // The candidates that type check and the ones that could not be decided
    // compete: upstream aborts with an `OverloadResolution` marked `undecided`,
    // whose claim says that a search reached its depth limit. The abort is itself
    // undecided, so an enclosing candidate inherits it.
    self.cutoff = true
    self.abort_message(
      self.undecided_overload_message(id.span, successes, undecided),
    )
  }
  None
}

///|
/// Upstream's `OverloadResolution` for a candidate whose implicit search was cut
/// off: the claim, the line introducing the candidates, and one paragraph per
/// candidate — the ones that type check with their declaration, the undecided
/// one with the failure that cut its search off.
fn Typer::undecided_overload_message(
  self : Typer,
  span : Span,
  successes : ArrayView[
    (Sym, TyRes[ValueType], TyperState, Array[(Span, String)]),
  ],
  undecided : ArrayView[FailedCandidate],
) -> Message {
  let candidates : Array[Candidate] = []
  for s in successes {
    candidates.push(self.candidate_of(s.0, []))
  }
  for f in undecided {
    candidates.push(self.candidate_of(f.sym, f.muted))
  }
  Message::error(
    span, "Cannot decide which overload to call: an implicit search reached its depth limit.",
  )
  .details(["There are multiple overloads, which all could type check:"])
  .candidates(candidates)
}

///|
/// One candidate of an unresolved overload as the drawing needs it: the span of
/// its defining identifier (which is drawn with the candidate's bullet on it)
/// and the diagnostics that rejected it.
fn Typer::candidate_of(
  self : Typer,
  sym : Sym,
  errors : ArrayView[Message],
) -> Candidate {
  {
    text: "\{sym.name().qualified_name()} of type \{self.candidate_type(sym)}",
    declaration: sym.def_id(),
    errors: errors.to_owned(),
  }
}

///|
/// Upstream's `OverloadResolution` when several candidates type check: the
/// title, the line introducing them, and one paragraph per candidate — each
/// drawn with its declaration.
fn Typer::ambiguous_overload_message(
  self : Typer,
  span : Span,
  successes : ArrayView[
    (Sym, TyRes[ValueType], TyperState, Array[(Span, String)]),
  ],
) -> Message {
  let candidates : Array[Candidate] = successes.map(s => {
    self.candidate_of(s.0, [])
  })
  Message::error(span, "Ambiguous overload.")
  .details(["There are multiple overloads, which all would type check:"])
  .candidates(candidates)
}

///|
/// The function type of a callable symbol, together with its type and block
/// parameters (which are needed to check named arguments).
fn Typer::find_function_type_for(
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
/// How an unresolved overload reads (upstream `OverloadResolution.claim` when all
/// candidates fail). The claim is also how a *nested* overload failure is
/// recognised: a diagnostic that is itself an unresolved overload is not the
/// shared problem below, because it does not say what is wrong with the
/// candidate — upstream only reports a shared diagnostic on its own when it
/// stands on its own (`Context.abortWith(OverloadResolution)`).
let overload_failure_claim : String = "Cannot typecheck call."

///|
/// Whether a diagnostic is an unresolved overload of its own.
fn is_overload_failure(m : Message) -> Bool {
  m.text == overload_failure_claim &&
  m.details.any(d => {
    d == "There are multiple overloads, which all fail to check:"
  })
}

///|
/// Whether a diagnostic is an error (upstream `severity == Severity.Error`).
fn is_error_message(m : Message) -> Bool {
  match m.severity {
    Error => true
    _ => false
  }
}

///|
/// Whether two diagnostics are the same one: upstream compares the structured
/// messages (`Diagnostic` is a case class, so the severity, the place, the claim
/// and everything nested under it have to agree). Comparing only the claim would
/// make the implicit-argument failures of two overloads look like one shared
/// diagnostic, since they all read "Cannot instantiate implicit argument.".
fn same_message(a : Message, b : Message) -> Bool {
  is_error_message(a) == is_error_message(b) &&
  a.span.start == b.span.start &&
  a.span.end == b.span.end &&
  a.text == b.text &&
  a.details == b.details &&
  same_notes(a.notes, b.notes) &&
  same_messages(a.causes, b.causes) &&
  same_candidates(a.candidates, b.candidates)
}

///|
fn same_notes(
  a : ArrayView[@util.Subdiagnostic],
  b : ArrayView[@util.Subdiagnostic],
) -> Bool {
  guard a.length() == b.length() else { return false }
  for i in 0..<a.length() {
    let same = match (a[i], b[i]) {
      (
        @util.Subdiagnostic::Note(text_a, at_a),
        @util.Subdiagnostic::Note(text_b, at_b),
      ) => {
        let same_at = match (at_a, at_b) {
          (Some(x), Some(y)) => x.start == y.start && x.end == y.end
          (None, None) => true
          _ => false
        }
        text_a == text_b && same_at
      }
      (@util.Subdiagnostic::Help(text_a), @util.Subdiagnostic::Help(text_b)) =>
        text_a == text_b
      _ => false
    }
    guard same else { return false }
  }
  true
}

///|
fn same_messages(a : ArrayView[Message], b : ArrayView[Message]) -> Bool {
  guard a.length() == b.length() else { return false }
  for i in 0..<a.length() {
    guard same_message(a[i], b[i]) else { return false }
  }
  true
}

///|
fn same_candidates(a : ArrayView[Candidate], b : ArrayView[Candidate]) -> Bool {
  guard a.length() == b.length() else { return false }
  for i in 0..<a.length() {
    guard a[i].text == b[i].text &&
      a[i].declaration.start == b[i].declaration.start &&
      a[i].declaration.end == b[i].declaration.end &&
      same_messages(a[i].errors, b[i].errors) else {
      return false
    }
  }
  true
}

///|
/// The diagnostics every candidate of an overloaded call reports (upstream
/// `OverloadResolution.independent`): the ones of the first candidate that the
/// failures of all others contain as well. They do not depend on which candidate
/// is chosen, so they are reported once, on their own.
///
/// A failed nested call is never shared. Upstream compares the recorded
/// diagnostics as values, and an overload failure is `OverloadResolution` of
/// `Candidate`s that carry the *instantiated* function type of that attempt, so
/// two look-alike failures of the same nested call are different diagnostics:
/// `examples/neg/issue433b` keeps the `++` failure under both `run` candidates.
/// Comparing the rendered structure cannot see the instantiation, so the nested
/// failure would otherwise look shared and be hoisted out.
fn shared_failures(all_failures : ArrayView[FailedCandidate]) -> Array[Message] {
  let out : Array[Message] = []
  guard !all_failures.is_empty() else { return out }
  for m in all_failures[0].muted {
    if is_overload_failure(m) {
      continue
    }
    if out.any(o => same_message(o, m)) {
      continue
    }
    let mut everywhere = true
    for i in 1..<all_failures.length() {
      if !all_failures[i].muted.any(o => same_message(o, m)) {
        everywhere = false
        break
      }
    }
    if everywhere {
      out.push(m)
    }
  }
  out
}

///|
/// The diagnostics of one candidate that the shared ones do not already cover
/// (upstream `OverloadResolution.dependent`).
fn dependent_failures(
  muted : ArrayView[Message],
  shared : ArrayView[Message],
) -> Array[Message] {
  let out : Array[Message] = []
  for m in muted {
    if !shared.any(s => same_message(s, m)) {
      out.push(m)
    }
  }
  out
}

///|
/// A candidate of an overloaded call that was tried and did not type check.
priv struct FailedCandidate {
  sym : Sym
  /// The message the attempt aborted with, or `""` when it reported
  /// diagnostics instead (see `FailedCandidate::message`).
  error : String
  /// The diagnostics the attempt recorded.
  muted : Array[Message]
  /// The attempt's implicit search was cut off at its depth bound, so it did not
  /// fail for a reason: whether it would type check is unknown (upstream
  /// `Failure.Undecided`).
  undecided : Bool
}

///|
/// Why the candidate failed, as text (upstream `Failure.message`): the abort
/// message, or the diagnostics it recorded when it did not abort.
///
/// Built on demand: a call that resolves throws all of its failures away, and
/// joining the diagnostics of every failed candidate was pure garbage there.
fn FailedCandidate::message(self : FailedCandidate) -> String {
  let recorded = if self.error != "" {
    self.error
  } else {
    self.muted.map(m => m.text).join("; ")
  }
  if recorded == "" {
    "Type error"
  } else {
    recorded
  }
}

///|
/// Upstream's `resolveOverload` takes the notes and helps of a call without
/// candidates as a defaulted block (`explainMissing: Subdiagnostics ?=> Unit`).
/// Only a method call has them, so the caller says so explicitly.
priv enum ExplainMissing {
  Explain(() -> Array[@util.Subdiagnostic])
  NoExplanation
}

///|
/// Reports why every candidate of an overloaded call failed (upstream
/// `resolveOverload`'s tail): a call without candidates, the single candidate's
/// own diagnostics, or the candidate paragraphs of the overload error.
fn Typer::report_overload_failures(
  self : Typer,
  call : CallLike,
  all_failures : ArrayView[FailedCandidate],
  /// Upstream's `resolveOverload(id, results, explainMissing)`: the notes and
  /// helps of a call that found no candidate at all. Only a method call has
  /// them (`explainMissingMethod`), a function call passes none.
  explain_missing : ExplainMissing,
) -> TyRes[ValueType] raise EffektError {
  match all_failures {
    [only] =>
      // Upstream's `abortWith`: the only candidate that was tried reports its own
      // diagnostics, each at the span it belongs to, instead of one message at
      // the call. The first one is reported last so that the abort that stops the
      // phase carries exactly the message the boundary would otherwise repeat.
      if only.muted.is_empty() {
        self.abort(call.span, only.message())
      } else {
        for msg in only.muted[1:] {
          // `self.error_message`, not `self.ctx.report`: a nested call may itself
          // be checked while an enclosing candidate is muted, and then these
          // diagnostics have to stay muted as well.
          self.error_message(msg)
        }
        self.abort_message(only.muted[0])
      }
    [] => {
      let error = Message::error(
        call.span,
        "Cannot typecheck call to \{call.name}. Does a function/method with that name exist?",
      )
      let subs = match explain_missing {
        Explain(explain) => explain()
        NoExplanation => []
      }
      self.abort_message(error.subdiagnostics(subs))
    }
    _ => {
      let shared = shared_failures(all_failures)
      let dependent = all_failures.map(f => dependent_failures(f.muted, shared))
      let shared_errors = shared.filter(m => is_error_message(m))
      // Upstream `Context.abortWith(OverloadResolution)`: when some candidate
      // fails only because of an error that every candidate reports, that error
      // *is* the problem — report it (and the other shared diagnostics) and leave
      // the overload error out. A shared diagnostic that is an unresolved overload
      // of its own does not qualify: it only says that a nested call failed.
      if !shared_errors.is_empty() &&
        dependent.any(ds => !ds.any(d => is_error_message(d))) &&
        !shared_errors.any(m => is_overload_failure(m)) {
        for m in shared {
          if !same_message(m, shared_errors[0]) {
            self.error_message(m)
          }
        }
        self.abort_message(shared_errors[0])
      }
      // Otherwise the shared diagnostics are reported on their own first, and the
      // overload error follows with the candidate-specific diagnostics nested
      // under each candidate (upstream `FailedOverloadError`): a title line, the
      // line introducing the candidates, and one paragraph per candidate drawn
      // with its declaration and the diagnostics that rejected it.
      for m in shared {
        self.error_message(m)
      }
      let candidates : Array[Candidate] = all_failures.mapi((i, f) => {
        self.candidate_of(f.sym, dependent[i])
      })
      let message = Message::error(call.span, overload_failure_claim)
        .details(["There are multiple overloads, which all fail to check:"])
        .candidates(candidates)
      self.abort_message(message)
    }
  }
}

///|
/// The type a candidate is reported with (upstream `candidateType`): a block
/// candidate has a function type, a value candidate the type of the value.
fn Typer::candidate_type(self : Typer, sym : Sym) -> String {
  if sym.is_block_symbol() && !sym.is_ref_binder() {
    let tpe = self.lookup_block(sym) catch { _ => return "?" }
    "\{tpe}"
  } else {
    let tpe = self.lookup_value(sym) catch { _ => return "?" }
    "\{tpe}"
  }
}

///|
/// Whether a term is a computation, as `UnboxInference.isBlockLike` decides it
/// for the receiver of a method call: a variable of block type, an unboxed value
/// and a `new` are computations; a value (and a mutable variable) is not.
fn Typer::is_block_like(self : Typer, e : Term) -> Bool {
  match e.kind {
    @source.TermKind::Var(id) =>
      match self.symbol_of_id_opt(id) {
        Some(sym) => sym.is_block_symbol() && !sym.is_ref_binder()
        None => false
      }
    @source.TermKind::Unbox(_) | @source.TermKind::New(_) => true
    _ => false
  }
}

///|
/// A term for `unbox sym` (upstream `UnboxInference.unboxCallee`): the call of a
/// value's box, which is how a value is called as a function.
fn Typer::unboxed_callee(self : Typer, sym : Sym, span : Span) -> Term {
  let synthesized = span.synthesized()
  let id = @source.IdRef(sym.name().name, synthesized)
  self.assign_symbol(id.uid, sym)
  let value = mk_term(synthesized, @source.TermKind::Var(id))
  mk_term(synthesized, @source.TermKind::Unbox(value))
}

///|
/// Checks a call whose callee is an arbitrary expression (upstream
/// `checkCallOfExpr`): the callee is checked as a block, which unboxes a value,
/// and the resulting function type is called.
fn Typer::check_call_of_expr(
  self : Typer,
  call : CallLike,
  callee : Term,
  targs : ArrayView[ValueType],
  vargs : ArrayView[ValueArg],
  bargs : ArrayView[Term],
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  // Construct a hint: expected arity + return type. Block arguments are
  // excluded, their types would require block type unification.
  let hint : (Int32, ValueType)? = if bargs.is_empty() {
    expected.map(t => (vargs.length(), t))
  } else {
    None
  }
  let callee_res = self.check_expr_as_block(callee, None, hint)
  match callee_res.tpe {
    @symbols.BlockType::FunctionType(_, _, _, _, _, _) => {
      let res = self.check_call_to(
        call,
        [],
        [],
        callee_res.tpe,
        targs,
        vargs,
        bargs,
        expected,
      )
      TyRes(res.tpe, eff_union(res.effs, callee_res.effs))
    }
    _ => self.abort(callee.span, "Cannot infer function type for callee.")
  }
}

///|
/// Checks one candidate of a call against its function type, recording the
/// candidate's capture (upstream `checkCallToBlock`); a candidate that is a value
/// is called through its box instead (upstream `checkCallToCandidate`).
fn Typer::check_call_to_candidate(
  self : Typer,
  call : CallLike,
  candidate : Sym,
  targs : ArrayView[ValueType],
  vargs : ArrayView[ValueArg],
  bargs : ArrayView[Term],
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  if candidate.is_value_symbol() || candidate.is_ref_binder() {
    let callee = self.unboxed_callee(candidate, call.span)
    return self.check_call_of_expr(call, callee, targs, vargs, bargs, expected)
  }
  let (fun_tpe, _tparams, vps, bps) = self.find_function_type_for(candidate)
  let res = self.check_call_to(
    call, vps, bps, fun_tpe, targs, vargs, bargs, expected,
  )
  // The capture of the callee has to be available at the call site. The capture
  // of an operation is dealt with by the caller (`Do` and `MethodCall`).
  match candidate {
    @symbols.Sym::Operation(_) => ()
    _ => self.using_capture(self.lookup_capture(candidate))
  }
  res
}

///|
/// Checks a candidate of `receiver.id(...)` (upstream `checkReceiverCallTo`): the
/// receiver becomes the object of the method (an operation), the first block
/// argument (a computation), or the first value argument (a value or a function).
fn Typer::check_receiver_call_to(
  self : Typer,
  call : CallLike,
  receiver : Term,
  block_like : Bool,
  candidate : Sym,
  targs : ArrayView[ValueType],
  vargs : ArrayView[ValueArg],
  bargs : ArrayView[Term],
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  if candidate.is_operation() {
    // a method's object is a computation: a value receiver is unboxed
    // (upstream `UnboxInference.asBlock`)
    let recv = if block_like {
      receiver
    } else {
      mk_term(receiver.span.synthesized(), @source.TermKind::Unbox(receiver))
    }
    return self.check_method_call_to(
      call, recv, candidate, targs, vargs, bargs, expected,
    )
  }
  if block_like {
    self.check_call_to_candidate(
      call,
      candidate,
      targs,
      vargs,
      [receiver] + bargs.to_owned(),
      expected,
    )
  } else {
    let recv = @source.ValueArg::unnamed(receiver)
    self.check_call_to_candidate(
      call,
      candidate,
      targs,
      [recv] + vargs.to_owned(),
      bargs,
      expected,
    )
  }
}

///|
/// Checks a method call `receiver.id(...)` against one operation candidate: the
/// receiver has to be an object of the operation's interface (upstream
/// `checkMethodCall`).
fn Typer::check_method_call_to(
  self : Typer,
  call : CallLike,
  receiver : Term,
  operation : Sym,
  targs : ArrayView[ValueType],
  vargs : ArrayView[ValueArg],
  bargs : ArrayView[Term],
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  let recv = self.check_expr_as_block(receiver, None, None)
  let iface_tpe = self.st.u.prune_block(recv.tpe)
  let (iface_ctor, iface_args) = match iface_tpe {
    @symbols.BlockType::InterfaceType(ctor, args) => (ctor, args)
    _ =>
      self.abort(
        receiver.span,
        "Expected an interface type as receiver, but got \{recv.tpe}.",
      )
  }
  if operation_interface(operation) is Some(ctor) && ctor != iface_ctor {
    self.abort(
      receiver.span,
      "Expected an object of interface \{ctor.name().name}, but got \{recv.tpe}.",
    )
  }
  let (fun_tpe, tparams, vps, bps) = self.find_function_type_for(operation)
  // The number of explicitly provided type arguments is checked first and aborts
  // the candidate, so their consistency with the receiver is never reported on
  // top of it (`examples/neg/issue373/wrong_type_argument_arity`).
  if !targs.is_empty() && targs.length() != tparams.length() {
    self.abort(
      call.span,
      "Wrong number of type arguments, given \{targs.length()} but expected \{tparams.length()}",
    )
  }
  // manual type arguments have to be consistent with the receiver
  if !targs.is_empty() {
    for i in 0..<targs.length().min(iface_args.length()) {
      self.match_expected(iface_args[i], targs[i], None)
    }
  }
  let synth = if !targs.is_empty() {
    targs
  } else {
    self.fill_in_type_arguments(tparams, iface_args)
  }
  let res = self.check_call_to(
    call, vps, bps, fun_tpe, synth, vargs, bargs, expected,
  )
  TyRes(res.tpe, eff_union(res.effs, recv.effs))
}

///|
/// Checks a method call `receiver.id(...)` (upstream `checkReceiverCall`).
///
/// The namer resolves `id` to every term bound to that name, and each of them is
/// a candidate: an operation is called as a method of the receiver's interface, a
/// computation takes the receiver as its first block argument, and a value (or a
/// function) takes it as its first value argument. Which one it is, is decided
/// only here — `ExplicitCapabilities` then rebuilds the call from the symbol the
/// resolution settled on.
fn Typer::check_overloaded_method_call(
  self : Typer,
  call_node : Term,
  receiver : Term,
  id : IdRef,
  targs : ArrayView[ValueType],
  vargs : ArrayView[ValueArg],
  bargs : ArrayView[Term],
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  let sym = self.symbol_of_id(id)
  let (scopes, iscope) : (Array[Array[Sym]], @symbols.Scope?) = match sym {
    @symbols.Sym::CallTarget(ct) => (ct.symbols, ct.scope)
    // already resolved by a previous attempt to typecheck
    _ => ([[sym]], None)
  }
  let call = { uid: call_node.uid, span: call_node.span, name: id.name, }
  let block_like = self.is_block_like(receiver)
  let all_failures : Array[FailedCandidate] = []
  for candidates in scopes {
    // a scope is a *set* of candidates (upstream `Bindings.terms` is a Set):
    // the same symbol can be bound under several paths of the same scope
    let unique = unique_candidates(candidates)
    let (successes, failures) = self.try_candidates(
      unique,
      scopes.length() == 1 && unique.length() == 1,
      candidate => {
        self.check_receiver_call_to(
          call, receiver, block_like, candidate, targs, vargs, bargs, expected,
        )
      },
    )
    // Record what the method call resolved to: the namer resolves the name to
    // every candidate, and the backend rebuilds the call from this symbol.
    if self.resolve_scope(id, successes, failures) is Some(res) {
      return res
    }
    all_failures.append(failures)
  }
  let explain = Explain(() => {
    self.explain_missing_method(call, iscope, id, candidate => {
      self.check_receiver_call_to(
        call,
        receiver,
        block_like,
        candidate,
        targs,
        vargs,
        bargs,
        None,
      )
    })
  })
  self.report_overload_failures(call, all_failures, explain)
}

///|
/// Upstream's `explainMissingMethod`: why a method call found no candidate at
/// all. A `def` of that name whose scope has ended is pointed at, otherwise the
/// call is retried for every close name in scope and the ones that accept it are
/// suggested — "Did you mean weight?" for `Rope("four").wieght`.
///
/// `check` checks one candidate *without* the expected type: the suggestion must
/// not depend on an enclosing choice (upstream `checkCandidate(None)`).
fn Typer::explain_missing_method(
  self : Typer,
  call : CallLike,
  scope : @symbols.Scope?,
  id : IdRef,
  check : (Sym) -> TyRes[ValueType] raise EffektError,
) -> Array[@util.Subdiagnostic] {
  let scope = match scope {
    Some(s) => s
    None => return []
  }
  if @symbols.ended_term(scope, id.path, id.name) is Some(binder) {
    return [@symbols.note_ended(binder)]
  }
  let imports = self.ctx
    .call_imports_of(call.uid)
    .unwrap_or(@symbols.Bindings::empty())
  let candidates = @symbols.visible_terms(scope, imports, [])
  // `accepts`: does any candidate of that name type check the call?
  let accepts = (entry : (String, Array[Sym])) => {
    self.accepts_call(entry.1, check)
  }
  let closest = @util.close_matches(id.name, candidates, entry => entry.0)
    .filter(accepts)
    .closest()
  match @util.suggestion(closest.map(entry => entry.0)) {
    Some(help) => [@util.Subdiagnostic::Help(help)]
    None => []
  }
}

///|
/// Upstream's `accepts` in `didYouMeanMethod`: try every candidate of one name
/// and report whether one of them type checks the call (a candidate that fails
/// does not count, `try_candidates` mutes and swallows the diagnostics).
fn Typer::accepts_call(
  self : Typer,
  syms : ArrayView[Sym],
  check : (Sym) -> TyRes[ValueType] raise EffektError,
) -> Bool {
  let (successes, _) = self.try_candidates(syms, false, check)
  !successes.is_empty()
}

///|
/// The first type arguments of a method come from the receiver's interface.
fn Typer::fill_in_type_arguments(
  self : Typer,
  tparams : ArrayView[Sym],
  interface_args : ArrayView[ValueType],
) -> Array[ValueType] {
  let out : Array[ValueType] = []
  for i in 0..<tparams.length() {
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
