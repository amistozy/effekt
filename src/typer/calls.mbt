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
/// Upstream's `Style.indent`: two spaces in front of *every* line of a nested
/// message (`FailedOverloadError` and `ImplicitInstantiationError` render the
/// messages of their candidates that way).
///
/// A trailing newline of the nested message is *not* turned into an indented
/// empty line: Scala's `linesIterator` (which `Style.indent` uses) drops the
/// final empty line, and the outer message adds its own newline.
fn indent_message(text : String) -> String {
  let text = if text.has_suffix("\n") { text[:text.length() - 1] } else { text }
  text.split("\n").map(line => "  \{line}").join("\n")
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
    match self.st.u.prune_value(fun_vps[0]) {
      @symbols.ValueType::ValueTypeApp(ctor, args) =>
        if is_tuple_name(ctor.name().name) && args.length() == vargs.length() {
          hints.push(
            "Did you mean to call \{call.name} with a single tuple argument instead of separate arguments?",
          )
        }
      _ => ()
    }
  } else if vargs.length() == 1 && fun_vps.length() > 1 {
    match vargs[0].value.kind {
      @source.TermKind::Call(@source.CallTarget::IdTarget(id), _, args, _) =>
        if is_tuple_name(id.name) && args.length() == fun_vps.length() {
          hints.push(
            "Did you mean to call \{call.name} with \{args.length()} separate arguments instead of a tuple?",
          )
        }
      _ => ()
    }
  }
  hints
}

///|
/// Checks a call against a function type. This is the workhorse behind `Call`,
/// `Do` and `MethodCall`.
pub fn Typer::check_call_to(
  self : Typer,
  call : CallLike,
  known_vps : ArrayView[Sym],
  known_bps : ArrayView[Sym],
  fun_tpe : BlockType,
  targs : ArrayView[ValueType],
  vargs : ArrayView[ValueArg],
  bargs : ArrayView[Term],
  expected : ValueType?,
  scope : CapScope?,
) -> TyRes[ValueType] raise EffektError {
  ignore(scope)
  let callsite = self.st.current
  let span = call.span

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
  // `GenerateImplicitArgs`, see `with_implicit_guard`).
  let implicit_vargs : Array[Term] = []
  for i in vargs.length()..<fun_vps.length() {
    let tpe = inst.vparams[i]
    let stencil : ImplicitStencil = {
      name: known_vps[i].name().name,
      kind: "value argument",
      index: i,
      explanation: implicit_explanation(known_vps[i].name().name, tpe),
    }
    let (term, res) = self.check_implicit(call, stencil, "\{tpe}", () => {
      let term = self.implicit_value_term(call, known_vps[i], tpe)
      let res = self.with_implicit_guard(
        stencil.name,
        value_type_size(self.st.u.prune_value(tpe)),
        () => self.check_expr(term, Some(tpe)),
      )
      (term, res)
    })
    match tpe {
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
    let (term, res) = self.check_implicit(call, stencil, "\{btpe}", () => {
      let term = self.implicit_block_arg_term(call, known_bps[j], btpe)
      let res = self.with_implicit_guard(
        stencil.name,
        block_type_size(self.st.u.prune_block(btpe)),
        () => {
          self.flowing_into(capt, () => {
            self.check_expr_as_block(term, Some(btpe), None)
          })
        },
      )
      (term, res)
    })
    effs = eff_union(effs, res.effs)
    implicit_bargs.push(term)
  }
  if !implicit_vargs.is_empty() {
    self.st.ann.impl_vargs.set(call.uid, implicit_vargs)
  }
  if !implicit_bargs.is_empty() {
    self.st.ann.impl_bargs.set(call.uid, implicit_bargs)
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

  let capt_params = capt_args[bargs.length() + implicit_bargs.length():].to_owned()
  for i in 0..<capt_params.length().min(capabilities.length()) {
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
    "\{parts[0:parts.length() - 1].join(", ")} and \{last}"
  }
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
  Array[(Sym, String, Array[Message])],
) {
  let before = self.st.backup()
  let successes : Array[
    (Sym, TyRes[ValueType], TyperState, Array[(Span, String)]),
  ] = []
  let failures : Array[(Sym, String, Array[Message])] = []
  // With a single candidate there is nothing to backtrack: upstream calls
  // `checkCallTo` directly, so the diagnostics of that (only) candidate —
  // including its hints — are reported instead of being buffered.
  for c in candidates {
    self.st = before.backup()
    let muting_before = self.muting
    let error_before = self.muted_error
    let messages_before = self.muted_messages
    let infos_before = self.muted_infos
    self.muting = true
    self.muted_error = false
    self.muted_messages = []
    self.muted_infos = []
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
    let infos = self.muted_infos.copy()
    // restore the enclosing attempt's diagnostics
    self.muting = muting_before
    self.muted_error = error_before
    self.muted_messages = messages_before
    self.muted_infos = infos_before

    let recorded = if err != "" {
      err
    } else {
      muted.map(m => m.text).join("; ")
    }
    let final = if recorded == "" { "Type error" } else { recorded }
    match res {
      Some(r) =>
        if failed {
          failures.push((c, final, muted))
          if alone {
            self.replay_infos(infos)
          }
        } else {
          successes.push((c, r, after, infos))
        }
      None => {
        failures.push((c, final, muted))
        if alone {
          self.replay_infos(infos)
        }
      }
    }
  }
  self.st = before
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
  if provided > total {
    return false
  }
  if provided == total {
    return true
  }
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
fn Typer::candidates_in_order(
  self : Typer,
  candidates : ArrayView[Sym],
) -> Array[Sym] {
  ignore(self)
  let keys = candidates.map(s => s.name().qualified_name())
  let sorted = candidates.to_owned()
  let sorted_keys = keys.copy()
  // insertion sort: the lists are short and it is stable
  for i in 1..<sorted.length() {
    let current = sorted[i]
    let current_key = sorted_keys[i]
    let mut j = i - 1
    while j >= 0 && string_less(current_key, sorted_keys[j]) {
      sorted[j + 1] = sorted[j]
      sorted_keys[j + 1] = sorted_keys[j]
      j = j - 1
    }
    sorted[j + 1] = current
    sorted_keys[j + 1] = current_key
  }
  sorted
}

///|
/// Lexicographic comparison by code unit. `String`'s own `Compare` orders by
/// length first, which is not the order the diagnostics need
/// (`array::println` before `effekt::println`).
fn string_less(a : String, b : String) -> Bool {
  let ca = a.to_array()
  let cb = b.to_array()
  let n = if ca.length() < cb.length() { ca.length() } else { cb.length() }
  for i in 0..<n {
    let x = ca[i].to_int()
    let y = cb[i].to_int()
    guard x == y else { return x < y }
  }
  ca.length() < cb.length()
}

///|
/// Checks a (potentially overloaded) function call.
pub fn Typer::check_overloaded_function_call(
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
  let all_failures : Array[(Sym, String, Array[Message])] = []
  for candidates in scopes {
    // a scope is a *set* of candidates (upstream `Bindings.terms` is a Set):
    // the same symbol can be bound under several paths of the same scope
    let unique = self.candidates_in_order(dedup_syms(candidates))
    let (successes, failures) = self.try_candidates(
      unique,
      scopes.length() == 1 && unique.length() == 1,
      candidate => {
        let (fun_tpe, _tparams, vps, bps) = self.find_function_type_for(
          candidate,
        )
        let res = self.check_call_to(
          call,
          vps,
          bps,
          fun_tpe,
          targs,
          vargs,
          bargs,
          expected,
          None,
        )
        // The capture of the callee has to be available at the call site
        // (`findFunctionTypeFor(...)._2` in upstream `checkOverloadedFunctionCall`).
        // Without it a function that is bound to a capability (`at io`) can be
        // called from where the capability is not in scope.
        match candidate {
          @symbols.Sym::Operation(_) => ()
          _ => self.using_capture(self.lookup_capture(candidate))
        }
        res
      },
    )

    if successes.length() == 1 {
      let (found, res, state, infos) = successes[0]
      self.st = state
      self.replay_infos(infos)
      self.assign_symbol(id.uid, found)
      return res
    } else if successes.length() > 1 {
      // Same scope, several candidates typecheck: upstream reports an
      // ambiguity error here (`AmbiguousOverloadError`). That also covers the
      // eta-expanded call of an implicit argument whose name has several
      // overloads that would all type check (`qualified-error`).
      //
      // The diagnostic is placed at the *reference* (`Context.spanOf(id)`),
      // not at the call: `examples/neg/name-based-implicits/type-tag-complex`
      // underlines the 7 characters of `typeTag`, not `typeTag()`.
      self.abort(id.span, self.ambiguous_overload_message(successes))
    }
    all_failures.append(failures)
  }
  match all_failures {
    [(_, msg, muted)] =>
      // Upstream's `abortWith`: the only candidate that was tried reports its own
      // diagnostics, each at the span it belongs to, instead of one message at
      // the call. The first one is reported last so that the abort that stops the
      // phase carries exactly the message the boundary would otherwise repeat.
      if muted.is_empty() {
        self.abort(call.span, msg)
      } else {
        for msg in muted[1:] {
          // `self.error_message`, not `self.ctx.report`: a nested call may itself
          // be checked while an enclosing candidate is muted, and then these
          // diagnostics have to stay muted as well.
          self.error_message(msg)
        }
        self.abort_message(muted[0])
      }
    [] =>
      self.abort(
        call.span,
        "Cannot typecheck call to \{call.name}. Does a function/method with that name exist?",
      )
    _ => {
      // Upstream's `FailedOverloadError`: a title line, then one paragraph per
      // candidate with the candidate's own diagnostics indented below it, and a
      // trailing newline (which is the blank line before the excerpt in the
      // recorded `.check` files). A diagnostic of a candidate is rendered like
      // any other *except* for the `* note:`/`* help:` markers: upstream's
      // `contentWithSubdiagnostics` puts them on their own indented lines.
      let explanations : Array[String] = all_failures.map(f => {
        let (sym, msg, muted) = f
        let content = if !muted.is_empty() {
          muted.map(m => m.content_with_notes()).join("\n")
        } else {
          msg
        }
        let explanation =
          $|Possible overload: \{sym.name().qualified_name()} of type \{self.lookup_block(sym)}
          $|\{indent_message(content)}
        explanation
      })
      let message =
        $|Cannot typecheck call.
        $|There are multiple overloads, which all fail to check:
        $|
        $|\{explanations.join("\n\n")}
        $|
      self.abort(call.span, message)
    }
  }
}

///|
/// Upstream's `AmbiguousOverload`: the title, then one line per candidate with
/// the names padded to the longest one.
fn Typer::ambiguous_overload_message(
  self : Typer,
  successes : ArrayView[
    (Sym, TyRes[ValueType], TyperState, Array[(Span, String)]),
  ],
) -> String raise EffektError {
  let names : Array[String] = successes.map(s => {
    let (sym, _, _, _) = s
    sym.name().qualified_name()
  })
  let mut longest = 0
  for name in names {
    if name.length() > longest {
      longest = name.length()
    }
  }
  let explanations : Array[String] = []
  for i in 0..<successes.length() {
    let sym = successes[i].0
    let name = names[i]
    let padding = " ".repeat(longest - name.length())
    explanations.push("- \{name}: \{padding}\{self.lookup_block(sym)}")
  }
  let message =
    $|Ambiguous overload.
    $|There are multiple overloads, which all would type check:
    $|\{explanations.join("\n")}
  message
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
  targs : ArrayView[ValueType],
  vargs : ArrayView[ValueArg],
  bargs : ArrayView[Term],
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  match receiver.kind {
    @source.TermKind::Var(recv_id) =>
      if self.symbol_of_id_opt(recv_id) is Some(s) {
        if s.is_value_symbol() || s.is_ref_binder() {
          self.abort(
            receiver.span,
            "`\{recv_id.name}.\{id.name}` is uniform function call syntax on a value, which has to be desugared by `unbox_inference` before type checking (did the pipeline type check the tree returned by `unbox_inference`?).",
          )
        }
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
  if candidates.is_empty() {
    self.abort(
      id.span,
      "Method \{id.name} not found for receiver of type \{recv.tpe}.",
    )
  }
  let call = { uid: call_node.uid, span: call_node.span, name: id.name, }
  for candidates_scope in [self.candidates_in_order(candidates)] {
    let (successes, failures) = self.try_candidates(
      candidates_scope,
      candidates_scope.length() == 1,
      candidate => {
        let (fun_tpe, tparams, vps, bps) = self.find_function_type_for(
          candidate,
        )
        // Upstream's `checkOverloadedMethodCall`: the number of explicitly
        // provided type arguments is checked first and aborts the candidate, so
        // their consistency with the receiver is never reported on top of it
        // (`examples/neg/issue373/wrong_type_argument_arity`).
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
        self.check_call_to(
          call,
          vps,
          bps,
          fun_tpe,
          synth,
          vargs,
          bargs,
          expected,
          None,
        )
      },
    )
    if successes.length() == 1 {
      let (found, res, state, infos) = successes[0]
      self.st = state
      self.replay_infos(infos)
      // Record the operation this method call resolved to: the namer resolves
      // an operation name to an overloaded `CallTarget`, and the backend needs
      // the concrete operation to build the `Invoke`.
      self.assign_symbol(id.uid, found)
      return TyRes(res.tpe, eff_union(res.effs, recv.effs))
    } else if successes.length() > 1 {
      self.abort(id.span, self.ambiguous_overload_message(successes))
    }
    match failures {
      // Upstream's `abortWith` (through `resolveOverload`): the only candidate
      // that was tried reports its own diagnostics, each at its span, instead of
      // one message at the call.
      [(_, msg, muted)] =>
        if muted.is_empty() {
          self.abort(call.span, msg)
        } else {
          for msg in muted[1:] {
            self.error_message(msg)
          }
          self.abort_message(muted[0])
        }
      _ => ()
    }
  }
  self.abort(call.span, "Cannot typecheck method call to \{id.name}.")
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
