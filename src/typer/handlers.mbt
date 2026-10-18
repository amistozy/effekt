// Blocks: block literals, object / handler implementations and `try ... with`.
//
// Mirrors `checkExprAsBlock`, `checkFunctionArgument`,
// `inferFunctionArgument`, `checkImplementation` and the `TryHandle` case of
// `effekt/Typer.scala`.

///|
/// Checks a term in a *block* position, i.e. where a computation is expected.
pub fn Typer::check_expr_as_block(
  self : Typer,
  e : Term,
  expected : BlockType?,
  hint : (Int32, ValueType)?,
) -> TyRes[BlockType] raise EffektError {
  self.focus = e.span
  let res = self.check_expr_as_block_kind(e, expected, hint)
  self.annotate_block(e.uid, res.tpe)
  self.annotate_effects(e.uid, res.effs)
  res
}

///|
fn Typer::check_expr_as_block_kind(
  self : Typer,
  e : Term,
  expected : BlockType?,
  hint : (Int32, ValueType)?,
) -> TyRes[BlockType] raise EffektError {
  match e.kind {
    @source.TermKind::Unbox(inner) => {
      // Use `expected` to guide the inference of the boxed type.
      let expected_tpe : ValueType? = match expected {
        Some(t) =>
          Some(
            @symbols.ValueType::BoxedType(
              t,
              @symbols.Captures::CaptVar(self.fresh_capt_var("unbox")),
            ),
          )
        None => None
      }
      let res = self.check_expr(inner, expected_tpe)
      match self.st.u.prune_value(res.tpe) {
        @symbols.ValueType::BoxedType(btpe, capt2) => {
          self.using_capture(capt2)
          TyRes::new(btpe, res.effs)
        }
        @symbols.ValueType::ValueTypeRef(x) =>
          if self.st.u.is_type_var(x) {
            match hint {
              Some(h) => {
                let (arity, ret_tpe) = h
                let vps : Array[ValueType] = []
                for k = 0; k < arity; k = k + 1 {
                  vps.push(
                    @symbols.ValueType::ValueTypeRef(
                      self.fresh_type_var(
                        Sym::type_param(Name::local("_"), Span::missing()),
                      ),
                    ),
                  )
                }
                let partial_fn = @symbols.BlockType::FunctionType(
                  [],
                  [],
                  vps,
                  [],
                  ret_tpe,
                  Effects::empty(),
                )
                let capt_var = @symbols.Captures::CaptVar(
                  self.fresh_capt_var("unbox"),
                )
                self.match_expected(
                  res.tpe,
                  @symbols.ValueType::BoxedType(partial_fn, capt_var),
                  None,
                )
                self.using_capture(capt_var)
                TyRes::new(partial_fn, res.effs)
              }
              None =>
                self.abort(
                  e.span,
                  "Unbox requires a boxed type, but got \{res.tpe}.",
                )
            }
          } else {
            self.abort(
              e.span,
              "Unbox requires a boxed type, but got \{res.tpe}.",
            )
          }
        _ =>
          self.abort(e.span, "Unbox requires a boxed type, but got \{res.tpe}.")
      }
    }
    @source.TermKind::Var(id) => {
      let sym = self.symbol_of_id(id)
      if sym.is_block_symbol() && !sym.is_ref_binder() {
        let tpe = self.lookup_block(sym)
        match expected {
          Some(exp) => self.match_declared(tpe, exp, id.span)
          None => ()
        }
        self.using_capture(self.lookup_capture(sym))
        TyRes::new(tpe, Effects::empty())
      } else {
        self.abort(
          e.span,
          "Expected a block variable, but \{id.name} is a value. Maybe use explicit syntax: { () => \{id.name} }",
        )
      }
    }
    @source.TermKind::New(implementation) => {
      let res = self.check_implementation(implementation, None)
      match expected {
        Some(exp) => self.match_declared(res.tpe, exp, e.span)
        None => ()
      }
      res
    }
    @source.TermKind::MethodCall(_, _, _, _, _) =>
      self.panic("Nested capability selection not yet supported")
    @source.TermKind::BlockLiteral(_, _, _, _) =>
      match expected {
        Some(t) =>
          match t {
            @symbols.BlockType::FunctionType(_, _, _, _, _, _) =>
              self.check_function_argument(e, t)
            _ =>
              self.abort(
                e.span,
                "Block literal has a function type, but expected type is: \{t}",
              )
          }
        None => self.infer_function_argument(e)
      }
    _ => self.abort(e.span, "Expected block, but got an expression.")
  }
}

///|
fn Typer::match_declared(
  self : Typer,
  got : BlockType,
  declared : BlockType,
  span : Span,
) -> Unit raise EffektError {
  self.unify_block_types(
    self.st.u.prune_block(got),
    self.st.u.prune_block(declared),
    Declaration(
      self.st.u.prune_value(t_bottom()),
      self.st.u.prune_value(t_top()),
    ),
  )
  ignore(span)
}

///|
fn Typer::match_declared_value(
  self : Typer,
  got : ValueType,
  declared : ValueType,
  span : Span,
) -> Unit raise EffektError {
  ignore(span)
  self.unify_value_types(
    self.st.u.prune_value(got),
    self.st.u.prune_value(declared),
    Declaration(self.st.u.prune_value(got), self.st.u.prune_value(declared)),
  )
}

///|
/// Checks a block literal against an expected function type.
pub fn Typer::check_function_argument(
  self : Typer,
  node : Term,
  expected : BlockType,
) -> TyRes[BlockType] raise EffektError {
  let arg = node
  match arg.kind {
    @source.TermKind::BlockLiteral(tparams, vparams, bparams, body) => {
      // (1) what we already know
      let (cps, vps, bps, ret, effs) = match expected {
        @symbols.BlockType::FunctionType(_, capts, vps, bps, ret, effs) =>
          (capture_params_of(capts), vps, bps, ret, effs)
        _ => self.abort(arg.span, "Expected a function type.")
      }
      if vparams.length() != vps.length() {
        self.abort(
          arg.span,
          "Wrong number of arguments to function: expected \{vps.length()} value arguments, but got \{vparams.length()}.",
        )
      }
      if bparams.length() != bps.length() {
        self.abort(
          arg.span,
          "Wrong number of arguments to function: expected \{bps.length()} block arguments, but got \{bparams.length()}.",
        )
      }

      // (2) check the type annotations of the parameters and bind them
      let value_types : Array[ValueType] = []
      for i = 0; i < vparams.length(); i = i + 1 {
        let p = vparams[i]
        let sym = self.symbol_of_def(p.id)
        let tpe = match symbol_value_type(sym) {
          Some(got) => {
            self.match_declared_value(got, vps[i], p.id.span)
            got
          }
          None => vps[i]
        }
        self.bind_value(sym, tpe)
        value_types.push(tpe)
      }
      let block_types : Array[BlockType] = []
      for i = 0; i < bparams.length(); i = i + 1 {
        let p = bparams[i]
        let sym = self.symbol_of_def(p.id)
        let capture = match sym {
          @symbols.Sym::BlockParam(bp) => bp.capture
          _ => Sym::capture_param(Name::local("anon"))
        }
        let tpe = match symbol_block_type(sym) {
          Some(got) => {
            self.match_declared(got, bps[i], p.id.span)
            got
          }
          None => bps[i]
        }
        self.bind_block(sym, tpe)
        self.bind_capture(sym, @symbols.Captures::CaptureSetOf([capture]))
        block_types.push(tpe)
      }

      // (3) the effects are handled by this function
      let distinct_effs = effs.distinct()
      let capabilities = canonical_order(distinct_effs.effects).map(e => {
        self.fresh_capability_for(e, Sym::capture_param(effect_name(e)))
      })
      let capt_params = block_types.map(_ => {
        Sym::capture_param(Name::local("x"))
      })
      ignore(capt_params)

      let capt_param_syms : Array[Sym] = []
      for i = 0; i < bparams.length(); i = i + 1 {
        match self.symbol_of_def(bparams[i].id) {
          @symbols.Sym::BlockParam(bp) => capt_param_syms.push(bp.capture)
          _ => capt_param_syms.push(Sym::capture_param(Name::local("anon")))
        }
      }
      for c in capabilities {
        capt_param_syms.push(capture_of_capability(c))
      }

      let capt_subst = Substitutions::captures(
        cps,
        captures_of_params(capt_param_syms),
      )
      let expected_return = capt_subst.substitute_value(ret)

      // (4) check the body
      let body_region = @symbols.Captures::CaptVar(
        self.fresh_capt_var("anonymous"),
      )
      let res = self.binding_capabilities(node.uid, capabilities, () => {
        self.flowing_into(body_region, () => {
          self.check_stmt(body, Some(expected_return))
        })
      })
      self.using_capture_without(body_region, capt_param_syms)

      let tpe = @symbols.BlockType::FunctionType(
        tparams.map(p => self.symbol_of_def(p)),
        captures_of_params(capt_param_syms),
        value_types,
        block_types,
        res.tpe,
        distinct_effs,
      )
      self.annotate_block(arg.uid, tpe)
      // The handled effects are compared after substitution: a handler for a
      // polymorphic operation (`with source[A]`, where `source`'s parameter is
      // declared `() => Unit / next[A]`) is only instantiated *while* the body
      // is checked, so the effect recorded in `distinct_effs` may still mention
      // an unsolved unification variable. Prune before subtracting, exactly as
      // `check_try_handle` does, or the handled operation is left over as
      // unhandled.
      TyRes::new(
        tpe,
        eff_diff(
          self.st.u.prune_effects(res.effs),
          self.st.u.prune_effects(distinct_effs),
        ),
      )
    }
    _ => self.abort(arg.span, "Expected a block literal.")
  }
}

///|
/// Infers the type of a block literal that is not checked against an expected
/// function type. All parameters have to be annotated.
pub fn Typer::infer_function_argument(
  self : Typer,
  node : Term,
) -> TyRes[BlockType] raise EffektError {
  let arg = node
  match arg.kind {
    @source.TermKind::BlockLiteral(tparams, vparams, bparams, body) => {
      let type_params : Array[Sym] = tparams.map(p => self.symbol_of_def(p))
      let value_types : Array[ValueType] = []
      for p in vparams {
        let sym = self.symbol_of_def(p.id)
        let tpe = match symbol_value_type(sym) {
          Some(t) => t
          None =>
            self.abort(
              p.id.span,
              "Value parameter \{p.id.name} of a block literal is ambiguous, please provide a type annotation.",
            )
        }
        self.bind_value(sym, tpe)
        value_types.push(tpe)
      }
      let block_types : Array[BlockType] = []
      for p in bparams {
        let sym = self.symbol_of_def(p.id)
        let tpe = match symbol_block_type(sym) {
          Some(t) => t
          None =>
            self.abort(
              p.id.span,
              "Block parameter \{p.id.name} of a block literal is ambiguous, please provide a type annotation.",
            )
        }
        self.bind_block(sym, tpe)
        block_types.push(tpe)
      }
      let inferred = @symbols.Captures::CaptVar(
        self.fresh_capt_var("anonymous"),
      )
      let (res, caps) = self.binding_all_capabilities(node.uid, () => {
        self.flowing_into(inferred, () => self.check_stmt(body, None))
      })
      let distinct_effs = res.effs.distinct()
      let capabilities = canonical_order(distinct_effs.effects).map(e => {
        match caps.get(interface_key(e)) {
          Some(cap) => cap
          None =>
            self.fresh_capability_for(e, Sym::capture_param(effect_name(e)))
        }
      })
      self.bind_capabilities(node.uid, capabilities)
      let capt_param_syms : Array[Sym] = []
      for p in bparams {
        match self.symbol_of_def(p.id) {
          @symbols.Sym::BlockParam(bp) => capt_param_syms.push(bp.capture)
          _ => capt_param_syms.push(Sym::capture_param(Name::local("anon")))
        }
      }
      for c in capabilities {
        capt_param_syms.push(capture_of_capability(c))
      }
      let fun_type = @symbols.BlockType::FunctionType(
        type_params,
        captures_of_params(capt_param_syms),
        value_types,
        block_types,
        res.tpe,
        distinct_effs,
      )
      self.using_capture_without(inferred, capt_param_syms)
      ignore(type_params)
      self.annotate_block(arg.uid, fun_type)
      TyRes::new(fun_type, Effects::empty())
    }
    _ => self.abort(arg.span, "Expected a block literal.")
  }
}

///|
/// Checks an object or handler implementation. `continuation` is only provided
/// when a continuation is captured (i.e. for effect handlers).
pub fn Typer::check_implementation(
  self : Typer,
  implementation : Implementation,
  continuation : (ValueType, Sym)?,
) -> TyRes[BlockType] raise EffektError {
  self.focus = implementation.span
  let tpe = self.resolve_block_ref(implementation.interface)
  let (interface, targs) = match tpe {
    @symbols.BlockType::InterfaceType(ctor, args) => (ctor, args)
    _ => self.abort(implementation.span, "Expected an interface type.")
  }
  let operations = match interface {
    @symbols.Sym::Interface(i) => i.operations
    _ => []
  }

  // (3) check that all operations are covered
  let covered : Array[Sym] = implementation.clauses.map(c => {
    self.symbol_of_id(c.id)
  })
  let not_covered = operations.filter(o => !covered.any(c => c == o))
  if not_covered.length() > 0 {
    let names : Array[String] = not_covered.map(o => o.name().name)
    self.error(
      implementation.span,
      "Missing definitions for operations: \{names.join(", ")}",
    )
  }
  let seen : Array[Sym] = []
  for c in covered {
    if seen.contains(c) {
      self.error(implementation.span, "Duplicate definitions of operations")
    }
    seen.push(c)
  }

  let mut handler_effects = Effects::empty()
  for clause in implementation.clauses {
    let effs = self.check_op_clause(
      implementation, interface, targs, clause, continuation,
    )
    handler_effects = eff_union(handler_effects, effs)
  }
  self.annotate_block(implementation.uid, tpe)
  TyRes::new(tpe, handler_effects)
}

///|
fn Typer::check_op_clause(
  self : Typer,
  _implementation : Implementation,
  interface : Sym,
  targs : Array[ValueType],
  clause : OpClause,
  continuation : (ValueType, Sym)?,
) -> Effects raise EffektError {
  let operations = match interface {
    @symbols.Sym::Interface(i) => i.operations
    _ => []
  }
  // The declared operation this clause implements.
  let mut found_op : Sym? = None
  for o in operations {
    if o.name().name == clause.id.name {
      found_op = Some(o)
    }
  }
  let declared_op = match found_op {
    Some(o) => o
    None =>
      self.abort(
        clause.span,
        "Operation \{clause.id.name} not defined in \{interface.name().name}.",
      )
  }
  let declared = self.lookup_function_type(declared_op)
  let view = match declared_op.as_callable() {
    Some(v) => v
    None => self.abort(clause.span, "Expected an operation symbol.")
  }

  match clause.ret {
    Some(t) =>
      match t.kind {
        @source.TypeKind::Effectful(_, _) =>
          self.abort(
            clause.span,
            "Unexpected type annotation on operation \{clause.id.name}.",
          )
        _ => ()
      }
    None => ()
  }

  // arity checks
  let declared_tparams = view.tparams
  let declared_vparams = view.vparams
  let declared_bparams = view.bparams
  if clause.tparams.length() > 0 {
    self.assert_arity(
      clause.span,
      "type parameters",
      clause.tparams.length(),
      declared_tparams.length() - targs.length(),
      clause.id.name,
    )
  }
  self.assert_arity(
    clause.span,
    "value parameters",
    clause.vparams.length(),
    declared_vparams.length(),
    clause.id.name,
  )

  // The parameters C, D, ... are existentials
  let existential_params : Array[Sym] = if clause.tparams.length() ==
    declared_tparams.length() - targs.length() {
    clause.tparams.map(p => self.symbol_of_def(p))
  } else {
    let missing = declared_tparams[targs.length():]
      .to_owned()
      .map(t => t.name().name)
    self.abort(
      clause.span,
      "Operation \{clause.id.name} requires additional parameters: [\{missing.join(", ")}]",
    )
  }
  let existentials = existential_params.map(t => {
    @symbols.ValueType::ValueTypeRef(t)
  })
  let canonical = canonical_order(
    view.annotated_effects.unwrap_or(Effects::empty()).distinct().effects,
  )

  match continuation {
    // an object implementation: there is no continuation
    None => {
      self.assert_arity(
        clause.span,
        "block parameters",
        clause.bparams.length(),
        declared_bparams.length(),
        clause.id.name,
      )
      let cparams_for_blocks : Array[Sym] = []
      for p in clause.bparams {
        match self.symbol_of_def(p.id) {
          @symbols.Sym::BlockParam(bp) => cparams_for_blocks.push(bp.capture)
          _ => cparams_for_blocks.push(Sym::capture_param(Name::local("anon")))
        }
      }
      let cparams_for_effects = canonical.map(t => {
        Sym::capture_param(effect_name(t))
      })
      let cparams = cparams_for_blocks + cparams_for_effects
      let (vps, bps, tpe, effs) = self.instantiate(
        declared,
        declared_tparams,
        targs + existentials,
        cparams.map(c => @symbols.Captures::CaptureSetOf([c])),
      )
      for i = 0; i < clause.vparams.length() && i < vps.length(); i = i + 1 {
        let p = clause.vparams[i]
        let sym = self.symbol_of_def(p.id)
        let annotated = symbol_value_type(sym)
        match annotated {
          Some(got) => self.match_declared_value(got, vps[i], p.id.span)
          None => ()
        }
        self.bind_value(sym, annotated.unwrap_or(vps[i]))
      }
      for i = 0; i < clause.bparams.length() && i < bps.length(); i = i + 1 {
        let p = clause.bparams[i]
        let sym = self.symbol_of_def(p.id)
        let capture = match sym {
          @symbols.Sym::BlockParam(bp) => bp.capture
          _ => Sym::capture_param(Name::local("anon"))
        }
        let annotated = symbol_block_type(sym)
        match annotated {
          Some(got) => self.match_declared(got, bps[i], p.id.span)
          None => ()
        }
        self.bind_block(sym, annotated.unwrap_or(bps[i]))
        self.bind_capture(sym, @symbols.Captures::CaptureSetOf([capture]))
      }
      let capabilities = canonical_order(effs.distinct().effects)
        .zip(cparams_for_effects)
        .map(pair => {
          let (t, c) = pair
          self.fresh_capability_for(t, c)
        })
      let body_region = @symbols.Captures::CaptVar(
        self.fresh_capt_var("opclause"),
      )
      let res = self.binding_capabilities(clause.uid, capabilities, () => {
        self.flowing_into(body_region, () => {
          self.check_stmt(clause.body, Some(tpe))
        })
      })
      self.using_capture_without(body_region, cparams)
      self.annotate_value(clause.uid, res.tpe)
      eff_diff(res.effs, effs)
    }

    // a handler implementation: we have a continuation
    Some((ret, continuation_capt)) => {
      if clause.bparams.length() > 0 {
        self.error(
          clause.span,
          "Block parameters are bound by resume and not the effect operation itself",
        )
      }
      let is_bidirectional = canonical.length() > 0 ||
        declared_bparams.length() > 0
      let cparams_for_blocks : Array[Sym] = declared_bparams.map(p => {
        Sym::capture_param(p.name())
      })
      let cparams_for_effects = canonical.map(t => {
        Sym::capture_param(effect_name(t))
      })
      let cparams = cparams_for_blocks + cparams_for_effects
      let (vps, bps, tpe, effs) = self.instantiate(
        declared,
        declared_tparams,
        targs + existentials,
        cparams.map(c => @symbols.Captures::CaptureSetOf([c])),
      )
      for i = 0; i < clause.vparams.length() && i < vps.length(); i = i + 1 {
        let p = clause.vparams[i]
        let sym = self.symbol_of_def(p.id)
        let annotated = symbol_value_type(sym)
        match annotated {
          Some(got) => self.match_declared_value(got, vps[i], p.id.span)
          None => ()
        }
        self.bind_value(sym, annotated.unwrap_or(vps[i]))
      }
      // (4) synthesize the type of the continuation
      let resume_type = if is_bidirectional {
        let inner = @symbols.BlockType::FunctionType(
          [],
          captures_of_params(cparams),
          [],
          bps,
          tpe,
          effs.distinct(),
        )
        let resume_capt = Sym::capture_param(Name::local("resumeBlock"))
        @symbols.BlockType::FunctionType(
          [],
          captures_of_params([resume_capt]),
          [],
          [inner],
          ret,
          Effects::empty(),
        )
      } else {
        @symbols.BlockType::FunctionType(
          [],
          [],
          [tpe],
          [],
          ret,
          Effects::empty(),
        )
      }
      let resume_sym = self.symbol_of_def(clause.resume)
      self.bind_block(resume_sym, resume_type)
      self.bind_capture(
        resume_sym,
        @symbols.Captures::CaptureSetOf([continuation_capt]),
      )
      let res = self.check_stmt(clause.body, Some(ret))
      self.annotate_value(clause.uid, res.tpe)
      res.effs
    }
  }
}

///|
fn Typer::assert_arity(
  self : Typer,
  span : Span,
  kind : String,
  got : Int32,
  expected : Int32,
  name : String,
) -> Unit raise EffektError {
  if got != expected {
    self.abort(
      span,
      "Number of \{kind} (\{got}) does not match declaration of '\{name}', which expects \{expected}.",
    )
  }
}

///|
/// Checks `try { prog } with ...`: mirrors the `TryHandle` case.
pub fn Typer::check_try_handle(
  self : Typer,
  node : Term,
  prog : Stmt,
  handlers : Array[Handler],
  expected : ValueType?,
) -> TyRes[ValueType] raise EffektError {
  // (1) extract all handled effects and capabilities
  let provided_capabilities : Array[Sym] = []
  for h in handlers {
    let effect = self.resolve_block_ref(h.implementation.interface)
    let capability = match h.capability {
      Some(bp) => self.symbol_of_def(bp.id)
      None =>
        self.fresh_capability_for(
          effect,
          Sym::capture_param(effect_name(effect)),
        )
    }
    let tpe = self.lookup_block(capability)
    self.bind_block(capability, tpe)
    self.bind_capture(
      capability,
      @symbols.Captures::CaptureSetOf([capture_of_capability(capability)]),
    )
    provided_capabilities.push(capability)
  }

  // fresh capture variable for the continuations
  let continuation_capt_sym = self.fresh_capt_var("handler")
  let continuation_capt = @symbols.Captures::CaptVar(continuation_capt_sym)
  let handled_captures = provided_capabilities.map(c => capture_of_capability(c))
  let continuation_handled = self.without(continuation_capt, handled_captures)

  // (2) check the handled program
  let prog_res = self.binding_capabilities(node.uid, provided_capabilities, () => {
    self.flowing_into(continuation_handled, () => {
      self.check_stmt(prog, expected)
    })
  })

  // (3) check the handlers
  let mut handler_effs = Effects::empty()
  for h in handlers {
    let res = self.flowing_into(continuation_handled, () => {
      self.check_implementation(
        h.implementation,
        Some((prog_res.tpe, continuation_capt_sym)),
      )
    })
    handler_effs = eff_union(handler_effs, res.effs)
  }

  // (4) wellformedness checks
  // the handled effects are compared after substitution: a capability may
  // have been created while a type argument was still an unsolved variable
  let handled_effects : Array[BlockType] = []
  for cap in provided_capabilities {
    match self.st.bt.get(cap.uid()) {
      Some(t) => handled_effects.push(self.st.u.prune_block(t))
      None => ()
    }
  }
  self.warn_about_handlers(
    handlers,
    provided_capabilities,
    handled_effects,
    // The effects of the handled program can still mention unification
    // variables (calling a generic function like `raise[A, E]` instantiates
    // `Exception[?E]`); prune before comparing, otherwise a handler for the
    // instantiated effect is not recognised as used.
    self.st.u.prune_effects(prog_res.effs),
  )

  // (5) the return type of the handled statement must not mention any of the
  // bound capabilities
  let bound_captures = provided_capabilities.map(c => capture_of_capability(c))
  self.check_no_capture_escape(
    bound_captures,
    free_captures_value(prog_res.tpe),
    prog.span,
    "The return type \{prog_res.tpe} of the handled statement is not allowed to refer to any of the bound capabilities.",
  )

  // the captures of the handler continue flowing into the outer scope
  self.using_capture(continuation_capt)
  TyRes::new(
    prog_res.tpe,
    eff_union(
      eff_diff(
        self.st.u.prune_effects(prog_res.effs),
        Effects::new(handled_effects),
      ),
      handler_effs,
    ),
  )
}

///|
/// Warns about multiple handlers for the same effect and about handlers for
/// effects that are not used. (Upstream reports these as warnings, too.)
fn Typer::warn_about_handlers(
  self : Typer,
  handlers : Array[Handler],
  capabilities : Array[Sym],
  effects : Array[BlockType],
  used : Effects,
) -> Unit {
  let explicit : Array[Sym] = []
  for h in handlers {
    match h.capability {
      Some(bp) =>
        match self.ctx.symbol_of(bp.id.uid) {
          Some(s) => explicit.push(s)
          None => ()
        }
      None => ()
    }
  }
  for i = 0; i < effects.length(); i = i + 1 {
    let mut count = 0
    let mut all_explicit = true
    let mut all_implicit = true
    for j = 0; j < effects.length(); j = j + 1 {
      if interface_type_equal(effects[i], effects[j]) {
        count = count + 1
        if explicit.contains(capabilities[j]) {
          all_implicit = false
        } else {
          all_explicit = false
        }
      }
    }
    if count > 1 && !all_explicit {
      let message =
        $|There are multiple handlers for effect \{effects[i]}; this might not be intended.
        $|Maybe bind capabilities explicitly (e.g. `try { ... } with c: MyEffect { ... }`)?
      self.warning(handlers[0].span, message)
    }
    if all_implicit && !eff_contains(used, effects[i]) {
      self.warning(
        handlers[0].span,
        "Handling effect \{effects[i]}, which seems not to be used by the program.",
      )
    }
  }
}
