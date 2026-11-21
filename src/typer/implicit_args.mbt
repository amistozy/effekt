// Name-based implicit arguments.
//
// Mirrors `effekt/source/GenerateImplicitArgs.scala` (the part the upstream
// tests exercise). A parameter declared `?name` is filled in at the call site
// by looking `name` up in the lexical scope of the call:
//
//   - a value parameter becomes a `Var` of the term bound to `name`;
//   - a block parameter of interface type becomes a `Var` of the capability
//     object bound to `name`;
//   - a block parameter of function type becomes an eta-expanded block literal
//     applying the function bound to `name`;
//   - a value parameter of boxed type boxes such a block literal;
//   - the two special names `callId` and `sourcePosition` are generated.
//
// The generated terms are checked like ordinary arguments and recorded in the
// annotations that `ExplicitCapabilities` splices into the call.

///|
/// What the type checker is trying to instantiate: upstream's
/// `GenerateImplicitArgs.ImplicitStencil`, reduced to what the diagnostic needs.
/// `explanation` is the stencil-specific paragraph that upstream prints between
/// the heading and the nested diagnostics (`None` for an ordinary `?name`).
pub struct ImplicitStencil {
  name : String
  /// `"value argument"` or `"block argument"`.
  kind : String
  /// Position of the parameter in the parameter list, rendered as `1st`, ...
  index : Int32
  explanation : String?
}

///|
/// `Cannot instantiate 1st block argument foo of type ...`: upstream's
/// `ImplicitInstantiation.formatIndex`.
fn ordinal(index : Int32) -> String {
  match index {
    0 => "1st"
    1 => "2nd"
    2 => "3rd"
    n => "\{n + 1}th"
  }
}

///|
/// The paragraph a stencil prints between its heading and the nested
/// diagnostics (upstream `ImplicitStencil.explanation`). The text contains its
/// own line breaks and is indented as a whole.
fn implicit_explanation(name : String, tpe : ValueType) -> String? {
  match name {
    "callId" =>
      Some(
        "Implicit callId will generate a unique Int for each call to this function in the source code.",
      )
    "sourcePosition" => {
      let text =
        #|Implicit sourcePosition will call
        #|SourcePosition(file, start_line, start_col, end_line, end_col)
        #|with the respective values for the source position of the call.
      Some(text)
    }
    _ =>
      match tpe {
        @symbols.ValueType::BoxedType(_, _) => {
          let text =
            #|An implicit argument of a boxed type will be instantiated by boxing the block that an implicit block argument of the same name would be instantiated to.
          Some(text)
        }
        _ => None
      }
  }
}

///|
/// Checks a generated implicit argument (upstream's `GenerateImplicitArgs.Try`
/// around each attempt). A failure — an abort inside the check or a diagnostic
/// it recorded — is not reported as itself: upstream turns it into an
/// `ImplicitInstantiationError` that says the implicit argument cannot be
/// instantiated and nests the diagnostics below that line.
fn[T] Typer::check_implicit(
  self : Typer,
  /// Where the argument list the implicit argument belongs to is written: the
  /// diagnostic points there (upstream reports the failure of the generated
  /// tree, whose span is the span of that list).
  span : Span,
  stencil : ImplicitStencil,
  tpe : String,
  run : () -> T raise EffektError,
) -> T raise EffektError {
  let ((result, failure), muted_error, errors, infos, cut_off) = self.muted(() => {
    (Some(run()), None) catch {
      EffektError::Fatal(msg) => (None, Some(msg))
      EffektError::Internal(m) => raise EffektError::Internal(m)
    }
  })
  let failed = muted_error || failure is Some(_)
  if failed {
    self.cutoff = cut_off
    self.abort_message(implicit_failure(span, stencil, tpe, errors, failure))
  }
  for entry in infos {
    self.info(entry.0, entry.1)
  }
  result.unwrap()
}

///|
/// Generates the tree of an implicit argument (upstream's stencil, which
/// `GenerateImplicitArgs` resolves *before* the tree is checked). A stencil that
/// cannot be resolved at all — the name it stands for is not bound — is reported
/// at the call itself, since that is where upstream's `Error` stencil aborts: at
/// the current focus, not at the generated tree.
fn[T] Typer::generate_implicit(
  self : Typer,
  /// The call whose implicit argument is being generated; a failure is reported
  /// here (upstream's stencil aborts at the focus).
  span : Span,
  stencil : ImplicitStencil,
  tpe : String,
  generate : () -> T raise EffektError,
) -> T raise EffektError {
  let ((value, failure), _, errors, infos, cut_off) = self.muted(() => {
    (Some(generate()), None) catch {
      EffektError::Fatal(msg) => (None, Some(msg))
      EffektError::Internal(m) => raise EffektError::Internal(m)
    }
  })
  if failure is Some(_) {
    self.cutoff = cut_off
    // Upstream aborts at the *focus*, so everything the attempt recorded is
    // reported at the call: the stencil is resolved before there is a tree to
    // point at.
    let errors = errors.map(entry => { ..entry, span, })
    self.abort_message(implicit_failure(span, stencil, tpe, errors, failure))
  }
  for entry in infos {
    self.info(entry.0, entry.1)
  }
  value.unwrap()
}

///|
/// The diagnostic of an implicit argument that cannot be instantiated
/// (upstream `ImplicitInstantiation`): the claim, one line naming the argument
/// and its type, the stencil's explanation, and the nested diagnostics of the
/// failure — each drawn with its own place one gutter deeper.
///
/// `span` is where the failure is reported: the call for a stencil that cannot be
/// resolved, the argument list for a generated tree that does not type check.
fn implicit_failure(
  span : Span,
  stencil : ImplicitStencil,
  tpe : String,
  errors : ArrayView[Message],
  failure : String?,
) -> Message {
  let details : Array[String] = [
    "Cannot instantiate \{ordinal(stencil.index)} \{stencil.kind} \{stencil.name} of type \{tpe}.",
  ]
  if stencil.explanation is Some(explanation) {
    for line in explanation.split("\n") {
      details.push(line.to_owned())
    }
  }
  let mut message = Message::error(
    span, "Cannot instantiate implicit argument.",
  ).details(details)
  for entry in errors {
    message = message.cause(entry)
  }
  if errors.is_empty() && failure is Some(msg) {
    // The attempt aborted without recording a diagnostic of its own: the message
    // it aborted with is what made it fail.
    message = message.cause(Message::error(span, msg))
  }
  message
}

///|
/// The lexical context of a call site, as recorded by the namer: the scope
/// chain and the names opened from the imported modules.
///
/// Upstream resolves an implicit argument with `scope.lookupOverloaded`, where
/// its `Scoping` consults the bindings of the scope chain *and* the imports.
/// The two live in different places in this port (the imports only exist while
/// the namer runs), so the namer records both.
priv struct ImplicitScope {
  scope : @symbols.Scope
  imports : @symbols.Bindings
}

///|
fn Typer::implicit_scope(
  self : Typer,
  call : CallLike,
) -> ImplicitScope raise EffektError {
  match self.ctx.call_scope_of(call.uid) {
    Some(scope) =>
      {
        scope,
        imports: self.ctx
        .call_imports_of(call.uid)
        .unwrap_or(@symbols.Bindings::empty()),
      }
    None =>
      self.abort(
        call.span,
        "Internal: the namer did not record a scope for this call site.",
      )
  }
}

///|
fn Typer::var_term_for(self : Typer, sym : Sym, span : Span) -> Term {
  let name = sym.name().name
  let id = @source.IdRef(name, span)
  self.assign_symbol(id.uid, sym)
  mk_term(span, @source.TermKind::Var(id))
}

///|
fn int_literal_term(value : Int64, span : Span) -> Term {
  mk_term(span, @source.TermKind::Literal(@source.LInt(value), t_int()))
}

///|
/// `?name: T` where `T` is not special: the term bound to `name`.
fn Typer::implicit_var_term(
  self : Typer,
  call : CallLike,
  span : Span,
  name : String,
) -> Term raise EffektError {
  let scope = self.implicit_scope(call)
  match @symbols.lookup_term_in_scope(scope.scope, scope.imports, name) {
    Some(sym) => self.var_term_for(sym, span.synthesized())
    None =>
      // Upstream's `Scope.lookupFirstTerm`: the failure is reported at the
      // generated reference and ends up nested under "Cannot instantiate ...".
      self.abort(span.synthesized(), "Could not resolve term \{name}")
  }
}

///|
/// `?sourcePosition: String`: calls the function `SourcePosition` with the file
/// name and the 1-based start / end line and column of the call.
fn Typer::source_position_term(
  self : Typer,
  call : CallLike,
) -> Term? raise EffektError {
  let scope = self.implicit_scope(call)
  let candidates = @symbols.lookup_functions_in_scope(
    scope.scope,
    scope.imports,
    "SourcePosition",
  )
  guard !candidates.is_empty() else { return None }
  let span = call.span.synthesized()
  let from = call.span.source.offset_to_position(call.span.start)
  let to = call.span.source.offset_to_position(call.span.end)
  let file = mk_term(
    span,
    @source.TermKind::Literal(
      @source.LString(call.span.source.name),
      t_string(),
    ),
  )
  let args : Array[@source.ValueArg] = [
    @source.ValueArg::unnamed(file),
    @source.ValueArg::unnamed(int_literal_term(from.line.to_int64(), span)),
    @source.ValueArg::unnamed(int_literal_term(from.column.to_int64(), span)),
    @source.ValueArg::unnamed(int_literal_term(to.line.to_int64(), span)),
    @source.ValueArg::unnamed(int_literal_term(to.column.to_int64(), span)),
  ]
  let target = @source.IdRef("SourcePosition", span)
  self.assign_symbol(
    target.uid,
    @symbols.Sym::call_target(candidates, Some(scope.scope)),
  )
  let call = mk_term(
    span,
    @source.TermKind::Call(@source.CallTarget::IdTarget(target), [], args, []),
  )
  self.st.ann = {
    ..self.st.ann,
    implicit_calls: self.st.ann.implicit_calls.add(call.uid, true),
  }
  self.ctx.assign_call_scope(call.uid, scope.scope)
  self.ctx.assign_call_imports(call.uid, scope.imports)
  Some(call)
}

///|
/// `{ ?name: (A) => B }`: an eta-expanded call to the function `name`, i.e.
/// `{ (arg0: A) => name(arg0) }` (upstream `instantiateImplicitBlock`).
fn Typer::implicit_block_term(
  self : Typer,
  call : CallLike,
  span : Span,
  name : String,
  btpe : BlockType,
) -> Term raise EffektError {
  match btpe {
    @symbols.BlockType::InterfaceType(_, _) =>
      self.implicit_var_term(call, span, name)
    @symbols.BlockType::FunctionType(_, _, vps, bps, _, _) => {
      let span = span.synthesized()
      let vparams : Array[@source.ValueParam] = []
      let vargs : Array[@source.ValueArg] = []
      for i, vp in vps {
        let pname = "value_arg\{i}"
        let sym = Sym::value_param(Name::local(pname), Some(vp), span)
        let id = @source.IdDef(pname, span)
        self.assign_symbol(id.uid, sym)
        vparams.push({
          id,
          tpe: Some(mk_type(span, @source.ValueTypeTree(vp))),
          is_implicit: false,
        })
        vargs.push(@source.ValueArg::unnamed(self.var_term_for(sym, span)))
      }
      let bparams : Array[@source.BlockParam] = []
      let bargs : Array[Term] = []
      for j, bp in bps {
        let pname = "block_arg\{j}"
        let capture = Sym::capture_param(Name::local(pname))
        let sym = Sym::block_param(
          Name::local(pname),
          Some(bp),
          capture,
          false,
          span,
        )
        let id = @source.IdDef(pname, span)
        self.assign_symbol(id.uid, sym)
        bparams.push({
          id,
          tpe: Some(mk_type(span, @source.BlockTypeTree(bp))),
          is_implicit: false,
        })
        bargs.push(self.var_term_for(sym, span))
      }
      let scope = self.implicit_scope(call)
      // Like for `f(...)`: a value in the innermost scope shadows the blocks
      // (upstream calls `resolveFunctionCalltarget` here), so no candidate is
      // left and the generated call fails — instead of silently using a function
      // of the same name from an outer scope.
      let candidates = @symbols.block_candidates(
        @symbols.lookup_terms_in_scope(scope.scope, scope.imports, name),
      )
      let target = @source.IdRef(name, span)
      self.assign_symbol(
        target.uid,
        @symbols.Sym::call_target(candidates, Some(scope.scope)),
      )
      let callee = mk_term(
        span,
        @source.TermKind::Call(
          @source.CallTarget::IdTarget(target),
          [],
          vargs,
          bargs,
        ),
      )
      // The generated call is itself a call site: record the scope, so that
      // implicit arguments *it* needs (recursive implicits, e.g. `typeTag` or
      // `myShow` for a list) can be resolved the same way.
      self.ctx.assign_call_scope(callee.uid, scope.scope)
      self.ctx.assign_call_imports(callee.uid, scope.imports)
      self.st.ann = {
        ..self.st.ann,
        implicit_calls: self.st.ann.implicit_calls.add(callee.uid, true),
      }
      let body = mk_stmt(span, @source.StmtKind::Return(callee))
      mk_term(span, @source.TermKind::BlockLiteral([], vparams, bparams, body))
    }
  }
}

///|
/// `?name: (A) => B at {}`: box the block literal that the corresponding
/// implicit block argument would generate (upstream `BoxedStencil`).
fn Typer::implicit_boxed_term(
  self : Typer,
  call : CallLike,
  span : Span,
  name : String,
  btpe : BlockType,
) -> Term raise EffektError {
  let span = span.synthesized()
  let block = self.implicit_block_term(call, span, name, btpe)
  mk_term(span, @source.TermKind::Box(None, block))
}

///|
/// Generates the implicit value argument for `param` (`?name: tpe`).
fn Typer::implicit_value_term(
  self : Typer,
  call : CallLike,
  span : Span,
  param : Sym,
  tpe : ValueType,
) -> Term raise EffektError {
  let name = param.name().name
  match name {
    "callId" =>
      int_literal_term(@util.fresh_uid().to_int64(), span.synthesized())
    "sourcePosition" =>
      match self.source_position_term(call) {
        Some(t) => t
        None => self.implicit_var_term(call, span, name)
      }
    _ =>
      match tpe {
        @symbols.ValueType::BoxedType(btpe, _) =>
          self.implicit_boxed_term(call, span, name, btpe)
        _ => self.implicit_var_term(call, span, name)
      }
  }
}

///|
/// Generates the implicit block argument for `param` (`{ ?name: btpe }`).
fn Typer::implicit_block_arg_term(
  self : Typer,
  call : CallLike,
  span : Span,
  param : Sym,
  btpe : BlockType,
) -> Term raise EffektError {
  self.implicit_block_term(call, span, param.name().name, btpe)
}

// ---------------------------------------------------------------------------
// The recursion guard
// ---------------------------------------------------------------------------

///|
/// How many nested instantiations of the same name may keep the type from
/// getting smaller before the candidate is given up (upstream
/// `GenerateImplicitArgs.maxRecurse`).
let max_implicit_recursion : Int32 = 10

///|
/// The size of a value type (upstream `GenerateImplicitArgs.typeSize`). The
/// guard below only counts a recursion level when this number does not shrink,
/// so an instantiation that reaches a structurally smaller type is progress —
/// `?display: List[Int] => String` resolving through `list::display` to
/// `?display: Int => String` — while one that keeps solving a type variable
/// (`?A := List[?B]` forever) is not.
fn value_type_size(t : @symbols.ValueType) -> Int32 {
  match t {
    @symbols.ValueType::BoxedType(block, _) => 1 + block_type_size(block)
    @symbols.ValueType::ValueTypeRef(_) => 5
    @symbols.ValueType::ValueTypeApp(_, args) =>
      1 + args.fold(init=0, (acc, arg) => acc + value_type_size(arg))
  }
}

///|
fn block_type_size(t : @symbols.BlockType) -> Int32 {
  match t {
    @symbols.BlockType::FunctionType(tparams, cparams, vps, bps, result, effs) => {
      let mut size = tparams.length() +
        cparams.length() +
        value_type_size(result)
      for vp in vps {
        size = size + value_type_size(vp)
      }
      for bp in bps {
        size = size + block_type_size(bp)
      }
      size + effects_size(effs)
    }
    @symbols.BlockType::InterfaceType(_, args) =>
      1 + args.fold(init=0, (acc, arg) => acc + value_type_size(arg))
  }
}

///|
fn effects_size(effs : @symbols.Effects) -> Int32 {
  effs.effects.fold(init=0, (acc, eff) => acc + 1 + block_type_size(eff))
}

///|
/// Runs `run` under the recursion guard of the name-based implicit arguments.
///
/// Mirrors upstream `GenerateImplicitArgs.recursionGuard`: an instantiation of
/// `name` whose type is not smaller than the previous one at the same name is
/// a recursion level, and more than `max_implicit_recursion` of those means the
/// search is not making progress. Without the guard the generated eta-expanded
/// call of an implicit whose type is still an unsolved unification variable
/// keeps solving `?A := List[?B]` and the substitution chain grows without
/// bound (the whole compiler hangs; `examples/pos/name-based-implicits/display`
/// is the smallest program that shows it).
///
/// Upstream additionally retries the body with a growing budget
/// (`iterativeDeepening`); the budget is fixed here at `max_implicit_recursion`
/// because a legitimate chain — `?display` for a `List` — shrinks the type at
/// every level and therefore never counts against the budget at all.
fn[T] Typer::with_implicit_guard(
  self : Typer,
  name : String,
  size : Int32,
  run : () -> T raise EffektError,
) -> T raise EffektError {
  let before = self.st.implicit_stack.get(name)
  let (depth, last_size) = match before {
    Some(entry) => entry
    None => (0, size)
  }
  let grew = size >= last_size
  let depth = if grew { depth + 1 } else { depth }
  if grew && depth > max_implicit_recursion {
    // Upstream reports `ImplicitMaxRecursion`, which is `undecided`: the search
    // was cut off, so the enclosing candidate is not *known* to fail.
    self.cutoff = true
    self.abort(
      self.focus,
      "Aborted recursive instantiation of the implicit argument \{name} after \{max_implicit_recursion} levels with non-decreasing types.",
    )
  }
  self.st.implicit_stack.set(name, (depth, size))
  let result = run()
  // A failure leaves the entry behind; the enclosing overload candidate is
  // rolled back as a whole, so it cannot leak into a sibling attempt.
  match before {
    Some(entry) => self.st.implicit_stack.set(name, entry)
    None => ignore(self.st.implicit_stack.remove(name))
  }
  result
}
