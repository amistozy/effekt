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
  let id = @source.IdRef::new(name, span)
  self.ctx.assign_symbol(id.uid, sym)
  mk_term(span, @source.TermKind::Var(id))
}

///|
fn int_literal_term(value : Int32, span : Span) -> Term {
  mk_term(span, @source.TermKind::Literal(@source.LInt(value), t_int()))
}

///|
/// `?name: T` where `T` is not special: the term bound to `name`.
fn Typer::implicit_var_term(
  self : Typer,
  call : CallLike,
  name : String,
) -> Term raise EffektError {
  let scope = self.implicit_scope(call)
  match @symbols.lookup_term_in_scope(scope.scope, scope.imports, name) {
    Some(sym) => self.var_term_for(sym, call.span.synthesized())
    None =>
      self.abort(
        call.span,
        "Cannot resolve the implicit argument \{name}: no term of that name is in scope.",
      )
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
  if candidates.length() == 0 {
    return None
  }
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
    @source.ValueArg::unnamed(int_literal_term(from.line, span)),
    @source.ValueArg::unnamed(int_literal_term(from.column, span)),
    @source.ValueArg::unnamed(int_literal_term(to.line, span)),
    @source.ValueArg::unnamed(int_literal_term(to.column, span)),
  ]
  let target = @source.IdRef::new("SourcePosition", span)
  self.ctx.assign_symbol(target.uid, @symbols.Sym::call_target(candidates))
  let call = mk_term(
    span,
    @source.TermKind::Call(@source.CallTarget::IdTarget(target), [], args, []),
  )
  self.st.ann.implicit_calls.set(call.uid, true)
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
  name : String,
  btpe : BlockType,
) -> Term raise EffektError {
  match btpe {
    @symbols.BlockType::InterfaceType(_, _) =>
      self.implicit_var_term(call, name)
    @symbols.BlockType::FunctionType(_, _, vps, bps, _, _) => {
      let span = call.span.synthesized()
      let vparams : Array[@source.ValueParam] = []
      let vargs : Array[@source.ValueArg] = []
      for i, vp in vps {
        let pname = "value_arg\{i}"
        let sym = Sym::value_param(Name::local(pname), Some(vp), span)
        let id = @source.IdDef::new(pname, span)
        self.ctx.assign_symbol(id.uid, sym)
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
        let id = @source.IdDef::new(pname, span)
        self.ctx.assign_symbol(id.uid, sym)
        bparams.push({
          id,
          tpe: Some(mk_type(span, @source.BlockTypeTree(bp))),
          is_implicit: false,
        })
        bargs.push(self.var_term_for(sym, span))
      }
      let scope = self.implicit_scope(call)
      let candidates = @symbols.lookup_functions_in_scope(
        scope.scope,
        scope.imports,
        name,
      )
      if candidates.length() == 0 {
        self.abort(
          call.span,
          "Cannot resolve the implicit block argument \{name}: no function of that name is in scope.",
        )
      }
      let target = @source.IdRef::new(name, span)
      self.ctx.assign_symbol(target.uid, @symbols.Sym::call_target(candidates))
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
      self.st.ann.implicit_calls.set(callee.uid, true)
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
  name : String,
  btpe : BlockType,
) -> Term raise EffektError {
  let span = call.span.synthesized()
  let block = self.implicit_block_term(call, name, btpe)
  mk_term(span, @source.TermKind::Box(None, block))
}

///|
/// Generates the implicit value argument for `param` (`?name: tpe`).
fn Typer::implicit_value_term(
  self : Typer,
  call : CallLike,
  param : Sym,
  tpe : ValueType,
) -> Term raise EffektError {
  let name = param.name().name
  match name {
    "callId" => int_literal_term(@util.fresh_uid(), call.span.synthesized())
    "sourcePosition" =>
      match self.source_position_term(call) {
        Some(t) => t
        None => self.implicit_var_term(call, name)
      }
    _ =>
      match tpe {
        @symbols.ValueType::BoxedType(btpe, _) =>
          self.implicit_boxed_term(call, name, btpe)
        _ => self.implicit_var_term(call, name)
      }
  }
}

///|
/// Generates the implicit block argument for `param` (`{ ?name: btpe }`).
fn Typer::implicit_block_arg_term(
  self : Typer,
  call : CallLike,
  param : Sym,
  btpe : BlockType,
) -> Term raise EffektError {
  self.implicit_block_term(call, param.name().name, btpe)
}
