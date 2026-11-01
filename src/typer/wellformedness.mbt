// Wellformedness of inferred types.
//
// Mirrors the parts of `effekt/typer/Wellformedness.scala` that matter for the
// JavaScript backend: capabilities and regions must not escape through the
// type of a value that outlives them.
//
// Upstream tracks a `WFContext` of types and captures in scope while
// traversing the already type checked tree. We check the same property
// *locally* at the places where an escape would be observable (the return type
// of a handled statement, of a function body, of a block literal body and of a
// region body), which gives the same diagnostics for the common cases.
//
// Not implemented (see the report): scope extrusion of type parameters of
// existentials / higher-rank functions, and the exhaustivity-related parts
// (those live in `exhaustivity.mbt`).

///|
/// The free captures of a capture set: capture parameters and lexical regions
/// are free, resources (`io`, `global`, ...) are not — like upstream.
pub fn free_captures(c : Captures) -> Array[Sym] {
  match c {
    @symbols.Captures::CaptureSetOf(cs) => cs.filter(s => is_free_capture(s))
    @symbols.Captures::CaptVar(x) => [x]
  }
}

///|
fn is_free_capture(s : Sym) -> Bool {
  match s {
    @symbols.Sym::CaptureParam(_) => true
    @symbols.Sym::LexicalRegion(_) => true
    /// Unification variables are an artifact of inference, not a capture a
    /// binder could drop (upstream `freeCapture` only matches the concrete
    /// constructors), so they are not free.
    @symbols.Sym::CaptUnificationVar(_) => false
    _ => false
  }
}

///|
pub fn free_captures_value(t : ValueType) -> Array[Sym] {
  match t {
    @symbols.ValueType::ValueTypeRef(_) => []
    @symbols.ValueType::ValueTypeApp(_, args) => {
      let out : Array[Sym] = []
      for a in args {
        push_new(out, free_captures_value(a))
      }
      out
    }
    @symbols.ValueType::BoxedType(b, c) => {
      let out = free_captures_block(b)
      push_new(out, free_captures(c))
      out
    }
  }
}

///|
pub fn free_captures_block(t : BlockType) -> Array[Sym] {
  match t {
    @symbols.BlockType::InterfaceType(_, args) => {
      let out : Array[Sym] = []
      for a in args {
        push_new(out, free_captures_value(a))
      }
      out
    }
    @symbols.BlockType::FunctionType(_, capts, vps, bps, ret, effs) => {
      let bound = capture_params_of(capts)
      let out : Array[Sym] = []
      for v in vps {
        push_new(out, free_captures_value(v))
      }
      for b in bps {
        push_new(out, free_captures_block(b))
      }
      for e in effs.effects {
        push_new(out, free_captures_block(e))
      }
      for c in capts {
        push_new(out, free_captures(c))
      }
      push_new(out, free_captures_value(ret))
      out.filter(c => !bound.contains(c))
    }
  }
}

///|
/// The free type parameters of a value type.
pub fn free_types_value(t : ValueType, bound : Array[Sym]) -> Array[Sym] {
  match t {
    @symbols.ValueType::ValueTypeRef(x) =>
      if bound.contains(x) {
        []
      } else {
        match x {
          @symbols.Sym::TypeParam(_) => [x]
          _ => []
        }
      }
    @symbols.ValueType::ValueTypeApp(_, args) => {
      let out : Array[Sym] = []
      for a in args {
        push_new(out, free_types_value(a, bound))
      }
      out
    }
    @symbols.ValueType::BoxedType(b, _) => free_types_block(b, bound)
  }
}

///|
pub fn free_types_block(t : BlockType, bound : Array[Sym]) -> Array[Sym] {
  match t {
    @symbols.BlockType::InterfaceType(_, args) => {
      let out : Array[Sym] = []
      for a in args {
        push_new(out, free_types_value(a, bound))
      }
      out
    }
    @symbols.BlockType::FunctionType(tparams, _, vps, bps, ret, effs) => {
      let inner = bound + tparams
      let out : Array[Sym] = []
      for v in vps {
        push_new(out, free_types_value(v, inner))
      }
      for b in bps {
        push_new(out, free_types_block(b, inner))
      }
      for e in effs.effects {
        push_new(out, free_types_block(e, inner))
      }
      push_new(out, free_types_value(ret, inner))
      out
    }
  }
}

///|
fn push_new(out : Array[Sym], xs : Array[Sym]) -> Unit {
  for x in xs {
    if !out.contains(x) {
      out.push(x)
    }
  }
}

///|
/// Checks that the captures bound by a handler / function / region do not
/// escape through an inferred type.
pub fn Typer::check_no_capture_escape(
  self : Typer,
  bound : Array[Sym],
  free : Array[Sym],
  span : Span,
  msg : String,
) -> Unit {
  let escaping = free.filter(c => bound.contains(c))
  if escaping.length() > 0 {
    self.error(
      span,
      "\{msg} Escaping: \{@symbols.Captures::CaptureSetOf(escaping)}",
    )
  }
}

// ---------------------------------------------------------------------------
// Escapes of captures through inferred types
// ---------------------------------------------------------------------------
//
// Upstream runs a `Visit` over the checked tree with a `WFContext` of the type
// and capture parameters that are in scope (`effekt/typer/Wellformedness.scala`)
// and reports every capture of an inferred type that is *not* in scope: a
// binder introduces captures for its body, and a type inferred in that body may
// not mention captures the binder will drop again (a region's region, a
// handler's capabilities, a block literal's parameters).
//
// The check is therefore only sound with the scopes: the same type is fine
// inside the binder and an escape outside it.
//
// Not implemented: the reports for type parameters of existentials and
// higher-rank functions (their scopes are tracked, but nothing is reported).

///|
/// The captures that are in scope while the tree is walked (upstream
/// `WFContext`).
priv struct WFScope {
  captures : Array[Sym]
}

///|
fn WFScope::empty() -> WFScope {
  { captures: [], }
}

///|
/// Extends the scope by the given captures.
fn WFScope::bind(self : WFScope, captures : Array[Sym]) -> WFScope {
  let cs = self.captures.copy()
  for c in captures {
    if !cs.contains(c) {
      cs.push(c)
    }
  }
  { captures: cs, }
}

///|
/// Runs the escape checks over a checked module (upstream `Wellformedness`).
pub fn Typer::check_capture_escapes(self : Typer, module : ModuleDecl) -> Unit {
  for d in module.defs {
    self.wf_def(d, WFScope::empty())
  }
}

///|
/// The captures a capability binder binds (`BlockParam.capture`).
fn Typer::wf_capability_captures(self : Typer, uid : Int32) -> Array[Sym] {
  let out : Array[Sym] = []
  for c in self.ctx.bound_capabilities_of(uid) {
    let capt = capture_of_capability(c)
    if !out.contains(capt) {
      out.push(capt)
    }
  }
  out
}

///|
/// The captures of a parameter list. The symbols are looked up leniently: a
/// tree that a test built by hand may not have a symbol for every parameter.
fn Typer::wf_param_captures(
  self : Typer,
  bparams : Array[@source.BlockParam],
) -> Array[Sym] {
  let out : Array[Sym] = []
  for bp in bparams {
    match self.ctx.symbol_of(bp.id.uid) {
      Some(sym) =>
        for c in self.lookup_capture(sym).to_array() {
          if !out.contains(c) {
            out.push(c)
          }
        }
      None => ()
    }
  }
  out
}

///|
/// The captures a mutable variable or a region binder introduces. Two symbols
/// are involved: `VarDef` binds the binder symbol itself as the current
/// capture, while a use of the variable flows its `capture` (a
/// `LexicalRegion`) into the inferred type. Both have to count as in scope.
fn Typer::wf_mutable_captures(self : Typer, sym : Sym) -> Array[Sym] {
  let out = self.lookup_capture(sym).to_array()
  match sym {
    @symbols.Sym::VarBinder(v) =>
      if !out.contains(v.capture) {
        out.push(v.capture)
      }
    @symbols.Sym::RegBinder(r) =>
      if !out.contains(r.region) {
        out.push(r.region)
      }
    _ => ()
  }
  out
}

///|
/// The captures of a type that a passing binder could drop. Capture variables
/// still present in a committed type are inference artifacts (they are created
/// by `fresh_capt_var` as `CaptureParam`s, so the symbol kind alone does not
/// identify them).
fn Typer::free_captures_of(self : Typer, t : ValueType) -> Array[Sym] {
  free_captures_value(t).filter(c => !self.st.u.is_capt_var(c))
}

///|
/// Reports the captures of `tpe` that are not in `scope` (upstream
/// `Wellformedness.wellformed`).
fn Typer::wf_check(
  self : Typer,
  tpe : ValueType,
  span : Span,
  scope : WFScope,
  detail : String,
) -> Unit {
  let escaping = self
    .free_captures_of(tpe)
    .filter(c => !scope.captures.contains(c))
  if escaping.length() == 0 {
    return
  }
  let message = if escaping.length() == 1 {
    "Capture \{escaping[0].name().name} escapes through type \{tpe}\{detail}."
  } else {
    "Captures \{@symbols.Captures::CaptureSetOf(escaping)} escape through type \{tpe}\{detail}."
  }
  self.error(span, message)
}

///|
/// The check for the return type of a handled statement: the bound
/// capabilities are gone when the statement returns, so the type may not
/// mention any of them (upstream's specific message for `TryHandle`).
fn Typer::wf_check_handled(
  self : Typer,
  tpe : ValueType,
  span : Span,
  scope : WFScope,
  bound : Array[Sym],
) -> Unit {
  let free = self.free_captures_of(tpe)
  let mentioned = free.filter(c => bound.contains(c))
  if mentioned.length() > 0 {
    self.error(
      span,
      "The return type \{tpe} of the handled statement is not allowed to refer to any of the bound capabilities, but mentions: \{@symbols.Captures::CaptureSetOf(mentioned)}.",
    )
  }
  self.wf_check(
    tpe, span, scope, " inferred as return type of the handled statement",
  )
}

///|
fn Typer::wf_def(self : Typer, d : Def, scope : WFScope) -> Unit {
  match d.kind {
    @source.DefKind::FunDef(id, _, _, bparams, _, _, body) => {
      let captures = self.wf_capability_captures(d.uid) +
        self.wf_param_captures(bparams)
      let inner = scope.bind(captures)
      self.wf_stmt(body, inner)
      match self.ctx.value_type_of(body.uid) {
        Some(tpe) =>
          self.wf_check(
            tpe,
            body.span,
            inner,
            " inferred as return type of \{id.name}",
          )
        None => ()
      }
    }
    @source.DefKind::RegDef(_, _, _, init) => self.wf_stmt(init, scope)
    @source.DefKind::ValDef(_, _, body) => self.wf_stmt(body, scope)
    @source.DefKind::VarDef(_, _, body) => self.wf_stmt(body, scope)
    @source.DefKind::DefDef(_, _, _, body) => self.wf_term(body, scope)
    @source.DefKind::NamespaceDef(_, defs) =>
      for inner in defs {
        self.wf_def(inner, scope)
      }
    _ => ()
  }
}

///|
fn Typer::wf_stmt(self : Typer, s : Stmt, scope : WFScope) -> Unit {
  match s.kind {
    @source.StmtKind::DefStmt(d, rest) =>
      match d.kind {
        @source.DefKind::VarDef(id, _, rhs) => {
          // The variable's own capture is in scope for the initial value and
          // for the rest of the computation, but not outside it: the type of
          // the rest has to be checked before it is added.
          let var_captures = match self.ctx.symbol_of(id.uid) {
            Some(sym) => self.wf_mutable_captures(sym)
            None => []
          }
          match self.ctx.value_type_of(rest.uid) {
            Some(tpe) => {
              let escaping = self
                .free_captures_of(tpe)
                .filter(c => var_captures.contains(c))
              if escaping.length() > 0 {
                self.error(
                  s.span,
                  "Local variable \{id.name} escapes through the returned value of type \{tpe}.",
                )
              }
            }
            None => ()
          }
          let inner = scope.bind(var_captures)
          self.wf_stmt(rhs, inner)
          self.wf_stmt(rest, inner)
        }
        _ => {
          self.wf_def(d, scope)
          self.wf_stmt(rest, scope)
        }
      }
    @source.StmtKind::ExprStmt(e, rest) => {
      self.wf_term(e, scope)
      self.wf_stmt(rest, scope)
    }
    @source.StmtKind::Return(e) => self.wf_term(e, scope)
    @source.StmtKind::BlockStmt(inner) => self.wf_stmt(inner, scope)
  }
}

///|
fn Typer::wf_term(self : Typer, t : Term, scope : WFScope) -> Unit {
  match t.kind {
    @source.TermKind::Var(_) | @source.TermKind::Literal(_, _) => ()
    @source.TermKind::Assign(_, e) => self.wf_term(e, scope)
    @source.TermKind::Hole(_, template) =>
      for s in template.args {
        self.wf_stmt(s, scope)
      }
    @source.TermKind::Box(_, block) => self.wf_term(block, scope)
    @source.TermKind::Unbox(inner) => self.wf_term(inner, scope)
    @source.TermKind::Select(receiver, _) => self.wf_term(receiver, scope)
    @source.TermKind::Do(_, _, vargs, bargs) => {
      self.wf_type_arguments(t.uid, t.span, scope)
      self.wf_args(vargs, bargs, scope)
    }
    @source.TermKind::Call(target, _, vargs, bargs) => {
      match target {
        @source.CallTarget::ExprTarget(e) => self.wf_term(e, scope)
        @source.CallTarget::IdTarget(_) => ()
      }
      self.wf_type_arguments(t.uid, t.span, scope)
      self.wf_args(vargs, bargs, scope)
    }
    @source.TermKind::MethodCall(receiver, _, _, vargs, bargs) => {
      self.wf_term(receiver, scope)
      self.wf_type_arguments(t.uid, t.span, scope)
      self.wf_args(vargs, bargs, scope)
    }
    @source.TermKind::If(guards, thn, els) => {
      self.wf_guards(guards, scope)
      self.wf_stmt(thn, scope)
      self.wf_stmt(els, scope)
      match self.ctx.value_type_of(t.uid) {
        Some(tpe) =>
          self.wf_check(
            tpe,
            t.span,
            scope,
            " inferred for the result of the if statement",
          )
        None => ()
      }
    }
    @source.TermKind::While(guards, body, default) => {
      self.wf_guards(guards, scope)
      self.wf_stmt(body, scope)
      match default {
        Some(d) => self.wf_stmt(d, scope)
        None => ()
      }
      match self.ctx.value_type_of(t.uid) {
        Some(tpe) =>
          self.wf_check(
            tpe,
            t.span,
            scope,
            " inferred for the result of the while statement",
          )
        None => ()
      }
    }
    @source.TermKind::Match(scrutinees, clauses, default) => {
      for sc in scrutinees {
        self.wf_term(sc, scope)
      }
      for c in clauses {
        self.wf_guards(c.guards, scope)
        self.wf_stmt(c.body, scope)
      }
      match default {
        Some(d) => self.wf_stmt(d, scope)
        None => ()
      }
      match self.ctx.value_type_of(t.uid) {
        Some(tpe) =>
          self.wf_check(
            tpe,
            t.span,
            scope,
            " inferred as return type of the match",
          )
        None => ()
      }
    }
    @source.TermKind::TryHandle(prog, handlers) => {
      // The capabilities the handler binds are in scope for the handled
      // program, but not for the handlers themselves, and not once the
      // statement returns.
      let bound = self.wf_capability_captures(t.uid)
      self.wf_stmt(prog, scope.bind(bound))
      for h in handlers {
        self.wf_implementation(h.implementation, scope)
      }
      match self.ctx.value_type_of(prog.uid) {
        Some(tpe) => self.wf_check_handled(tpe, prog.span, scope, bound)
        None => ()
      }
    }
    @source.TermKind::Region(id, body) => {
      let capture = match self.ctx.symbol_of(id.uid) {
        Some(sym) => self.lookup_capture(sym).to_array()
        None => []
      }
      let inner = scope.bind(capture)
      self.wf_stmt(body, inner)
      match self.ctx.value_type_of(body.uid) {
        Some(tpe) => {
          let escaping = self
            .free_captures_of(tpe)
            .filter(c => capture.contains(c))
          if escaping.length() > 0 {
            self.error(
              body.span,
              "The return type \{tpe} of the region body is not allowed to refer to region \{id.name}.",
            )
          }
          self.wf_check(
            tpe,
            body.span,
            inner,
            " inferred as return type of the region body",
          )
        }
        None => ()
      }
    }
    @source.TermKind::BlockLiteral(_, _, bparams, body) => {
      let captures = self.wf_capability_captures(t.uid) +
        self.wf_param_captures(bparams)
      let inner = scope.bind(captures)
      self.wf_stmt(body, inner)
      match self.ctx.value_type_of(body.uid) {
        Some(tpe) =>
          self.wf_check(tpe, t.span, inner, " inferred as return type")
        None => ()
      }
    }
    @source.TermKind::New(implementation) =>
      self.wf_implementation(implementation, scope)
  }
}

///|
fn Typer::wf_type_arguments(
  self : Typer,
  uid : Int32,
  span : Span,
  scope : WFScope,
) -> Unit {
  for tpe in self.ctx.type_arguments_of(uid) {
    self.wf_check(tpe, span, scope, " inferred as a type argument")
  }
}

///|
fn Typer::wf_args(
  self : Typer,
  vargs : Array[ValueArg],
  bargs : Array[Term],
  scope : WFScope,
) -> Unit {
  for a in vargs {
    self.wf_term(a.value, scope)
  }
  for b in bargs {
    self.wf_term(b, scope)
  }
}

///|
fn Typer::wf_guards(
  self : Typer,
  guards : Array[MatchGuard],
  scope : WFScope,
) -> Unit {
  for g in guards {
    match g.kind {
      @source.GuardKind::BooleanGuard(e) => self.wf_term(e, scope)
      @source.GuardKind::PatternGuard(scrutinee, _) =>
        self.wf_term(scrutinee, scope)
    }
  }
}

///|
fn Typer::wf_implementation(
  self : Typer,
  implementation : Implementation,
  scope : WFScope,
) -> Unit {
  for clause in implementation.clauses {
    let captures = self.wf_capability_captures(clause.uid) +
      self.wf_param_captures(clause.bparams)
    let inner = scope.bind(captures)
    self.wf_stmt(clause.body, inner)
    match self.ctx.value_type_of(clause.body.uid) {
      Some(tpe) =>
        self.wf_check(
          tpe,
          clause.body.span,
          inner,
          " inferred as return type of operation \{clause.id.name}",
        )
      None => ()
    }
  }
}
