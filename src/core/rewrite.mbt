// A congruence over the core tree.
//
// Mirrors `effekt/core/Tree.scala`'s `trait Rewrite`: every node is rebuilt from
// its rewritten children, and a pass overrides the few node kinds it cares
// about. Upstream expresses that with inheritance; here the overridable parts
// are the hooks of [[Rewrite]], which return a replacement for a node (`Some`)
// or leave it to the congruence (`None`).
//
// The hooks raise `EffektError`, the port's compiler error, so that a pass may
// use the tree annotations (`Stmt::infer_type`, `type.mbt`).
//
// Everything — ids, capture sets, types, declarations, externs — is rebuilt, so
// a hook that maps ids (`on_id`) renames *all* occurrences, exactly like
// upstream's `rewrite(id: Id)`. That is a plain substitution, not a scoped
// renaming: it is for code that rebinds what it renames (see the `renaming` of
// `StaticResumptions::joinpoint`), while `renamer.mbt` freshens binders.

///|
/// See the module comment.
priv struct Rewrite {
  /// Replaces a statement; `None` rebuilds it from the rewritten children.
  on_stmt : ((Rewrite, Stmt) -> Stmt? raise EffektError)?
  /// Replaces a block; `None` rebuilds it from the rewritten children.
  on_block : ((Rewrite, Block) -> Block? raise EffektError)?
  /// Replaces a symbol wherever it occurs, in types and capture sets too.
  on_id : ((Sym) -> Sym)?
  /// Replaces a capture set wherever it occurs.
  on_captures : ((Captures) -> Captures)?
}

///|
fn Rewrite::new(
  on_stmt : ((Rewrite, Stmt) -> Stmt? raise EffektError)?,
  on_id : ((Sym) -> Sym)?,
  on_captures : ((Captures) -> Captures)?,
  on_block : ((Rewrite, Block) -> Block? raise EffektError)?,
) -> Rewrite {
  { on_stmt, on_id, on_captures, on_block, }
}

// ---------------------------------------------------------------------------
// Symbols, capture sets and types
// ---------------------------------------------------------------------------

///|
fn Rewrite::rewrite_id(self : Rewrite, id : Sym) -> Sym {
  match self.on_id {
    Some(f) => f(id)
    None => id
  }
}

///|
fn Rewrite::rewrite_captures(self : Rewrite, capt : Captures) -> Captures {
  match self.on_captures {
    Some(f) => f(capt)
    None =>
      match capt {
        CaptureSetOf(cs) =>
          CaptureSetOf(dedup_syms(cs.map(c => self.rewrite_id(c))))
        CaptVar(c) => CaptVar(self.rewrite_id(c))
      }
  }
}

///|
fn Rewrite::rewrite_value_type(self : Rewrite, tpe : ValueType) -> ValueType {
  match tpe {
    ValueVar(sym) => ValueVar(self.rewrite_id(sym))
    ValueData(sym, targs) =>
      ValueData(
        self.rewrite_id(sym),
        targs.map(t => self.rewrite_value_type(t)),
      )
    ValueBoxed(block, capt) =>
      ValueBoxed(self.rewrite_block_type(block), self.rewrite_captures(capt))
  }
}

///|
fn Rewrite::rewrite_block_type(self : Rewrite, tpe : BlockType) -> BlockType {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result) =>
      FunctionType(
        tparams.map(t => self.rewrite_id(t)),
        cparams.map(c => self.rewrite_captures(c)),
        vparams.map(t => self.rewrite_value_type(t)),
        bparams.map(t => self.rewrite_block_type(t)),
        result.map(t => self.rewrite_value_type(t)),
      )
    InterfaceType(sym, targs) =>
      InterfaceType(
        self.rewrite_id(sym),
        targs.map(t => self.rewrite_value_type(t)),
      )
    PromptType(answer) =>
      PromptType(answer.map(t => self.rewrite_value_type(t)))
    ResumeType(result, answer) =>
      ResumeType(
        result.map(t => self.rewrite_value_type(t)),
        answer.map(t => self.rewrite_value_type(t)),
      )
  }
}

// ---------------------------------------------------------------------------
// Expressions and blocks
// ---------------------------------------------------------------------------

///|
fn Rewrite::rewrite_expr(self : Rewrite, e : Expr) -> Expr raise EffektError {
  match e {
    ValueVar(id, tpe) =>
      ValueVar(self.rewrite_id(id), self.rewrite_value_type(tpe))
    Literal(value, tpe) => Literal(value, self.rewrite_value_type(tpe))
    PureApp(callee, targs, vargs) =>
      PureApp(
        self.rewrite_block_var(callee),
        targs.map(t => self.rewrite_value_type(t)),
        vargs.map(v => self.rewrite_expr(v)),
      )
    Make(data, tag, targs, vargs) =>
      Make(
        self.rewrite_value_type(data),
        self.rewrite_id(tag),
        targs.map(t => self.rewrite_value_type(t)),
        vargs.map(v => self.rewrite_expr(v)),
      )
    Box(block, capt) =>
      Box(self.rewrite_block(block), self.rewrite_captures(capt))
  }
}

///|
fn Rewrite::rewrite_block_var(self : Rewrite, b : BlockVar) -> BlockVar {
  BlockVar::new(
    self.rewrite_id(b.id),
    self.rewrite_block_type(b.annotated_tpe),
    self.rewrite_captures(b.annotated_capt),
  )
}

///|
fn Rewrite::rewrite_block(self : Rewrite, b : Block) -> Block raise EffektError {
  match self.on_block {
    Some(f) =>
      match f(self, b) {
        Some(replacement) => replacement
        None => self.rewrite_block_children(b)
      }
    None => self.rewrite_block_children(b)
  }
}

///|
/// The congruence for blocks: rebuild `b` from its rewritten children.
fn Rewrite::rewrite_block_children(
  self : Rewrite,
  b : Block,
) -> Block raise EffektError {
  match b {
    BlockVar(v) => BlockVar(self.rewrite_block_var(v))
    BlockLit(lit) => BlockLit(self.rewrite_block_lit(lit))
    Unbox(e) => Unbox(self.rewrite_expr(e))
    New(implementation) => New(self.rewrite_implementation(implementation))
  }
}

///|
fn Rewrite::rewrite_block_lit(
  self : Rewrite,
  lit : BlockLit,
) -> BlockLit raise EffektError {
  BlockLit::new(
    lit.tparams.map(t => self.rewrite_id(t)),
    lit.cparams.map(c => self.rewrite_id(c)),
    lit.vparams.map(p => self.rewrite_value_param(p)),
    lit.bparams.map(p => self.rewrite_block_param(p)),
    self.rewrite_stmt(lit.body),
  )
}

///|
fn Rewrite::rewrite_value_param(self : Rewrite, p : ValueParam) -> ValueParam {
  ValueParam(self.rewrite_id(p.id), self.rewrite_value_type(p.tpe))
}

///|
fn Rewrite::rewrite_block_param(self : Rewrite, p : BlockParam) -> BlockParam {
  BlockParam(
    self.rewrite_id(p.id),
    self.rewrite_block_type(p.tpe),
    self.rewrite_captures(p.capt),
  )
}

///|
fn Rewrite::rewrite_clause(
  self : Rewrite,
  clause : Clause,
) -> Clause raise EffektError {
  Clause(clause.tag, self.rewrite_block_lit(clause.body))
}

///|
fn Rewrite::rewrite_implementation(
  self : Rewrite,
  implementation : Implementation,
) -> Implementation raise EffektError {
  Implementation(
    self.rewrite_block_type(implementation.interface),
    implementation.operations.map(op => self.rewrite_operation(op)),
  )
}

///|
fn Rewrite::rewrite_operation(
  self : Rewrite,
  op : Operation,
) -> Operation raise EffektError {
  Operation(
    self.rewrite_id(op.name),
    op.tparams.map(t => self.rewrite_id(t)),
    op.cparams.map(c => self.rewrite_id(c)),
    op.vparams.map(p => self.rewrite_value_param(p)),
    op.bparams.map(p => self.rewrite_block_param(p)),
    self.rewrite_stmt(op.body),
  )
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
fn Rewrite::rewrite_stmt(self : Rewrite, s : Stmt) -> Stmt raise EffektError {
  match self.on_stmt {
    Some(f) =>
      match f(self, s) {
        Some(replacement) => replacement
        None => self.rewrite_stmt_children(s)
      }
    None => self.rewrite_stmt_children(s)
  }
}

///|
/// The congruence: rebuild `s` from its rewritten children.
fn Rewrite::rewrite_stmt_children(
  self : Rewrite,
  s : Stmt,
) -> Stmt raise EffektError {
  match s {
    Def(id, block, body) =>
      Def(
        self.rewrite_id(id),
        self.rewrite_block(block),
        self.rewrite_stmt(body),
      )
    Let(id, binding, body) =>
      Let(
        self.rewrite_id(id),
        self.rewrite_expr(binding),
        self.rewrite_stmt(body),
      )
    ImpureApp(id, callee, targs, vargs, bargs, body) =>
      ImpureApp(
        self.rewrite_id(id),
        self.rewrite_block_var(callee),
        targs.map(t => self.rewrite_value_type(t)),
        vargs.map(v => self.rewrite_expr(v)),
        bargs.map(b => self.rewrite_block(b)),
        self.rewrite_stmt(body),
      )
    Return(exprs) => Return(exprs.map(e => self.rewrite_expr(e)))
    Val(ids, binding, body) =>
      Val(
        ids.map(id => self.rewrite_id(id)),
        self.rewrite_stmt(binding),
        self.rewrite_stmt(body),
      )
    App(callee, targs, vargs, bargs) =>
      App(
        self.rewrite_block(callee),
        targs.map(t => self.rewrite_value_type(t)),
        vargs.map(v => self.rewrite_expr(v)),
        bargs.map(b => self.rewrite_block(b)),
      )
    Invoke(callee, method, method_tpe, targs, vargs, bargs) =>
      Invoke(
        self.rewrite_block(callee),
        self.rewrite_id(method),
        self.rewrite_block_type(method_tpe),
        targs.map(t => self.rewrite_value_type(t)),
        vargs.map(v => self.rewrite_expr(v)),
        bargs.map(b => self.rewrite_block(b)),
      )
    If(cond, thn, els) =>
      If(
        self.rewrite_expr(cond),
        self.rewrite_stmt(thn),
        self.rewrite_stmt(els),
      )
    Match(scrutinee, annotated, clauses, default) =>
      Match(
        self.rewrite_expr(scrutinee),
        annotated.map(t => self.rewrite_value_type(t)),
        clauses.map(c => self.rewrite_clause(c)),
        match default {
          Some(body) => Some(self.rewrite_stmt(body))
          None => None
        },
      )
    Region(body) => Region(self.rewrite_block_lit(body))
    Alloc(id, init, region, body) =>
      Alloc(
        self.rewrite_id(id),
        self.rewrite_expr(init),
        self.rewrite_id(region),
        self.rewrite_stmt(body),
      )
    Var(ref, init, capture, body) =>
      Var(
        self.rewrite_id(ref),
        self.rewrite_expr(init),
        self.rewrite_id(capture),
        self.rewrite_stmt(body),
      )
    Get(id, annotated_tpe, ref, annotated_capt, body) =>
      Get(
        self.rewrite_id(id),
        self.rewrite_value_type(annotated_tpe),
        self.rewrite_id(ref),
        self.rewrite_captures(annotated_capt),
        self.rewrite_stmt(body),
      )
    Put(ref, annotated_capt, value, body) =>
      Put(
        self.rewrite_id(ref),
        self.rewrite_captures(annotated_capt),
        self.rewrite_expr(value),
        self.rewrite_stmt(body),
      )
    Reset(body) => Reset(self.rewrite_block_lit(body))
    Shift(prompt, k, body) =>
      Shift(
        self.rewrite_block_var(prompt),
        self.rewrite_block_param(k),
        self.rewrite_stmt(body),
      )
    Resume(k, body) =>
      Resume(self.rewrite_block_var(k), self.rewrite_stmt(body))
    Hole(annotated, span) =>
      Hole(annotated.map(t => self.rewrite_value_type(t)), span)
  }
}

// ---------------------------------------------------------------------------
// Toplevel
// ---------------------------------------------------------------------------

///|
fn Rewrite::rewrite_toplevel(
  self : Rewrite,
  toplevel : Toplevel,
) -> Toplevel raise EffektError {
  match toplevel {
    ToplevelDef(id, block) =>
      ToplevelDef(self.rewrite_id(id), self.rewrite_block(block))
    ToplevelVal(id, binding) =>
      ToplevelVal(self.rewrite_id(id), self.rewrite_stmt(binding))
  }
}

///|
fn Rewrite::rewrite_declaration(
  self : Rewrite,
  declaration : Declaration,
) -> Declaration {
  match declaration {
    DeclarationData(id, tparams, constructors) =>
      DeclarationData(
        self.rewrite_id(id),
        tparams.map(t => self.rewrite_id(t)),
        constructors.map(c => self.rewrite_constructor(c)),
      )
    DeclarationInterface(id, tparams, properties) =>
      DeclarationInterface(
        self.rewrite_id(id),
        tparams.map(t => self.rewrite_id(t)),
        properties.map(p => self.rewrite_property(p)),
      )
  }
}

///|
fn Rewrite::rewrite_constructor(
  self : Rewrite,
  constructor : Constructor,
) -> Constructor {
  Constructor(
    self.rewrite_id(constructor.id),
    constructor.tparams.map(t => self.rewrite_id(t)),
    constructor.fields.map(f => self.rewrite_field(f)),
  )
}

///|
fn Rewrite::rewrite_field(self : Rewrite, field : Field) -> Field {
  Field(self.rewrite_id(field.id), self.rewrite_value_type(field.tpe))
}

///|
fn Rewrite::rewrite_property(self : Rewrite, property : Property) -> Property {
  Property(self.rewrite_id(property.id), self.rewrite_block_type(property.tpe))
}

///|
fn Rewrite::rewrite_extern_body(
  self : Rewrite,
  body : ExternBody[Expr],
) -> ExternBody[Expr] raise EffektError {
  match body {
    StringExternBody(flag, template) =>
      StringExternBody(flag, template.map(e => self.rewrite_expr(e)))
    Unsupported(error) => Unsupported(error)
  }
}

///|
fn Rewrite::rewrite_extern(
  self : Rewrite,
  e : Extern,
) -> Extern raise EffektError {
  match e {
    ExternData(id, tparams, body) =>
      ExternData(
        self.rewrite_id(id),
        tparams.map(t => self.rewrite_id(t)),
        self.rewrite_extern_body(body),
      )
    ExternInterface(id, tparams, body) =>
      ExternInterface(
        self.rewrite_id(id),
        tparams.map(t => self.rewrite_id(t)),
        self.rewrite_extern_body(body),
      )
    ExternDef(
      id,
      signature,
      tparams,
      cparams,
      vparams,
      bparams,
      result,
      capt,
      body
    ) =>
      ExternDef(
        self.rewrite_id(id),
        signature,
        tparams.map(t => self.rewrite_id(t)),
        cparams.map(c => self.rewrite_id(c)),
        vparams.map(p => self.rewrite_value_param(p)),
        bparams.map(p => self.rewrite_block_param(p)),
        self.rewrite_value_type(result),
        self.rewrite_captures(capt),
        self.rewrite_extern_body(body),
      )
    ExternInclude(flag, path) => ExternInclude(flag, path)
  }
}

///|
fn Rewrite::rewrite_module(
  self : Rewrite,
  module : ModuleDecl,
) -> ModuleDecl raise EffektError {
  ModuleDecl(
    module.path,
    module.includes,
    module.declarations.map(d => self.rewrite_declaration(d)),
    module.externs.map(e => self.rewrite_extern(e)),
    module.definitions.map(d => self.rewrite_toplevel(d)),
    module.exports.map(id => self.rewrite_id(id)),
  )
}
