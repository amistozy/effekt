// The Effekt syntax tree.
//
// Mirrors `effekt/source/Tree.scala`. To make side tables (resolved symbols,
// inferred types) keyable, every node is a struct carrying a unique `uid` and
// its source `span`, with the actual shape in a `kind` enum.

///|
/// An identifier occurring in binding position.
pub(all) struct IdDef {
  uid : Int32
  path : Array[String]
  name : String
  span : Span
}

///|
/// An identifier occurring in use position.
pub(all) struct IdRef {
  uid : Int32
  path : Array[String]
  name : String
  span : Span
}

///|
pub fn IdDef::new(name : String, span : Span) -> IdDef {
  { uid: fresh_uid(), path: [], name, span, }
}

///|
pub fn IdDef::qualified(
  path : Array[String],
  name : String,
  span : Span,
) -> IdDef {
  { uid: fresh_uid(), path, name, span, }
}

///|
pub fn IdRef::new(name : String, span : Span) -> IdRef {
  { uid: fresh_uid(), path: [], name, span, }
}

///|
pub fn IdRef::qualified(
  path : Array[String],
  name : String,
  span : Span,
) -> IdRef {
  { uid: fresh_uid(), path, name, span, }
}

///|
/// A literal value as written in the source.
pub(all) enum LiteralValue {
  LUnit
  LBool(Bool)
  LInt(Int32)
  LDouble(Double)
  LString(String)
  LChar(Int32)
  LByte(Int32)
}

///|
pub impl Show for LiteralValue with fn output(self, logger) {
  match self {
    LUnit => logger.write_string("()")
    LBool(b) => logger.write_string(b.to_string())
    LInt(i) => logger.write_string(i.to_string())
    LDouble(d) => logger.write_string(d.to_string())
    LString(s) => logger.write_string("\"\{s}\"")
    LChar(c) => logger.write_string("'\{c}'")
    LByte(b) => logger.write_string(b.to_string())
  }
}

///|
pub(all) struct ValueArg {
  name : String?
  value : Term
  span : Span
}

///|
pub fn ValueArg::named(name : String, value : Term, span : Span) -> ValueArg {
  { name: Some(name), value, span, }
}

///|
pub fn ValueArg::unnamed(value : Term) -> ValueArg {
  { name: None, value, span: value.span, }
}

///|
/// The meta-data preceding a definition (documentation, `private`, `extern`).
pub(all) struct Info {
  doc : String?
  is_private : Bool
  is_extern : Bool
}

///|
pub fn Info::empty() -> Info {
  { doc: None, is_private: false, is_extern: false, }
}

///|
/// Feature flags select which extern body applies to the current backend.
pub(all) enum FeatureFlag {
  NamedFeatureFlag(String)
  Default
}

///|
pub fn FeatureFlag::matches(self : FeatureFlag, name : String) -> Bool {
  match self {
    NamedFeatureFlag(n) => n == name
    Default => true
  }
}

///|
pub fn FeatureFlag::matches_any(
  self : FeatureFlag,
  names : Array[String],
) -> Bool {
  match self {
    NamedFeatureFlag(n) => names.any(x => x == n)
    Default => true
  }
}

///|
pub fn FeatureFlag::is_default(self : FeatureFlag) -> Bool {
  match self {
    Default => true
    _ => false
  }
}

///|
pub impl Show for FeatureFlag with fn output(self, logger) {
  match self {
    NamedFeatureFlag(n) => logger.write_string(n)
    Default => logger.write_string("else")
  }
}

///|
/// The body of an `extern` definition.
pub(all) enum ExternBody {
  /// A raw template (usually JS), with interpolated Effekt terms.
  StringExternBody(FeatureFlag, Template[Term])
  /// An extern implemented in Effekt itself.
  EffektExternBody(FeatureFlag, Stmt)
  /// The extern is not supported by this backend.
  Unsupported(String)
}

///|
pub fn ExternBody::flag(self : ExternBody) -> FeatureFlag {
  match self {
    StringExternBody(f, _) => f
    EffektExternBody(f, _) => f
    Unsupported(_) => Default
  }
}

///|
pub fn ExternBody::is_supported_by(self : ExternBody, name : String) -> Bool {
  match self {
    StringExternBody(f, _) => f.matches(name)
    EffektExternBody(f, _) => f.matches(name)
    Unsupported(_) => false
  }
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

///|
pub(all) struct TypeTree {
  uid : Int32
  span : Span
  kind : TypeKind
}

///|
pub(all) enum TypeKind {
  /// A reference to a named type.
  TypeRef(IdRef, Array[TypeTree])
  /// A synthesized value type (not parsed).
  ValueTypeTree(ValueType)
  /// A synthesized block type (not parsed).
  BlockTypeTree(BlockType)
  /// The type of a first-class computation.
  BoxedType(TypeTree, CaptureSetTree)
  /// The type of a second-class function.
  FunctionType(
    Array[IdDef],
    Array[TypeTree],
    Array[(IdDef?, TypeTree)],
    TypeTree,
    EffectsTree
  )
  /// A value type together with its effects.
  Effectful(TypeTree, EffectsTree)
}

///|
pub(all) struct EffectsTree {
  span : Span
  effs : Array[TypeTree]
}

///|
pub fn EffectsTree::pure(span : Span) -> EffectsTree {
  { span, effs: [], }
}

///|
pub(all) struct CaptureSetTree {
  span : Span
  captures : Array[IdRef]
}

// ---------------------------------------------------------------------------
// Patterns and guards
// ---------------------------------------------------------------------------

///|
pub(all) struct MatchPattern {
  uid : Int32
  span : Span
  kind : PatternKind
}

///|
pub(all) enum PatternKind {
  /// `case a => ...`
  AnyPattern(IdDef)
  /// `case Cons(a, as) => ...`
  TagPattern(IdRef, Array[MatchPattern])
  /// `case _ => ...`
  IgnorePattern
  /// `case 42 => ...`
  LiteralPattern(LiteralValue, ValueType)
  /// `case a, b => ...`
  MultiPattern(Array[MatchPattern])
}

///|
pub(all) struct MatchGuard {
  uid : Int32
  span : Span
  kind : GuardKind
}

///|
pub(all) enum GuardKind {
  BooleanGuard(Term)
  /// `<EXPR> is <PATTERN>`
  PatternGuard(Term, MatchPattern)
}

///|
pub(all) struct MatchClause {
  uid : Int32
  span : Span
  pattern : MatchPattern
  guards : Array[MatchGuard]
  body : Stmt
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
pub(all) struct Stmt {
  uid : Int32
  span : Span
  kind : StmtKind
}

///|
pub(all) enum StmtKind {
  DefStmt(Def, Stmt)
  ExprStmt(Term, Stmt)
  Return(Term)
  BlockStmt(Stmt)
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

///|
pub(all) struct Term {
  uid : Int32
  span : Span
  kind : TermKind
}

///|
pub(all) enum CallTarget {
  IdTarget(IdRef)
  ExprTarget(Term)
}

///|
pub fn CallTarget::span_of(self : CallTarget) -> Span {
  match self {
    IdTarget(id) => id.span
    ExprTarget(r) => r.span
  }
}

///|
pub(all) enum TermKind {
  /// Variable / value or block use.
  Var(IdRef)
  Assign(IdRef, Term)
  Literal(LiteralValue, ValueType)
  Hole(IdDef, Template[Stmt])
  /// Boxing / unboxing to represent first-class values.
  Box(CaptureSetTree?, Term)
  Unbox(Term)
  /// Field selection, i.e. `record.field`.
  Select(Term, IdRef)
  /// A call to an effect operation, i.e. `do raise()`.
  Do(IdRef, Array[TypeTree], Array[ValueArg], Array[Term])
  /// A call to a named function or to an expression.
  Call(CallTarget, Array[TypeTree], Array[ValueArg], Array[Term])
  /// A method call or capability call, i.e. `exc.raise()`.
  MethodCall(Term, IdRef, Array[TypeTree], Array[ValueArg], Array[Term])
  If(Array[MatchGuard], Stmt, Stmt)
  While(Array[MatchGuard], Stmt, Stmt?)
  Match(Array[Term], Array[MatchClause], Stmt?)
  TryHandle(Stmt, Array[Handler])
  Region(IdDef, Stmt)
  BlockLiteral(Array[IdDef], Array[ValueParam], Array[BlockParam], Stmt)
  New(Implementation)
}

// ---------------------------------------------------------------------------
// Definitions
// ---------------------------------------------------------------------------

///|
pub(all) struct ValueParam {
  id : IdDef
  tpe : TypeTree?
  is_implicit : Bool
}

///|
pub(all) struct BlockParam {
  id : IdDef
  tpe : TypeTree?
  is_implicit : Bool
}

///|
pub(all) struct Def {
  uid : Int32
  span : Span
  info : Info
  kind : DefKind
}

///|
pub(all) enum DefKind {
  FunDef(
    IdDef,
    Array[IdDef],
    Array[ValueParam],
    Array[BlockParam],
    CaptureSetTree?,
    TypeTree?,
    Stmt
  )
  ValDef(IdDef, TypeTree?, Stmt)
  RegDef(IdDef, TypeTree?, IdRef, Stmt)
  VarDef(IdDef, TypeTree?, Stmt)
  DefDef(IdDef, CaptureSetTree?, TypeTree?, Term)
  NamespaceDef(IdDef, Array[Def])
  InterfaceDef(IdDef, Array[IdDef], Array[Operation])
  DataDef(IdDef, Array[IdDef], Array[Constructor])
  RecordDef(IdDef, Array[IdDef], Array[ValueParam])
  TypeDef(IdDef, Array[IdDef], TypeTree)
  EffectDef(IdDef, Array[IdDef], EffectsTree)
  ExternType(IdDef, Array[IdDef], Array[ExternBody])
  ExternDef(
    IdDef,
    Array[IdDef],
    Array[ValueParam],
    Array[BlockParam],
    CaptureSetTree,
    TypeTree,
    Array[ExternBody]
  )
  ExternResource(IdDef, TypeTree)
  ExternInterface(IdDef, Array[IdDef], Array[ExternBody])
  ExternInclude(FeatureFlag, String, String?)
}

///|
pub fn Def::id_def(self : Def) -> IdDef {
  match self.kind {
    FunDef(id, _, _, _, _, _, _) => id
    ValDef(id, _, _) => id
    RegDef(id, _, _, _) => id
    VarDef(id, _, _) => id
    DefDef(id, _, _, _) => id
    NamespaceDef(id, _) => id
    InterfaceDef(id, _, _) => id
    DataDef(id, _, _) => id
    RecordDef(id, _, _) => id
    TypeDef(id, _, _) => id
    EffectDef(id, _, _) => id
    ExternType(id, _, _) => id
    ExternDef(id, _, _, _, _, _, _) => id
    ExternResource(id, _) => id
    ExternInterface(id, _, _) => id
    ExternInclude(_, _, _) => IdDef::new("", self.span)
  }
}

///|
pub(all) struct Constructor {
  uid : Int32
  span : Span
  id : IdDef
  tparams : Array[IdDef]
  params : Array[ValueParam]
  doc : String?
}

///|
pub(all) struct Operation {
  uid : Int32
  span : Span
  id : IdDef
  tparams : Array[IdDef]
  vparams : Array[ValueParam]
  bparams : Array[BlockParam]
  ret : TypeTree
  doc : String?
}

// ---------------------------------------------------------------------------
// Implementations and handlers
// ---------------------------------------------------------------------------

///|
pub(all) struct Implementation {
  uid : Int32
  span : Span
  interface : TypeTree
  clauses : Array[OpClause]
}

///|
pub(all) struct Handler {
  uid : Int32
  span : Span
  capability : BlockParam?
  implementation : Implementation
}

///|
pub(all) struct OpClause {
  uid : Int32
  span : Span
  id : IdRef
  tparams : Array[IdDef]
  vparams : Array[ValueParam]
  bparams : Array[BlockParam]
  ret : TypeTree?
  body : Stmt
  resume : IdDef
}

// ---------------------------------------------------------------------------
// Modules
// ---------------------------------------------------------------------------

///|
pub(all) struct Include {
  path : String
  span : Span
}

///|
pub(all) struct ModuleDecl {
  uid : Int32
  span : Span
  path : String
  includes : Array[Include]
  defs : Array[Def]
  doc : String?
}

// ---------------------------------------------------------------------------
// Smart constructors
// ---------------------------------------------------------------------------

///|
pub fn mk_term(span : Span, kind : TermKind) -> Term {
  { uid: fresh_uid(), span, kind, }
}

///|
pub fn mk_stmt(span : Span, kind : StmtKind) -> Stmt {
  { uid: fresh_uid(), span, kind, }
}

///|
pub fn mk_def(span : Span, info : Info, kind : DefKind) -> Def {
  { uid: fresh_uid(), span, info, kind, }
}

///|
pub fn mk_type(span : Span, kind : TypeKind) -> TypeTree {
  { uid: fresh_uid(), span, kind, }
}

///|
pub fn mk_pattern(span : Span, kind : PatternKind) -> MatchPattern {
  { uid: fresh_uid(), span, kind, }
}

///|
pub fn mk_guard(span : Span, kind : GuardKind) -> MatchGuard {
  { uid: fresh_uid(), span, kind, }
}

///|
/// The value type of a literal.
pub fn literal_type(v : LiteralValue) -> ValueType {
  match v {
    LUnit => t_unit()
    LBool(_) => t_bool()
    LInt(_) => t_int()
    LDouble(_) => t_double()
    LString(_) => t_string()
    LChar(_) => t_char()
    LByte(_) => t_byte()
  }
}
