// Tree structure of programs in the internal core representation.
//
// Mirrors `effekt/core/Tree.scala`. Core uses `symbols.Symbol` as names; in this
// port that is `@symbols.Sym`, and symbols are compared by `uid`.
//
// ----------[[ effekt.core.Tree ]]----------
//
//   ─ [[ Tree ]]
//     │─ [[ ModuleDecl ]]
//     │─ [[ Declaration ]]
//     │  │─ [[ DeclarationData ]]
//     │  │─ [[ DeclarationInterface ]]
//     │
//     │─ [[ Constructor ]]
//     │─ [[ Field ]]
//     │─ [[ Property ]]
//     │─ [[ Extern ]]
//     │  │─ [[ ExternDef ]]
//     │  │─ [[ ExternInclude ]]
//     │
//     │─ [[ ExternBody ]]
//     │  │─ [[ StringExternBody ]]
//     │  │─ [[ Unsupported ]]
//     │
//     │─ [[ Block ]]
//     │  │─ [[ BlockVar ]]
//     │  │─ [[ BlockLit ]]
//     │  │─ [[ Unbox ]]
//     │  │─ [[ New ]]
//     │
//     │─ [[ Stmt ]]
//     │  │─ [[ Def ]]
//     │  │─ [[ Let ]]
//     │  │─ [[ Return ]]
//     │  │─ [[ Val ]]
//     │  │─ [[ App ]]
//     │  │─ [[ Invoke ]]
//     │  │─ [[ If ]]
//     │  │─ [[ Match ]]
//     │  │─ [[ Region ]]
//     │  │─ [[ Alloc ]]
//     │  │─ [[ Var ]]
//     │  │─ [[ Get ]]
//     │  │─ [[ Put ]]
//     │  │─ [[ Reset ]]
//     │  │─ [[ Shift ]]
//     │  │─ [[ Resume ]]
//     │  │─ [[ Hole ]]
//     │
//     │─ [[ Implementation ]]
//
// -------------------------------------------

///|
/// A module declaration; the path should be an Effekt include path, not a
/// system dependent file path.
pub(all) struct ModuleDecl {
  path : String
  includes : Array[String]
  declarations : Array[Declaration]
  externs : Array[Extern]
  definitions : Array[Toplevel]
  exports : Array[Sym]
}

///|
pub fn ModuleDecl::new(
  path : String,
  includes : Array[String],
  declarations : Array[Declaration],
  externs : Array[Extern],
  definitions : Array[Toplevel],
  exports : Array[Sym],
) -> ModuleDecl {
  { path, includes, declarations, externs, definitions, exports, }
}

// ---------------------------------------------------------------------------
// Toplevel data and interface declarations
// ---------------------------------------------------------------------------

///|
/// Toplevel data and interface declarations.
pub(all) enum Declaration {
  /// `type Id[tparams] { constructors... }`
  DeclarationData(Sym, Array[Sym], Array[Constructor])
  /// `interface Id[tparams] { properties... }`
  DeclarationInterface(Sym, Array[Sym], Array[Property])
}

///|
pub fn Declaration::id(self : Declaration) -> Sym {
  match self {
    DeclarationData(id, _, _) => id
    DeclarationInterface(id, _, _) => id
  }
}

///|
pub(all) struct Constructor {
  id : Sym
  tparams : Array[Sym]
  fields : Array[Field]
}

///|
pub fn Constructor::new(
  id : Sym,
  tparams : Array[Sym],
  fields : Array[Field],
) -> Constructor {
  { id, tparams, fields, }
}

///|
pub(all) struct Field {
  id : Sym
  tpe : ValueType
}

///|
pub fn Field::new(id : Sym, tpe : ValueType) -> Field {
  { id, tpe, }
}

///|
pub(all) struct Property {
  id : Sym
  tpe : BlockType
}

///|
pub fn Property::new(id : Sym, tpe : BlockType) -> Property {
  { id, tpe, }
}

// ---------------------------------------------------------------------------
// FFI external definitions
// ---------------------------------------------------------------------------

///|
/// FFI external definitions.
///
/// Upstream distinguishes `ExternBody[Nothing]` (for data and interface
/// externs, where only `Unsupported` can occur) from `ExternBody[Expr]`. Since
/// MoonBit has no bottom type, both are spelled `ExternBody[Expr]` here; the
/// data/interface cases are only ever constructed with `Unsupported`.
pub(all) enum Extern {
  ExternData(Sym, Array[Sym], ExternBody[Expr])
  ExternInterface(Sym, Array[Sym], ExternBody[Expr])
  ExternDef(
    Sym,
    QualifiedSignature,
    Array[Sym],
    Array[Sym],
    Array[ValueParam],
    Array[BlockParam],
    ValueType,
    Captures,
    ExternBody[Expr]
  )
  ExternInclude(FeatureFlag, String)
}

///|
/// The signature of an extern definition, as used for linking.
pub(all) struct QualifiedSignature {
  name : String
}

///|
pub fn QualifiedSignature::new(name : String) -> QualifiedSignature {
  { name, }
}

///|
pub(all) enum ExternBody[T] {
  /// A raw template (usually JS) with interpolated core expressions.
  StringExternBody(FeatureFlag, Template[T])
  /// The extern is not supported by the requested backend.
  Unsupported(EffektError)
}

///|
pub fn[T] ExternBody::flag(self : ExternBody[T]) -> FeatureFlag {
  match self {
    StringExternBody(flag, _) => flag
    Unsupported(_) => Default
  }
}

///|
pub fn[T] ExternBody::is_supported_by(
  self : ExternBody[T],
  name : String,
) -> Bool {
  match self {
    StringExternBody(flag, _) => flag.matches(name)
    Unsupported(_) => false
  }
}

///|
/// Definitions at the toplevel of a module.
pub(all) enum Toplevel {
  ToplevelDef(Sym, Block)
  ToplevelVal(Sym, Stmt)
}

///|
pub fn Toplevel::id(self : Toplevel) -> Sym {
  match self {
    ToplevelDef(id, _) => id
    ToplevelVal(id, _) => id
  }
}

// ---------------------------------------------------------------------------
// Pure expressions
// ---------------------------------------------------------------------------

///|
/// Pure expressions (no IO effects, no control effects).
pub(all) enum Expr {
  ValueVar(Sym, ValueType)
  Literal(LiteralValue, ValueType)
  /// Pure FFI calls. Invariant: the block is a variable.
  PureApp(BlockVar, Array[ValueType], Array[Expr])
  /// A constructor call. `data` is the data type, `tag` the constructor.
  Make(Sym, Sym, Array[ValueType], Array[Expr])
  Box(Block, Captures)
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

///|
pub(all) enum Block {
  BlockVar(BlockVar)
  BlockLit(BlockLit)
  Unbox(Expr)
  New(Implementation)
}

///|
/// A variable of block type together with its (annotated) type and captures.
pub(all) struct BlockVar {
  id : Sym
  annotated_tpe : BlockType
  annotated_capt : Captures
}

///|
pub fn BlockVar::new(
  id : Sym,
  annotated_tpe : BlockType,
  annotated_capt : Captures,
) -> BlockVar {
  { id, annotated_tpe, annotated_capt, }
}

///|
/// A block literal: `{ [tparams][cparams](vparams){bparams} => body }`.
pub(all) struct BlockLit {
  tparams : Array[Sym]
  cparams : Array[Sym]
  vparams : Array[ValueParam]
  bparams : Array[BlockParam]
  body : Stmt
}

///|
pub fn BlockLit::new(
  tparams : Array[Sym],
  cparams : Array[Sym],
  vparams : Array[ValueParam],
  bparams : Array[BlockParam],
  body : Stmt,
) -> BlockLit {
  { tparams, cparams, vparams, bparams, body, }
}

///|
pub(all) struct ValueParam {
  id : Sym
  tpe : ValueType
}

///|
pub fn ValueParam::new(id : Sym, tpe : ValueType) -> ValueParam {
  { id, tpe, }
}

///|
pub(all) struct BlockParam {
  id : Sym
  tpe : BlockType
  capt : Captures
}

///|
pub fn BlockParam::new(
  id : Sym,
  tpe : BlockType,
  capt : Captures,
) -> BlockParam {
  { id, tpe, capt, }
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
pub(all) enum Stmt {
  // Definitions
  Def(Sym, Block, Stmt)
  Let(Sym, Expr, Stmt)
  ImpureApp(Sym, BlockVar, Array[ValueType], Array[Expr], Array[Block], Stmt)
  // Fine-grain CBV
  Return(Expr)
  Val(Sym, Stmt, Stmt)
  App(Block, Array[ValueType], Array[Expr], Array[Block])
  Invoke(Block, Sym, BlockType, Array[ValueType], Array[Expr], Array[Block])
  // Local control flow
  If(Expr, Stmt, Stmt)
  Match(Expr, ValueType, Array[Clause], Stmt?)
  // (Type-monomorphic?) regions
  Region(BlockLit)
  Alloc(Sym, Expr, Sym, Stmt)
  /// Creates a fresh state handler to model local (backtrackable) state.
  /// `capture` is a binding occurrence, e.g. `state(init) { [x]{x: Ref} => ... }`.
  Var(Sym, Expr, Sym, Stmt)
  /// e.g. `let x: T = !ref @ r; body`
  Get(Sym, ValueType, Sym, Captures, Stmt)
  /// e.g. `ref @ r := value; body`
  Put(Sym, Captures, Expr, Stmt)
  /// Binds a fresh prompt in `body` and delimits the scope of captured
  /// continuations: `Reset({ [cap]{p: Prompt[answer] at cap} => stmt: answer})`.
  Reset(BlockLit)
  /// Captures the continuation up to the given prompt.
  Shift(BlockVar, BlockParam, Stmt)
  /// Bidirectional resume: runs the given statement in the original context.
  Resume(BlockVar, Stmt)
  // Others
  Hole(ValueType, Span)
}

///|
/// A match clause: the constructor tag and the block implementing the case.
pub(all) struct Clause {
  tag : Sym
  body : BlockLit
}

///|
pub fn Clause::new(tag : Sym, body : BlockLit) -> Clause {
  { tag, body, }
}

// ---------------------------------------------------------------------------
// Implementations
// ---------------------------------------------------------------------------

///|
/// An instance of an interface, concretely implementing the operations.
///
/// Used to represent handlers / capabilities, and objects / modules.
pub(all) struct Implementation {
  /// Upstream this is `BlockType.Interface`; here it is a `BlockType` that is
  /// an `InterfaceType`.
  interface : BlockType
  operations : Array[Operation]
}

///|
pub fn Implementation::new(
  interface : BlockType,
  operations : Array[Operation],
) -> Implementation {
  { interface, operations, }
}

///|
/// An implementation of a method / effect operation.
pub(all) struct Operation {
  name : Sym
  tparams : Array[Sym]
  cparams : Array[Sym]
  vparams : Array[ValueParam]
  bparams : Array[BlockParam]
  body : Stmt
}

///|
pub fn Operation::new(
  name : Sym,
  tparams : Array[Sym],
  cparams : Array[Sym],
  vparams : Array[ValueParam],
  bparams : Array[BlockParam],
  body : Stmt,
) -> Operation {
  { name, tparams, cparams, vparams, bparams, body, }
}

// ---------------------------------------------------------------------------
// Helper types
// ---------------------------------------------------------------------------

///|
/// The value type used where upstream would infer one: this port does not
/// include `core/Type.scala`'s type inference, so the few places that need an
/// inferred type record an "error" type instead.
pub fn unknown_value_type() -> ValueType {
  ValueTypeApp(Sym::error_value_type(Span::missing()), [])
}

///|
/// See `unknown_value_type`.
pub fn unknown_block_type() -> BlockType {
  InterfaceType(Sym::error_block_type(Span::missing()), [])
}
