// Symbols.
//
// Mirrors `effekt/symbols/symbols.scala`. Where the Scala implementation uses
// a trait hierarchy (`TermSymbol`, `ValueSymbol`, `BlockSymbol`, `TypeSymbol`),
// we use a single `Sym` enum whose variants carry plain structs. All symbol
// identity is by `uid`, exactly like the upstream `Symbol.id`.

///|
/// The base of every symbol: a unique id and a name.
pub(all) struct SymBase {
  uid : Int32
  name : Name
  /// The span of the defining occurrence (used for diagnostics only).
  decl : Span
}

///|
fn base(name : Name, decl : Span) -> SymBase {
  { uid: fresh_uid(), name, decl, }
}

///|
fn anon_base(name : String) -> SymBase {
  { uid: fresh_uid(), name: Name::local(name), decl: Span::missing(), }
}

// ---------------------------------------------------------------------------
// Value symbols
// ---------------------------------------------------------------------------

///|
pub(all) struct ValueParamSym {
  base : SymBase
  mut tpe : ValueType?
  is_implicit : Bool
}

///|
pub(all) struct ValBinderSym {
  base : SymBase
  mut tpe : ValueType?
}

///|
pub(all) struct HoleSym {
  base : SymBase
  mut expected_type : ValueType?
  mut arg_types : Array[ValueType?]
}

///|
pub(all) struct WildcardSym {
  base : SymBase
}

///|
pub(all) struct TmpValueSym {
  base : SymBase
}

// ---------------------------------------------------------------------------
// Block symbols
// ---------------------------------------------------------------------------

///|
/// Every tracked block parameter gives rise to a capture parameter.
pub(all) struct BlockParamSym {
  base : SymBase
  mut tpe : BlockType?
  capture : Sym
  is_implicit : Bool
}

///|
pub(all) struct ExternResourceSym {
  base : SymBase
  tpe : BlockType
  capture : Sym
}

///|
pub(all) struct ResumeParamSym {
  base : SymBase
}

///|
pub(all) struct UserFunctionSym {
  base : SymBase
  tparams : Array[Sym]
  vparams : Array[Sym]
  bparams : Array[Sym]
  annotated_captures : Array[Sym]?
  annotated_result : ValueType?
  annotated_effects : Effects?
}

///|
pub(all) struct LambdaSym {
  base : SymBase
  vparams : Array[Sym]
  bparams : Array[Sym]
}

///|
pub(all) struct RegBinderSym {
  base : SymBase
  mut tpe : ValueType?
  region : Sym
}

///|
pub(all) struct VarBinderSym {
  base : SymBase
  mut tpe : ValueType?
  capture : Sym
}

///|
pub(all) struct DefBinderSym {
  base : SymBase
  caps : Array[Sym]?
  mut tpe : BlockType?
}

///|
/// A synthetic symbol representing potentially multiple call targets
/// (overloaded functions / methods). Refined by the typer.
pub(all) struct CallTargetSym {
  base : SymBase
  symbols : Array[Array[Sym]]
}

///|
pub(all) struct OperationSym {
  base : SymBase
  tparams : Array[Sym]
  vparams : Array[Sym]
  bparams : Array[Sym]
  result_type : ValueType
  effects : Effects
  mut interface : Sym
}

///|
pub(all) struct ConstructorSym {
  base : SymBase
  tparams : Array[Sym]
  mut fields : Array[Sym]
  mut tpe : Sym
}

///|
pub(all) struct FieldSym {
  base : SymBase
  param : Sym
  constructor : Sym
}

///|
pub(all) struct ExternFunctionSym {
  base : SymBase
  tparams : Array[Sym]
  vparams : Array[Sym]
  bparams : Array[Sym]
  result : ValueType
  effects : Effects
  capture : Array[Sym]
}

///|
pub(all) struct TmpBlockSym {
  base : SymBase
}

// ---------------------------------------------------------------------------
// Type symbols
// ---------------------------------------------------------------------------

///|
pub(all) struct TypeParamSym {
  base : SymBase
}

///|
pub(all) struct UnificationVarSym {
  base : SymBase
  underlying : Sym
}

///|
pub(all) struct TypeAliasSym {
  base : SymBase
  tparams : Array[Sym]
  tpe : ValueType
}

///|
pub(all) struct DataTypeSym {
  base : SymBase
  tparams : Array[Sym]
  mut constructors : Array[Sym]
}

///|
pub(all) struct RecordSym {
  base : SymBase
  tparams : Array[Sym]
  mut constructor : Sym
}

///|
pub(all) struct ExternTypeSym {
  base : SymBase
  tparams : Array[Sym]
}

///|
pub(all) struct ErrorValueTypeSym {
  base : SymBase
  tparams : Array[Sym]
}

///|
pub(all) struct InterfaceSym {
  base : SymBase
  tparams : Array[Sym]
  mut operations : Array[Sym]
}

///|
pub(all) struct ExternInterfaceSym {
  base : SymBase
  tparams : Array[Sym]
}

///|
pub(all) struct ErrorBlockTypeSym {
  base : SymBase
  tparams : Array[Sym]
}

///|
/// Effect aliases are *not* block types: the namer dealiases them before use.
pub(all) struct EffectAliasSym {
  base : SymBase
  tparams : Array[Sym]
  effs : Effects
}

// ---------------------------------------------------------------------------
// Captures
// ---------------------------------------------------------------------------

///|
pub(all) enum CaptUnificationRole {
  VariableInstantiation(Sym)
  HandlerRegion
  RegionRegion
  VarRegion
  FunctionRegion
  ExternDefRegion
  BlockRegion
  AnonymousFunctionRegion
  InferredBox
  InferredUnbox
  OpClause
  /// `handled` is a list of captures being subtracted.
  Subtraction(Array[Sym], Sym)
  Substitution
}

///|
pub(all) struct CaptUnificationVarSym {
  base : SymBase
  role : CaptUnificationRole
}

///|
pub(all) struct CaptureParamSym {
  base : SymBase
}

///|
pub(all) struct LexicalRegionSym {
  base : SymBase
}

///|
pub(all) struct ResourceSym {
  base : SymBase
}

///|
/// The single symbol type of the compiler.
pub(all) enum Sym {
  // values
  ValueParam(ValueParamSym)
  ValBinder(ValBinderSym)
  Hole(HoleSym)
  Wildcard(WildcardSym)
  TmpValue(TmpValueSym)
  // blocks
  BlockParam(BlockParamSym)
  ExternResource(ExternResourceSym)
  ResumeParam(ResumeParamSym)
  UserFunction(UserFunctionSym)
  Lambda(LambdaSym)
  RegBinder(RegBinderSym)
  VarBinder(VarBinderSym)
  DefBinder(DefBinderSym)
  CallTarget(CallTargetSym)
  Operation(OperationSym)
  Constructor(ConstructorSym)
  Field(FieldSym)
  ExternFunction(ExternFunctionSym)
  TmpBlock(TmpBlockSym)
  // types
  TypeParam(TypeParamSym)
  UnificationVar(UnificationVarSym)
  TypeAlias(TypeAliasSym)
  DataType(DataTypeSym)
  Record(RecordSym)
  ExternType(ExternTypeSym)
  ErrorValueType(ErrorValueTypeSym)
  Interface(InterfaceSym)
  ExternInterface(ExternInterfaceSym)
  ErrorBlockType(ErrorBlockTypeSym)
  EffectAlias(EffectAliasSym)
  // captures
  CaptUnificationVar(CaptUnificationVarSym)
  CaptureParam(CaptureParamSym)
  LexicalRegion(LexicalRegionSym)
  Resource(ResourceSym)
}

///|
pub fn Sym::base(self : Sym) -> SymBase {
  match self {
    ValueParam(s) => s.base
    ValBinder(s) => s.base
    Hole(s) => s.base
    Wildcard(s) => s.base
    TmpValue(s) => s.base
    BlockParam(s) => s.base
    ExternResource(s) => s.base
    ResumeParam(s) => s.base
    UserFunction(s) => s.base
    Lambda(s) => s.base
    RegBinder(s) => s.base
    VarBinder(s) => s.base
    DefBinder(s) => s.base
    CallTarget(s) => s.base
    Operation(s) => s.base
    Constructor(s) => s.base
    Field(s) => s.base
    ExternFunction(s) => s.base
    TmpBlock(s) => s.base
    TypeParam(s) => s.base
    UnificationVar(s) => s.base
    TypeAlias(s) => s.base
    DataType(s) => s.base
    Record(s) => s.base
    ExternType(s) => s.base
    ErrorValueType(s) => s.base
    Interface(s) => s.base
    ExternInterface(s) => s.base
    ErrorBlockType(s) => s.base
    EffectAlias(s) => s.base
    CaptUnificationVar(s) => s.base
    CaptureParam(s) => s.base
    LexicalRegion(s) => s.base
    Resource(s) => s.base
  }
}

///|
pub fn Sym::uid(self : Sym) -> Int32 {
  self.base().uid
}

///|
pub fn Sym::name(self : Sym) -> Name {
  self.base().name
}

///|
pub fn Sym::decl(self : Sym) -> Span {
  self.base().decl
}

///|
/// Symbols are compared by identity (`uid`), not by name.
pub impl Eq for Sym with fn equal(self, other) {
  self.uid() == other.uid()
}

///|
pub impl Show for Sym with fn output(self, logger) {
  self.name().output(logger)
}

// Kind predicates, standing in for the trait hierarchy.

///|
pub fn Sym::is_value_symbol(self : Sym) -> Bool {
  match self {
    ValueParam(_) | ValBinder(_) | Hole(_) | Wildcard(_) | TmpValue(_) => true
    _ => false
  }
}

///|
pub fn Sym::is_block_symbol(self : Sym) -> Bool {
  match self {
    BlockParam(_)
    | ExternResource(_)
    | ResumeParam(_)
    | UserFunction(_)
    | Lambda(_)
    | RegBinder(_)
    | VarBinder(_)
    | DefBinder(_)
    | CallTarget(_)
    | Operation(_)
    | Constructor(_)
    | Field(_)
    | ExternFunction(_)
    | TmpBlock(_) => true
    _ => false
  }
}

///|
pub fn Sym::is_term_symbol(self : Sym) -> Bool {
  self.is_value_symbol() || self.is_block_symbol()
}

///|
pub fn Sym::is_type_symbol(self : Sym) -> Bool {
  self.is_term_symbol() == false
}

///|
pub fn Sym::is_ref_binder(self : Sym) -> Bool {
  match self {
    RegBinder(_) | VarBinder(_) => true
    _ => false
  }
}

///|
pub fn Sym::is_block_type_constructor(self : Sym) -> Bool {
  match self {
    Interface(_) | ExternInterface(_) | ErrorBlockType(_) => true
    _ => false
  }
}

///|
pub fn Sym::is_value_type_constructor(self : Sym) -> Bool {
  match self {
    DataType(_) | Record(_) | ExternType(_) | ErrorValueType(_) => true
    _ => false
  }
}

///|
pub fn Sym::is_type_var(self : Sym) -> Bool {
  match self {
    TypeParam(_) | UnificationVar(_) => true
    _ => false
  }
}

///|
pub fn Sym::is_capture(self : Sym) -> Bool {
  match self {
    CaptUnificationVar(_) | CaptureParam(_) | LexicalRegion(_) | Resource(_) =>
      true
    _ => false
  }
}

///|
/// Is this a callable that can be applied to arguments?
pub fn Sym::is_callable(self : Sym) -> Bool {
  match self {
    UserFunction(_)
    | Operation(_)
    | Constructor(_)
    | Field(_)
    | ExternFunction(_)
    | Lambda(_) => true
    _ => false
  }
}

///|
pub fn Sym::is_operation(self : Sym) -> Bool {
  match self {
    Operation(_) => true
    _ => false
  }
}

///|
pub fn Sym::is_synthetic(self : Sym) -> Bool {
  match self {
    Field(_)
    | Constructor(_)
    | CallTarget(_)
    | Wildcard(_)
    | TmpValue(_)
    | TmpBlock(_)
    | ResumeParam(_) => true
    _ => false
  }
}

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

///|
pub fn Sym::value_param(name : Name, tpe : ValueType?, decl : Span) -> Sym {
  ValueParam({ base: base(name, decl), tpe, is_implicit: false, })
}

///|
pub fn Sym::implicit_param(name : Name, tpe : ValueType?, decl : Span) -> Sym {
  ValueParam({ base: base(name, decl), tpe, is_implicit: true, })
}

///|
pub fn Sym::block_param(
  name : Name,
  tpe : BlockType?,
  capture : Sym,
  is_implicit : Bool,
  decl : Span,
) -> Sym {
  BlockParam({ base: base(name, decl), tpe, capture, is_implicit, })
}

///|
pub fn Sym::resume_param() -> Sym {
  ResumeParam({ base: anon_base("resume"), })
}

///|
pub fn Sym::wildcard() -> Sym {
  Wildcard({ base: anon_base("_"), })
}

///|
pub fn Sym::tmp_value(hint : String) -> Sym {
  TmpValue({ base: anon_base("v_\{hint}"), })
}

///|
pub fn Sym::tmp_block(hint : String) -> Sym {
  TmpBlock({ base: anon_base("b_\{hint}"), })
}

///|
pub fn Sym::type_param(name : Name, decl : Span) -> Sym {
  TypeParam({ base: base(name, decl), })
}

///|
pub fn Sym::capture_param(name : Name) -> Sym {
  CaptureParam({ base: anon_base(name.name), })
}

///|
pub fn Sym::lexical_region(name : Name, decl : Span) -> Sym {
  LexicalRegion({ base: base(name, decl), })
}

///|
pub fn Sym::resource(name : Name) -> Sym {
  Resource({ base: anon_base(name.name), })
}

///|
pub fn Sym::error_value_type(decl : Span) -> Sym {
  ErrorValueType({
    base: { uid: fresh_uid(), name: Name::anon(), decl, },
    tparams: [],
  })
}

///|
pub fn Sym::error_block_type(decl : Span) -> Sym {
  ErrorBlockType({
    base: { uid: fresh_uid(), name: Name::anon(), decl, },
    tparams: [],
  })
}

///|
pub fn Sym::call_target(symbols : Array[Array[Sym]]) -> Sym {
  CallTarget({ base: anon_base("__calltarget"), symbols, })
}

// ---------------------------------------------------------------------------
// Callable views
// ---------------------------------------------------------------------------

///|
/// The parameter lists / annotations of a callable symbol.
pub(all) struct CallableView {
  tparams : Array[Sym]
  vparams : Array[Sym]
  bparams : Array[Sym]
  annotated_captures : Array[Sym]?
  annotated_result : ValueType?
  annotated_effects : Effects?
}

///|
pub fn Sym::as_callable(self : Sym) -> CallableView? {
  match self {
    UserFunction(f) =>
      Some({
        tparams: f.tparams,
        vparams: f.vparams,
        bparams: f.bparams,
        annotated_captures: f.annotated_captures,
        annotated_result: f.annotated_result,
        annotated_effects: f.annotated_effects,
      })
    Operation(o) =>
      Some({
        tparams: o.tparams,
        vparams: o.vparams,
        bparams: o.bparams,
        annotated_captures: None,
        annotated_result: Some(o.result_type),
        annotated_effects: Some(o.effects),
      })
    Constructor(c) =>
      Some({
        tparams: c.tparams,
        vparams: c.fields.map(f => field_param(f)),
        bparams: [],
        annotated_captures: None,
        annotated_result: Some(constructor_applied_datatype(self)),
        annotated_effects: Some(Effects::empty()),
      })
    Field(f) =>
      Some({
        tparams: constructor_tparams(f.constructor),
        vparams: [
          Sym::value_param(
            f.constructor.name(),
            Some(constructor_applied_datatype(f.constructor)),
            Span::missing(),
          ),
        ],
        bparams: [],
        annotated_captures: None,
        annotated_result: Some(field_return_type(self)),
        annotated_effects: Some(Effects::empty()),
      })
    ExternFunction(f) =>
      Some({
        tparams: f.tparams,
        vparams: f.vparams,
        bparams: f.bparams,
        annotated_captures: Some(f.capture),
        annotated_result: Some(f.result),
        annotated_effects: Some(f.effects),
      })
    Lambda(l) =>
      Some({
        tparams: [],
        vparams: l.vparams,
        bparams: l.bparams,
        annotated_captures: None,
        annotated_result: None,
        annotated_effects: None,
      })
    _ => None
  }
}

///|
pub fn field_param(f : Sym) -> Sym {
  match f {
    Field(fd) => fd.param
    _ => Sym::wildcard()
  }
}

///|
pub fn constructor_tparams(c : Sym) -> Array[Sym] {
  match c {
    Constructor(cd) => cd.tparams
    _ => []
  }
}

///|
pub fn constructor_applied_datatype(c : Sym) -> ValueType {
  match c {
    Constructor(cd) =>
      ValueTypeApp(cd.tpe, cd.tparams.map(t => ValueTypeRef(t)))
    _ => ValueTypeApp(Sym::error_value_type(Span::missing()), [])
  }
}

///|
pub fn field_return_type(f : Sym) -> ValueType {
  match f {
    Field(fd) =>
      match fd.param {
        ValueParam(p) =>
          match p.tpe {
            Some(t) => t
            None => ValueTypeApp(Sym::error_value_type(Span::missing()), [])
          }
        _ => ValueTypeApp(Sym::error_value_type(Span::missing()), [])
      }
    _ => ValueTypeApp(Sym::error_value_type(Span::missing()), [])
  }
}

///|
/// The type of a callable: `annotatedType` upstream. Only defined when the
/// callable has both a result type and an effect annotation.
pub fn Sym::annotated_type(self : Sym) -> BlockType? {
  let c = self.as_callable()
  match c {
    None => None
    Some(c) =>
      match (c.annotated_result, c.annotated_effects) {
        (Some(ret), Some(effs)) => {
          let vps : Array[ValueType] = []
          for v in c.vparams {
            match v {
              ValueParam(p) =>
                match p.tpe {
                  Some(t) => vps.push(t)
                  None => ()
                }
              _ => ()
            }
          }
          let bcapt : Array[Captures] = []
          let bps : Array[BlockType] = []
          for b in c.bparams {
            match b {
              BlockParam(bp) => {
                bcapt.push(CaptureSetOf([bp.capture]))
                match bp.tpe {
                  Some(t) => bps.push(t)
                  None => ()
                }
              }
              _ => ()
            }
          }
          let distinct = effs.distinct()
          let capt : Array[Captures] = canonical_order(distinct.effects).map(e => {
            CaptureSetOf([
              Sym::capture_param(e.interface_name().unwrap_or(Name::anon())),
            ])
          })
          Some(FunctionType(c.tparams, bcapt + capt, vps, bps, ret, distinct))
        }
        (_, _) => None
      }
  }
}

// ---------------------------------------------------------------------------
// Captures
// ---------------------------------------------------------------------------

///|
/// Something that can be substituted by a capture set.
pub(all) enum Captures {
  /// A concrete set of captures.
  CaptureSetOf(Array[Sym])
  /// A capture unification variable (only during type checking).
  CaptVar(Sym)
}

///|
pub fn Captures::empty() -> Captures {
  CaptureSetOf([])
}

///|
pub fn Captures::is_pure(self : Captures) -> Bool {
  match self {
    CaptureSetOf(cs) => cs.length() == 0
    CaptVar(_) => false
  }
}

///|
pub fn Captures::to_array(self : Captures) -> Array[Sym] {
  match self {
    CaptureSetOf(cs) => cs
    CaptVar(c) => [c]
  }
}

///|
pub fn Captures::union(self : Captures, other : Captures) -> Captures {
  match (self, other) {
    (CaptureSetOf(a), CaptureSetOf(b)) => CaptureSetOf(dedup_syms(a + b))
    (CaptVar(c), _other) => CaptVar(c)
    (_self, CaptVar(c)) => CaptVar(c)
  }
}

///|
/// Structural equality on capture sets. A capture set is unordered, so this
/// is set equality; a capture variable only ever equals itself.
pub impl Eq for Captures with fn equal(self, other) {
  match (self, other) {
    (CaptureSetOf(xs), CaptureSetOf(ys)) =>
      xs.all(x => ys.contains(x)) && ys.all(y => xs.contains(y))
    (CaptVar(x), CaptVar(y)) => x == y
    _ => false
  }
}

///|
/// Capture sets print as `{a, b}`; an unsolved capture variable as `?x`.
pub impl Show for Captures with fn output(self, logger) {
  match self {
    CaptureSetOf(cs) => {
      let rendered = cs.map(s => s.name().qualified_name()).join(", ")
      logger.write_string("{\{rendered}}")
    }
    CaptVar(x) => logger.write_string("?\{x.name().qualified_name()}")
  }
}

///|
pub fn dedup_syms(xs : Array[Sym]) -> Array[Sym] {
  let out : Array[Sym] = []
  for x in xs {
    if !out.contains(x) {
      out.push(x)
    }
  }
  out
}

///|
pub fn Captures::diff(self : Captures, other : Captures) -> Captures {
  match (self, other) {
    (CaptureSetOf(a), CaptureSetOf(b)) =>
      CaptureSetOf(a.filter(x => !b.contains(x)))
    (CaptVar(c), _) => CaptVar(c)
    (self, _) => self
  }
}
