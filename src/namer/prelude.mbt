// Names that are used unqualified throughout the `namer` package.
//
// The namer is the only phase that both creates symbols and looks into the
// syntax tree, so it needs a lot of names from all three foundation packages.

///|
using @util {type EffektError, type Span, fresh_uid}

///|
using @symbols {
  type Bindings,
  type BlockType,
  type Captures,
  type Effects,
  type Module,
  type Name,
  type Scoping,
  type Sym,
  type ValueType,
}

///|
using @source {
  type BlockParam,
  type CaptureSetTree,
  type Def,
  type EffectsTree,
  type Handler,
  type IdDef,
  type IdRef,
  type Implementation,
  type MatchClause,
  type MatchGuard,
  type MatchPattern,
  type ModuleDecl,
  type Operation,
  type Stmt,
  type Term,
  type TypeTree,
  type ValueArg,
  type ValueParam,
}
