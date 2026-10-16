// Names used unqualified throughout the `compiler` package.

///|
using @util {
  type Span,
  type EffektError,
  type Source,
  type Message,
  type Severity,
  fresh_uid,
}

///|
using @symbols {
  type Sym,
  type Name,
  type Module,
  type ValueType,
  type BlockType,
}

///|
using @source {
  type Context,
  type Config,
  type ModuleDecl,
  type Def,
  type Term,
  type Stmt,
  type Include,
  type FeatureFlag,
}
