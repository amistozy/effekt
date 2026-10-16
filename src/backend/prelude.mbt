// Names used unqualified throughout the `backend` package.

///|
using @util {type Span, type EffektError, type Template, fresh_uid}

///|
using @symbols {
  type Sym,
  type Name,
  type ValueType,
  type BlockType,
  type Effects,
  type Captures,
  sym_in,
}

///|
using @source {type Context, type ModuleDecl}

///|
using @namer {type ResolvedModule}
