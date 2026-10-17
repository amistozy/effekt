// Names used unqualified throughout the `source` package.

///|
using @util {
  type Span,
  type EffektError,
  type Template,
  type Source,
  type Message,
  type Severity,
  fresh_uid,
}

///|
using @symbols {
  type ValueType,
  type BlockType,
  type Effects,
  type Sym,
  type Captures,
  t_unit,
  t_bool,
  t_int,
  t_double,
  t_string,
  t_char,
  t_byte,
}
