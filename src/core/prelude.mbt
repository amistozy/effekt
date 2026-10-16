// Names used unqualified throughout the `core` package.
//
// Mirrors the imports at the top of `effekt/core/Tree.scala`: core programs use
// `symbols.Symbol` as names and the type language of `effekt/symbols/types`.

///|
using @util {
  type Span,
  type EffektError,
  type Template,
  type Doc,
  type Message,
  empty_doc,
  text,
  doc_cat,
  doc_spacecat,
  doc_space,
  doc_line,
  doc_group,
  doc_nest,
  doc_hardline,
  hcat,
  hsep,
  vcat,
  vsep,
  punctuate,
  comma,
  parens_inner,
  braces_inner,
  brackets_inner,
  nested,
  intercalate,
  render,
  render_width,
}

///|
using @symbols {
  type Sym,
  type Name,
  type ValueType,
  type BlockType,
  type Captures,
  type Effects,
  sym_eq,
  sym_in,
  dedup_syms,
  // built-in types and effects
  t_unit,
  t_bool,
  t_int,
  t_double,
  t_string,
  t_char,
  t_byte,
  t_region,
  t_state,
  // built-in symbols
  core_builtin_to_string,
  core_builtins,
  is_core_builtin,
  // type queries (mirrors the parts of `core/Type.scala` we do port)
  field_return_type,
  field_param,
  constructor_tparams,
  constructor_applied_datatype,
  value_type_equal,
  block_type_equal,
  interface_type_equal,
  canonical_order,
}

///|
using @source {type FeatureFlag, type LiteralValue}
