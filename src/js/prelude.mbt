// Names used unqualified throughout the `js` package.

///|
using @util {
  type EffektError,
  type Span,
  type Doc,
  type Template,
  empty_doc,
  text,
  doc_cat,
  doc_spacecat,
  doc_space,
  doc_line,
  doc_group,
  doc_nest,
  hcat,
  hsep,
  vcat,
  vsep,
  parens_inner,
  braces_inner,
  brackets_inner,
  nested,
  intercalate,
  punctuate,
  comma,
  render,
  render_width,
}

///|
using @symbols {
  type JSName,
  type Sym,
  type Name,
  type ValueType,
  type BlockType,
  type Captures,
  sym_eq,
}

///|
using @source {type FeatureFlag, type LiteralValue}

///|
using @core {type Declaration, type DeclarationContext, type Constructor}

///|
/// Raises an internal compiler error. The polymorphic result type lets it stand
/// in for any expected value.
pub fn[T] internal_error(msg : String) -> T raise EffektError {
  raise EffektError::Internal("Internal compiler error: \{msg}")
}

///|
/// A fresh value symbol with the given name.
///
/// Upstream `core.Id(name)` mints an `Id` that is compared by name; here symbols
/// are compared by `uid`, so every call mints a genuinely fresh symbol.
pub fn fresh_sym(name : String) -> Sym {
  @symbols.Sym::value_param(@symbols.Name::local(name), None, Span::missing())
}
