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
  doc_group,
  hcat,
  vcat,
  vsep,
  parens_inner,
  parens_list,
  braces_list,
  brackets_list,
  braced_block,
  intercalate,
  nested,
  punctuate,
  comma,
  render_width,
  internal_error,
}

///|
using @symbols {type JSName, type Sym}

///|
using @source {type LiteralValue}

///|
/// A fresh value symbol with the given name.
///
/// Upstream `core.Id(name)` mints an `Id` that is compared by name; here symbols
/// are compared by `uid`, so every call mints a genuinely fresh symbol.
pub fn fresh_sym(name : String) -> Sym {
  @symbols.Sym::value_param(@symbols.Name::local(name), None, Span::missing())
}
