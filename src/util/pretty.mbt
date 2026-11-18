// A Wadler/Leijen style pretty printer, standing in for kiama's
// `ParenPrettyPrinter`. Only the combinators used by the Effekt backends are
// provided.

///|
/// A pretty-printing document.
pub(all) enum Doc {
  Empty
  /// Literal text (must not contain newlines).
  Text(String)
  /// Horizontal concatenation.
  Cat(Doc, Doc)
  /// Increase the indentation of line breaks inside `inner`.
  Nest(Int32, Doc)
  /// A space when the enclosing group fits on one line, otherwise a newline.
  Line
  /// Nothing when the enclosing group fits, otherwise a newline.
  SoftBreak
  /// Always a newline.
  HardLine
  /// Try to print `inner` on a single line.
  Group(Doc)
}

///|
pub fn empty_doc() -> Doc {
  Empty
}

///|
pub fn text(s : String) -> Doc {
  Text(s)
}

///|
pub fn doc_cat(a : Doc, b : Doc) -> Doc {
  match (a, b) {
    (Empty, _) => b
    (_, Empty) => a
    _ => Cat(a, b)
  }
}

///|
pub fn doc_space() -> Doc {
  Text(" ")
}

///|
pub fn doc_line() -> Doc {
  Line
}

///|
pub fn doc_nest(n : Int32, d : Doc) -> Doc {
  Nest(n, d)
}

///|
pub fn doc_group(d : Doc) -> Doc {
  Group(d)
}

///|
/// `<+>`: concatenation with a single space.
pub fn doc_spacecat(a : Doc, b : Doc) -> Doc {
  doc_cat(a, doc_cat(doc_space(), b))
}

///|
pub fn hcat(docs : ArrayView[Doc]) -> Doc {
  docs.fold(init=Empty, doc_cat)
}

///|
/// `docs` folded with `sep` between neighbours, and `Empty` when there are none.
fn separated_by(docs : ArrayView[Doc], sep : Doc) -> Doc {
  match docs.length() {
    0 => Empty
    _ => docs[1:].fold(init=docs[0], (acc, d) => doc_cat(acc, doc_cat(sep, d)))
  }
}

///|
pub fn vcat(docs : ArrayView[Doc]) -> Doc {
  separated_by(docs, HardLine)
}

///|
/// Vertical separation: line breaks that become spaces when the enclosing
/// group fits on one line.
pub fn vsep(docs : ArrayView[Doc]) -> Doc {
  separated_by(docs, Line)
}

///|
pub fn hsep(docs : ArrayView[Doc]) -> Doc {
  separated_by(docs, doc_space())
}

///|
pub fn punctuate(docs : ArrayView[Doc], sep : Doc) -> Doc {
  separated_by(docs, sep)
}

///|
/// Upstream effekt's `util.intercalate(a, b)`: `a[0], b[0], a[1], b[1], …`,
/// followed by the rest of the longer sequence.
pub fn[A] intercalate(xs : ArrayView[A], ys : ArrayView[A]) -> Array[A] {
  let out : Array[A] = []
  for i in 0..<xs.length().max(ys.length()) {
    if i < xs.length() {
      out.push(xs[i])
    }
    if i < ys.length() {
      out.push(ys[i])
    }
  }
  out
}

///|
pub fn comma() -> Doc {
  Text(",")
}

///|
pub fn parens_inner(d : Doc) -> Doc {
  doc_cat(Text("("), doc_cat(d, Text(")")))
}

///|
pub fn braces_inner(d : Doc) -> Doc {
  doc_cat(Text("{"), doc_cat(d, Text("}")))
}

///|
fn brackets_inner(d : Doc) -> Doc {
  doc_cat(Text("["), doc_cat(d, Text("]")))
}

///|
/// `group (nest (line <> d))` — the standard "hang" combinator.
pub fn nested(d : Doc) -> Doc {
  doc_group(doc_nest(2, doc_cat(Line, d)))
}

///|
/// `docs` in parentheses, separated by commas: an empty list is `()`.
pub fn parens_list(docs : ArrayView[Doc]) -> Doc {
  parens_inner(punctuate(docs, comma()))
}

///|
/// `docs` in braces, separated by commas: an empty list is `{}`.
pub fn braces_list(docs : ArrayView[Doc]) -> Doc {
  braces_inner(punctuate(docs, comma()))
}

///|
/// `docs` in brackets, separated by commas: an empty list is `[]`.
pub fn brackets_list(docs : ArrayView[Doc]) -> Doc {
  brackets_inner(punctuate(docs, comma()))
}

///|
/// `block(content) = "{" <> nest(line <> content) <> line <> "}"`: the two soft
/// lines collapse to `{ content }` when the group fits.
pub fn braced_block(content : Doc) -> Doc {
  braces_inner(doc_cat(doc_nest(2, doc_cat(doc_line(), content)), doc_line()))
}

// Rendering
// ---------

///|
/// The rendering mode of a document under a group.
#derive(Eq)
pub(all) enum Mode {
  Flat
  Break
}

///|
priv struct RenderItem {
  indent : Int32
  mode : Mode
  doc : Doc
}

///|
/// Renders a document, breaking lines so that the output ideally fits within
/// `width` columns.
pub fn render(doc : Doc) -> String {
  render_width(doc, 80)
}

///|
/// Ends the current line and starts the next one at column `indent`.
fn newline(buf : StringBuilder, indent : Int32) -> Unit {
  buf.write_string("\n")
  buf.write_string(" ".repeat(indent))
}

///|
pub fn render_width(doc : Doc, width : Int32) -> String {
  let buf = StringBuilder()
  let mut col = 0
  let stack : Array[RenderItem] = [{ indent: 0, mode: Break, doc, }]
  while stack.pop() is Some(item) {
    match item.doc {
      Empty => ()
      Text(s) => {
        buf.write_string(s)
        col = col + s.length()
      }
      Cat(a, b) => {
        stack.push({ indent: item.indent, mode: item.mode, doc: b, })
        stack.push({ indent: item.indent, mode: item.mode, doc: a, })
      }
      Nest(n, d) =>
        stack.push({ indent: item.indent + n, mode: item.mode, doc: d, })
      Line =>
        if item.mode == Flat {
          buf.write_string(" ")
          col = col + 1
        } else {
          newline(buf, item.indent)
          col = item.indent
        }
      SoftBreak =>
        if item.mode == Break {
          newline(buf, item.indent)
          col = item.indent
        }
      HardLine => {
        newline(buf, item.indent)
        col = item.indent
      }
      Group(d) => {
        let mode = if fits(width - col, d) { Flat } else { Break }
        stack.push({ indent: item.indent, mode, doc: d, })
      }
    }
  }
  buf.to_string()
}

///|
/// Conservative "does this document fit into `space` columns" check.
fn fits(space : Int32, doc : Doc) -> Bool {
  guard space >= 0 else { return false }
  let mut remaining = space
  let stack : Array[Doc] = [doc]
  while stack.pop() is Some(d) {
    match d {
      Empty => ()
      Text(s) => {
        remaining = remaining - s.length()
        if remaining < 0 {
          return false
        }
      }
      Cat(a, b) => {
        stack.push(b)
        stack.push(a)
      }
      Nest(_, inner) => stack.push(inner)
      Group(inner) => stack.push(inner)
      Line => {
        remaining = remaining - 1
        if remaining < 0 {
          return false
        }
      }
      SoftBreak => ()
      HardLine => return false
    }
  }
  true
}
