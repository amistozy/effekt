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
pub fn doc_softbreak() -> Doc {
  SoftBreak
}

///|
pub fn doc_hardline() -> Doc {
  HardLine
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
pub fn hcat(docs : Array[Doc]) -> Doc {
  docs.fold(init=Empty, doc_cat)
}

///|
pub fn vcat(docs : Array[Doc]) -> Doc {
  match docs.length() {
    0 => Empty
    _ =>
      docs[1:].fold(init=docs[0], (acc, d) => doc_cat(acc, doc_cat(HardLine, d)))
  }
}

///|
/// Vertical separation: line breaks that become spaces when the enclosing
/// group fits on one line.
pub fn vsep(docs : Array[Doc]) -> Doc {
  match docs.length() {
    0 => Empty
    _ => docs[1:].fold(init=docs[0], (acc, d) => doc_cat(acc, doc_cat(Line, d)))
  }
}

///|
pub fn hsep(docs : Array[Doc]) -> Doc {
  match docs.length() {
    0 => Empty
    _ =>
      docs[1:].fold(init=docs[0], (acc, d) => {
        doc_cat(acc, doc_cat(Text(" "), d))
      })
  }
}

///|
/// Like `vsep`, but each separator is a single space when flat.
pub fn fill_sep(docs : Array[Doc]) -> Doc {
  vsep(docs)
}

///|
pub fn punctuate(docs : Array[Doc], sep : Doc) -> Doc {
  match docs.length() {
    0 => Empty
    _ => docs[1:].fold(init=docs[0], (acc, d) => doc_cat(acc, doc_cat(sep, d)))
  }
}

///|
pub fn intercalate(seps : Array[String], docs : Array[Doc]) -> Array[Doc] {
  let out : Array[Doc] = []
  for i = 0; i < docs.length(); i = i + 1 {
    if i > 0 && i - 1 < seps.length() {
      out.push(Text(seps[i - 1]))
    }
    out.push(docs[i])
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
pub fn brackets_inner(d : Doc) -> Doc {
  doc_cat(Text("["), doc_cat(d, Text("]")))
}

///|
/// `group (nest (line <> d))` — the standard "hang" combinator.
pub fn nested(d : Doc) -> Doc {
  doc_group(doc_nest(2, doc_cat(Line, d)))
}

///|
pub fn nested_at(indent : Int32, d : Doc) -> Doc {
  doc_group(doc_nest(indent, doc_cat(Line, d)))
}

// Rendering
// ---------

///|
/// The rendering mode of a document under a group.
pub(all) enum Mode {
  Flat
  Break
} derive(Eq)

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
pub fn render_width(doc : Doc, width : Int32) -> String {
  let buf = StringBuilder()
  let mut col = 0
  let stack : Array[RenderItem] = [{ indent: 0, mode: Break, doc, }]
  while stack.length() > 0 {
    let item = stack.pop().unwrap()
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
          buf.write_string("\n")
          for i = 0; i < item.indent; i = i + 1 {
            buf.write_string(" ")
          }
          col = item.indent
        }
      SoftBreak =>
        if item.mode == Flat {
          ()
        } else {
          buf.write_string("\n")
          for i = 0; i < item.indent; i = i + 1 {
            buf.write_string(" ")
          }
          col = item.indent
        }
      HardLine => {
        buf.write_string("\n")
        for i = 0; i < item.indent; i = i + 1 {
          buf.write_string(" ")
        }
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
  if space < 0 {
    return false
  }
  let mut remaining = space
  let stack : Array[Doc] = [doc]
  while stack.length() > 0 {
    let d = stack.pop().unwrap()
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
