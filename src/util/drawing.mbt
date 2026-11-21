// Drawing a diagnostic as a tree of lines.
//
// Mirrors `effekt/util/Drawing.scala` and the `layout`/`render` half of
// `effekt/util/ColoredMessaging.scala`. A diagnostic is drawn as
//
//   <header>
//   <the source line its span points at, with carets under the span>
//   <blank>
//   <one line of prose about the claim, per detail>
//   <one paragraph per candidate / nested cause / note>
//
// with nested paragraphs indented by a gutter (`|  `) per level. Upstream
// builds an intermediate list of lines (`Line.Code` / `Line.Text` /
// `Line.Blank`) and renders that; this port does the same, since the alignment
// of the gutters depends on the width of the largest line number in the whole
// drawing.

///|
/// The kind of an item under a diagnostic (upstream `Drawing.ItemKind`).
pub(all) enum ItemKind {
  Note
  Help
}

///|
/// How the item reads after its bullet: `* note: ` / `* help: `.
pub fn ItemKind::word(self : ItemKind) -> String {
  match self {
    Note => "note: "
    Help => "help: "
  }
}

///|
/// What a line leads with (upstream `Lead`): a bullet on the first line of an
/// item, and a hanging indent on the lines below it so that they line up.
priv enum Lead {
  Bullet(ItemKind?)
  Hang
}

///|
fn Lead::text(self : Lead) -> String {
  match self {
    Bullet(kind) =>
      match kind {
        Some(k) => "* " + k.word()
        None => "* "
      }
    Hang => "  "
  }
}

///|
/// One line of the drawing.
priv enum Line {
  /// A source line, at a position and in a source (so that a line from another
  /// file can be labelled with it).
  Code(Span, Int32, Lead?, String)
  /// A line of prose.
  Text(Int32, Lead?, String)
  /// A blank line at a nesting depth: an empty one at depth 0, a gutter at
  /// deeper ones so that the nesting stays visible.
  Blank(Int32)
}

///|
/// The lines drawn so far together with where the next one goes (upstream
/// `ColoredMessaging.Lines`).
priv struct Drawing {
  lines : Array[Line]
  mut depth : Int32
  mut lead : Lead?
}

///|
fn Drawing::new() -> Drawing {
  { lines: [], depth: 0, lead: None, }
}

///|
fn Drawing::emit(self : Drawing, line : Line) -> Unit {
  self.lines.push(line)
  self.lead = self.lead.map(_ => Hang)
}

///|
fn Drawing::text(self : Drawing, text : String) -> Unit {
  self.emit(Text(self.depth, self.lead, text))
}

///|
fn Drawing::code(self : Drawing, span : Span, code : String) -> Unit {
  self.emit(Code(span, self.depth, self.lead, code))
}

///|
fn Drawing::blank(self : Drawing) -> Unit {
  self.lines.push(Blank(self.depth))
}

///|
/// Runs `block` one level deeper, with no lead (upstream `deeper`).
fn[T] Drawing::deeper(self : Drawing, block : () -> T) -> T {
  let depth = self.depth
  let lead = self.lead
  self.depth = depth + 1
  self.lead = None
  let result = block()
  self.depth = depth
  self.lead = lead
  result
}

///|
/// Runs `block` with a bullet on its first line (upstream `item`).
fn[T] Drawing::item(self : Drawing, kind : ItemKind?, block : () -> T) -> T {
  self.lead = Some(Bullet(kind))
  let result = block()
  self.lead = None
  result
}

///|
/// Runs `block`, prefixed by a blank line if it drew anything (upstream
/// `children`: "a blank line between a node's place and its children, if it has
/// any").
fn Drawing::children(self : Drawing, block : () -> Unit) -> Unit {
  let before = self.lines.length()
  let depth = self.depth
  block()
  if self.lines.length() > before {
    self.lines.insert(before, Blank(depth))
  }
}

// ---------------------------------------------------------------------------
// The source lines a drawing shows
// ---------------------------------------------------------------------------

///|
/// A source line to draw, with the carets that go under its span (upstream
/// `Drawing.Excerpt`).
priv struct Excerpt {
  span : Span
  code : String
  marker : String
}

///|
/// The line `span` starts on, or `None` when the span has no place or the line
/// cannot be read (upstream `Drawing.excerpt`).
fn excerpt_of(span : Span) -> Excerpt? {
  guard span.origin != Missing else { return None }
  let pos = span.position()
  let code = span.source.line_text(pos.line)
  guard code != "" else { return None }
  let end = span.source.offset_to_position(span.end)
  let width = if end.line == pos.line && end.column > pos.column {
    end.column - pos.column
  } else {
    1
  }
  Some({ span, code, marker: " ".repeat(pos.column - 1) + "^".repeat(width), })
}

///|
/// The excerpt of a message's own span, if it has one.
fn excerpts_of(m : Message) -> Array[Excerpt] {
  match excerpt_of(m.span) {
    Some(e) => [e]
    None => []
  }
}

///|
/// The excerpts a whole paragraph shows, including the ones of the paragraphs
/// nested in it (upstream `excerpts(block)`, which decides whether a blank line
/// separates two paragraphs).
fn excerpt_count(m : Message) -> Int32 {
  let mut count = excerpts_of(m).length()
  for candidate in m.candidates {
    if !candidate.declaration.is_missing() &&
      excerpt_of(candidate.declaration) is Some(_) {
      count += 1
    }
    for error in candidate.errors {
      count += excerpt_count(error)
    }
  }
  for cause in m.causes {
    count += excerpt_count(cause)
  }
  for note in m.notes {
    match note {
      Note(_, at) =>
        if at is Some(span) && excerpt_of(span) is Some(_) {
          count += 1
        }
      Help(_) => ()
    }
  }
  count
}

// ---------------------------------------------------------------------------
// Laying out one message
// ---------------------------------------------------------------------------

///|
/// Draws one excerpt: its source line, then the carets with the claim of the
/// diagnostic appended (upstream `layout(e: Excerpt, claim)`).
fn Drawing::excerpt_line(
  self : Drawing,
  excerpt : Excerpt,
  claim : String?,
) -> Unit {
  self.code(excerpt.span, excerpt.code)
  let marker = match claim {
    Some(text) => excerpt.marker + " " + text
    None => excerpt.marker
  }
  self.text(marker)
}

///|
/// Draws a diagnostic as a nested paragraph: its own place with the claim
/// hanging off the carets, then its body one level deeper (upstream
/// `Block.Nested`).
fn Drawing::nested(self : Drawing, m : Message) -> Unit {
  match excerpt_of(m.span) {
    Some(e) => self.excerpt_line(e, Some(m.claim()))
    None => self.text(m.claim())
  }
  self.children(() => self.deeper(() => self.body(m)))
}

///|
/// Draws one candidate of an unresolved overload (upstream `Block.Candidate`):
/// the bullet goes on the candidate's *declaration*, which is underlined with
/// its identifier, and the diagnostics that rejected it hang below it.
fn Drawing::candidate(self : Drawing, c : Candidate) -> Unit {
  match excerpt_of(c.declaration) {
    Some(e) => {
      self.item(None, () => self.excerpt_line(e, None))
      self.deeper(() => self.blocks(c.errors))
    }
    None => {
      self.item(None, () => self.text(c.text))
      self.deeper(() => self.blocks(c.errors))
    }
  }
}

///|
/// Draws a note or a help (upstream `Block.Item`): the bullet on the text, and
/// the place it talks about one level deeper.
fn Drawing::subdiagnostic(self : Drawing, sub : Subdiagnostic) -> Unit {
  match sub {
    Note(text, at) => {
      self.item(Some(ItemKind::Note), () => self.text(text))
      self.deeper(() => {
        if at is Some(span) {
          if excerpt_of(span) is Some(e) {
            self.excerpt_line(e, None)
          }
        }
      })
    }
    Help(text) => {
      self.item(Some(ItemKind::Help), () => self.text(text))
      self.deeper(() => ())
    }
  }
}

///|
/// Draws the paragraphs of a diagnostics' body: the candidates of an unresolved
/// overload, then the nested causes, then the notes and helps. Consecutive
/// paragraphs are separated by a blank line when either of them shows source
/// (upstream `layout(blocks)` with `separated`).
fn Drawing::blocks(self : Drawing, errors : ArrayView[Message]) -> Unit {
  let blocks : Array[BlockRef] = []
  for m in errors {
    blocks.push(BlockRef::Nested(m))
  }
  self.paragraphs(blocks)
}

///|
/// Draws the body of one diagnostic (upstream `layout(body)`): the prose about
/// the claim, then its paragraphs.
fn Drawing::body(self : Drawing, m : Message) -> Unit {
  for detail in m.details {
    self.text(detail)
  }
  let blocks : Array[BlockRef] = []
  for c in m.candidates {
    blocks.push(BlockRef::Candidate(c))
  }
  for cause in m.causes {
    blocks.push(BlockRef::Nested(cause))
  }
  for sub in m.notes {
    blocks.push(BlockRef::Item(sub))
  }
  self.paragraphs(blocks)
}

///|
priv enum BlockRef {
  Candidate(Candidate)
  Nested(Message)
  Item(Subdiagnostic)
}

///|
fn spans(block : BlockRef) -> Bool {
  match block {
    Candidate(c) =>
      (!c.declaration.is_missing() && excerpt_of(c.declaration) is Some(_)) ||
      c.errors.any(e => excerpt_count(e) > 0)
    Nested(m) => excerpt_count(m) > 0
    Item(Note(_, at)) =>
      match at {
        Some(span) => excerpt_of(span) is Some(_)
        None => false
      }
    Item(Help(_)) => false
  }
}

///|
fn Drawing::paragraphs(self : Drawing, blocks : ArrayView[BlockRef]) -> Unit {
  for i, block in blocks {
    if i > 0 && (spans(blocks[i - 1]) || spans(block)) {
      self.blank()
    }
    match block {
      Candidate(c) => self.candidate(c)
      Nested(m) => self.nested(m)
      Item(sub) => self.subdiagnostic(sub)
    }
  }
}

// ---------------------------------------------------------------------------
// Rendering the drawn lines
// ---------------------------------------------------------------------------

///|
/// The path a diagnostic shows: always with forward slashes, so that the same
/// diagnostic reads the same on every platform (upstream `homogenizePath`).
fn shown_name(source : Source) -> String {
  let name = source.shown_name()
  let out = StringBuilder()
  for c in name {
    if c == '\\' {
      out.write_char('/')
    } else {
      out.write_char(c)
    }
  }
  out.to_string()
}

///|
/// `path:line:column:`, or just `line:column:` for a source without a name
/// (upstream `ColoredMessaging.place`).
fn place_text(span : Span) -> String {
  let pos = span.position()
  let name = shown_name(span.source)
  if name == "" {
    "\{pos.line}:\{pos.column}:"
  } else {
    "\{name}:\{pos.line}:\{pos.column}:"
  }
}

///|
/// The heading of a diagnostic: severity, place, and the first line of the
/// claim with the phase appended (upstream `heading`).
fn heading(m : Message) -> String {
  let title = with_phase(m.text, m.phase)
  if m.span.origin == Missing {
    "[\{m.severity}] \{title}"
  } else {
    "[\{m.severity}] \{place_text(m.span)} \{title}"
  }
}

///|
/// Renders the drawn lines, aligned to the widest line number of the whole
/// drawing (upstream `render`).
///
/// A source line is labelled with its file when it comes from a different
/// source than the line before it (`   /libraries/common/list.effekt:431:5`),
/// which is how a candidate whose declaration is in a library reads.
fn render_lines(
  lines : ArrayView[Line],
  gutter : Int32,
  header_source : Source?,
) -> Array[String] {
  let out : Array[String] = []
  let mut previous : Source? = header_source
  let padding = " ".repeat(gutter)
  for line in lines {
    match line {
      Code(span, depth, lead, code) => {
        let source = span.source
        let labelled = match previous {
          Some(prev) => prev.name != source.name
          None => true
        }
        let location = if labelled {
          let place = place_text(span)
          "   " + place[:place.length() - 1].to_owned()
        } else {
          ""
        }
        let number = span.position().line.to_string()
        out.push(
          "\{padding[:gutter - number.length()]}\{number}  \{guides(depth)}\{lead_text(lead)}\{code}\{location}",
        )
        previous = Some(source)
      }
      Text(depth, lead, text) =>
        out.push("\{padding}  \{guides(depth)}\{lead_text(lead)}\{text}")
      Blank(0) => out.push("")
      Blank(depth) => out.push("\{padding}  \{blank_guides(depth)}")
    }
  }
  out
}

///|
/// The indent that keeps a nested paragraph under the one it belongs to:
/// one `|  ` per level.
fn guides(depth : Int32) -> String {
  let out = StringBuilder()
  for _ in 0..<depth {
    out.write_string("|  ")
  }
  out.to_string()
}

///|
/// The same gutter for a blank line inside a nested paragraph.
fn blank_guides(depth : Int32) -> String {
  let out = StringBuilder()
  for i in 0..<depth {
    if i > 0 {
      out.write_string("  ")
    }
    out.write_string("|")
  }
  out.to_string()
}

///|
fn lead_text(lead : Lead?) -> String {
  match lead {
    Some(l) => l.text()
    None => ""
  }
}
