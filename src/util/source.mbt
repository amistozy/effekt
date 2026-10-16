// Source files, positions and spans.
//
// Mirrors `effekt/util/Source.scala` and `effekt/source/Tree.scala` (Span).
// A `Source` is a plain in-memory file: the compiler never touches the file
// system itself, all IO happens in the driver.

///|
/// A position in a source file. Lines and columns are 1-based, matching the
/// convention used by the upstream compiler and by most editors.
pub(all) struct Position {
  line : Int32
  column : Int32
} derive(Eq, Debug)

///|
pub impl Show for Position with fn output(self, logger) {
  logger.write_string(self.line.to_string())
  logger.write_string(":")
  logger.write_string(self.column.to_string())
}

///|
/// An in-memory source file.
///
/// `line_starts` caches the offset at which each 1-based line begins so that
/// offset <-> position conversion is a binary search.
pub(all) struct Source {
  name : String
  content : String
  line_starts : Array[Int32]
}

///|
pub fn Source::new(name : String, content : String) -> Source {
  let starts : Array[Int32] = [0]
  for i = 0; i < content.length(); i = i + 1 {
    if content[i] == '\n' {
      starts.push(i + 1)
    }
  }
  { name, content, line_starts: starts, }
}

///|
/// An empty source, used for synthetic spans.
pub fn Source::empty() -> Source {
  Source::new("", "")
}

///|
pub fn Source::line_count(self : Source) -> Int32 {
  self.line_starts.length()
}

///|
/// The offset at which `line` (1-based) starts. Clamped to the file.
pub fn Source::line_start(self : Source, line : Int32) -> Int32 {
  if line <= 1 {
    0
  } else if line > self.line_starts.length() {
    self.content.length()
  } else {
    self.line_starts[line - 1]
  }
}

///|
/// The text of `line` (1-based), without the trailing newline.
pub fn Source::line_text(self : Source, line : Int32) -> String {
  if line < 1 || line > self.line_starts.length() {
    return ""
  }
  let from = self.line_starts[line - 1]
  let to = if line < self.line_starts.length() {
    self.line_starts[line]
  } else {
    self.content.length()
  }
  let raw = self.content[from:to].to_owned()
  if raw.has_suffix("\n") {
    raw[0:raw.length() - 1].to_owned()
  } else {
    raw
  }
}

///|
/// Convert a 0-based character offset into a `Position`.
pub fn Source::offset_to_position(self : Source, offset : Int32) -> Position {
  let clamped = if offset < 0 {
    0
  } else if offset > self.content.length() {
    self.content.length()
  } else {
    offset
  }
  // Binary search for the last line_start <= clamped
  let mut lo = 0
  let mut hi = self.line_starts.length() - 1
  while lo < hi {
    let mid = (lo + hi + 1) / 2
    if self.line_starts[mid] <= clamped {
      lo = mid
    } else {
      hi = mid - 1
    }
  }
  { line: lo + 1, column: clamped - self.line_starts[lo] + 1, }
}

///|
/// Convert a `Position` back into a 0-based character offset.
pub fn Source::position_to_offset(self : Source, pos : Position) -> Int32 {
  self.line_start(pos.line) + pos.column - 1
}

///|
/// Extracts the text between two positions (end exclusive).
pub fn Source::text_between(
  self : Source,
  from : Position,
  to : Position,
) -> String {
  let a = self.position_to_offset(from)
  let b = self.position_to_offset(to)
  if b <= a {
    ""
  } else {
    self.content[a:b].to_owned()
  }
}

///|
/// The origin of a span.
///
/// - `Real`: the node has a direct representation in the source code.
/// - `Synthesized`: the node is not written by the user, but the span points
///   at the place where the user *could* have written it.
/// - `Missing`: no span information available (yet).
pub(all) enum Origin {
  Real
  Synthesized
  Missing
} derive(Eq, Debug)

///|
/// A region of a source file.
pub(all) struct Span {
  pub source : Source
  pub start : Int32
  pub end : Int32
  pub origin : Origin
}

///|
pub fn Span::new(source : Source, start : Int32, end : Int32) -> Span {
  { source, start, end, origin: Real, }
}

///|
pub fn Span::with_origin(
  source : Source,
  start : Int32,
  end : Int32,
  origin : Origin,
) -> Span {
  { source, start, end, origin, }
}

///|
pub fn Span::missing() -> Span {
  { source: Source::empty(), start: 0, end: 0, origin: Missing, }
}

///|
pub fn Span::missing_in(source : Source) -> Span {
  { source, start: 0, end: 0, origin: Missing, }
}

///|
/// A synthetic empty span immediately after this one.
pub fn Span::empty_after(self : Span) -> Span {
  {
    source: self.source,
    start: self.end + 1,
    end: self.end + 1,
    origin: Synthesized,
  }
}

///|
/// A synthetic copy of this span (same region, different origin).
pub fn Span::synthesized(self : Span) -> Span {
  {
    source: self.source,
    start: self.start,
    end: self.end,
    origin: Synthesized,
  }
}

///|
pub fn Span::is_missing(self : Span) -> Bool {
  self.origin == Missing
}

///|
/// The text covered by this span, if the span has real source information.
pub fn Span::text(self : Span) -> String? {
  if self.origin == Missing || self.source.content == "" {
    return None
  }
  let a = if self.start < 0 { 0 } else { self.start }
  let b = if self.end > self.source.content.length() {
    self.source.content.length()
  } else {
    self.end
  }
  if b <= a {
    None
  } else {
    Some(self.source.content[a:b].to_owned())
  }
}

///|
/// Extends a span to cover everything up to `other`.
pub fn Span::to_span(self : Span, other : Span) -> Span {
  if self.source.name != other.source.name {
    return self
  }
  {
    source: self.source,
    start: self.start,
    end: other.end,
    origin: self.origin,
  }
}

///|
pub fn Span::merge(self : Span, other : Span) -> Span {
  if self.origin == Missing {
    return other
  }
  if other.origin == Missing {
    return self
  }
  let a = if self.start <= other.start { self } else { other }
  let b = if self.end >= other.end { self } else { other }
  if a.source.name != b.source.name {
    return a
  }
  { source: a.source, start: a.start, end: b.end, origin: a.origin, }
}

///|
pub fn Span::position(self : Span) -> Position {
  self.source.offset_to_position(self.start)
}

///|
pub fn Span::range_text(self : Span) -> String {
  let from = self.source.offset_to_position(self.start)
  let to = self.source.offset_to_position(self.end)
  self.source.text_between(from, to)
}

///|
/// Ordering used for sorting diagnostics. Spans in different files are
/// ordered by file name.
pub fn Span::compare(self : Span, other : Span) -> Int32 {
  let nc = compare_string(self.source.name, other.source.name)
  if nc != 0 {
    return nc
  }
  if self.start != other.start {
    return self.start - other.start
  }
  self.end - other.end
}

///|
pub fn compare_string(a : String, b : String) -> Int32 {
  if a < b {
    -1
  } else if a > b {
    1
  } else {
    0
  }
}

///|
pub impl Show for Span with fn output(self, logger) {
  let pos = self.position()
  logger.write_string(self.source.name)
  logger.write_string(":")
  logger.write_string(pos.line.to_string())
  logger.write_string(":")
  logger.write_string(pos.column.to_string())
}
