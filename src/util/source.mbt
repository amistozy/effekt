// Source files, positions and spans.
//
// Mirrors `effekt/util/Source.scala` and `effekt/source/Tree.scala` (Span).
// A `Source` is a plain in-memory file: the compiler never touches the file
// system itself, all IO happens in the driver.

///|
/// A position in a source file. Lines and columns are 1-based, matching the
/// convention used by the upstream compiler and by most editors.
#derive(Eq, Debug)
pub(all) struct Position {
  line : Int32
  column : Int32
}

///|
pub impl Show for Position with fn output(self, logger) {
  logger.write_string("\{self.line}:\{self.column}")
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
  /// The name to *show* in a diagnostic, when it differs from `name`: a file
  /// found under an include root is named by how the root is shown there, which
  /// is how the standard library reads as `/libraries/common/list.effekt`
  /// (upstream `IncludedFileSource.shown`). Empty means "same as `name`".
  shown : String
}

///|
pub fn Source::Source(name : String, content : String) -> Source {
  let starts : Array[Int32] = [0]
  for i in 0..<content.length() {
    if content[i] == '\n' {
      starts.push(i + 1)
    }
  }
  { name, content, line_starts: starts, shown: "", }
}

///|
/// The name diagnostics print for this source: the include root's view of it if
/// it was found through one, the name it was read under otherwise (upstream
/// `shownName`).
pub fn Source::shown_name(self : Source) -> String {
  if self.shown == "" {
    self.name
  } else {
    self.shown
  }
}

///|
/// A source found through an include root, shown as `<root>/<path>` no matter
/// where the root lives on disk.
pub fn Source::included(
  name : String,
  content : String,
  shown : String,
) -> Source {
  { ..Source(name, content), shown, }
}

///|
/// The same source text under a different name. The diagnostics of an imported
/// module are reported with the include path it was reached by, which upstream
/// writes as `./<path>.effekt` (a `VirtualFileSource`).
pub fn Source::renamed(self : Source, name : String) -> Source {
  { ..self, name, }
}

///|
/// An empty source, used for synthetic spans.
pub fn Source::empty() -> Source {
  Source("", "")
}

///|
/// The offset at which `line` (1-based) starts. Clamped to the file.
fn Source::line_start(self : Source, line : Int32) -> Int32 {
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
fn Source::line_text(self : Source, line : Int32) -> String {
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
  // A line ends at its terminator, which may be `\n` or `\r\n`: a source line
  // read from a file with Windows line endings must not carry the `\r` into a
  // diagnostic (the standard library is checked out that way here).
  if raw.has_suffix("\n") {
    let line = raw[0:raw.length() - 1].to_owned()
    if line.has_suffix("\r") {
      line[0:line.length() - 1].to_owned()
    } else {
      line
    }
  } else {
    raw
  }
}

///|
/// Convert a 0-based character offset into a `Position`.
pub fn Source::offset_to_position(self : Source, offset : Int32) -> Position {
  let clamped = offset.clamp(min=0, max=self.content.length())
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
fn Source::position_to_offset(self : Source, pos : Position) -> Int32 {
  self.line_start(pos.line) + pos.column - 1
}

///|
/// Extracts the text between two positions (end exclusive).
fn Source::text_between(
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
#derive(Eq, Debug)
pub(all) enum Origin {
  Real
  Synthesized
  Missing
}

///|
/// A region of a source file.
pub(all) struct Span {
  source : Source
  start : Int32
  end : Int32
  origin : Origin
}

///|
pub fn Span::Span(source : Source, start : Int32, end : Int32) -> Span {
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
/// A synthetic empty span immediately after this one (upstream
/// `Span.emptyAfter`): it sits at the end of this span, so a diagnostic there
/// underlines a single character.
pub fn Span::empty_after(self : Span) -> Span {
  { source: self.source, start: self.end, end: self.end, origin: Synthesized, }
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
  let a = self.start.max(0)
  let b = self.end.min(self.source.content.length())
  if b <= a {
    None
  } else {
    Some(self.source.content[a:b].to_owned())
  }
}

///|
/// Extends a span to cover everything up to `other`.
pub fn Span::to_span(self : Span, other : Span) -> Span {
  guard self.source.name == other.source.name else { self }
  Span::with_origin(self.source, self.start, other.end, self.origin)
}

///|
pub fn Span::merge(self : Span, other : Span) -> Span {
  guard self.origin != Missing else { return other }
  guard other.origin != Missing else { return self }
  let a = if self.start <= other.start { self } else { other }
  let b = if self.end >= other.end { self } else { other }
  guard a.source.name == b.source.name else { a }
  Span::with_origin(a.source, a.start, b.end, a.origin)
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
pub impl Show for Span with fn output(self, logger) {
  let pos = self.position()
  logger.write_string("\{self.source.name}:\{pos.line}:\{pos.column}")
}

// ---------------------------------------------------------------------------
// Literate sources
// ---------------------------------------------------------------------------

///|
/// What a code fence of a literate source is (upstream
/// `MarkdownSource.FenceType`).
priv enum FenceType {
  FenceRepl
  FenceIgnore
  FenceCode
  FenceOther
}

///|
/// A fence line: the language after the backticks (if any) and the
/// `:`-separated options (upstream's `fenceLine` regex
/// ``^```\s*(\w+)?\s*((?::[^:\n]*)*)$``).
priv struct Fence {
  lang : String?
  opts : Array[String]
}

///|
fn is_word_char(c : Char) -> Bool {
  (c >= 'a' && c <= 'z') ||
  (c >= 'A' && c <= 'Z') ||
  (c >= '0' && c <= '9') ||
  c == '_'
}

///|
fn is_fence_space(c : Char) -> Bool {
  c == ' ' || c == '\t'
}

///|
fn chars_text(chars : ArrayView[Char], from : Int32, to : Int32) -> String {
  let out = StringBuilder()
  for i in from..<to {
    out.write_char(chars[i])
  }
  out.to_string()
}

///|
/// The fence a line introduces or closes, if it is one.
fn parse_fence(line : String) -> Fence? {
  let chars = line.to_array()
  let n = chars.length()
  guard n >= 3 && chars[0] == '`' && chars[1] == '`' && chars[2] == '`' else {
    return None
  }
  let mut i = 3
  while i < n && is_fence_space(chars[i]) {
    i += 1
  }
  let lang_start = i
  while i < n && is_word_char(chars[i]) {
    i += 1
  }
  let lang = if i > lang_start {
    Some(chars_text(chars, lang_start, i))
  } else {
    None
  }
  while i < n && is_fence_space(chars[i]) {
    i += 1
  }
  guard i != n else { return Some({ lang, opts: [], }) }
  guard chars[i] == ':' else { return None }
  // `ots.split(":").tail`: the options are what follows the first colon, split
  // at further colons.
  let opts : Array[String] = []
  let mut start = i + 1
  let mut j = start
  while j <= n {
    if j == n || chars[j] == ':' {
      opts.push(chars_text(chars, start, j))
      start = j + 1
    }
    j += 1
  }
  Some({ lang, opts, })
}

///|
/// The lines of `text` the way Scala's `linesIterator` splits them: a trailing
/// line terminator does not produce an empty last line, and `\r\n` ends a line.
fn markdown_lines(text : String) -> Array[String] {
  let out : Array[String] = []
  let n = text.length()
  guard n != 0 else { return out }
  let mut start = 0
  for i in 0..<n {
    if text[i] == '\n' {
      out.push(strip_line_end(text, start, i))
      start = i + 1
    }
  }
  if start < n {
    out.push(strip_line_end(text, start, n))
  }
  out
}

///|
fn strip_line_end(text : String, from : Int32, to : Int32) -> String {
  if to > from && text[to - 1] == '\r' {
    text[from:to - 1].to_owned()
  } else {
    text[from:to].to_owned()
  }
}

///|
/// The program a literate source contains (upstream `MarkdownSource.content`).
///
/// All lines outside a code fence become empty lines, so that a diagnostic
/// keeps pointing at the line of the markdown file it came from. A fence is a
/// `Code` fence when it is written as ```` ```effekt ```` or without a language,
/// an `Other` one when it names another language (its content is dropped), and
/// `Ignore`/`Repl` when the options say so. A `Repl` fence is wrapped in
/// `def replN() = { ... }` and a `main` that prints each result with `show` is
/// appended — which is how the case studies in `examples/casestudies` are
/// written.
pub fn markdown_program(text : String) -> String {
  let lines = markdown_lines(text)
  let out : Array[String] = []
  let mut code : Array[String] = []
  let mut fence : FenceType? = None
  let mut repls = 0
  for line in lines {
    match parse_fence(line) {
      Some(f) =>
        if f.opts.contains("ignore") {
          fence = Some(FenceIgnore)
          out.push("")
        } else if f.opts.contains("repl") {
          fence = Some(FenceRepl)
          // the opening fence becomes the wrapper's header, at its own line
          out.push("def repl\{repls}() = {")
          repls += 1
        } else {
          match fence {
            // the opening fence: the language decides what happens to the body
            None => {
              fence = match f.lang {
                Some(l) =>
                  if l == "effekt" {
                    Some(FenceCode)
                  } else {
                    Some(FenceOther)
                  }
                None => Some(FenceCode)
              }
              out.push("")
            }
            // the closing fence: emit the body here, where it was collected
            Some(kind) => {
              match kind {
                FenceRepl => {
                  for l in code {
                    out.push(l)
                  }
                  out.push("}")
                }
                FenceCode => {
                  if !code.is_empty() {
                    for l in code {
                      out.push(l)
                    }
                  }
                  out.push("")
                }
                // an ignored fence and a fence of another language: the body
                // keeps its lines but none of its code
                FenceIgnore | FenceOther => {
                  for _ in code {
                    out.push("")
                  }
                  out.push("")
                }
              }
              fence = None
              code = []
            }
          }
        }
      // inside a fence the line is buffered; outside it only keeps the count
      None =>
        match fence {
          Some(_) => code.push(line)
          None => out.push("")
        }
    }
  }
  let mut program = out.join("\n")
  if repls > 0 {
    let printed : Array[String] = []
    for i in 0..<repls {
      printed.push("println(repl\{i}().show)")
    }
    // upstream's `main`, appended after the program (see `MarkdownSource`)
    program = program +
      "\ndef main() = {\n" +
      printed.join("\n") +
      "\n()\n}\n      "
  }
  program
}
