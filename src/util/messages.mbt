// Diagnostics: compiler messages attached to spans.
//
// Mirrors `effekt/util/Messages.scala` and `effekt/util/ColoredMessaging.scala`.

///|
#derive(Eq, Debug)
pub(all) enum Severity {
  Error
  Warning
  Info
}

///|
pub impl Show for Severity with fn output(self, logger) {
  match self {
    Error => logger.write_string("error")
    Warning => logger.write_string("warning")
    Info => logger.write_string("info")
  }
}

///|
/// A fact about a diagnostic, optionally at its own place (`Note`), or a way to
/// fix it (`Help`). Rendered under the diagnostic as a `* note:`/`* help:` item.
///
/// Mirrors `messages.Subdiagnostic`.
pub(all) enum Subdiagnostic {
  Note(String, Span?)
  Help(String)
}

///|
pub fn Subdiagnostic::text(self : Subdiagnostic) -> String {
  match self {
    Note(text, _) => text
    Help(text) => text
  }
}

///|
pub(all) struct Message {
  severity : Severity
  span : Span
  text : String
  /// The compilation phase that reported the message, rendered as `[typer]`
  /// after the first line of the message (`ColoredMessaging.contentWithPhase`).
  phase : String?
  /// Notes and helps shown under the diagnostic (`Diagnostic.subdiagnostics`).
  notes : Array[Subdiagnostic]
}

///|
pub fn Message::new(severity : Severity, span : Span, text : String) -> Message {
  { severity, span, text, phase: None, notes: [], }
}

///|
pub fn Message::error(span : Span, text : String) -> Message {
  Message::new(Error, span, text)
}

///|
pub fn Message::warning(span : Span, text : String) -> Message {
  Message::new(Warning, span, text)
}

///|
pub fn Message::info(text : String) -> Message {
  Message::new(Info, Span::missing(), text)
}

///|
/// An informational message at a source position. Upstream's hints ("Did you
/// mean ...?") are reported at the position they talk about, which is what
/// places them in the IDE and in the test corpus (which matches by line).
pub fn Message::info_at(span : Span, text : String) -> Message {
  Message::new(Info, span, text)
}

///|
/// The same message, tagged with the phase that produced it.
pub fn Message::with_phase(self : Message, phase : String) -> Message {
  { ..self, phase: Some(phase), }
}

///|
/// Adds a note, optionally at a place of its own.
pub fn Message::note(self : Message, text : String, at : Span?) -> Message {
  let notes = self.notes.copy()
  notes.push(Note(text, at))
  { ..self, notes, }
}

///|
/// Adds a suggestion how to fix the diagnostic.
pub fn Message::help(self : Message, text : String) -> Message {
  let notes = self.notes.copy()
  notes.push(Help(text))
  { ..self, notes, }
}

///|
/// A rendered source line: the 1-based line number, the line itself and the
/// marker underlining the span (`ColoredMessaging.Excerpt`).
priv struct Excerpt {
  line : Int32
  code : String
  marker : String
}

///|
/// The line where `span` starts, marked to its end on that line.
fn excerpt_of(span : Span) -> Excerpt? {
  if span.origin == Missing {
    return None
  }
  let pos = span.position()
  let code = span.source.line_text(pos.line)
  if code == "" {
    return None
  }
  let end = span.source.offset_to_position(span.end)
  let width = if end.line == pos.line && end.column > pos.column {
    end.column - pos.column
  } else {
    1
  }
  let marker = StringBuilder()
  for i = 0; i < pos.column - 1; i = i + 1 {
    marker.write_string(" ")
  }
  for i = 0; i < width; i = i + 1 {
    marker.write_string("^")
  }
  Some({ line: pos.line, code, marker: marker.to_string(), })
}

///|
fn spaces(count : Int32) -> String {
  let buf = StringBuilder()
  for i = 0; i < count; i = i + 1 {
    buf.write_string(" ")
  }
  buf.to_string()
}

///|
/// The line number, right-aligned to the width of the widest line number of the
/// diagnostic and its notes.
fn align_line(line : Int32, width : Int32) -> String {
  let shown = line.to_string()
  spaces(width - shown.length()) + shown
}

///|
/// The reason text with the phase appended to its *first* line; continuation
/// lines are printed verbatim (`ColoredMessaging.contentWithPhase`).
fn with_phase(text : String, phase : String?) -> String {
  let suffix = match phase {
    Some(p) => " [\{p}]"
    None => ""
  }
  let lines = text.split("\n").map(s => s.to_owned()).collect()
  if lines.length() == 0 {
    return suffix
  }
  lines[0] = lines[0] + suffix
  lines.join("\n")
}

///|
/// Renders a message the way upstream's `ColoredMessaging` does (without the
/// colors):
///
/// ```text
/// [error] path/to/file.effekt:2:10: Could not resolve type Boolean [namer]
/// 2  def alwaysTrue(): Boolean = true
///                      ^^^^^^^
///
///    * help: Did you mean Bool?
/// ```
///
/// The caret line underlines the span when it fits on one line and marks a
/// single character otherwise. Notes and helps are rendered as items under the
/// diagnostic, each preceded by a blank line, and a note that has a place of
/// its own gets an excerpt separated from the diagnostic's by a gutter (`|`).
/// The test corpus records its `.check` files with exactly this formatting.
pub fn Message::render(self : Message) -> String {
  let primary = excerpt_of(self.span)
  // One gutter for the whole diagnostic, as wide as its largest line number.
  let mut width = 0
  match primary {
    Some(e) => width = e.line.to_string().length()
    None => ()
  }
  let items : Array[(String, String, Excerpt?)] = []
  for note in self.notes {
    match note {
      Note(text, at) => {
        let excerpt = match at {
          Some(span) => excerpt_of(span)
          None => None
        }
        match excerpt {
          Some(e) => {
            let len = e.line.to_string().length()
            if len > width {
              width = len
            }
          }
          None => ()
        }
        items.push(("note", text, excerpt))
      }
      Help(text) => items.push(("help", text, None))
    }
  }
  let lines : Array[String] = []
  let sev = self.severity.to_string()
  let text = with_phase(self.text, self.phase)
  let header = if self.span.origin == Missing {
    "[\{sev}] \{text}"
  } else {
    let pos = self.span.position()
    "[\{sev}] \{self.span.source.name}:\{pos.line}:\{pos.column}: \{text}"
  }
  lines.push(header)
  let mut previous_excerpt = match primary {
    Some(e) => {
      lines.push(align_line(e.line, width) + "  " + e.code)
      lines.push(spaces(width) + "  " + e.marker)
      true
    }
    None => false
  }
  for i = 0; i < items.length(); i = i + 1 {
    let (kind, text, excerpt) = items[i]
    if i == 0 || excerpt is Some(_) || previous_excerpt {
      lines.push("")
    }
    lines.push(spaces(width + 2) + "* " + kind + ": " + text)
    match excerpt {
      Some(e) => {
        lines.push(align_line(e.line, width) + "  |  " + e.code)
        lines.push(spaces(width + 2) + "|  " + e.marker)
        previous_excerpt = true
      }
      None => previous_excerpt = false
    }
  }
  lines.join("\n")
}

///|
/// The internal-error escape hatch. Mirrors `INTERNAL_ERROR` upstream.
pub fn internal_error(msg : String) -> Unit raise EffektError {
  raise EffektError::Internal("Internal compiler error: \{msg}")
}

///|
/// Errors that abort the current compilation phase.
pub(all) suberror EffektError {
  /// A user-visible error that aborts compilation.
  Fatal(String)
  /// An invariant violation: a bug in the compiler.
  Internal(String)
}
