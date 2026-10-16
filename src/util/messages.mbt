// Diagnostics: compiler messages attached to spans.
//
// Mirrors `effekt/util/Messages.scala`.

///|
pub(all) enum Severity {
  Error
  Warning
  Info
} derive(Eq, Debug)

///|
pub impl Show for Severity with fn output(self, logger) {
  match self {
    Error => logger.write_string("error")
    Warning => logger.write_string("warning")
    Info => logger.write_string("info")
  }
}

///|
pub(all) struct Message {
  severity : Severity
  span : Span
  text : String
}

///|
pub fn Message::error(span : Span, text : String) -> Message {
  { severity: Error, span, text, }
}

///|
pub fn Message::warning(span : Span, text : String) -> Message {
  { severity: Warning, span, text, }
}

///|
pub fn Message::info(text : String) -> Message {
  { severity: Info, span: Span::missing(), text, }
}

///|
/// Renders a message with a source excerpt, in the style of the upstream
/// compiler's `ColoredMessaging` (without the colors).
pub fn Message::render(self : Message) -> String {
  let buf = StringBuilder()
  let sev = self.severity.to_string()
  buf.write_string(sev)
  if self.span.origin != Missing {
    let pos = self.span.position()
    buf.write_string(":")
    buf.write_string(self.span.source.name)
    buf.write_string(":")
    buf.write_string(pos.line.to_string())
    buf.write_string(":")
    buf.write_string(pos.column.to_string())
  }
  buf.write_string(": ")
  buf.write_string(self.text)
  if self.span.origin != Missing {
    buf.write_string("\n")
    let line = self.span.position().line
    let text = self.span.source.line_text(line)
    if text != "" {
      buf.write_string(text)
      buf.write_string("\n")
      let col = self.span.position().column - 1
      for i = 0; i < col; i = i + 1 {
        buf.write_string(" ")
      }
      let width = if self.span.end > self.span.start {
        let w = self.span.end - self.span.start
        if w > text.length() - col {
          1
        } else {
          w
        }
      } else {
        1
      }
      for i = 0; i < width; i = i + 1 {
        buf.write_string("^")
      }
    }
  }
  buf.to_string()
}

///|
/// The internal-error escape hatch. Mirrors `INTERNAL_ERROR` upstream.
pub fn internal_error(msg : String) -> Unit raise EffektError {
  raise EffektError::Internal("Internal compiler error: " + msg)
}

///|
/// Errors that abort the current compilation phase.
pub(all) suberror EffektError {
  /// A user-visible error that aborts compilation.
  Fatal(String)
  /// An invariant violation: a bug in the compiler.
  Internal(String)
}
