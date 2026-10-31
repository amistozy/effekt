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
/// An informational message at a source position. Upstream's hints ("Did you
/// mean ...?") are reported at the position they talk about, which is what
/// places them in the IDE and in the test corpus (which matches by line).
pub fn Message::info_at(span : Span, text : String) -> Message {
  { severity: Info, span, text, }
}

///|
/// Renders a message the way upstream's `ColoredMessaging` does (without the
/// colors):
///
/// ```text
/// [warning] path/to/file.effekt:3:5 Handling effect Foo, which seems not to be used by the program.
///   try { do Foo() } with Foo { () }
///   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
/// ```
///
/// The caret line underlines the span when it fits on one line and marks a
/// single character otherwise, which is what upstream's `formatMessage` does
/// for a multi-line range. The test corpus records its `.check` files with
/// exactly this formatting, so the program output and the diagnostics of a
/// positive test can be compared against it.
pub fn Message::render(self : Message) -> String {
  let buf = StringBuilder()
  let sev = self.severity.to_string()
  if self.span.origin == Missing {
    buf.write_string("[\{sev}] ")
    buf.write_string(self.text)
    return buf.to_string()
  }
  let pos = self.span.position()
  buf.write_string(
    "[\{sev}] \{self.span.source.name}:\{pos.line}:\{pos.column}: ",
  )
  buf.write_string(self.text)
  let text = self.span.source.line_text(pos.line)
  if text != "" {
    buf.write_string("\n")
    buf.write_string(text)
    buf.write_string("\n")
    let end = self.span.source.offset_to_position(self.span.end)
    let width = if end.line == pos.line && end.column > pos.column {
      end.column - pos.column
    } else {
      1
    }
    for i = 0; i < pos.column - 1; i = i + 1 {
      buf.write_string(" ")
    }
    for i = 0; i < width; i = i + 1 {
      buf.write_string("^")
    }
  }
  buf.to_string()
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
