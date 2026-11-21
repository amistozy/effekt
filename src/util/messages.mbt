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
  /// Prose about the claim, one line each, drawn under the excerpt
  /// (`Reason.details`): "There are multiple overloads, which all fail to
  /// check:", "Cannot instantiate 1st block argument foo of type ...".
  details : Array[String]
  /// Notes and helps shown under the diagnostic (`Diagnostic.subdiagnostics`).
  notes : Array[Subdiagnostic]
  /// Diagnostics nested under this one (`Reason.causes`), e.g. the failure that
  /// made an implicit argument impossible to instantiate.
  causes : Array[Message]
  /// The candidates of an unresolved overload (`Reason.alternatives`).
  candidates : Array[Candidate]
  /// How the message reads on a caret line, when that is not simply its first
  /// line (`Reason.claim` versus `Reason.show`).
  claim_text : String?
}

///|
/// One candidate of an unresolved overload (upstream `messages.Candidate`).
pub(all) struct Candidate {
  /// How the candidate reads when its declaration cannot be shown: `` `foo` of
  /// type ... `` (`Candidate.show`).
  text : String
  /// The span of the defining identifier, whose source line is drawn with the
  /// candidate's bullet on it (`Candidate.definitionTree`).
  declaration : Span
  /// The diagnostics that rejected this candidate (`Candidate.errors`).
  errors : Array[Message]
}

///|
pub fn Message::Message(
  severity : Severity,
  span : Span,
  text : String,
) -> Message {
  {
    severity,
    span,
    text,
    phase: None,
    details: [],
    notes: [],
    causes: [],
    candidates: [],
    claim_text: None,
  }
}

///|
pub fn Message::error(span : Span, text : String) -> Message {
  Message(Error, span, text)
}

///|
pub fn Message::warning(span : Span, text : String) -> Message {
  Message(Warning, span, text)
}

///|
pub fn Message::info(text : String) -> Message {
  Message(Info, Span::missing(), text)
}

///|
/// An informational message at a source position. Upstream's hints ("Did you
/// mean ...?") are reported at the position they talk about, which is what
/// places them in the IDE and in the test corpus (which matches by line).
pub fn Message::info_at(span : Span, text : String) -> Message {
  Message(Info, span, text)
}

///|
/// The same message, tagged with the phase that produced it.
pub fn Message::with_phase(self : Message, phase : String) -> Message {
  { ..self, phase: Some(phase), }
}

///|
/// The content of the message followed by one line per note and help, without
/// any markers. This is what a *nested* diagnostic looks like inside the text of
/// another one — upstream's `Style.contentWithSubdiagnostics`, which
/// `FailedOverloadError` and `ImplicitInstantiationError` indent under the
/// heading of their candidate.
pub fn Message::content_with_notes(self : Message) -> String {
  ([self.text] + self.notes.map(note => note.text())).join("\n")
}

///|
/// Adds a note, optionally at a place of its own.
pub fn Message::note(self : Message, text : String, at : Span?) -> Message {
  { ..self, notes: self.notes + [Note(text, at)], }
}

///|
/// Adds a suggestion how to fix the diagnostic.
pub fn Message::help(self : Message, text : String) -> Message {
  { ..self, notes: self.notes + [Help(text)], }
}

///|
/// Adds the notes and helps a scope explanation produced (upstream's
/// `abort(msg) { explainMissingTerm(id) }`, whose block appends to the
/// subdiagnostics of the message).
pub fn Message::subdiagnostics(
  self : Message,
  subs : ArrayView[Subdiagnostic],
) -> Message {
  { ..self, notes: self.notes + subs.to_owned(), }
}

///|
/// Adds the prose about the claim, which is drawn under the excerpt
/// (`Reason.details`).
pub fn Message::details(self : Message, details : ArrayView[String]) -> Message {
  { ..self, details: self.details + details.to_owned(), }
}

///|
/// Adds a diagnostic nested under this one (`Reason.causes`): it is drawn with
/// its own place and claim, one gutter deeper.
pub fn Message::cause(self : Message, cause : Message) -> Message {
  { ..self, causes: self.causes + [cause], }
}

///|
/// Adds the candidates of an unresolved overload (`Reason.alternatives`).
pub fn Message::candidates(
  self : Message,
  candidates : ArrayView[Candidate],
) -> Message {
  { ..self, candidates: self.candidates + candidates.to_owned(), }
}

///|
/// The claim of a message as it hangs off a caret: the one-line version of its
/// heading (upstream's `Reason.claim`, which a diagnostic spells out separately
/// when its heading is the aligned multi-line form).
pub fn Message::claim(self : Message) -> String {
  match self.claim_text {
    Some(text) => text
    None =>
      match self.text.find("\n") {
        Some(i) => self.text[:i].to_owned()
        None => self.text
      }
  }
}

///|
/// Spells out how the message reads on a caret line, when that differs from its
/// heading (upstream `Reason.claim` versus `Reason.show`).
pub fn Message::with_claim(self : Message, claim : String) -> Message {
  { ..self, claim_text: Some(claim), }
}

///|
/// The reason text with the phase appended to its *first* line; continuation
/// lines are printed verbatim (`ColoredMessaging.contentWithPhase`). A trailing
/// newline is kept: a message built as a string may end with one to separate the
/// claim from the excerpt below it.
pub fn with_phase(text : String, phase : String?) -> String {
  let suffix = match phase {
    Some(p) => " [\{p}]"
    None => ""
  }
  match text.find("\n") {
    Some(i) => text[:i].to_owned() + suffix + text[i:].to_owned()
    None => text + suffix
  }
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
/// single character otherwise. The lines below the excerpt are the message's
/// prose (`details`), and its paragraphs follow: the candidates of an unresolved
/// overload (each drawn with its declaration), the nested causes, and the notes
/// and helps. `src/util/drawing.mbt` lays those out. The test corpus records its
/// `.check` files with exactly this formatting.
pub fn Message::render(self : Message) -> String {
  let drawing = Drawing::new()
  for excerpt in excerpts_of(self) {
    drawing.excerpt_line(excerpt, None)
  }
  drawing.children(() => drawing.body(self))
  // One gutter for the whole drawing, as wide as its largest line number.
  let mut gutter = 0
  for line in drawing.lines {
    if line is Code(span, _, _, _) {
      let number = span.position().line.to_string()
      gutter = gutter.max(number.length())
    }
  }
  let header_source = if self.span.origin == Missing {
    None
  } else {
    Some(self.span.source)
  }
  let body = render_lines(drawing.lines, gutter, header_source)
  ([heading(self)] + body).join("\n")
}

///|
/// The internal-error escape hatch. Mirrors `INTERNAL_ERROR` upstream; the
/// result type is polymorphic so that it can stand in for any expected value.
pub fn[T] internal_error(msg : String) -> T raise EffektError {
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
