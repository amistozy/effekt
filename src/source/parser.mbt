// The Effekt parser.
//
// A faithful port of `effekt/shared/src/main/scala/effekt/Parser.scala`.
//
// Upstream is written in a combinator style with by-name arguments, a "span"
// dynamic variable (`nonterminal`), backtracking via exceptions (`backtrack`),
// and `Many`/`Maybe` wrappers that carry spans. In MoonBit the by-name
// arguments become closures `() -> T raise EffektError`, the exceptions become
// `EffektError::Fatal`, and the dynamic variable becomes the mutable field
// `Parser::start`.
//
// The public entry points are `parse_module_decl` and `parse_term`.

// ---------------------------------------------------------------------------
// Spanned lists and optional values
// ---------------------------------------------------------------------------

///|
/// A non-empty list of parsed items together with the span of the whole list.
pub struct Many[T] {
  items : Array[T]
  span : Span
}

///|
pub fn[T] Many::new(items : Array[T], span : Span) -> Many[T] {
  { items, span, }
}

///|
pub fn[T] Many::empty(span : Span) -> Many[T] {
  { items: [], span, }
}

///|
/// The items, without the span information (Scala's `unspan`).
pub fn[T] Many::unspan(self : Many[T]) -> Array[T] {
  self.items
}

///|
pub fn[T] Many::size(self : Many[T]) -> Int32 {
  self.items.length()
}

///|
/// An optional parse result together with a span (Scala's `Maybe[T]`).
pub struct Maybe[T] {
  value : T?
  span : Span
}

///|
pub fn[T] Maybe::some(value : T, span : Span) -> Maybe[T] {
  { value: Some(value), span, }
}

///|
pub fn[T] Maybe::none(span : Span) -> Maybe[T] {
  { value: None, span, }
}

///|
pub fn[T] Maybe::get_or_else(self : Maybe[T], default : T) -> T {
  self.value.unwrap_or(default)
}

///|
/// Like `get_or_else`, but the default is only computed if needed.
pub fn[T] Maybe::get_or_else_lazy(
  self : Maybe[T],
  default : () -> T raise EffektError,
) -> T raise EffektError {
  match self.value {
    Some(v) => v
    None => default()
  }
}

///|
pub fn[T] Maybe::or_else(
  self : Maybe[T],
  other : () -> Maybe[T] raise EffektError,
) -> Maybe[T] raise EffektError {
  match self.value {
    Some(_) => self
    None => other()
  }
}

///|
pub fn[T, U] Maybe::map(
  self : Maybe[T],
  f : (T) -> U raise EffektError,
) -> Maybe[U] raise EffektError {
  match self.value {
    Some(v) => { value: Some(f(v)), span: self.span, }
    None => { value: None, span: self.span, }
  }
}

///|
pub fn[T] Maybe::non_empty(self : Maybe[T]) -> Bool {
  match self.value {
    Some(_) => true
    None => false
  }
}

///|
/// A value together with the span it was parsed from.
pub struct Spanned[T] {
  unspan : T
  span : Span
}

///|
/// A string template with interpolated (spanned) holes.
pub struct SpannedTemplate[T] {
  strings : Array[Spanned[String]]
  args : Array[Spanned[T]]
}

// ---------------------------------------------------------------------------
// Operator precedence
// ---------------------------------------------------------------------------

///|
/// Associativity of an infix operator. `AssocNone` means "non-associative":
/// using it twice in a row without parentheses is an error.
pub(all) enum Associativity {
  AssocLeft
  AssocRight
  AssocNone
}

///|
pub(all) enum Precedence {
  LeftBindsTighter
  RightBindsTighter
  Ambiguous
}

///|
/// Encodes the precedence of infix operators as a partial order.
/// See `effekt/Precedence.scala`.
pub struct PrecedenceTable {
  ops : Array[TokenKind]
  assoc : Array[(TokenKind, Associativity)]
  matrix : Array[Array[Bool]]
}

///|
fn array_index_of(xs : Array[TokenKind], x : TokenKind) -> Int32 {
  for i = 0; i < xs.length(); i = i + 1 {
    if xs[i] == x {
      return i
    }
  }
  -1
}

///|
/// The precedence table used by the parser. Mirrors `Parser.precedenceTable`.
pub fn build_precedence_table() -> PrecedenceTable {
  let relations : Array[(TokenKind, TokenKind)] = []
  let assoc : Array[(TokenKind, Associativity)] = []
  for op in [TEqEqEq, TNotEqEq, TLtEq, TGtEq, TLt, TGt] {
    assoc.push((op, AssocNone))
  }
  let loosen = fn(looser : Array[TokenKind], tighter : Array[TokenKind]) {
    for l in looser {
      for t in tighter {
        relations.push((l, t))
      }
    }
  }
  let same_level = fn(a : Array[TokenKind], b : Array[TokenKind]) {
    loosen(a, b)
    loosen(b, a)
  }
  // We want `+` and `-` (as well as `*` and `/`) to bind equally strong and
  // use associativity instead to disambiguate.
  same_level([TPlus], [TMinus])
  same_level([TStar], [TSlash])
  loosen([TBarBar], [TAmpAmp])
  loosen([TAmpAmp], [TBar])
  loosen([TBar], [TAmp])
  loosen([TAmp], [TEqEqEq, TNotEqEq, TLtEq, TGtEq, TLt, TGt])
  loosen([TEqEqEq, TNotEqEq, TLtEq, TGtEq, TLt, TGt], [
    TDotDot,
    TDotDotDot,
    TTilde,
    TTildeGt,
    TLtTilde,
  ])
  loosen([TDotDot, TDotDotDot, TTilde, TTildeGt, TLtTilde], [
    TPlusPlus,
    TMinusMinus,
    TPlus,
    TMinus,
    TLtLt,
    TGtGt,
    THat,
    THatHat,
  ])
  loosen([TPlusPlus, TMinusMinus, TPlus, TMinus, TLtLt, TGtGt, THat, THatHat], [
    TStar,
    TSlash,
  ])
  // The operators, in the order in which they first appear.
  let ops : Array[TokenKind] = []
  for pair in relations {
    let (l, t) = pair
    if !ops.contains(l) {
      ops.push(l)
    }
    if !ops.contains(t) {
      ops.push(t)
    }
  }
  let n = ops.length()
  let matrix : Array[Array[Bool]] = []
  for i = 0; i < n; i = i + 1 {
    matrix.push(Array::make(n, false))
  }
  for pair in relations {
    let (l, t) = pair
    let i = array_index_of(ops, l)
    let j = array_index_of(ops, t)
    if i >= 0 && j >= 0 {
      matrix[i][j] = true
    }
  }
  // Transitive closure (Floyd-Warshall; the table is tiny).
  for k = 0; k < n; k = k + 1 {
    for i = 0; i < n; i = i + 1 {
      for j = 0; j < n; j = j + 1 {
        if matrix[i][k] && matrix[k][j] {
          matrix[i][j] = true
        }
      }
    }
  }
  { ops, assoc, matrix, }
}

///|
fn PrecedenceTable::is_operator(self : PrecedenceTable, op : TokenKind) -> Bool {
  array_index_of(self.ops, op) >= 0
}

///|
fn PrecedenceTable::associativity(
  self : PrecedenceTable,
  op : TokenKind,
) -> Associativity {
  for entry in self.assoc {
    let (o, a) = entry
    if o == op {
      return a
    }
  }
  AssocLeft
}

///|
fn PrecedenceTable::reaches(
  self : PrecedenceTable,
  a : TokenKind,
  b : TokenKind,
) -> Bool {
  let i = array_index_of(self.ops, a)
  let j = array_index_of(self.ops, b)
  if i < 0 || j < 0 {
    return false
  }
  self.matrix[i][j]
}

///|
fn PrecedenceTable::compare(
  self : PrecedenceTable,
  left : TokenKind,
  right : TokenKind,
) -> Precedence {
  if left == right || (self.reaches(left, right) && self.reaches(right, left)) {
    // same operator, or explicitly declared at the same level: use associativity
    match (self.associativity(left), self.associativity(right)) {
      (AssocLeft, _) | (_, AssocLeft) => LeftBindsTighter
      (AssocRight, _) | (_, AssocRight) => RightBindsTighter
      _ => Ambiguous
    }
  } else if self.reaches(left, right) {
    RightBindsTighter
  } else if self.reaches(right, left) {
    LeftBindsTighter
  } else {
    Ambiguous
  }
}

// ---------------------------------------------------------------------------
// The parser
// ---------------------------------------------------------------------------

///|
/// A "soft" diagnostic: parsing continues, but the diagnostic is reported.
pub struct RecoverableDiagnostic {
  kind : Severity
  message : String
  start : Int32
  end : Int32
}

///|
pub struct Parser {
  tokens : Array[Token]
  source : Source
  context : Context
  /// Always points to the first token after the previously consumed one
  /// (whitespace excluded).
  mut position : Int32
  /// The previously consumed token.
  mut previous : Token?
  mut current_label : String?
  /// The `_start` dynamic variable of upstream: the start of the innermost
  /// `nonterminal`.
  mut start : Int32
  /// Token index at which the last hard failure happened.
  mut fail_position : Int32
  diagnostics : Array[RecoverableDiagnostic]
  precedence : PrecedenceTable
}

///|
pub fn Parser::new(
  tokens : Array[Token],
  source : Source,
  context : Context,
) -> Parser raise EffektError {
  let parser : Parser = {
    tokens,
    source,
    context,
    position: 0,
    previous: None,
    current_label: None,
    start: 0,
    fail_position: 0,
    diagnostics: [],
    precedence: build_precedence_table(),
  }
  // HACK: eat spaces before we begin!
  parser.spaces()
  if parser.position != 0 {
    parser.previous = Some(parser.token_at(parser.position))
  }
  parser
}

// Interfacing with the token stream
// ---------------------------------

///|
/// The token at a given index, or the last token (EOF) if out of range.
fn Parser::raw_token_at(self : Parser, i : Int32) -> Token {
  if i < 0 {
    Token::new(0, 0, TEOF)
  } else if i >= self.tokens.length() {
    if self.tokens.length() > 0 {
      self.tokens[self.tokens.length() - 1]
    } else {
      Token::new(0, 0, TEOF)
    }
  } else {
    self.tokens[i]
  }
}

///|
fn Parser::recover(
  self : Parser,
  token_kind : TokenKind,
  token_position : Int32,
) -> TokenKind raise EffektError {
  match token_kind {
    TError(err) => {
      let recovered : TokenKind = match err {
        UnterminatedStringLike(kind) => self.recover(kind, token_position)
        UnterminatedComment => TComment("<unterminated>")
        EmptyCharLiteral => TChr('?'.to_int())
        MultipleCodePointsInChar => TChr('?'.to_int())
        InvalidIntegerFormat => TInteger(0)
        InvalidDoubleFormat => TFloat(@double.not_a_number)
        _ => self.fail(err.message())
      }
      // NOTE: this relies on the fact that the `fail` above throws!
      self.soft_fail(err.message(), token_position, token_position)
      recovered
    }
    _ => token_kind
  }
}

///|
fn Parser::fail_on_error_token(
  self : Parser,
  token : Token,
  token_position : Int32,
) -> Token raise EffektError {
  match token.kind {
    TError(_) =>
      Token::new(
        token.start,
        token.end,
        self.recover(token.kind, token_position),
      )
    _ => token
  }
}

///|
/// The token at an index, with error recovery applied.
fn Parser::token_at(self : Parser, i : Int32) -> Token raise EffektError {
  let token = self.raw_token_at(i)
  self.fail_on_error_token(token, i)
}

///|
fn Parser::peek_token(self : Parser) -> Token raise EffektError {
  self.token_at(self.position)
}

///|
fn Parser::peek_kind(self : Parser) -> TokenKind raise EffektError {
  self.peek_token().kind
}

///|
fn Parser::peek(self : Parser, kind : TokenKind) -> Bool raise EffektError {
  self.peek_kind() == kind
}

///|
/// Peeks `offset` *tokens* (not characters) ahead of the current one,
/// skipping whitespace.
fn Parser::peek_at(self : Parser, offset : Int32) -> Token raise EffektError {
  let mut i = self.position
  let mut remaining = offset
  while i < self.tokens.length() {
    let token = self.fail_on_error_token(self.tokens[i], i)
    if token.kind.is_space() {
      i = i + 1
    } else if remaining <= 0 {
      return token
    } else {
      i = i + 1
      remaining = remaining - 1
    }
  }
  self.fail("Unexpected end of file")
}

///|
fn Parser::peek_at_kind(
  self : Parser,
  offset : Int32,
  kind : TokenKind,
) -> Bool raise EffektError {
  self.peek_at(offset).kind == kind
}

///|
fn Parser::skip_if(self : Parser, kind : TokenKind) -> Bool raise EffektError {
  if self.peek_kind() == kind {
    self.skip()
    true
  } else {
    false
  }
}

///|
fn Parser::has_next(self : Parser) -> Bool {
  self.position < self.tokens.length()
}

///|
fn Parser::next(self : Parser) -> Token raise EffektError {
  let t = self.token_at(self.position)
  self.skip()
  t
}

///|
/// Skips the current token and then all subsequent whitespace.
fn Parser::skip(self : Parser) -> Unit raise EffektError {
  self.previous = Some(self.token_at(self.position))
  self.position = self.position + 1
  self.current_label = None
  self.spaces()
}

///|
fn Parser::spaces(self : Parser) -> Unit raise EffektError {
  while self.has_next() {
    let kind = self.peek_kind()
    if kind.is_space() {
      self.position = self.position + 1
    } else {
      return
    }
  }
}

///|
fn Parser::consume(self : Parser, kind : TokenKind) -> Unit raise EffektError {
  if !self.has_next() {
    self.fail("Expected \{kind.explain()}, but reached end of file")
  }
  if self.peek_kind() != kind {
    self.fail_expected(kind.explain(), self.peek_kind())
  }
  let _ = self.next()
}

///|
/// Did the previous (non-space) token end the line, i.e. is there a newline
/// between it and the token we are looking at?
fn Parser::saw_newline_last(self : Parser) -> Bool raise EffektError {
  let mut i = self.position - 1
  while i >= 0 {
    let token = self.fail_on_error_token(self.tokens[i], i)
    if token.kind.is_space() && token.kind != TNewline {
      i = i - 1
    } else if token.kind == TNewline {
      return true
    } else {
      return false
    }
  }
  self.fail("Unexpected start of file")
}

///|
/// The current position, i.e. the position *after* the previous token.
/// (Lexer positions are inclusive, spans are half-open.)
fn Parser::pos(self : Parser) -> Int32 {
  match self.previous {
    Some(t) => t.end + 1
    None => 0
  }
}

// Failures and diagnostics
// ------------------------

///|
fn[T] Parser::fail(self : Parser, msg : String) -> T raise EffektError {
  self.fail_position = self.position
  raise EffektError::Fatal(msg)
}

///|
fn[T] Parser::fail_expected(
  self : Parser,
  expected : String,
  got : TokenKind,
) -> T raise EffektError {
  let label = match self.current_label {
    Some(l) => l
    None => expected
  }
  self.fail("Expected \{label} but got \{got.explain()}")
}

///|
fn Parser::soft_fail(
  self : Parser,
  message : String,
  start : Int32,
  end : Int32,
) -> Unit {
  self.diagnostics.push({ kind: Error, message, start, end, })
}

///|
fn Parser::warn(
  self : Parser,
  message : String,
  start : Int32,
  end : Int32,
) -> Unit {
  self.diagnostics.push({ kind: Warning, message, start, end, })
}

///|
fn[T] Parser::soft_fail_with(
  self : Parser,
  message : String,
  p : () -> T raise EffektError,
) -> T raise EffektError {
  let start_position = self.position
  let result = p()
  let end_position = self.position
  if start_position == end_position {
    self.soft_fail(message, start_position, start_position)
  } else {
    self.soft_fail(message, start_position, end_position - 1)
  }
  result
}

///|
/// Reports a diagnostic for the tokens in the index range `[from, to]`.
fn Parser::report(
  self : Parser,
  msg : String,
  from : Int32,
  to : Int32,
  severity : Severity,
) -> Unit {
  let from_token = self.raw_token_at(from)
  let to_token = self.raw_token_at(to)
  let span = Span::new(self.source, from_token.start, to_token.end + 1)
  match severity {
    Error => self.context.report(Message::error(span, msg))
    Warning => self.context.report(Message::warning(span, msg))
    Info => self.context.report(Message::info(msg))
  }
}

///|
fn Parser::report_recoverable_diagnostics(self : Parser) -> Unit {
  for d in self.diagnostics {
    self.report(d.message, d.start, d.end, d.kind)
  }
}

// Spans
// -----

///|
/// A span from `start` to the end of the previously consumed token.
fn Parser::span_from(self : Parser, start : Int32) -> Span {
  let end = self.pos()
  if start > end {
    // We did not consume anything (except for whitespace), so we generate an
    // empty span just after the previous token.
    Span::new(self.source, end, end)
  } else {
    Span::new(self.source, start, end)
  }
}

///|
/// A span from the start of the innermost `nonterminal` to the previous token.
fn Parser::span(self : Parser) -> Span {
  self.span_from(self.start)
}

///|
/// The handler for the "span" effect: everything parsed inside `p` reports its
/// span relative to the first token `p` sees.
fn[T] Parser::nonterminal(
  self : Parser,
  p : () -> T raise EffektError,
) -> T raise EffektError {
  let saved = self.start
  self.start = self.peek_token().start
  let res = p() catch {
    Fatal(m) => {
      self.start = saved
      raise EffektError::Fatal(m)
    }
    Internal(m) => {
      self.start = saved
      raise EffektError::Internal(m)
    }
  }
  self.start = saved
  res
}

///|
fn[T] Parser::nonterminal_at(
  self : Parser,
  span : Span,
  p : () -> T raise EffektError,
) -> T raise EffektError {
  let saved = self.start
  self.start = span.start
  let res = p() catch {
    Fatal(m) => {
      self.start = saved
      raise EffektError::Fatal(m)
    }
    Internal(m) => {
      self.start = saved
      raise EffektError::Internal(m)
    }
  }
  self.start = saved
  res
}

// Combinators
// -----------

///|
/// Guards `thn` by token `t` and consumes the token itself, if present.
fn[T] Parser::when(
  self : Parser,
  t : TokenKind,
  thn : () -> T raise EffektError,
  els : () -> T raise EffektError,
) -> T raise EffektError {
  if self.peek(t) {
    self.consume(t)
    thn()
  } else {
    els()
  }
}

///|
/// Runs `p`, and if it fails, restores the parser state and returns `None`.
fn[T] Parser::backtrack(
  self : Parser,
  restore_recoverable : Bool,
  p : () -> T raise EffektError,
) -> Maybe[T] raise EffektError {
  let before = self.position
  let before_previous = self.previous
  let label_before = self.current_label
  let recoverable_before = self.diagnostics.copy()
  let before_end = self.raw_token_at(before).end
  let result = try {
    let value = p()
    let end = self.pos()
    let start = before_end
    let sp = if start > end {
      Span::new(self.source, end, end)
    } else {
      Span::new(self.source, start, end)
    }
    Maybe::some(value, sp)
  } catch {
    Fatal(_) => {
      self.position = before
      self.previous = before_previous
      self.current_label = label_before
      if restore_recoverable {
        self.diagnostics.clear()
        self.diagnostics.append(recoverable_before)
      }
      let p = self.pos()
      Maybe::none(Span::with_origin(self.source, p, p, Synthesized))
    }
    Internal(m) => raise EffektError::Internal(m)
  }
  result
}

///|
/// Marks the current parse position with a label, used for error messages.
fn[T] Parser::labelled(
  self : Parser,
  label : String,
  p : () -> T raise EffektError,
) -> T raise EffektError {
  let label_before = self.current_label
  if self.current_label is None {
    self.current_label = Some(label)
  }
  let res = p()
  self.current_label = label_before
  res
}

///|
fn[T] Parser::parens(
  self : Parser,
  p : () -> T raise EffektError,
) -> T raise EffektError {
  self.consume(TLParen)
  let res = p()
  self.consume(TRParen)
  res
}

///|
fn[T] Parser::braces(
  self : Parser,
  p : () -> T raise EffektError,
) -> T raise EffektError {
  self.consume(TLBrace)
  let res = p()
  self.consume(TRBrace)
  res
}

///|
/// Parses `p (sep p)* sep? after`, soft failing when `fail_on_singleton` is set
/// and the "list" has one element and a trailing separator.
fn[T] Parser::delimited_until(
  self : Parser,
  p : () -> T raise EffektError,
  sep : TokenKind,
  after : TokenKind,
  fail_on_singleton : Bool,
) -> Array[T] raise EffektError {
  let components : Array[T] = []
  components.push(p())
  while self.peek(sep) {
    self.consume(sep)
    if !self.peek(after) {
      // if `after` follows `sep`, then it was trailing
      components.push(p())
    } else if fail_on_singleton && components.length() == 1 {
      self.soft_fail(
        "There are no one-element tuples. Remove the trailing `\{sep.explain()}` to group, or add another element.",
        self.position - 1,
        self.position - 1,
      )
    }
  }
  self.consume(after)
  components
}

///|
/// Repeats `p`, separated by `sep`, enclosed by `before` and `after`.
fn[T] Parser::some(
  self : Parser,
  p : () -> T raise EffektError,
  before : TokenKind,
  sep : TokenKind,
  after : TokenKind,
  fail_on_singleton : Bool,
) -> Many[T] raise EffektError {
  self.nonterminal(() => {
    self.consume(before)
    let items = self.delimited_until(p, sep, after, fail_on_singleton)
    Many::new(items, self.span())
  })
}

///|
/// Repeats `p` at least once, separated by `sep` (no delimiters, no trailing
/// separators).
fn[T] Parser::some_sep(
  self : Parser,
  p : () -> T raise EffektError,
  sep : TokenKind,
) -> Many[T] raise EffektError {
  self.nonterminal(() => {
    let components : Array[T] = []
    components.push(p())
    while self.peek(sep) {
      self.consume(sep)
      components.push(p())
    }
    Many::new(components, self.span())
  })
}

///|
fn[T] Parser::some_while_kind(
  self : Parser,
  p : () -> T raise EffektError,
  lookahead : TokenKind,
) -> Many[T] raise EffektError {
  self.some_while(p, () => self.peek(lookahead))
}

///|
fn[T] Parser::some_while(
  self : Parser,
  p : () -> T raise EffektError,
  predicate : () -> Bool raise EffektError,
) -> Many[T] raise EffektError {
  self.nonterminal(() => {
    let components : Array[T] = []
    components.push(p())
    while predicate() {
      components.push(p())
    }
    Many::new(components, self.span())
  })
}

///|
fn[T] Parser::many_while_kind(
  self : Parser,
  p : () -> T raise EffektError,
  lookahead : TokenKind,
) -> Array[T] raise EffektError {
  self.many_while(p, () => self.peek(lookahead))
}

///|
fn[T] Parser::many_while(
  _self : Parser,
  p : () -> T raise EffektError,
  predicate : () -> Bool raise EffektError,
) -> Array[T] raise EffektError {
  let components : Array[T] = []
  while predicate() {
    components.push(p())
  }
  components
}

///|
fn[T] Parser::many_until_kind(
  self : Parser,
  p : () -> T raise EffektError,
  lookahead : TokenKind,
) -> Array[T] raise EffektError {
  self.many_until(p, () => self.peek(lookahead))
}

///|
fn[T] Parser::many_until(
  self : Parser,
  p : () -> T raise EffektError,
  predicate : () -> Bool raise EffektError,
) -> Array[T] raise EffektError {
  self.many_while(p, () => !predicate())
}

///|
fn[T] Parser::many(
  self : Parser,
  p : () -> T raise EffektError,
  before : TokenKind,
  sep : TokenKind,
  after : TokenKind,
) -> Many[T] raise EffektError {
  self.nonterminal(() => {
    self.consume(before)
    if self.peek(after) {
      self.consume(after)
      Many::empty(self.span())
    } else {
      let items = self.delimited_until(p, sep, after, false)
      Many::new(items, self.span())
    }
  })
}

///|
fn[T] Parser::spanned(
  self : Parser,
  p : () -> T raise EffektError,
) -> Spanned[T] raise EffektError {
  self.nonterminal(() => {
    let value = p()
    { unspan: value, span: self.span(), }
  })
}

///|
fn[T] Parser::documented(
  self : Parser,
  p : (Info) -> T raise EffektError,
) -> T raise EffektError {
  self.nonterminal(() => p(self.info()))
}

///|
fn[A] interleave(xs : Array[A], ys : Array[A]) -> Array[A] {
  let result : Array[A] = []
  let mut i = 0
  while i < xs.length() || i < ys.length() {
    if i < xs.length() {
      result.push(xs[i])
    }
    if i < ys.length() {
      result.push(ys[i])
    }
    i = i + 1
  }
  result
}

///|
fn join_strings(xs : Array[String], sep : String) -> String {
  let buf = StringBuilder()
  for i = 0; i < xs.length(); i = i + 1 {
    if i > 0 {
      buf.write_string(sep)
    }
    buf.write_string(xs[i])
  }
  buf.to_string()
}

///|
fn[T] array_init(xs : Array[T]) -> Array[T] {
  let result : Array[T] = []
  for i = 0; i < xs.length() - 1; i = i + 1 {
    result.push(xs[i])
  }
  result
}

///|
fn[T] SpannedTemplate::unspan_template(
  self : SpannedTemplate[T],
) -> Template[T] {
  Template::new(self.strings.map(s => s.unspan), self.args.map(a => a.unspan))
}

// ---------------------------------------------------------------------------
// Documentation and definition metadata
// ---------------------------------------------------------------------------

///|
/// Does this info carry any documentation or modifier?
fn Info::is_non_empty(self : Info) -> Bool {
  match self.doc {
    Some(_) => true
    None => self.is_private || self.is_extern
  }
}

///|
/// Collects consecutive `///` doc comment lines.
fn Parser::maybe_documentation(self : Parser) -> String? raise EffektError {
  let mut found = false
  let docs : Array[String] = []
  let mut go = true
  while go {
    match self.peek_kind() {
      TDocComment(message) => {
        found = true
        let _ = self.next()
        docs.push(message)
      }
      _ => go = false
    }
  }
  if !found {
    None
  } else {
    Some(join_strings(docs, "\\n"))
  }
}

///|
/// Parses `/// doc`, `private`, `extern` before a definition.
fn Parser::info(self : Parser) -> Info raise EffektError {
  self.nonterminal(() => {
    let doc = self.maybe_documentation()
    let is_private = self.when(KPrivate, () => true, () => false)
    let is_extern = self.when(KExtern, () => true, () => false)
    { doc, is_private, is_extern, }
  })
}

///|
fn Parser::assert_extern(self : Parser, info : Info) -> Unit {
  if !info.is_extern {
    self.soft_fail(
      "Extern definitions require `extern` modifier",
      self.position,
      self.position,
    )
  }
}

///|
/// Definitions introduced by `val`, `def`, ... must not carry `extern` or
/// `private` modifiers.
fn Parser::only_doc(self : Parser, info : Info) -> Info {
  if info.is_extern {
    self.soft_fail(
      "Modifier `extern` is not allowed",
      self.position,
      self.position,
    )
  }
  if info.is_private {
    self.soft_fail(
      "Modifier `private` is not allowed",
      self.position,
      self.position,
    )
  }
  info
}

///|
fn Parser::default_capture(_self : Parser, span : Span) -> CaptureSetTree {
  { span, captures: [IdRef::qualified(["effekt"], "io", span)], }
}

// ---------------------------------------------------------------------------
// Modules
// ---------------------------------------------------------------------------

///|
/// The module path derived from the file name: the base name without directory
/// and extension.
fn Parser::default_module_path(self : Parser) -> String {
  let name = self.source.name
  let mut start = 0
  for i = 0; i < name.length(); i = i + 1 {
    if name[i] == '/' || name[i] == '\\' {
      start = i + 1
    }
  }
  let base = name[start:name.length()].to_owned()
  let mut end = base.length()
  let mut found = false
  for i = 0; i < base.length(); i = i + 1 {
    if !found && base[i] == '.' {
      end = i
      found = true
    }
  }
  base[0:end].to_owned()
}

///|
fn Parser::shebang(self : Parser) -> Unit raise EffektError {
  let mut go = true
  while go {
    match self.peek_kind() {
      TShebang(_) => {
        let kind = self.peek_kind()
        self.consume(kind)
      }
      _ => go = false
    }
  }
}

///|
/// Main entry point.
fn Parser::program(self : Parser) -> ModuleDecl raise EffektError {
  self.nonterminal(() => {
    // skip spaces at the start
    self.spaces()
    self.shebang()
    self.spaces()
    // potential documentation for the file / module
    self.documented(info => {
      let mut name = self.default_module_path()
      let mut module_info = Info::empty()
      let mut unused_info : Info? = None
      let kind = self.peek_kind()
      if kind == KModule {
        self.consume(KModule)
        name = self.module_name()
        module_info = info
      } else if kind == KImport && info.is_non_empty() {
        self.soft_fail(
          "Imports cannot be documented",
          self.position,
          self.position,
        )
        name = self.default_module_path()
        module_info = Info::empty()
      } else {
        name = self.default_module_path()
        module_info = Info::empty()
        unused_info = Some(info)
      }
      let imports = self.many_while_kind(() => self.include_decl(), KImport)
      let definitions = match unused_info {
        Some(i) =>
          if i.is_non_empty() {
            self.toplevel_defs_with(i)
          } else {
            self.toplevel_defs()
          }
        None => self.toplevel_defs()
      }
      if !self.peek(TEOF) {
        // NOTE: This means we expected EOF, but there's still some _stuff_ left over.
        let _ = self.soft_fail_with("Expected top-level definition", () => {
          self.many_until_kind(() => self.skip(), TEOF)
        })
      }
      let doc = self.only_doc(module_info).doc
      let span = self.span()
      {
        uid: fresh_uid(),
        span,
        path: name,
        includes: imports,
        defs: definitions,
        doc,
      }
    })
  })
}

///|
fn Parser::include_decl(self : Parser) -> Include raise EffektError {
  self.nonterminal(() => {
    self.consume(KImport)
    let path = self.module_name()
    { path, span: self.span(), }
  })
}

///|
fn Parser::module_name(self : Parser) -> String raise EffektError {
  self.labelled("module name", () => {
    let ids = self.some_sep(() => self.ident(), TSlash)
    join_strings(ids.items, "/")
  })
}

///|
fn Parser::is_toplevel(self : Parser) -> Bool raise EffektError {
  match self.peek_kind() {
    KVal
    | KDef
    | KType
    | KEffect
    | KNamespace
    | KInterface
    | KRecord
    | KVar
    | KInclude
    | KExtern => true
    _ => false
  }
}

///|
/// Only aliases for toplevel defs as of upstream #1251.
fn Parser::is_definition(self : Parser) -> Bool raise EffektError {
  self.is_toplevel()
}

///|
fn Parser::definition(self : Parser) -> Def raise EffektError {
  self.toplevel()
}

///|
fn Parser::definitions(self : Parser) -> Array[Def] raise EffektError {
  self.toplevel_defs()
}

// ---------------------------------------------------------------------------
// Top level definitions
// ---------------------------------------------------------------------------

///|
fn Parser::toplevel(self : Parser) -> Def raise EffektError {
  self.documented(doc => self.toplevel_def(doc))
}

///|
fn Parser::toplevel_def(self : Parser, info : Info) -> Def raise EffektError {
  if info.is_extern {
    return self.extern_def_with(info)
  }
  let kind = self.peek_kind()
  match kind {
    KVal => self.val_def(info)
    KDef => self.def_def(info)
    KInterface => self.interface_def(info, KInterface)
    KType => self.type_or_alias_def(info)
    KRecord => self.record_def(info)
    KEffect => self.effect_or_operation_def(info)
    KNamespace => self.namespace_def(info)
    KVar => self.var_def(info)
    _ => self.fail("Expected a definition")
  }
}

///|
fn Parser::toplevel_defs(self : Parser) -> Array[Def] raise EffektError {
  self.documented(info => self.toplevel_defs_with(info))
}

///|
fn Parser::toplevel_defs_with(
  self : Parser,
  info : Info,
) -> Array[Def] raise EffektError {
  self.nonterminal(() => {
    if self.peek(KNamespace) {
      self.consume(KNamespace)
      let id = self.id_def()
      if self.peek(TLBrace) {
        let defs = self.braces(() => self.toplevel_defs())
        let rest = self.toplevel_defs()
        let span = self.span()
        let result : Array[Def] = [mk_def(span, info, NamespaceDef(id, defs))]
        result.append(rest)
        result
      } else {
        let defs = self.toplevel_defs()
        let span = self.span()
        [mk_def(span, info, NamespaceDef(id, defs))]
      }
    } else if info.is_extern || self.is_toplevel() {
      let def = self.nonterminal(() => self.toplevel_def(info))
      let rest = self.toplevel_defs()
      let result : Array[Def] = [def]
      result.append(rest)
      result
    } else {
      []
    }
  })
}

///|
fn Parser::val_def(self : Parser, info : Info) -> Def raise EffektError {
  self.consume(KVal)
  let id = self.id_def()
  let tpe = self.maybe_value_type_annotation()
  self.consume(TAssign)
  let body = self.stmt()
  let doc_info = self.only_doc(info)
  mk_def(self.span(), doc_info, ValDef(id, tpe, body))
}

///|
/// In statement position, val-definitions can also be destructing:
///   i.e. val (l, r) = point(); ...
fn Parser::val_stmt(self : Parser, in_braces : Bool) -> Stmt raise EffektError {
  self.documented(info => {
    let start_pos = self.peek_token().start
    // Make sure there's either a `:` or `=` next, otherwise goto `matchLhs`
    let simple = self.backtrack(true, () => {
      self.consume(KVal)
      let id = self.id_def()
      let can_cut = self.peek(TColon) || self.peek(TAssign)
      if !can_cut {
        self.fail("Expected a `:` or a `=`")
      }
      id
    })
    match simple.value {
      Some(id) => {
        let tpe = self.maybe_value_type_annotation()
        self.consume(TAssign)
        let binding = self.stmt()
        let end_pos = self.pos()
        let def = mk_def(
          Span::new(self.source, start_pos, end_pos),
          self.only_doc(info),
          ValDef(id, tpe, binding),
        )
        self.semi()
        let rest = self.stmts(in_braces)
        mk_stmt(self.span(), StmtKind::DefStmt(def, rest))
      }
      None => {
        self.consume(KVal)
        let pattern = self.match_pattern()
        let guards = self.many_while_kind(
          () => {
            self.consume(KAnd)
            self.match_guard()
          },
          KAnd,
        )
        self.consume(TAssign)
        match pattern.kind {
          AnyPattern(id) if guards.length() == 0 => {
            let binding = self.stmt()
            let end_pos = self.pos()
            let def = mk_def(
              Span::new(self.source, start_pos, end_pos),
              self.only_doc(info),
              ValDef(id, None, binding),
            )
            self.semi()
            let rest = self.stmts(in_braces)
            mk_stmt(self.span(), StmtKind::DefStmt(def, rest))
          }
          _ => {
            // matches do not support doc comments, so we ignore `info`
            let scrutinee = self.expr()
            let default : Stmt? = self.when(KElse, () => Some(self.stmt()), () => {
              None
            })
            let end_pos = self.pos()
            self.semi()
            let body = self.stmts(in_braces)
            let clause : MatchClause = {
              uid: fresh_uid(),
              span: Span::new(
                self.source,
                pattern.span.start,
                scrutinee.span.end,
              ),
              pattern,
              guards,
              body,
            }
            let matching = mk_term(
              Span::new(self.source, start_pos, end_pos),
              Match([scrutinee], [clause], default),
            )
            mk_stmt(self.span().synthesized(), StmtKind::Return(matching))
          }
        }
      }
    }
  })
}

///|
fn Parser::var_def(self : Parser, info : Info) -> Def raise EffektError {
  self.consume(KVar)
  let id = self.id_def()
  let tpe = self.maybe_value_type_annotation()
  let reg : IdRef? = self.when(in_kind(), () => Some(self.id_ref()), () => None)
  self.consume(TAssign)
  let body = self.stmt()
  let doc_info = self.only_doc(info)
  match reg {
    Some(r) => mk_def(self.span(), doc_info, RegDef(id, tpe, r, body))
    None => mk_def(self.span(), doc_info, VarDef(id, tpe, body))
  }
}

///|
fn Parser::def_def(self : Parser, info : Info) -> Def raise EffektError {
  self.consume(KDef)
  let id = self.id_def()
  let is_block_def = self.peek(TColon) ||
    self.peek(TAssign) ||
    self.peek(at_kind())
  if is_block_def {
    // (: <VALUETYPE>)? `=` <EXPR>
    let captures = self.maybe_capture_set().value
    let tpe = self.maybe_block_type_annotation()
    self.consume(TAssign)
    let body = self.expr()
    mk_def(self.span(), info, DefDef(id, captures, tpe, body))
  } else {
    // [...](<PARAM>...) {...} `=` <STMT>
    let (tps, vps, bps) = self.params()
    let captures = self.maybe_capture_set().value
    let ret = self.maybe_return_annotation()
    self.consume(TAssign)
    let body = self.stmts(false)
    mk_def(self.span(), info, FunDef(id, tps, vps, bps, captures, ret, body))
  }
}

///|
/// Right now: data type definitions (should be renamed to `data`) and type
/// aliases.
fn Parser::type_or_alias_def(
  self : Parser,
  info : Info,
) -> Def raise EffektError {
  self.consume(KType)
  let id = self.id_def()
  let tps = self.maybe_type_params()
  if self.peek(TAssign) {
    self.consume(TAssign)
    let tpe = self.value_type()
    mk_def(self.span(), info, TypeDef(id, tps.items, tpe))
  } else {
    let constructors = self.braces(() => {
      self.many_until_kind(
        () => {
          let ctor = self.ctor()
          self.semi()
          ctor
        },
        TRBrace,
      )
    })
    mk_def(self.span(), info, DataDef(id, tps.items, constructors))
  }
}

///|
fn Parser::record_def(self : Parser, info : Info) -> Def raise EffektError {
  self.consume(KRecord)
  let id = self.id_def()
  let tps = self.maybe_type_params()
  let params = self.value_params()
  mk_def(self.span(), info, RecordDef(id, tps.items, params.items))
}

///|
fn Parser::ctor(self : Parser) -> Constructor raise EffektError {
  self.labelled("constructor", () => {
    self.documented(info => {
      let id = self.id_def()
      let tps = self.maybe_type_params()
      let params = self.value_params()
      let doc = self.only_doc(info).doc
      let span = self.span()
      {
        uid: fresh_uid(),
        span,
        id,
        tparams: tps.items,
        params: params.items,
        doc,
      }
    })
  })
}

///|
/// On the top-level both
///    effect Foo = {}
/// and
///    effect Foo(): Int
/// are allowed. We simply backtrack, since effect definitions shouldn't be
/// very long and cannot be nested.
fn Parser::effect_or_operation_def(
  self : Parser,
  info : Info,
) -> Def raise EffektError {
  // We used to use `effect Foo { def a(); def b(); ... }` for multi-operation
  // interfaces, but now we use `interface Foo { ... }` instead. If we can't
  // parse `effectDef` or `operationDef`, we should try parsing an interface
  // with the wrong keyword and report an error to the user if the malformed
  // interface would be valid.
  let first = self.backtrack(true, () => self.effect_def(info))
  let second = first.or_else(() => {
    self.backtrack(false, () => {
      self.soft_fail_with(
        "Unexpected 'effect', did you mean to declare an interface of multiple operations using the 'interface' keyword?",
        () => self.interface_def(info, KEffect),
      )
    })
  })
  // NOTE: the default must be lazy, `operation_def` consumes tokens.
  second.get_or_else_lazy(() => self.operation_def(info))
}

///|
fn Parser::effect_def(self : Parser, info : Info) -> Def raise EffektError {
  // effect <NAME> = <EFFECTS>
  self.consume(KEffect)
  let id = self.id_def()
  let tps = self.maybe_type_params()
  self.consume(TAssign)
  let effs = self.effects()
  mk_def(self.span(), info, EffectDef(id, tps.items, effs))
}

///|
/// effect <NAME>[...](...): ...
fn Parser::operation_def(self : Parser, info : Info) -> Def raise EffektError {
  self.consume(KEffect)
  let op = self.operation(info)
  let id = IdDef::new(op.id.name, op.id.span)
  let single : Operation = { ..op, tparams: [], }
  mk_def(self.span(), info, InterfaceDef(id, op.tparams, [single]))
}

///|
fn Parser::operation(self : Parser, info : Info) -> Operation raise EffektError {
  self.nonterminal(() => {
    let id = self.id_def()
    let (tps, vps, bps) = self.params()
    let ret = self.return_annotation()
    let doc = self.only_doc(info).doc
    let span = self.span()
    {
      uid: fresh_uid(),
      span,
      id,
      tparams: tps,
      vparams: vps,
      bparams: bps,
      ret,
      doc,
    }
  })
}

///|
fn Parser::interface_def(
  self : Parser,
  info : Info,
  keyword : TokenKind,
) -> Def raise EffektError {
  self.consume(keyword)
  let id = self.id_def()
  let tps = self.maybe_type_params()
  self.consume(TLBrace)
  let ops = self.many_until_kind(
    () => {
      self.documented(op_info => {
        self.labelled("} or another operation declaration", () => {
          self.consume(KDef)
          self.operation(op_info)
        })
      })
    },
    TRBrace,
  )
  self.consume(TRBrace)
  mk_def(self.span(), info, InterfaceDef(id, tps.items, ops))
}

///|
fn Parser::namespace_def(self : Parser, info : Info) -> Def raise EffektError {
  self.consume(KNamespace)
  let id = self.id_def()
  if self.peek(TLBrace) {
    // namespace foo { <DEFINITION>* }
    let defs = self.braces(() => self.definitions())
    let doc_info = self.only_doc(info)
    mk_def(self.span(), doc_info, NamespaceDef(id, defs))
  } else {
    // namespace foo
    // <DEFINITION>*
    self.semi()
    let defs = self.definitions()
    let doc_info = self.only_doc(info)
    mk_def(self.span(), doc_info, NamespaceDef(id, defs))
  }
}

// ---------------------------------------------------------------------------
// Extern definitions
// ---------------------------------------------------------------------------

///|
fn Parser::extern_def_with(self : Parser, info : Info) -> Def raise EffektError {
  self.assert_extern(info)
  let kind = self.peek_kind()
  match kind {
    KType => self.extern_type(info)
    KInterface => self.extern_interface(info)
    KResource => self.extern_resource(info)
    KInclude => self.extern_include(info)
    KDef => self.extern_fun(info)
    // extern """..."""
    // extern js """..."""
    _ => self.extern_string(info)
  }
}

///|
fn Parser::extern_type(self : Parser, info : Info) -> Def raise EffektError {
  self.consume(KType)
  let id = self.id_def()
  let tps = self.maybe_type_params()
  let bodies = self.maybe_extern_bodies(
    () => self.fail("extern type's do not support splices"),
    () => self.fail("extern type`s do not support Effekt right hand sides."),
  )
  mk_def(self.span(), info, ExternType(id, tps.items, bodies.items))
}

///|
fn Parser::extern_interface(
  self : Parser,
  info : Info,
) -> Def raise EffektError {
  self.consume(KInterface)
  let id = self.id_def()
  let tps = self.maybe_type_params()
  let bodies = self.maybe_extern_bodies(
    () => self.fail("extern type's do not support splices"),
    () => self.fail("extern type`s do not support Effekt right hand sides."),
  )
  mk_def(self.span(), info, ExternInterface(id, tps.items, bodies.items))
}

///|
fn Parser::extern_resource(self : Parser, info : Info) -> Def raise EffektError {
  self.consume(KResource)
  let id = self.id_def()
  let tpe = self.block_type_annotation()
  mk_def(self.span(), info, ExternResource(id, tpe))
}

///|
fn Parser::extern_include(self : Parser, info : Info) -> Def raise EffektError {
  self.consume(KInclude)
  let ff = self.maybe_feature_flag()
  let path = self.path_lit()
  mk_def(self.span(), info, ExternInclude(ff, path, None))
}

///|
/// A "virtual source" extern: `extern js """ ... """`.
///
/// Upstream parses a *single* string literal here (`expect("string literal")`),
/// which means that an interpolated string like `extern js "log(${x})"` would
/// leave the splice tokens unparsed. We instead consume the whole template, so
/// that such declarations parse; the literal fragments are concatenated into
/// the extern's contents.
fn Parser::extern_string(self : Parser, info : Info) -> Def raise EffektError {
  let ff = self.maybe_feature_flag()
  let template = self.template(() => self.expr())
  let contents = join_strings(template.strings.map(s => s.unspan), "")
  if template.args.length() > 0 {
    self.warn(
      "Splices in an extern string are not supported; use `extern def` with feature-flagged bodies instead",
      self.position,
      self.position,
    )
  }
  mk_def(self.span(), info, ExternInclude(ff, "", Some(contents)))
}

///|
fn Parser::extern_fun(self : Parser, info : Info) -> Def raise EffektError {
  self.consume(KDef)
  let id = self.id_def()
  let (tps, vps, bps) = self.params()
  let captures = self.maybe_capture_set()
  let ret = self.return_annotation()
  let bodies = self.maybe_extern_bodies(() => self.expr(), () => {
    self.stmts(true)
  })
  let captures = match captures.value {
    Some(c) => c
    None => self.default_capture(captures.span.synthesized())
  }
  mk_def(
    self.span(),
    info,
    ExternDef(id, tps, vps, bps, captures, ret, bodies.items),
  )
}

///|
/// An extern body is either a string template (optionally with a feature flag
/// prefix) or an Effekt implementation in braces.
fn Parser::extern_body(
  self : Parser,
  splice : () -> Term raise EffektError,
  eff : () -> Stmt raise EffektError,
) -> ExternBody raise EffektError {
  self.nonterminal(() => {
    match self.peek_kind() {
      TIdent(_) =>
        self.labelled("extern body (string or block)", () => {
          if self.peek_at_kind(1, TLBrace) {
            let flag = self.feature_flag()
            self.consume(TLBrace)
            let body = eff()
            self.consume(TRBrace)
            let _span = self.span()
            EffektExternBody(flag, body)
          } else {
            self.string_extern_body(splice)
          }
        })
      _ => self.string_extern_body(splice)
    }
  })
}

///|
fn Parser::string_extern_body(
  self : Parser,
  splice : () -> Term raise EffektError,
) -> ExternBody raise EffektError {
  let flag = self.maybe_feature_flag()
  let template = self.template(splice).unspan_template()
  let _span = self.span()
  StringExternBody(flag, template)
}

///|
fn Parser::maybe_extern_bodies(
  self : Parser,
  splice : () -> Term raise EffektError,
  eff : () -> Stmt raise EffektError,
) -> Many[ExternBody] raise EffektError {
  self.nonterminal(() => {
    if self.peek(TAssign) {
      self.consume(TAssign)
      let bodies = self.many_while(() => self.extern_body(splice, eff), () => {
        self.is_extern_body_start()
      })
      Many::new(bodies, self.span())
    } else {
      Many::empty(self.span())
    }
  })
}

///|
fn Parser::is_extern_body_start(self : Parser) -> Bool raise EffektError {
  match self.peek_kind() {
    TStr(_, _) | TIdent(_) | TLBrace => true
    _ => false
  }
}

///|
/// Templates containing unquotes `${...}`.
fn Parser::template(
  self : Parser,
  of : () -> Term raise EffektError,
) -> SpannedTemplate[Term] raise EffektError {
  self.nonterminal(() => {
    let first = self.spanned(() => self.string_lit())
    let args : Array[Spanned[Term]] = []
    let strings : Array[Spanned[String]] = []
    while self.peek(TSpliceStart) {
      self.consume(TSpliceStart)
      args.push(self.spanned(of))
      self.consume(TSpliceEnd)
      strings.push(self.spanned(() => self.string_lit()))
    }
    let all_strings : Array[Spanned[String]] = [first]
    all_strings.append(strings)
    { strings: all_strings, args, }
  })
}

///|
/// Parses a feature flag, i.e. `js`, `jsNode`, `default`, ...
fn Parser::feature_flag(self : Parser) -> FeatureFlag raise EffektError {
  let kind = self.peek_kind()
  match kind {
    TIdent(name) => {
      let _ = self.next()
      if name == "default" {
        Default
      } else {
        NamedFeatureFlag(name)
      }
    }
    _ => self.fail_expected("feature flag identifier", kind)
  }
}

///|
fn Parser::maybe_feature_flag(self : Parser) -> FeatureFlag raise EffektError {
  self.nonterminal(() => {
    let flag = self.backtrack(true, () => self.feature_flag())
    flag.get_or_else(Default)
  })
}

///|
fn Parser::path_lit(self : Parser) -> String raise EffektError {
  self.nonterminal(() => {
    let kind = self.peek_kind()
    match kind {
      TStr(s, false) => {
        let _ = self.next()
        s
      }
      _ => self.fail_expected("path as string literal", kind)
    }
  })
}

///|
/// Parses a string literal (already unescaped by the lexer).
fn Parser::string_lit(self : Parser) -> String raise EffektError {
  self.nonterminal(() => {
    let kind = self.peek_kind()
    match kind {
      TStr(s, _) => {
        let _ = self.next()
        s
      }
      _ => self.fail_expected("string literal", kind)
    }
  })
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
/// Tokens that delimit a statement.
fn Parser::return_position(self : Parser) -> Bool raise EffektError {
  self.peek(TRBrace) ||
  self.peek(TSpliceEnd) ||
  self.peek(KCase) ||
  self.peek(THoleEnd) ||
  self.peek(TEOF)
}

///|
fn Parser::is_semi(self : Parser) -> Bool raise EffektError {
  let kind = self.peek_kind()
  if kind == TSemi {
    true
  } else if self.return_position() {
    true
  } else {
    self.saw_newline_last()
  }
}

///|
fn Parser::semi(self : Parser) -> Unit raise EffektError {
  let kind = self.peek_kind()
  if kind == TSemi {
    self.consume(TSemi)
  } else if self.return_position() {
    ()
  } else if self.saw_newline_last() {
    ()
  } else {
    self.fail("Expected terminator: `;` or a newline")
  }
}

///|
fn Parser::maybe_semi(self : Parser) -> Unit raise EffektError {
  if self.is_semi() {
    self.semi()
  }
}

///|
fn Parser::stmts(self : Parser, in_braces : Bool) -> Stmt raise EffektError {
  self.labelled("statements", () => {
    self.nonterminal(() => {
      let kind = self.peek_kind()
      if kind == TLBrace {
        let inner = self.braces(() => self.stmts(true))
        mk_stmt(self.span(), StmtKind::BlockStmt(inner))
      } else if kind == KVal {
        self.val_stmt(in_braces)
      } else if kind == KVar {
        let def = self.var_def(Info::empty())
        self.semi()
        let rest = self.stmts(in_braces)
        mk_stmt(self.span(), StmtKind::DefStmt(def, rest))
      } else if self.is_definition() && in_braces {
        let def = self.definition()
        self.semi()
        let rest = self.stmts(in_braces)
        mk_stmt(self.span(), StmtKind::DefStmt(def, rest))
      } else if self.is_definition() {
        self.fail("Definitions are only allowed, when enclosed in braces.")
      } else if kind == KWith {
        self.with_stmt(in_braces)
      } else if kind == KReturn {
        // trailing semicolon only allowed when in braces
        self.consume(KReturn)
        let e = self.expr()
        if in_braces {
          self.maybe_semi()
        }
        mk_stmt(self.span(), StmtKind::Return(e))
      } else if (kind == TRBrace || kind == TSpliceEnd) && in_braces {
        // Unexpected end of <STMTS>: insert a synthetic `return ()` into the block
        let sp = self.span().empty_after()
        let unit = mk_term(sp, TermKind::Literal(LUnit, t_unit()))
        mk_stmt(sp, StmtKind::Return(unit))
      } else if !in_braces {
        // for now we do not allow multiple expressions in single-statement mode
        let e = self.expr()
        mk_stmt(self.span(), StmtKind::Return(e))
      } else {
        let e = self.expr()
        self.semi()
        if self.return_position() {
          mk_stmt(self.span(), StmtKind::Return(e))
        } else {
          let rest = self.stmts(in_braces)
          mk_stmt(self.span(), StmtKind::ExprStmt(e, rest))
        }
      }
    })
  })
}

///|
/// with val <PATTERN> (, <PATTERN>)* (and <GUARD>)* = <EXPR> (else <STMT>)?; <STMTS>
/// with def <BLOCKPARAM> = <EXPR>; <STMTS>
/// with <EXPR>; <STMTS>
fn Parser::with_stmt(self : Parser, in_braces : Bool) -> Stmt raise EffektError {
  self.consume(KWith)
  let kind = self.peek_kind()
  if kind == KVal {
    self.consume(KVal)
    let patterns = self.some_sep(() => self.match_pattern(), TComma)
    let guards = self.many_while_kind(
      () => {
        self.consume(KAnd)
        self.match_guard()
      },
      KAnd,
    )
    self.consume(TAssign)
    let call = self.expr()
    let fallback : Stmt? = self.when(KElse, () => Some(self.stmt()), () => None)
    self.semi()
    let body = self.stmts(in_braces)
    self.desugar_with_patterns(
      patterns,
      guards,
      call,
      fallback,
      body,
      self.span(),
    )
  } else if kind == KDef {
    self.consume(KDef)
    let params : Array[BlockParam] = if self.peek(TLBrace) {
      self.block_params_opt()
    } else {
      // TODO copy position
      [self.block_param_opt()]
    }
    self.consume(TAssign)
    let call = self.expr()
    self.semi()
    let body = self.stmts(in_braces)
    let block_lit = mk_term(
      body.span.synthesized(),
      TermKind::BlockLiteral([], [], params, body),
    )
    self.desugar_with(call, block_lit, self.span())
  } else {
    let call = self.expr()
    self.semi()
    let body = self.stmts(in_braces)
    let block_lit = mk_term(
      body.span.synthesized(),
      TermKind::BlockLiteral([], [], [], body),
    )
    self.desugar_with(call, block_lit, self.span())
  }
}

///|
/// Desugars `with val` with pattern(s), optional guards, and optional fallback.
fn Parser::desugar_with_patterns(
  self : Parser,
  patterns : Many[MatchPattern],
  guards : Array[MatchGuard],
  call : Term,
  fallback : Stmt?,
  body : Stmt,
  with_span : Span,
) -> Stmt {
  // Check if all patterns are simple variable bindings or ignored, with no
  // guards and no fallback.
  let all_simple_vars = guards.length() == 0 &&
    (match fallback {
      Some(_) => false
      None => true
    }) &&
    patterns.items.all(p => {
      match p.kind {
        AnyPattern(_) | IgnorePattern => true
        _ => false
      }
    })
  let block_lit : Term = if all_simple_vars {
    // Simple case: desugar to: call { (x, y, _, ...) => body }
    let vparams : Array[ValueParam] = patterns.items.map(p => {
      match p.kind {
        AnyPattern(id) => { id, tpe: None, is_implicit: false, }
        _ =>
          {
            id: IdDef::new("__ignored", p.span.synthesized()),
            tpe: None,
            is_implicit: false,
          }
      }
    })
    mk_term(
      body.span.synthesized(),
      TermKind::BlockLiteral([], vparams, [], body),
    )
  } else {
    // Complex case: desugar to: call { case pat1, pat2, ... and guard => body; ... }
    let pattern_list = patterns.items
    let names : Array[String] = []
    for i = 0; i < pattern_list.length(); i = i + 1 {
      names.push("__withArg\{i}")
    }
    let vparams : Array[ValueParam] = []
    for i = 0; i < pattern_list.length(); i = i + 1 {
      let sp = pattern_list[i].span
      vparams.push({
        id: IdDef::new(names[i], sp.synthesized()),
        tpe: None,
        is_implicit: false,
      })
    }
    let scrutinees : Array[Term] = []
    for i = 0; i < pattern_list.length(); i = i + 1 {
      let sp = pattern_list[i].span
      scrutinees.push(
        mk_term(
          sp.synthesized(),
          TermKind::Var(IdRef::new(names[i], sp.synthesized())),
        ),
      )
    }
    let pattern : MatchPattern = if pattern_list.length() == 1 {
      pattern_list[0]
    } else {
      mk_pattern(patterns.span, PatternKind::MultiPattern(pattern_list))
    }
    let clause : MatchClause = {
      uid: fresh_uid(),
      span: Span::with_origin(
        self.source,
        pattern.span.start,
        body.span.end,
        Synthesized,
      ),
      pattern,
      guards,
      body,
    }
    let match_expr = mk_term(
      with_span,
      TermKind::Match(scrutinees, [clause], None),
    )
    let match_body = mk_stmt(
      with_span.synthesized(),
      StmtKind::Return(match_expr),
    )
    mk_term(
      with_span.synthesized(),
      TermKind::BlockLiteral([], vparams, [], match_body),
    )
  }
  self.desugar_with(call, block_lit, with_span)
}

///|
fn Parser::desugar_with(
  _self : Parser,
  call : Term,
  block_lit : Term,
  with_span : Span,
) -> Stmt {
  match call.kind {
    MethodCall(receiver, id, tps, vargs, bargs) => {
      let new_bargs = bargs.copy()
      new_bargs.push(block_lit)
      let call = mk_term(
        call.span,
        TermKind::MethodCall(receiver, id, tps, vargs, new_bargs),
      )
      mk_stmt(with_span.synthesized(), StmtKind::Return(call))
    }
    Call(target, tps, vargs, bargs) => {
      let new_bargs = bargs.copy()
      new_bargs.push(block_lit)
      let call = mk_term(
        call.span,
        TermKind::Call(target, tps, vargs, new_bargs),
      )
      mk_stmt(with_span.synthesized(), StmtKind::Return(call))
    }
    Var(id) => {
      let call = mk_term(
        call.span,
        TermKind::Call(IdTarget(id), [], [], [block_lit]),
      )
      mk_stmt(with_span.synthesized(), StmtKind::Return(call))
    }
    Do(id, targs, vargs, bargs) => {
      let new_bargs = bargs.copy()
      new_bargs.push(block_lit)
      let call = mk_term(call.span, TermKind::Do(id, targs, vargs, new_bargs))
      mk_stmt(with_span.synthesized(), StmtKind::Return(call))
    }
    _ => {
      let call = mk_term(
        call.span.synthesized(),
        TermKind::Call(ExprTarget(call), [], [], [block_lit]),
      )
      mk_stmt(with_span.synthesized(), StmtKind::Return(call))
    }
  }
}

///|
fn Parser::stmt(self : Parser) -> Stmt raise EffektError {
  self.labelled("statement", () => {
    self.nonterminal(() => {
      if self.peek(TLBrace) {
        let inner = self.braces(() => self.stmts(true))
        mk_stmt(self.span(), StmtKind::BlockStmt(inner))
      } else {
        self.when(
          KReturn,
          () => {
            let e = self.expr()
            mk_stmt(self.span(), StmtKind::Return(e))
          },
          () => {
            let e = self.expr()
            mk_stmt(self.span(), StmtKind::Return(e))
          },
        )
      }
    })
  })
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

///|
fn Parser::expr(self : Parser) -> Term raise EffektError {
  self.labelled("expression", () => self.expr_outer(None))
}

///|
fn Parser::if_expr(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    self.consume(KIf)
    let guards = self.parens(() => self.match_guards())
    let thn = self.stmts(false)
    let els = self.when(KElse, () => self.stmts(false), () => {
      let sp = self.span().empty_after()
      let unit = mk_term(sp, TermKind::Literal(LUnit, t_unit()))
      mk_stmt(sp, StmtKind::Return(unit))
    })
    mk_term(self.span(), TermKind::If(guards.items, thn, els))
  })
}

///|
fn Parser::while_expr(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    self.consume(KWhile)
    let guards = self.parens(() => self.match_guards())
    let body = self.stmts(false)
    let els : Stmt? = self.when(KElse, () => Some(self.stmts(false)), () => None)
    mk_term(self.span(), TermKind::While(guards.items, body, els))
  })
}

///|
fn Parser::do_expr(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    self.consume(KDo)
    let id = self.id_ref()
    let (targs, vargs, bargs) = self.arguments()
    mk_term(self.span(), TermKind::Do(id, targs, vargs, bargs))
  })
}

///|
/// <tryExpr> ::= try { <stmts> } <handler>+
/// <handler> ::= with (<idDef> :)? <implementation>
/// <implementation> ::= <interfaceType> { <opClause>+ }
fn Parser::try_expr(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    self.consume(KTry)
    let body = self.stmt()
    let handlers = self.some_while_kind(() => self.handler(), KWith)
    mk_term(self.span(), TermKind::TryHandle(body, handlers.items))
  })
}

///|
fn Parser::region_expr(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    self.consume(KRegion)
    let id = self.id_def()
    let body = self.stmt()
    mk_term(self.span(), TermKind::Region(id, body))
  })
}

///|
fn Parser::box_expr(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    self.consume(KBox)
    let e = if self.peek(TLBrace) {
      self.function_arg()
    } else {
      let p = self.prim_expr()
      self.call_expr(p)
    }
    let captures = self.backtrack(true, () => {
      self.consume(at_kind())
      self.capture_set()
    })
    mk_term(self.span(), TermKind::Box(captures.value, e))
  })
}

///|
fn Parser::unbox_expr(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    self.consume(KUnbox)
    let e = self.expr()
    mk_term(self.span(), TermKind::Unbox(e))
  })
}

///|
fn Parser::new_expr(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    self.consume(KNew)
    let implementation = self.implementation()
    mk_term(self.span(), TermKind::New(implementation))
  })
}

///|
fn Parser::handler(self : Parser) -> Handler raise EffektError {
  self.nonterminal(() => {
    self.consume(KWith)
    let name = self.backtrack(true, () => {
      let id = self.id_def()
      self.consume(TColon)
      id
    })
    let implementation = self.implementation()
    let capability : BlockParam? = match name.value {
      Some(n) =>
        Some({ id: n, tpe: Some(implementation.interface), is_implicit: false, })
      None => None
    }
    { uid: fresh_uid(), span: self.span(), capability, implementation, }
  })
}

///|
/// This nonterminal uses limited backtracking: it parses the interface type
/// multiple times.
fn Parser::implementation(self : Parser) -> Implementation raise EffektError {
  self.nonterminal(() => {
    self.labelled("interface implementation (starting with its name)", () => {
      let empty = self.empty_implementation()
      let implementation = empty.or_else(() => self.interface_implementation())
      implementation.get_or_else_lazy(() => self.operation_implementation())
    })
  })
}

///|
/// Interface[...] {}
fn Parser::empty_implementation(
  self : Parser,
) -> Maybe[Implementation] raise EffektError {
  self.backtrack(true, () => {
    let tpe = self.block_type_ref()
    self.consume(TLBrace)
    self.consume(TRBrace)
    let span = self.span()
    { uid: fresh_uid(), span, interface: tpe, clauses: [], }
  })
}

///|
/// Interface[...] { def <NAME> = ... }
fn Parser::interface_implementation(
  self : Parser,
) -> Maybe[Implementation] raise EffektError {
  let tpe = self.backtrack(true, () => {
    let tpe = self.block_type_ref()
    self.consume(TLBrace)
    if !self.peek(KDef) {
      self.fail(
        "Expected at least one operation definition to implement this interface.",
      )
    }
    tpe
  })
  tpe.map(tpe => {
    let clauses = self.many_until_kind(
      () => self.labelled("operation clause", () => self.op_clause()),
      TRBrace,
    )
    self.consume(TRBrace)
    let span = self.span()
    { uid: fresh_uid(), span, interface: tpe, clauses, }
  })
}

///|
/// Interface[...] { () => ... }
/// Interface[...] { case ... => ... }
fn Parser::operation_implementation(
  self : Parser,
) -> Implementation raise EffektError {
  let id = self.id_ref()
  let tps = self.maybe_type_args()
  let resume_def = self.implicit_resume()
  let arg = self.function_arg()
  let (vparams, bparams, body) = match arg.kind {
    BlockLiteral(_, vps, bps, body) => (vps, bps, body)
    _ => self.fail("Expected a block literal")
  }
  let synthesized_id = IdRef::new(id.name, id.span.synthesized())
  let interface = mk_type(
    id.span.synthesized(),
    TypeKind::TypeRef(id, tps.items),
  )
  let operation : OpClause = {
    uid: fresh_uid(),
    span: Span::with_origin(
      self.source,
      id.span.start,
      body.span.end,
      Synthesized,
    ),
    id: synthesized_id,
    tparams: [],
    vparams,
    bparams,
    ret: None,
    body,
    resume: resume_def,
  }
  { uid: fresh_uid(), span: self.span(), interface, clauses: [operation], }
}

///|
fn Parser::op_clause(self : Parser) -> OpClause raise EffektError {
  self.nonterminal(() => {
    self.consume(KDef)
    let id = self.id_ref()
    let (tps, vps, bps) = self.params_opt()
    let ret = self.maybe_return_annotation()
    self.consume(TAssign)
    let body = self.stmt()
    if self.is_semi() {
      self.semi()
      if !self.peek(TRBrace) && !self.peek(KDef) && !self.peek(TEOF) {
        let _ = self.soft_fail_with(
          "Unexpected tokens after operation definition. Expected either a new operation definition or the end of the implementation.",
          () => {
            while !self.peek(TRBrace) && !self.peek(KDef) && !self.peek(TEOF) {
              let _ = self.next()
            }
          },
        )
      }
    }
    // TODO the implicitResume needs to have the correct position assigned
    let resume_def = self.implicit_resume()
    {
      uid: fresh_uid(),
      span: self.span(),
      id,
      tparams: tps,
      vparams: vps,
      bparams: bps,
      ret,
      body,
      resume: resume_def,
    }
  })
}

///|
fn Parser::implicit_resume(self : Parser) -> IdDef raise EffektError {
  self.nonterminal(() => IdDef::new("resume", self.span()))
}

// ---------------------------------------------------------------------------
// Patterns and guards
// ---------------------------------------------------------------------------

///|
fn Parser::match_clause(self : Parser) -> MatchClause raise EffektError {
  self.nonterminal(() => {
    self.consume(KCase)
    let patterns = self.some_sep(() => self.match_pattern(), TComma)
    let pattern : MatchPattern = if patterns.items.length() == 1 {
      patterns.items[0]
    } else {
      mk_pattern(patterns.span, PatternKind::MultiPattern(patterns.items))
    }
    let guards = self.many_while_kind(
      () => {
        self.consume(KAnd)
        self.match_guard()
      },
      KAnd,
    )
    self.consume(TArrow)
    let body = self.stmts(true)
    { uid: fresh_uid(), span: self.span(), pattern, guards, body, }
  })
}

///|
fn Parser::match_guards(self : Parser) -> Many[MatchGuard] raise EffektError {
  self.nonterminal(() => self.some_sep(() => self.match_guard(), KAnd))
}

///|
fn Parser::match_guard(self : Parser) -> MatchGuard raise EffektError {
  self.nonterminal(() => {
    let e = self.expr()
    let pattern : MatchPattern? = self.when(
      KIs,
      () => Some(self.match_pattern()),
      () => None,
    )
    match pattern {
      Some(p) => mk_guard(self.span(), GuardKind::PatternGuard(e, p))
      None => mk_guard(self.span(), GuardKind::BooleanGuard(e))
    }
  })
}

///|
fn Parser::match_pattern(self : Parser) -> MatchPattern raise EffektError {
  self.nonterminal(() => {
    let kind = self.peek_kind()
    if kind == underscore_kind() {
      self.skip()
      mk_pattern(self.span(), PatternKind::IgnorePattern)
    } else if self.is_variable() {
      let id = self.id_ref()
      if self.peek(TLParen) {
        let args = self.many(
          () => self.match_pattern(),
          TLParen,
          TComma,
          TRParen,
        )
        mk_pattern(self.span(), PatternKind::TagPattern(id, args.items))
      } else if id.path.length() == 0 {
        mk_pattern(
          id.span,
          PatternKind::AnyPattern(IdDef::new(id.name, id.span)),
        )
      } else {
        self.fail("Cannot use qualified names to bind a pattern variable")
      }
    } else if self.is_literal() {
      let (value, _) = self.literal_value()
      mk_pattern(
        self.span(),
        PatternKind::LiteralPattern(value, literal_type(value)),
      )
    } else if kind == TLParen {
      let patterns = self.some(
        () => self.match_pattern(),
        TLParen,
        TComma,
        TRParen,
        false,
      )
      if patterns.items.length() == 1 {
        self.fail("Pattern matching on tuples requires more than one element")
      } else {
        let sp = self.span().synthesized()
        let tuple_id = IdRef::qualified(
          ["effekt"],
          "Tuple\{patterns.items.length()}",
          sp,
        )
        mk_pattern(
          self.span(),
          PatternKind::TagPattern(tuple_id, patterns.items),
        )
      }
    } else {
      self.fail_expected("pattern", kind)
    }
  })
}

///|
fn Parser::match_expr(
  self : Parser,
  scrutinee : Term,
) -> Term raise EffektError {
  self.consume(KMatch)
  self.consume(TLBrace)
  let kind = self.peek_kind()
  match kind {
    KCase | TRBrace => ()
    _ => self.fail_expected("case", kind)
  }
  let clauses = self.many_while_kind(() => self.match_clause(), KCase)
  self.consume(TRBrace)
  let default : Stmt? = self.when(KElse, () => Some(self.stmt()), () => None)
  mk_term(self.span(), TermKind::Match([scrutinee], clauses, default))
}

///|
fn Parser::assign_expr(
  self : Parser,
  assignee : Term,
) -> Term raise EffektError {
  let id = match assignee.kind {
    Var(id) => id
    _ => self.fail("Not a variable")
  }
  let kind = self.peek_kind()
  if kind == TAssign {
    self.consume(TAssign)
    let value = self.expr()
    mk_term(self.span(), TermKind::Assign(id, value))
  } else if kind == TColonAssign {
    let op = self.next()
    let rhs = self.expr()
    self.binary_op(assignee, op, rhs)
  } else {
    self.fail("unreachable")
  }
}

///|
/// This is a compound production for
///  - member_id selection <EXPR>.<NAME>
///  - method calls <EXPR>.<NAME>(...)
///  - function calls <EXPR>(...)
///
/// This way expressions like `foo.bar.baz()(x).bam.boo()` are
/// parsed with the correct left-associativity.
fn Parser::call_expr(self : Parser, callee : Term) -> Term raise EffektError {
  let mut e = callee
  let mut go = true
  while go && (self.peek(TDot) || self.is_arguments()) {
    let kind = self.peek_kind()
    if kind == TDot {
      self.consume(TDot)
      let member_id = self.id_ref()
      if self.is_arguments() {
        let (targs, vargs, bargs) = self.arguments()
        e = mk_term(
          self.span(),
          TermKind::MethodCall(e, member_id, targs, vargs, bargs),
        )
      } else {
        e = mk_term(self.span(), TermKind::MethodCall(e, member_id, [], [], []))
      }
    } else if self.is_arguments() {
      let target : CallTarget = match e.kind {
        Var(id) => IdTarget(id)
        _ => ExprTarget(e)
      }
      let (targs, vargs, bargs) = self.arguments()
      e = mk_term(self.span(), TermKind::Call(target, targs, vargs, bargs))
    } else {
      go = false
    }
  }
  e
}

///|
fn Parser::is_infix_op(self : Parser, op : TokenKind) -> Bool {
  self.precedence.is_operator(op)
}

///|
fn Parser::expr_outer(
  self : Parser,
  prev_op : TokenKind?,
) -> Term raise EffektError {
  self.nonterminal(() => {
    let mut left = self.prim_expr()
    let mut go = true
    while go {
      let kind = self.peek_kind()
      if self.is_infix_op(kind) {
        let precedence = match prev_op {
          Some(op) => self.precedence.compare(op, kind)
          None => RightBindsTighter
        }
        match precedence {
          LeftBindsTighter => go = false
          RightBindsTighter => {
            self.check_binary_op_whitespace()
            let op_token = self.next()
            let right = self.expr_outer(Some(kind))
            left = self.binary_op(left, op_token, right)
          }
          Ambiguous =>
            self.fail(
              "Ambiguous infix operator precedence for the usage of \{kind.explain()}. Consider adding parentheses.",
            )
        }
      } else if kind == KMatch {
        left = self.match_expr(left)
      } else if (kind == TAssign || kind == TColonAssign) && is_var_term(left) {
        left = self.assign_expr(left)
      } else if self.peek(TDot) || self.is_arguments() {
        left = self.call_expr(left)
      } else {
        go = false
      }
    }
    left
  })
}

///|
fn is_var_term(t : Term) -> Bool {
  match t.kind {
    Var(_) => true
    _ => false
  }
}

///|
fn Parser::is_thunked_op(_self : Parser, op : TokenKind) -> Bool {
  match op {
    TBarBar | TAmpAmp => true
    _ => false
  }
}

///|
fn Parser::op_name(_self : Parser, op : TokenKind) -> String {
  match op {
    TBarBar => "infixBarBar"
    TAmpAmp => "infixAmpAmp"
    TEqEqEq => "infixEq"
    TNotEqEq => "infixNeq"
    TLt => "infixLt"
    TGt => "infixGt"
    TLtEq => "infixLte"
    TGtEq => "infixGte"
    TColonAssign => "infixColonEq"
    TPlus => "infixPlus"
    // `+=` (`-=`, `*=`, `/=`) has the same name as `+` (`-`, `*`, `/`) due to
    // the way it is manually desugared in `primExpr`
    TPlusEq => "infixPlus"
    TMinus => "infixMinus"
    TMinusEq => "infixMinus"
    TStar => "infixStar"
    TStarEq => "infixStar"
    TSlash => "infixSlash"
    TSlashEq => "infixSlash"
    TPlusPlus => "infixPlusPlus"
    TGtGt => "infixGtGt"
    TLtLt => "infixLtLt"
    TMinusMinus => "infixMinusMinus"
    TTilde => "infixTilde"
    TTildeGt => "infixTildeGt"
    TLtTilde => "infixLtTilde"
    TBar => "infixBar"
    TAmp => "infixAmp"
    TDotDot => "infixDotDot"
    TDotDotDot => "infixDotDotDot"
    THatHat => "infixHatHat"
    THat => "infixHat"
    _ => "<not an operator>"
  }
}

///|
fn Parser::binary_op(
  self : Parser,
  lhs : Term,
  op : Token,
  rhs : Term,
) -> Term raise EffektError {
  self.nonterminal(() => {
    let op_span = Span::new(self.source, op.start, op.end).synthesized()
    let target = IdTarget(IdRef::new(self.op_name(op.kind), op_span))
    let full_span = Span::with_origin(
      self.source,
      lhs.span.start,
      rhs.span.end,
      Synthesized,
    )
    if self.is_thunked_op(op.kind) {
      let lhs_block = mk_term(
        lhs.span.synthesized(),
        TermKind::BlockLiteral(
          [],
          [],
          [],
          mk_stmt(lhs.span, StmtKind::Return(lhs)),
        ),
      )
      let rhs_block = mk_term(
        rhs.span.synthesized(),
        TermKind::BlockLiteral(
          [],
          [],
          [],
          mk_stmt(rhs.span, StmtKind::Return(rhs)),
        ),
      )
      mk_term(full_span, TermKind::Call(target, [], [], [lhs_block, rhs_block]))
    } else {
      mk_term(
        full_span,
        TermKind::Call(
          target,
          [],
          [ValueArg::unnamed(lhs), ValueArg::unnamed(rhs)],
          [],
        ),
      )
    }
  })
}

///|
/// Checks that the current token is surrounded by whitespace. If not, soft fails.
fn Parser::check_binary_op_whitespace(self : Parser) -> Unit {
  let ws_before = self.position > 0 &&
    self.raw_token_at(self.position - 1).kind.is_space()
  let ws_after = self.position + 1 < self.tokens.length() &&
    self.raw_token_at(self.position + 1).kind.is_space()
  if !ws_before || !ws_after {
    self.warn(
      "Missing whitespace around binary operator",
      self.position,
      self.position,
    )
  }
}

///|
fn Parser::prim_expr(self : Parser) -> Term raise EffektError {
  let kind = self.peek_kind()
  match kind {
    KIf => self.if_expr()
    KWhile => self.while_expr()
    KTry => self.try_expr()
    KRegion => self.region_expr()
    KBox => self.box_expr()
    KUnbox => self.unbox_expr()
    KNew => self.new_expr()
    KDo => self.do_expr()
    _ =>
      if self.is_string() {
        self.template_string(Maybe::none(self.span()))
      } else if self.is_literal() {
        self.literal()
      } else if self.is_variable() {
        let lhs = self.variable()
        let lhs_id = match lhs.kind {
          Var(id) => id
          _ => self.fail("Expected a variable")
        }
        let next_kind = self.peek_kind()
        match next_kind {
          TStr(_, _) => self.template_string(Maybe::some(lhs_id, lhs_id.span))
          _ =>
            match next_kind {
              TPlusEq | TMinusEq | TStarEq | TSlashEq => {
                let op = self.next()
                let operand = self.expr()
                let op_span = Span::new(self.source, op.start, op.end).synthesized()
                let rhs = mk_term(
                  Span::with_origin(
                    self.source,
                    lhs.span.start,
                    operand.span.end,
                    Synthesized,
                  ),
                  TermKind::Call(
                    IdTarget(IdRef::new(self.op_name(op.kind), op_span)),
                    [],
                    [ValueArg::unnamed(lhs), ValueArg::unnamed(operand)],
                    [],
                  ),
                )
                mk_term(self.span(), TermKind::Assign(lhs_id, rhs))
              }
              _ => lhs
            }
        }
      } else if self.is_hole() {
        self.hole()
      } else if self.is_tuple_or_group() {
        self.tuple_or_group()
      } else if self.is_list_literal() {
        self.list_literal()
      } else if kind == TSpliceStart {
        self.nonterminal(() => {
          let start_position = self.position
          let _ = self.many_until_kind(() => self.skip(), TSpliceEnd)
          let end_position = self.position
          if self.peek(TSpliceEnd) {
            self.consume(TSpliceEnd)
          } else if self.peek(TRBrace) {
            self.consume(TRBrace)
          }
          let msg = "Unexpected splice: string interpolation ${ ... } is only allowed in strings!"
          self.soft_fail(msg, start_position, end_position)
          let sp = self.span().synthesized()
          mk_term(sp, TermKind::Literal(LString("<splice>"), t_string()))
        })
      } else {
        self.fail(
          "Expected variables, literals, tuples, lists, holes or group but got \{kind.explain()}",
        )
      }
  }
}

///|
fn Parser::is_list_literal(self : Parser) -> Bool raise EffektError {
  self.peek(TLBracket)
}

///|
fn Parser::nil_tree(self : Parser) -> Term {
  let sp = self.span()
  mk_term(sp, TermKind::Call(IdTarget(IdRef::new("Nil", sp)), [], [], []))
}

///|
fn cons_tree(el : Spanned[Term], rest : Term) -> Term {
  let sp = el.span.synthesized()
  mk_term(
    sp,
    TermKind::Call(
      IdTarget(IdRef::new("Cons", sp)),
      [],
      [ValueArg::unnamed(el.unspan), ValueArg::unnamed(rest)],
      [],
    ),
  )
}

///|
fn Parser::list_literal(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    let items = self.many(
      () => self.spanned(() => self.expr()),
      TLBracket,
      TComma,
      TRBracket,
    )
    let mut result = self.nil_tree()
    for i = items.items.length() - 1; i >= 0; i = i - 1 {
      result = cons_tree(items.items[i], result)
    }
    result
  })
}

///|
fn Parser::is_tuple_or_group(self : Parser) -> Bool raise EffektError {
  self.peek(TLParen)
}

///|
fn Parser::tuple_or_group(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    let es = self.some(() => self.expr(), TLParen, TComma, TRParen, true)
    if es.items.length() == 1 {
      es.items[0]
    } else {
      let sp = self.span().synthesized()
      let args = es.items.map(e => ValueArg::unnamed(e))
      let id = IdRef::qualified(["effekt"], "Tuple\{es.items.length()}", sp)
      mk_term(sp, TermKind::Call(IdTarget(id), [], args, []))
    }
  })
}

///|
fn Parser::is_hole(self : Parser) -> Bool raise EffektError {
  match self.peek_kind() {
    TDiamond | THoleStart | THoleStr(_) => true
    _ => false
  }
}

///|
fn Parser::hole(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    let kind = self.peek_kind()
    match kind {
      TDiamond => {
        self.consume(TDiamond)
        let sp = self.span().synthesized()
        mk_term(
          self.span(),
          TermKind::Hole(IdDef::new("hole", sp), Template::empty()),
        )
      }
      THoleStart => {
        self.consume(THoleStart)
        let body = self.stmts(true)
        self.consume(THoleEnd)
        let sp = self.span().synthesized()
        mk_term(
          self.span(),
          TermKind::Hole(IdDef::new("hole", sp), Template::new([], [body])),
        )
      }
      THoleStr(_) => {
        let body = self.hole_template()
        let sp = self.span().synthesized()
        mk_term(self.span(), TermKind::Hole(IdDef::new("hole", sp), body))
      }
      _ => self.fail_expected("hole", kind)
    }
  })
}

///|
fn Parser::hole_template(self : Parser) -> Template[Stmt] raise EffektError {
  self.nonterminal(() => {
    let first = self.hole_string()
    let bodies : Array[Stmt] = []
    let strings : Array[String] = []
    while self.peek(TSpliceStart) {
      self.consume(TSpliceStart)
      let body = self.stmts(true)
      self.consume(TSpliceEnd)
      bodies.push(body)
      strings.push(self.hole_string())
    }
    let all_strings : Array[String] = [first]
    all_strings.append(strings)
    Template::new(all_strings, bodies)
  })
}

///|
fn Parser::hole_string(self : Parser) -> String raise EffektError {
  self.nonterminal(() => {
    let kind = self.peek_kind()
    match kind {
      THoleStr(s) => {
        let _ = self.next()
        s
      }
      _ => self.fail_expected("natural language text", kind)
    }
  })
}

///|
fn Parser::is_literal(self : Parser) -> Bool raise EffektError {
  match self.peek_kind() {
    TInteger(_) | TFloat(_) | TStr(_, _) | TChr(_) | TByt(_) | KTrue | KFalse =>
      true
    _ => self.is_unit_literal()
  }
}

///|
fn Parser::is_string(self : Parser) -> Bool raise EffektError {
  match self.peek_kind() {
    TStr(_, _) => true
    _ => false
  }
}

///|
/// Will also recognize ( ) as unit if we do not emit space in the lexer...
fn Parser::is_unit_literal(self : Parser) -> Bool raise EffektError {
  self.peek(TLParen) && self.peek_at_kind(1, TRParen)
}

///|
fn Parser::literal_value(
  self : Parser,
) -> (LiteralValue, Span) raise EffektError {
  self.nonterminal(() => {
    let kind = self.peek_kind()
    match kind {
      TInteger(v) => {
        let _ = self.next()
        (LInt(v), self.span())
      }
      TFloat(v) => {
        let _ = self.next()
        (LDouble(v), self.span())
      }
      TStr(s, _) => {
        let _ = self.next()
        (LString(s), self.span())
      }
      TChr(c) => {
        let _ = self.next()
        (LChar(c), self.span())
      }
      TByt(b) => {
        let _ = self.next()
        (LByte(b), self.span())
      }
      KTrue => {
        let _ = self.next()
        (LBool(true), self.span())
      }
      KFalse => {
        let _ = self.next()
        (LBool(false), self.span())
      }
      _ =>
        if self.is_unit_literal() {
          let _ = self.next()
          let _ = self.next()
          (LUnit, self.span())
        } else {
          self.fail_expected("a literal", kind)
        }
    }
  })
}

///|
fn Parser::literal(self : Parser) -> Term raise EffektError {
  let (value, span) = self.literal_value()
  mk_term(span, TermKind::Literal(value, literal_type(value)))
}

///|
fn Parser::template_string(
  self : Parser,
  splicer : Maybe[IdRef],
) -> Term raise EffektError {
  self.nonterminal_at(splicer.span, () => {
    let start = self.position
    let template = self.template(() => self.expr())
    match (splicer.value, template.strings.length(), template.args.length()) {
      // We do not need to apply any transformation if there are no splices
      // _and_ no custom handler id is given
      (None, 1, 0) => {
        let s = template.strings[0]
        mk_term(s.span, TermKind::Literal(LString(s.unspan), t_string()))
      }
      _ => {
        // s"a${x}b${y}" ~> s { do write("a"); do splice(x); do write("b"); do splice(y); return () }
        let target = match splicer.value {
          Some(id) => id
          None => {
            let synth_span = splicer.span.synthesized()
            let end = self.position - 1
            self.warn(
              "String interpolation requires an explicit interpolator. For example: s\"...\"",
              start, end,
            )
            IdRef::new("s", synth_span)
          }
        }
        let do_lits : Array[Term] = template.strings.map(s => {
          let sp = s.span.synthesized()
          let arg = mk_term(
            s.span,
            TermKind::Literal(LString(s.unspan), t_string()),
          )
          mk_term(
            sp,
            TermKind::Do(
              IdRef::new("write", sp),
              [],
              [ValueArg::unnamed(arg)],
              [],
            ),
          )
        })
        let do_splices : Array[Term] = template.args.map(arg => {
          let sp = arg.span.synthesized()
          mk_term(
            sp,
            TermKind::Do(
              IdRef::new("splice", sp),
              [],
              [ValueArg::unnamed(arg.unspan)],
              [],
            ),
          )
        })
        let exprs = interleave(do_lits, do_splices)
        let unit_span = self.span().synthesized()
        let unit = mk_term(unit_span, TermKind::Literal(LUnit, t_unit()))
        let mut body = mk_stmt(unit_span, StmtKind::Return(unit))
        for i = exprs.length() - 1; i >= 0; i = i - 1 {
          let sp = exprs[i].span.synthesized()
          body = mk_stmt(sp, StmtKind::ExprStmt(exprs[i], body))
        }
        let blk_span = self.span().synthesized()
        let blk = mk_term(blk_span, TermKind::BlockLiteral([], [], [], body))
        mk_term(blk_span, TermKind::Call(IdTarget(target), [], [], [blk]))
      }
    }
  })
}

// ---------------------------------------------------------------------------
// Identifiers
// ---------------------------------------------------------------------------

///|
fn Parser::is_variable(self : Parser) -> Bool raise EffektError {
  self.is_ident()
}

///|
fn Parser::variable(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    let id = self.id_ref()
    mk_term(self.span(), TermKind::Var(id))
  })
}

///|
fn Parser::is_id_ref(self : Parser) -> Bool raise EffektError {
  self.is_ident()
}

///|
fn Parser::id_ref(self : Parser) -> IdRef raise EffektError {
  self.nonterminal(() => {
    let ids = self.some_sep(() => self.ident(), TPathSep)
    IdRef::qualified(
      array_init(ids.items),
      ids.items[ids.items.length() - 1],
      self.span(),
    )
  })
}

///|
fn Parser::id_def(self : Parser) -> IdDef raise EffektError {
  self.nonterminal(() => {
    let ids = self.some_sep(() => self.ident(), TPathSep)
    IdDef::qualified(
      array_init(ids.items),
      ids.items[ids.items.length() - 1],
      self.span(),
    )
  })
}

///|
fn Parser::is_ident(self : Parser) -> Bool raise EffektError {
  match self.peek_kind() {
    TIdent(_) => true
    _ => false
  }
}

///|
fn Parser::ident(self : Parser) -> String raise EffektError {
  self.nonterminal(() => {
    let kind = self.peek_kind()
    match kind {
      TIdent(id) => {
        let _ = self.next()
        id
      }
      _ => self.fail_expected("identifier", kind)
    }
  })
}

// ---------------------------------------------------------------------------
// Arguments
// ---------------------------------------------------------------------------

///|
/// Argument lists cannot follow a linebreak:
///   foo      ==    foo;
///   ()             ()
fn Parser::is_arguments(self : Parser) -> Bool raise EffektError {
  !self.saw_newline_last() &&
  (self.peek(TLParen) || self.peek(TLBracket) || self.peek(TLBrace))
}

///|
fn Parser::arguments(
  self : Parser,
) -> (Array[TypeTree], Array[ValueArg], Array[Term]) raise EffektError {
  if !self.is_arguments() {
    self.fail_expected(
      "at least one argument section (types, values, or blocks)",
      self.peek_kind(),
    )
  }
  let targs = self.maybe_type_args()
  let vargs = self.maybe_value_args()
  let bargs = self.maybe_block_args()
  (targs.items, vargs, bargs)
}

///|
fn Parser::maybe_type_args(self : Parser) -> Many[TypeTree] raise EffektError {
  self.nonterminal(() => {
    if self.peek(TLBracket) {
      self.type_args()
    } else {
      Many::empty(self.span())
    }
  })
}

///|
fn Parser::maybe_value_args(self : Parser) -> Array[ValueArg] raise EffektError {
  if self.peek(TLParen) {
    self.value_args()
  } else {
    []
  }
}

///|
fn Parser::maybe_block_args(self : Parser) -> Array[Term] raise EffektError {
  if self.peek(TLBrace) {
    self.block_args()
  } else {
    []
  }
}

///|
fn Parser::value_arg(self : Parser) -> ValueArg raise EffektError {
  if self.is_ident() && self.peek_at_kind(1, TAssign) {
    self.nonterminal(() => {
      let name = self.ident()
      self.consume(TAssign)
      let value = self.expr()
      ValueArg::named(name, value, self.span())
    })
  } else {
    ValueArg::unnamed(self.expr())
  }
}

///|
fn Parser::type_args(self : Parser) -> Many[TypeTree] raise EffektError {
  self.nonterminal(() => {
    self.some(() => self.value_type(), TLBracket, TComma, TRBracket, false)
  })
}

///|
fn Parser::value_args(self : Parser) -> Array[ValueArg] raise EffektError {
  self.nonterminal(() => {
    self.many(() => self.value_arg(), TLParen, TComma, TRParen).items
  })
}

///|
fn Parser::block_args(self : Parser) -> Array[Term] raise EffektError {
  self.nonterminal(() => {
    self.some_while_kind(() => self.block_arg(), TLBrace).items
  })
}

///|
/// Note: for this nonterminal, we need some backtracking.
fn Parser::block_arg(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    let simple = self.backtrack(true, () => {
      self.consume(TLBrace)
      let v = self.variable()
      self.consume(TRBrace)
      v
    })
    match simple.value {
      Some(v) => v
      None => self.function_arg()
    }
  })
}

///|
fn Parser::function_arg(self : Parser) -> Term raise EffektError {
  self.nonterminal(() => {
    self.consume(TLBrace)
    let result = {
      let kind = self.peek_kind()
      if kind == KCase {
        // { case ... => ... }
        self.nonterminal(() => {
          let clauses = self.some_while_kind(() => self.match_clause(), KCase)
          let arg_spans : Array[Span] = match clauses.items[0].pattern.kind {
            MultiPattern(ps) => ps.map(p => p.span)
            _ => [clauses.span]
          }
          // TODO fresh names should be generated for the scrutinee
          let names : Array[String] = []
          for i = 0; i < arg_spans.length(); i = i + 1 {
            names.push("__arg\{i}")
          }
          let vparams : Array[ValueParam] = []
          for i = 0; i < arg_spans.length(); i = i + 1 {
            vparams.push({
              id: IdDef::new(names[i], arg_spans[i].synthesized()),
              tpe: None,
              is_implicit: false,
            })
          }
          let scrutinees : Array[Term] = []
          for i = 0; i < arg_spans.length(); i = i + 1 {
            scrutinees.push(
              mk_term(
                arg_spans[i].synthesized(),
                TermKind::Var(IdRef::new(names[i], arg_spans[i].synthesized())),
              ),
            )
          }
          let sp = self.span()
          let match_term = mk_term(
            sp,
            TermKind::Match(scrutinees, clauses.items, None),
          )
          let body = mk_stmt(sp.synthesized(), StmtKind::Return(match_term))
          mk_term(sp, TermKind::BlockLiteral([], vparams, [], body))
        })
      } else {
        // { (x: Int) => ... }
        let lambda = self.backtrack(true, () => {
          let (tps, vps, bps) = self.lambda_params()
          self.consume(TArrow)
          (tps, vps, bps)
        })
        match lambda.value {
          Some((tps, vps, bps)) => {
            let body = self.stmts(true)
            mk_term(self.span(), TermKind::BlockLiteral(tps, vps, bps, body))
          }
          None => {
            // { <STMTS> }
            let body = self.stmts(true)
            mk_term(self.span(), TermKind::BlockLiteral([], [], [], body))
          }
        }
      }
    }
    self.consume(TRBrace)
    result
  })
}

// ---------------------------------------------------------------------------
// Types
//
// Type grammar by precedence:
//
// Type ::= Id ('[' Type ',' ... ']')?                                refType
//        | '(' Type ',' ... ')'                                      atomicType
//        | '(' Type ')'
//        | Type '=>' Type ('/' SetType)?                            functionType
//        | '(' Type ',' ... ')' ('{' Type '}')* '=>' Type ('/' SetType)?
//        | Type 'at' Id                                              boxedType
//        | Type 'at' '{' Id ',' ... '}'
//        | Type ('/' SetType)?
//
// SetType ::= Type | '{' Type ',' ... '}'
// ---------------------------------------------------------------------------

///|
fn Parser::effects(self : Parser) -> EffectsTree raise EffektError {
  self.labelled("effect set", () => {
    self.nonterminal(() => {
      if self.peek(TLBrace) {
        let effects = self.many(() => self.ref_type(), TLBrace, TComma, TRBrace)
        { span: effects.span, effs: effects.items, }
      } else {
        let eff = self.ref_type()
        { span: self.span(), effs: [eff], }
      }
    })
  })
}

///|
fn Parser::maybe_effects(self : Parser) -> EffectsTree raise EffektError {
  self.nonterminal(() => {
    self.when(TSlash, () => self.effects(), () => {
      EffectsTree::pure(self.span().synthesized())
    })
  })
}

///|
fn Parser::ref_type(self : Parser) -> TypeTree raise EffektError {
  self.nonterminal(() => {
    let id = self.id_ref()
    let targs = self.maybe_type_args()
    mk_type(self.span(), TypeKind::TypeRef(id, targs.items))
  })
}

///|
fn type_tuple(tps : Many[TypeTree]) -> TypeTree {
  let sp = tps.span.synthesized()
  let id = IdRef::qualified(["effekt"], "Tuple\{tps.items.length()}", sp)
  mk_type(sp, TypeKind::TypeRef(id, tps.items))
}

///|
/// Parse atomic types: tuples, parenthesized types, type references (highest
/// precedence).
fn Parser::atomic_type(self : Parser) -> TypeTree raise EffektError {
  self.nonterminal(() => {
    if self.peek(TLParen) {
      let tpes = self.some(
        () => self.boxed_type(),
        TLParen,
        TComma,
        TRParen,
        true,
      )
      if tpes.items.length() == 1 {
        tpes.items[0]
      } else {
        type_tuple(tpes)
      }
    } else {
      self.ref_type()
    }
  })
}

///|
/// Complex function type: [T]*(Int, String)*{Exc} => Int / {Effect}
fn Parser::function_type_complex(
  self : Parser,
) -> Maybe[TypeTree] raise EffektError {
  let parts = self.backtrack(true, () => {
    let tparams = self.maybe_type_params()
    let vparams = self.maybe_value_types()
    let bparams = self.maybe_block_type_params()
    self.consume(TArrow)
    (tparams, vparams, bparams)
  })
  parts.map(parts => {
    let (tparams, vparams, bparams) = parts
    let ret = self.labelled("return type", () => self.atomic_type())
    let effs = self.maybe_effects()
    mk_type(
      self.span(),
      TypeKind::FunctionType(
        tparams.items,
        vparams.items,
        bparams.items,
        ret,
        effs,
      ),
    )
  })
}

///|
/// Simple function type: Int => Int
fn Parser::function_type_simple(
  self : Parser,
) -> Maybe[TypeTree] raise EffektError {
  let tpe = self.backtrack(true, () => {
    let t = self.ref_type()
    self.consume(TArrow)
    t
  })
  tpe.map(t => {
    let ret = self.atomic_type()
    let effs = self.maybe_effects()
    mk_type(self.span(), TypeKind::FunctionType([], [t], [], ret, effs))
  })
}

///|
/// Parse function types (middle precedence).
fn Parser::function_type(self : Parser) -> TypeTree raise EffektError {
  self.nonterminal(() => {
    let simple = self.function_type_simple()
    let tpe = simple.or_else(() => self.function_type_complex())
    tpe.get_or_else_lazy(() => self.atomic_type())
  })
}

///|
/// Parse boxed types and effectfuls (lowest precedence).
/// "Top-level" parser for a generic type.
fn Parser::boxed_type(self : Parser) -> TypeTree raise EffektError {
  self.nonterminal(() => {
    // Parse the function type first
    let tpe = self.function_type()
    let boxed = self.when(
      at_kind(),
      () => {
        let captures = self.labelled("capture set", () => self.capture_set())
        mk_type(self.span(), TypeKind::BoxedType(tpe, captures))
      },
      () => tpe,
    )
    if self.peek(TSlash) {
      let effs = self.maybe_effects()
      mk_type(self.span(), TypeKind::Effectful(boxed, effs))
    } else {
      boxed
    }
  })
}

///|
/// NOTE: ValueType, BlockType are just aliases for Type.
fn Parser::block_type(self : Parser) -> TypeTree raise EffektError {
  self.labelled("block type", () => self.boxed_type())
}

///|
fn Parser::value_type(self : Parser) -> TypeTree raise EffektError {
  self.labelled("value type", () => self.boxed_type())
}

///|
/// Completely specialized for TypeRef: we only parse `refType` here.
fn Parser::block_type_ref(self : Parser) -> TypeTree raise EffektError {
  self.ref_type()
}

///|
/// Somewhat specialized: we parse a normal type, if it's not effectful, then
/// pretend the effect set is empty.
fn Parser::effectful(self : Parser) -> TypeTree raise EffektError {
  self.nonterminal(() => {
    self.labelled("return-type and effects", () => {
      let tpe = self.boxed_type()
      match tpe.kind {
        Effectful(_, _) => tpe
        _ => {
          let p = self.pos()
          let effs = EffectsTree::pure(
            Span::with_origin(self.source, p, p, Synthesized),
          )
          mk_type(self.span(), TypeKind::Effectful(tpe, effs))
        }
      }
    })
  })
}

///|
fn Parser::maybe_capture_set(
  self : Parser,
) -> Maybe[CaptureSetTree] raise EffektError {
  self.nonterminal(() => {
    self.when(
      at_kind(),
      () => {
        let captures = self.capture_set()
        Maybe::some(captures, self.span())
      },
      () => Maybe::none(self.span()),
    )
  })
}

///|
fn Parser::capture_set(self : Parser) -> CaptureSetTree raise EffektError {
  self.nonterminal(() => {
    let kind = self.peek_kind()
    if kind == TLBrace {
      let captures = self.many(() => self.id_ref(), TLBrace, TComma, TRBrace)
      { span: self.span(), captures: captures.items, }
    } else if self.is_id_ref() {
      let id = self.id_ref()
      { span: self.span(), captures: [id], }
    } else {
      self.fail_expected("Expected a capture set.", kind)
    }
  })
}

///|
fn Parser::maybe_value_type_annotation(
  self : Parser,
) -> TypeTree? raise EffektError {
  self.nonterminal(() => {
    if self.peek(TColon) {
      Some(self.value_type_annotation())
    } else {
      None
    }
  })
}

///|
fn Parser::maybe_block_type_annotation(
  self : Parser,
) -> TypeTree? raise EffektError {
  self.nonterminal(() => {
    if self.peek(TColon) {
      Some(self.block_type_annotation())
    } else {
      None
    }
  })
}

///|
fn Parser::maybe_return_annotation(
  self : Parser,
) -> TypeTree? raise EffektError {
  self.nonterminal(() => {
    self.when(TColon, () => Some(self.effectful()), () => None)
  })
}

///|
fn Parser::return_annotation(self : Parser) -> TypeTree raise EffektError {
  if self.peek(TColon) {
    self.consume(TColon)
    self.effectful()
  } else {
    self.fail_expected("return type annotation", self.peek_kind())
  }
}

///|
fn Parser::value_type_annotation(self : Parser) -> TypeTree raise EffektError {
  if self.peek(TColon) {
    self.consume(TColon)
    self.value_type()
  } else {
    self.fail_expected("a type annotation", self.peek_kind())
  }
}

///|
fn Parser::block_type_annotation(self : Parser) -> TypeTree raise EffektError {
  if self.peek(TColon) {
    self.consume(TColon)
    self.block_type()
  } else {
    self.fail_expected("a type annotation", self.peek_kind())
  }
}

// ---------------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------------

///|
fn Parser::maybe_type_params(self : Parser) -> Many[IdDef] raise EffektError {
  self.nonterminal(() => {
    if self.peek(TLBracket) {
      self.type_params()
    } else {
      Many::empty(self.span())
    }
  })
}

///|
fn Parser::type_params(self : Parser) -> Many[IdDef] raise EffektError {
  self.nonterminal(() => {
    self.some(() => self.id_def(), TLBracket, TComma, TRBracket, false)
  })
}

///|
fn Parser::maybe_block_type_params(
  self : Parser,
) -> Many[(IdDef?, TypeTree)] raise EffektError {
  self.nonterminal(() => {
    if self.peek(TLBrace) {
      self.block_type_params()
    } else {
      Many::empty(self.span())
    }
  })
}

///|
fn Parser::block_type_params(
  self : Parser,
) -> Many[(IdDef?, TypeTree)] raise EffektError {
  self.nonterminal(() => {
    self.some_while_kind(() => self.block_type_param(), TLBrace)
  })
}

///|
fn Parser::block_type_param(
  self : Parser,
) -> (IdDef?, TypeTree) raise EffektError {
  self.nonterminal(() => {
    self.consume(TLBrace)
    let name = self.backtrack(true, () => {
      let id = self.id_def()
      self.consume(TColon)
      id
    })
    let tpe = self.block_type()
    self.consume(TRBrace)
    (name.value, tpe)
  })
}

///|
fn Parser::lambda_params(
  self : Parser,
) -> (Array[IdDef], Array[ValueParam], Array[BlockParam]) raise EffektError {
  self.nonterminal(() => {
    if self.is_variable() {
      let id = self.id_def()
      ([], [{ id, tpe: None, is_implicit: false, }], [])
    } else {
      self.params_opt()
    }
  })
}

///|
fn Parser::params(
  self : Parser,
) -> (Array[IdDef], Array[ValueParam], Array[BlockParam]) raise EffektError {
  self.nonterminal(() => {
    let tps = self.maybe_type_params()
    let vps = self.maybe_value_params()
    let bps = self.maybe_block_params()
    (tps.items, vps.items, bps.items)
  })
}

///|
fn Parser::params_opt(
  self : Parser,
) -> (Array[IdDef], Array[ValueParam], Array[BlockParam]) raise EffektError {
  self.nonterminal(() => {
    let tps = self.maybe_type_params()
    let vps = self.maybe_value_params_opt()
    let bps = self.maybe_block_params_opt()
    (tps.items, vps, bps)
  })
}

///|
fn Parser::maybe_value_params_opt(
  self : Parser,
) -> Array[ValueParam] raise EffektError {
  self.nonterminal(() => {
    if self.peek(TLParen) {
      self.value_params_opt()
    } else {
      []
    }
  })
}

///|
fn Parser::value_params_opt(
  self : Parser,
) -> Array[ValueParam] raise EffektError {
  self.nonterminal(() => {
    self.many(() => self.value_param_opt(), TLParen, TComma, TRParen).items
  })
}

///|
fn Parser::maybe_value_params(
  self : Parser,
) -> Many[ValueParam] raise EffektError {
  self.nonterminal(() => {
    if self.peek(TLParen) {
      self.value_params()
    } else {
      Many::empty(self.span())
    }
  })
}

///|
fn Parser::value_params(self : Parser) -> Many[ValueParam] raise EffektError {
  self.nonterminal(() => {
    self.many(() => self.value_param(), TLParen, TComma, TRParen)
  })
}

///|
fn Parser::value_param(self : Parser) -> ValueParam raise EffektError {
  self.nonterminal(() => {
    let is_implicit = self.skip_if(TQuestion)
    let id = self.id_def()
    let tpe = self.value_type_annotation()
    { id, tpe: Some(tpe), is_implicit, }
  })
}

///|
fn Parser::value_param_opt(self : Parser) -> ValueParam raise EffektError {
  self.nonterminal(() => {
    let is_implicit = self.skip_if(TQuestion)
    let id = self.id_def()
    let tpe = self.maybe_value_type_annotation()
    { id, tpe, is_implicit, }
  })
}

///|
fn Parser::maybe_block_params(
  self : Parser,
) -> Many[BlockParam] raise EffektError {
  self.nonterminal(() => {
    let params = self.many_while_kind(
      () => {
        self.consume(TLBrace)
        let p = self.block_param()
        self.consume(TRBrace)
        p
      },
      TLBrace,
    )
    Many::new(params, self.span())
  })
}

///|
fn Parser::maybe_block_params_opt(
  self : Parser,
) -> Array[BlockParam] raise EffektError {
  self.nonterminal(() => {
    self.many_while_kind(
      () => {
        self.consume(TLBrace)
        let p = self.block_param_opt()
        self.consume(TRBrace)
        p
      },
      TLBrace,
    )
  })
}

///|
fn Parser::block_params_opt(
  self : Parser,
) -> Array[BlockParam] raise EffektError {
  self.nonterminal(() => {
    self.some_while_kind(
      () => {
        self.consume(TLBrace)
        let p = self.block_param_opt()
        self.consume(TRBrace)
        p
      },
      TLBrace,
    ).items
  })
}

///|
fn Parser::block_param(self : Parser) -> BlockParam raise EffektError {
  self.nonterminal(() => {
    let is_implicit = self.skip_if(TQuestion)
    let id = self.id_def()
    let tpe = self.block_type_annotation()
    { id, tpe: Some(tpe), is_implicit, }
  })
}

///|
fn Parser::block_param_opt(self : Parser) -> BlockParam raise EffektError {
  self.nonterminal(() => {
    let is_implicit = self.skip_if(TQuestion)
    let id = self.id_def()
    let tpe = self.when(TColon, () => Some(self.block_type()), () => None)
    { id, tpe, is_implicit, }
  })
}

///|
fn Parser::maybe_value_types(self : Parser) -> Many[TypeTree] raise EffektError {
  self.nonterminal(() => {
    if self.peek(TLParen) {
      self.value_types()
    } else {
      Many::empty(self.span())
    }
  })
}

///|
fn Parser::value_types(self : Parser) -> Many[TypeTree] raise EffektError {
  self.nonterminal(() => {
    self.many(() => self.value_type(), TLParen, TComma, TRParen)
  })
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

///|
fn Parser::parse_program(self : Parser) -> ModuleDecl? raise EffektError {
  try {
    let decl = self.program()
    self.report_recoverable_diagnostics()
    // Don't fret unless we had a recoverable error
    if self.diagnostics.all(d => d.kind != Error) {
      Some(decl)
    } else {
      None
    }
  } catch {
    Fatal(msg) => {
      // Don't forget soft fails!
      self.report_recoverable_diagnostics()
      let pos = self.fail_position
      self.report(msg, pos, pos, Error)
      None
    }
    Internal(m) => raise EffektError::Internal(m)
  }
}

///|
/// Parses a single expression (used by the REPL and by tests).
fn Parser::parse_term_entry(self : Parser) -> Term? raise EffektError {
  try {
    let term = self.nonterminal(() => {
      self.spaces()
      let t = self.expr()
      if self.peek(TEOF) {
        t
      } else {
        self.fail("Unexpected item")
      }
    })
    self.report_recoverable_diagnostics()
    if self.diagnostics.all(d => d.kind != Error) {
      Some(term)
    } else {
      None
    }
  } catch {
    Fatal(msg) => {
      self.report_recoverable_diagnostics()
      let pos = self.fail_position
      self.report(msg, pos, pos, Error)
      None
    }
    Internal(m) => raise EffektError::Internal(m)
  }
}

///|
/// Parses an entire Effekt module. Errors are reported on the context; the
/// result is `None` if the parse failed.
pub fn parse_module_decl(
  source : Source,
  context : Context,
) -> ModuleDecl? raise EffektError {
  let tokens = Lexer::lex(source)
  let parser = Parser::new(tokens, source, context)
  parser.parse_program()
}

///|
/// Parses a single term/expression. Errors are reported on the context; the
/// result is `None` if the parse failed.
pub fn parse_term(
  source : Source,
  context : Context,
) -> Term? raise EffektError {
  let tokens = Lexer::lex(source)
  let parser = Parser::new(tokens, source, context)
  parser.parse_term_entry()
}

///|
/// Parses a single statement (convenience for tests).
pub fn parse_statement(
  source : Source,
  context : Context,
) -> Stmt? raise EffektError {
  let tokens = Lexer::lex(source)
  let parser = Parser::new(tokens, source, context)
  try {
    let stmt = parser.nonterminal(() => {
      parser.spaces()
      let s = parser.stmt()
      if parser.peek(TEOF) {
        s
      } else {
        parser.fail("Unexpected item")
      }
    })
    parser.report_recoverable_diagnostics()
    if parser.diagnostics.all(d => d.kind != Error) {
      Some(stmt)
    } else {
      None
    }
  } catch {
    Fatal(msg) => {
      parser.report_recoverable_diagnostics()
      let pos = parser.fail_position
      parser.report(msg, pos, pos, Error)
      None
    }
    Internal(m) => raise EffektError::Internal(m)
  }
}
