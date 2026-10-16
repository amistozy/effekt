// The Effekt lexer.
//
// Mirrors `effekt/lexer/Lexer.scala`. The lexer never throws: every error is
// reported as an `Error` token. String interpolation is handled by a stack of
// `Delimiter`s inside the lexer, which is why the parser can simply consume a
// flat token stream: for `"a ${x} b"` the lexer emits
//     Str("a ")  `${`  Ident("x")  `}$`  Str(" b")  Str("")
//
// Offsets in tokens are *inclusive* UTF-16 code unit offsets into the source,
// exactly as upstream.

///|
/// The different kinds of string-like literals supported by Effekt.
pub(all) enum Delimiter {
  //          "...",   """...""",      '...',    <"...">
  SingleString
  MultiString
  CharString
  HoleString
} derive(Eq)

///|
pub fn Delimiter::allows_interpolation(self : Delimiter) -> Bool {
  match self {
    SingleString | MultiString | HoleString => true
    CharString => false
  }
}

///|
pub fn Delimiter::is_multiline(self : Delimiter) -> Bool {
  match self {
    SingleString | CharString => false
    MultiString | HoleString => true
  }
}

///|
pub fn Delimiter::allows_escapes(self : Delimiter) -> Bool {
  !self.is_multiline()
}

///|
pub fn Delimiter::to_token_kind(
  self : Delimiter,
  contents : String,
) -> TokenKind {
  match self {
    SingleString => TStr(contents, false)
    MultiString => TStr(contents, true)
    HoleString => THoleStr(contents)
    CharString =>
      if contents.is_empty() {
        TError(EmptyCharLiteral)
      } else if code_point_count(contents) > 1 {
        TError(MultipleCodePointsInChar)
      } else {
        TChr(char_at(contents, 0).to_int())
      }
  }
}

// Character classification and helpers
// ------------------------------------

///|
/// The character at a UTF-16 code unit offset, or NUL past the end of input.
/// Surrogate pairs are combined into a single code point, so that offsets stay
/// in UTF-16 code units while characters are Unicode scalar values.
fn char_at(s : String, i : Int32) -> Char {
  if i < 0 || i >= s.length() {
    '\u{0}'
  } else {
    let u = s[i]
    if u.is_leading_surrogate() && i + 1 < s.length() {
      let v = s[i + 1]
      if v.is_trailing_surrogate() {
        let code_point = 65536 +
          ((u.to_uint().to_int() - 55296) << 10) +
          (v.to_uint().to_int() - 56320)
        code_point.unsafe_to_char()
      } else {
        '\u{FFFD}'
      }
    } else {
      u.to_char().unwrap_or('\u{FFFD}')
    }
  }
}

///|
/// The number of Unicode code points in a string.
fn code_point_count(s : String) -> Int32 {
  let mut i = 0
  let mut count = 0
  while i < s.length() {
    let u = s[i]
    if u.is_leading_surrogate() && i + 1 < s.length() {
      i = i + 2
    } else {
      i = i + 1
    }
    count = count + 1
  }
  count
}

///|
fn is_name_first(c : Char) -> Bool {
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
}

///|
fn is_name_rest(c : Char) -> Bool {
  is_name_first(c) || (c >= '0' && c <= '9') || c == '!' || c == '?' || c == '$'
}

///|
fn is_hex_digit(c : Char) -> Bool {
  (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
}

///|
fn is_digit(c : Char) -> Bool {
  c >= '0' && c <= '9'
}

///|
fn is_whitespace(c : Char) -> Bool {
  c.is_whitespace()
}

///|
fn hex_value(c : Char) -> Int32 {
  if c >= '0' && c <= '9' {
    c.to_int() - '0'.to_int()
  } else if c >= 'a' && c <= 'f' {
    c.to_int() - 'a'.to_int() + 10
  } else {
    c.to_int() - 'A'.to_int() + 10
  }
}

///|
/// Parses a decimal integer literal (an optional `-`, then digits). Values
/// outside the 64 bit range are rejected, exactly like upstream's
/// `toLongOption`.
fn parse_int_lit(s : String) -> Int32? {
  if s.length() == 0 {
    return None
  }
  let mut i = 0
  let mut neg = false
  if s[0] == '-' {
    neg = true
    i = 1
  }
  if i >= s.length() {
    return None
  }
  // The Java `Long.parseLong` algorithm: accumulate negatively so that
  // Int64::min_value is representable.
  let limit : Int64 = if neg {
    -9223372036854775807L - 1L
  } else {
    -9223372036854775807L
  }
  let multmin = limit / 10L
  let mut result : Int64 = 0L
  let mut started = false
  while i < s.length() {
    let u = s[i]
    if u < '0' || u > '9' {
      return None
    }
    let digit = (u.to_int() - 48).to_int64()
    if result < multmin {
      return None
    }
    result = result * 10L
    if result < limit + digit {
      return None
    }
    result = result - digit
    started = true
    i = i + 1
  }
  if !started {
    return None
  }
  let value = if neg { result } else { -result }
  Some(value.to_int())
}

///|
/// Parses a decimal floating point literal `[-] digits ['.' digits]`.
fn parse_double_lit(s : String) -> Double? {
  if s.length() == 0 {
    return None
  }
  let mut i = 0
  let mut neg = false
  if s[0] == '-' {
    neg = true
    i = 1
  }
  let mut int_part : Double = 0.0
  let mut seen_digit = false
  while i < s.length() && s[i] >= '0' && s[i] <= '9' {
    int_part = int_part * 10.0 + Double::from_int(s[i].to_int() - 48)
    seen_digit = true
    i = i + 1
  }
  if !seen_digit {
    return None
  }
  let mut result = int_part
  if i < s.length() && s[i] == '.' {
    i = i + 1
    let mut scale = 0.1
    while i < s.length() && s[i] >= '0' && s[i] <= '9' {
      result = result + Double::from_int(s[i].to_int() - 48) * scale
      scale = scale / 10.0
      i = i + 1
    }
  }
  if i != s.length() {
    return None
  }
  Some(if neg { -result } else { result })
}

///|
/// Parses a hex string of exactly two digits into a byte value.
fn parse_byte_lit(s : String) -> Int32? {
  if s.length() != 2 {
    return None
  }
  let mut acc = 0
  for i = 0; i < 2; i = i + 1 {
    let u = s[i]
    if !is_hex_digit(u.to_char().unwrap_or('\u{0}')) {
      return None
    }
    acc = acc * 16 + hex_value(u.to_char().unwrap_or('0'))
  }
  Some(acc)
}

// The lexer
// ---------

///|
/// Tracks brace/paren/bracket depth for string interpolation and error recovery.
pub struct Lexer {
  content : String
  mut current_char : Char
  mut next_char : Char
  /// UTF-16 offset of `current_char`
  mut offset : Int32
  /// UTF-16 offset at which the current token started
  mut token_start : Int32
  delimiters : Array[Delimiter]
  mut parens : Int32
  mut braces : Int32
  mut brackets : Int32
  interpolation_depths : Array[Int32]
  /// When we see the `}` ending an interpolation we must (1) return the `}$`
  /// token and (2) make sure the NEXT call to `next` resumes lexing a string.
  mut resume_string_next : Bool
  mut eof : Bool
}

///|
pub fn Lexer::new(source : Source) -> Lexer {
  let content = source.content
  let current = char_at(content, 0)
  {
    content,
    current_char: current,
    next_char: char_at(content, current.utf16_len()),
    offset: 0,
    token_start: 0,
    delimiters: [],
    parens: 0,
    braces: 0,
    brackets: 0,
    interpolation_depths: [],
    resume_string_next: false,
    eof: false,
  }
}

///|
pub fn Lexer::has_next(self : Lexer) -> Bool {
  !self.eof
}

///|
pub fn Lexer::next(self : Lexer) -> Token {
  self.token_start = self.offset
  let kind = self.next_token()
  if kind == TEOF {
    self.eof = true
    Token::new(self.token_start, self.offset, kind)
  } else {
    Token::new(self.token_start, self.offset - 1, kind)
  }
}

///|
/// Lexes an entire source file. The result includes the final `TEOF` token.
pub fn Lexer::lex(source : Source) -> Array[Token] {
  let lexer = Lexer::new(source)
  let tokens : Array[Token] = []
  while lexer.has_next() {
    tokens.push(lexer.next())
  }
  tokens
}

///|
fn Lexer::at_end_of_input(self : Lexer) -> Bool {
  self.current_char == '\u{0}'
}

///|
/// Advances the lexer by one, consuming (and returning) the current character.
fn Lexer::advance(self : Lexer) -> Char {
  let ret = self.current_char
  self.offset = self.offset + ret.utf16_len()
  self.current_char = self.next_char
  self.next_char = char_at(
    self.content,
    self.offset + self.current_char.utf16_len(),
  )
  ret
}

///|
fn Lexer::advance_k(self : Lexer, k : Int32) -> Unit {
  for i = 0; i < k; i = i + 1 {
    let _ = self.advance()
  }
}

///|
fn Lexer::advance_with(self : Lexer, k : Int32, kind : TokenKind) -> TokenKind {
  self.advance_k(k)
  kind
}

///|
/// The text between two absolute UTF-16 offsets.
fn Lexer::slice(self : Lexer, from : Int32, to : Int32) -> String {
  let lo = if from < 0 { 0 } else { from }
  let hi = if to > self.content.length() { self.content.length() } else { to }
  if hi <= lo {
    ""
  } else {
    self.content[lo:hi].to_owned()
  }
}

///|
/// The text of the current token, skipping `skip_after_start` characters at the
/// start and `skip_before_end` characters at the end.
fn Lexer::get_current_slice(
  self : Lexer,
  skip_after_start : Int32,
  skip_before_end : Int32,
) -> String {
  self.slice(self.token_start + skip_after_start, self.offset - skip_before_end)
}

///|
fn Lexer::advance_while(self : Lexer, predicate : (Char, Char) -> Bool) -> Unit {
  while predicate(self.current_char, self.next_char) && !self.at_end_of_input() {
    let _ = self.advance()
  }
}

///|
fn Lexer::advance_spaces(self : Lexer) -> TokenKind {
  self.advance_while(fn(curr, nxt) {
    if curr == '\r' && nxt == '\n' {
      false
    } else if curr == '\n' {
      false
    } else {
      is_whitespace(curr)
    }
  })
  TSpace
}

///|
fn Lexer::peek_ahead(self : Lexer, offset : Int32) -> Char {
  char_at(self.content, self.offset + offset)
}

///|
/// Are we at an interpolation boundary, i.e. does the current brace depth match
/// the depth at which the innermost interpolation started?
fn Lexer::is_at_interpolation_boundary(self : Lexer) -> Bool {
  let n = self.interpolation_depths.length()
  n > 0 && self.interpolation_depths[n - 1] == self.braces
}

///|
/// The "main" function for getting the next token kind.
fn Lexer::next_token(self : Lexer) -> TokenKind {
  // First handle pending string continuation / return from a splice.
  if self.resume_string_next {
    self.resume_string_next = false
    let n = self.delimiters.length()
    if n > 0 {
      return self.string_like(self.delimiters[n - 1], true)
    }
    // otherwise fallthrough
  }

  let c = self.current_char
  let n = self.next_char
  match (c, n) {
    // Whitespace: first try matching newlines, then whitespace-like
    ('\n', _) => self.advance_with(1, TNewline)
    ('\r', '\n') => self.advance_with(2, TNewline)
    (c, _) if is_whitespace(c) => self.advance_spaces()
    // Numbers
    ('0', 'x') if is_hex_digit(self.peek_ahead(2)) => {
      self.advance_k(2)
      self.byte()
    }
    (c, _) if is_digit(c) => self.number()
    // Identifiers and keywords
    (c, _) if is_name_first(c) => self.identifier()
    // String literals, character literals, hole string literals
    ('"', '"') if self.peek_ahead(2) == '"' => {
      self.advance_k(3)
      self.string_like(MultiString, false)
    }
    ('"', _) => {
      self.advance_k(1)
      self.string_like(SingleString, false)
    }
    ('\'', _) => {
      self.advance_k(1)
      self.string_like(CharString, false)
    }
    ('<', '"') => {
      self.advance_k(2)
      self.string_like(HoleString, false)
    }
    // Comments
    ('/', '*') => {
      self.advance_k(2)
      self.multiline_comment()
    }
    ('/', '/') => {
      self.advance_k(2)
      self.singleline_comment()
    }
    ('/', '=') => self.advance_with(2, TSlashEq)
    ('/', _) => self.advance_with(1, TSlash)
    // Shebang
    ('#', '!') => {
      self.advance_k(2)
      self.shebang()
    }
    ('.', '.') if self.peek_ahead(2) == '.' => self.advance_with(3, TDotDotDot)
    ('.', '.') => self.advance_with(2, TDotDot)
    ('.', _) => self.advance_with(1, TDot)
    // Two-character operators
    //
    // NOTE: `==` and `!=` are lexed into the token kinds `===` and `!==`.
    // This is what upstream does as well: the token kinds carry the spelling
    // of older Effekt versions, while the source syntax is `==` / `!=`.
    ('=', '=') => self.advance_with(2, TEqEqEq)
    ('=', '>') => self.advance_with(2, TArrow)
    ('=', _) => self.advance_with(1, TAssign)
    ('!', '=') => self.advance_with(2, TNotEqEq)
    ('!', _) => self.advance_with(1, TBang)
    ('^', '^') => self.advance_with(2, THatHat)
    ('^', _) => self.advance_with(1, THat)
    ('~', '>') => self.advance_with(2, TTildeGt)
    ('~', _) => self.advance_with(1, TTilde)
    ('<', '<') => self.advance_with(2, TLtLt)
    ('<', '=') => self.advance_with(2, TLtEq)
    ('<', '>') => self.advance_with(2, TDiamond)
    ('<', '{') => {
      self.braces = self.braces + 1
      self.advance_with(2, THoleStart)
    }
    ('<', '~') => self.advance_with(2, TLtTilde)
    ('<', _) => self.advance_with(1, TLt)
    ('>', '>') => self.advance_with(2, TGtGt)
    ('>', '=') => self.advance_with(2, TGtEq)
    ('>', _) => self.advance_with(1, TGt)
    (':', ':') => self.advance_with(2, TPathSep)
    (':', '=') => self.advance_with(2, TColonAssign)
    (':', _) => self.advance_with(1, TColon)
    ('|', '|') => self.advance_with(2, TBarBar)
    ('|', _) => self.advance_with(1, TBar)
    ('&', '&') => self.advance_with(2, TAmpAmp)
    ('&', _) => self.advance_with(1, TAmp)
    ('+', '+') => self.advance_with(2, TPlusPlus)
    ('+', '=') => self.advance_with(2, TPlusEq)
    ('+', _) => self.advance_with(1, TPlus)
    ('-', c) if is_digit(c) => {
      self.advance_k(1)
      self.number()
    }
    ('-', '=') => self.advance_with(2, TMinusEq)
    ('-', _) => self.advance_with(1, TMinus)
    ('*', '=') => self.advance_with(2, TStarEq)
    ('*', _) => self.advance_with(1, TStar)
    ('?', _) => self.advance_with(1, TQuestion)
    ('$', '{') => {
      self.interpolation_depths.push(self.braces + 1)
      self.braces = self.braces + 1
      self.advance_with(2, TSpliceStart)
    }
    ('$', _) => self.advance_with(1, TError(UnknownChar('$')))
    ('}', _) if self.is_at_interpolation_boundary() => {
      let _ = self.interpolation_depths.pop()
      self.braces = self.braces - 1
      self.resume_string_next = true // remember to resume with a string next!
      self.advance_with(1, TSpliceEnd)
    }
    // Single-character tokens
    (';', _) => self.advance_with(1, TSemi)
    ('@', _) => self.advance_with(1, TAt)
    ('{', _) => {
      self.braces = self.braces + 1
      self.advance_with(1, TLBrace)
    }
    ('}', '>') => {
      self.braces = self.braces - 1
      self.advance_with(2, THoleEnd)
    }
    ('}', _) => {
      self.braces = self.braces - 1
      self.advance_with(1, TRBrace)
    }
    ('(', _) => {
      self.parens = self.parens + 1
      self.advance_with(1, TLParen)
    }
    (')', _) => {
      self.parens = self.parens - 1
      self.advance_with(1, TRParen)
    }
    ('[', _) => {
      self.brackets = self.brackets + 1
      self.advance_with(1, TLBracket)
    }
    (']', _) => {
      self.brackets = self.brackets - 1
      self.advance_with(1, TRBracket)
    }
    (',', _) => self.advance_with(1, TComma)
    ('\u{0}', _) =>
      // EOF reached - provide context about unclosed constructs
      if self.interpolation_depths.length() > 0 && self.delimiters.length() > 0 {
        let depth = self.interpolation_depths.length()
        self.interpolation_depths.clear()
        self.delimiters.clear()
        TError(UnterminatedInterpolation(depth))
      } else if self.delimiters.length() > 0 {
        let n = self.delimiters.length()
        let latest = self.delimiters[n - 1]
        self.delimiters.clear()
        // NOTE: We only report the most recent one here...
        TError(UnterminatedStringLike(latest.to_token_kind("")))
      } else {
        TEOF
      }
    (c, _) => self.advance_with(1, TError(UnknownChar(c)))
  }
}

///|
fn Lexer::number(self : Lexer) -> TokenKind {
  // Consume the integer part
  self.advance_while(fn(curr, _) { is_digit(curr) })

  if self.current_char == '.' && is_digit(self.next_char) {
    let _ = self.advance() // consume '.'
    // Consume fractional part
    self.advance_while(fn(curr, _) { is_digit(curr) })
    let float_string = self.get_current_slice(0, 0)
    match parse_double_lit(float_string) {
      Some(d) => TFloat(d)
      None => TError(InvalidDoubleFormat)
    }
  } else {
    let integer_string = self.get_current_slice(0, 0)
    match parse_int_lit(integer_string) {
      Some(i) => TInteger(i)
      None => TError(InvalidIntegerFormat)
    }
  }
}

///|
fn Lexer::byte(self : Lexer) -> TokenKind {
  // Consume hex digits
  self.advance_while(fn(curr, _) { is_hex_digit(curr) })
  let hex_string = self.get_current_slice(2, 0)
  match parse_byte_lit(hex_string) {
    Some(b) => TByt(b)
    None => TError(InvalidByteFormat)
  }
}

///|
fn Lexer::identifier(self : Lexer) -> TokenKind {
  self.advance_while(fn(curr, _) { is_name_rest(curr) })
  let word = self.get_current_slice(0, 0)
  match keyword_kind(word) {
    Some(k) => k
    None => TIdent(word)
  }
}

///|
/// Lexes any kind of string given by `delimiter`. `continued` is set when we
/// return to lexing a string after a stint in a splice.
///
/// Contract: expects its caller to already consume the delimiter itself!
fn Lexer::string_like(
  self : Lexer,
  delimiter : Delimiter,
  continued : Bool,
) -> TokenKind {
  if !continued {
    self.delimiters.push(delimiter)
  }
  let contents = StringBuilder()
  while !self.at_end_of_input() {
    let c = self.current_char
    let n = self.next_char
    match (c, n) {
      // closing characters
      ('"', '"') if delimiter == MultiString && self.peek_ahead(2) == '"' => {
        self.advance_k(3)
        return self.close_string(delimiter, contents, true, false)
      }
      ('"', _) if delimiter == SingleString => {
        self.advance_k(1)
        return self.close_string(delimiter, contents, true, false)
      }
      ('"', '>') if delimiter == HoleString => {
        self.advance_k(2)
        return self.close_string(delimiter, contents, true, false)
      }
      ('\'', _) if delimiter == CharString => {
        self.advance_k(1)
        return self.close_string(delimiter, contents, true, false)
      }
      // escapes
      ('\\', _) if delimiter.allows_escapes() => {
        let _ = self.advance()
        match self.current_char {
          '\\' | '"' | '\'' | '$' => contents.write_char(self.advance())
          'n' => {
            let _ = self.advance()
            contents.write_char('\n')
          }
          'r' => {
            let _ = self.advance()
            contents.write_char('\r')
          }
          't' => {
            let _ = self.advance()
            contents.write_char('\t')
          }
          'u' => {
            let start = self.offset
            let _ = self.advance()
            let code_point = self.lex_unicode_escape()
            if code_point < 0 {
              return TError(
                InvalidEscapeSequence(self.slice(start, self.offset - 1)),
              )
            } else {
              contents.write_char(code_point.unsafe_to_char())
            }
          }
          c => return TError(InvalidEscapeSequence(c.to_string()))
        }
      }
      // interpolation
      ('$', '{') if delimiter.allows_interpolation() =>
        // We *do not* pop in this case, we need to keep the delimiter on the
        // stack in order to know into what kind of string we should resume!
        return self.close_string(delimiter, contents, false, false)
      // newlines
      ('\n', _) if !delimiter.is_multiline() =>
        return self.close_string(delimiter, contents, true, true)
      ('\r', '\n') if !delimiter.is_multiline() =>
        return self.close_string(delimiter, contents, true, true)
      // "normal" characters of a string
      (_, _) => contents.write_char(self.advance())
    }
  }
  // End of input reached
  self.close_string(delimiter, contents, true, true)
}

///|
/// Creates the correct token, taking care of the `delimiters` stack.
fn Lexer::close_string(
  self : Lexer,
  delimiter : Delimiter,
  contents : StringBuilder,
  should_pop : Bool,
  unterminated : Bool,
) -> TokenKind {
  if should_pop {
    let _ = self.delimiters.pop()
  }
  let kind = delimiter.to_token_kind(contents.to_string())
  if unterminated {
    TError(UnterminatedStringLike(kind))
  } else {
    kind
  }
}

///|
/// Returns a code point as a 32 bit integer, or -1 on failure.
fn Lexer::lex_unicode_escape(self : Lexer) -> Int32 {
  let c = self.current_char
  if c == '{' {
    let _ = self.advance()
    let start = self.offset
    self.advance_while(fn(curr, _) { curr != '}' })
    if self.current_char != '}' {
      return -1
    }
    let _ = self.advance() // consume '}'
    let hex_str = self.slice(start, self.offset - 1)
    parse_hex_int(hex_str)
  } else if is_hex_digit(c) {
    let start = self.offset
    self.advance_while(fn(curr, _) { is_hex_digit(curr) })
    let hex_str = self.slice(start, self.offset)
    parse_hex_int(hex_str)
  } else {
    -1
  }
}

///|
fn parse_hex_int(s : String) -> Int32 {
  if s.length() == 0 {
    return -1
  }
  let mut acc = 0
  for i = 0; i < s.length(); i = i + 1 {
    let u = s[i]
    if !is_hex_digit(u.to_char().unwrap_or('\u{0}')) {
      return -1
    }
    acc = acc * 16 + hex_value(u.to_char().unwrap_or('0'))
  }
  acc
}

///|
fn Lexer::singleline_comment(self : Lexer) -> TokenKind {
  let is_doc_comment = self.current_char == '/'
  self.advance_while(fn(curr, _) { curr != '\n' && curr != '\r' })
  if is_doc_comment {
    TDocComment(self.get_current_slice(3, 0)) // Remove '///'
  } else {
    TComment(self.get_current_slice(2, 0)) // Remove '//'
  }
}

///|
fn Lexer::multiline_comment(self : Lexer) -> TokenKind {
  let mut done = false
  while !self.at_end_of_input() && !done {
    let c = self.current_char
    let n = self.next_char
    match (c, n) {
      ('/', '*') => self.advance_k(2) // ignored!
      ('*', '/') => {
        self.advance_k(2)
        done = true
      }
      _ => {
        let _ = self.advance()
      }
    }
  }
  if !done {
    TError(UnterminatedComment)
  } else {
    // Remove `/*` and `*/`
    TComment(self.get_current_slice(2, 2))
  }
}

///|
fn Lexer::shebang(self : Lexer) -> TokenKind {
  self.advance_while(fn(curr, _) { curr != '\n' && curr != '\r' })
  TShebang(self.get_current_slice(2, 0)) // Remove `#!`
}
