// Token definitions for the Effekt lexer.
//
// Mirrors `effekt/lexer/Lexer.scala` (the `Token`, `TokenKind` and
// `LexerError` definitions). Tokens carry *inclusive* start and end offsets
// into the source, exactly like upstream: the parser turns them into
// half-open `Span`s by using `previous.end + 1` as the end of a span.

///|
/// Lexing errors. The lexer never throws: it produces an `Error` token, and
/// the parser decides whether the error is recoverable.
pub(all) enum LexerError {
  InvalidEscapeSequence(String)
  Expected(Char)
  UnknownChar(Char)
  UnterminatedStringLike(TokenKind)
  UnterminatedComment
  EmptyCharLiteral
  MultipleCodePointsInChar
  InvalidIntegerFormat
  InvalidDoubleFormat
  InvalidByteFormat
  UnterminatedInterpolation(Int32)
} derive(Eq)

///|
pub fn LexerError::message(self : LexerError) -> String {
  match self {
    InvalidEscapeSequence(str) =>
      "Invalid character in escape sequence: `\\" + str + "`"
    Expected(char) => "Expected '\{char}' while lexing"
    UnknownChar(char) => "Unknown character '\{char}' in file"
    UnterminatedStringLike(TStr(_, false)) =>
      "Unterminated single-line string; expected closing `\"` on the end of the line"
    UnterminatedStringLike(kind) => "Unterminated \{kind.explain()}"
    UnterminatedComment =>
      "Unterminated multi-line comment; expected closing `*/`"
    EmptyCharLiteral => "Empty character literal"
    MultipleCodePointsInChar =>
      "Character literal consists of multiple code points"
    InvalidIntegerFormat =>
      "Invalid integer format, not a 64bit integer literal"
    InvalidDoubleFormat => "Invalid float format, not a double literal"
    InvalidByteFormat =>
      "Invalid byte format, byte has to be exactly two hex digits"
    UnterminatedInterpolation(depth) =>
      "Unterminated string interpolation (\{depth} unclosed splices)"
  }
}

///|
/// The kind of a token. Symbol tokens are named after their spelling, keyword
/// tokens are prefixed with `K`.
pub(all) enum TokenKind {
  // control tokens
  TEOF
  TError(LexerError)
  TNewline
  // literals
  TInteger(Int32)
  TFloat(Double)
  TStr(String, Bool) // contents, multiline
  THoleStr(String)
  TChr(Int32)
  TByt(Int32)
  // identifiers
  TIdent(String)
  // misc
  TComment(String)
  TDocComment(String)
  TShebang(String)
  TSpace
  // symbols
  TAssign // =
  TColonAssign // :=
  TEqEqEq // ===
  TNotEqEq // !==
  TColon // :
  TSemi // ;
  TPathSep // ::
  TAt // @
  TSpliceStart // ${
  TLBrace // {
  TRBrace // }
  TSpliceEnd // }$
  TLParen // (
  TRParen // )
  TLBracket // [
  TRBracket // ]
  TComma // ,
  TQuote // '
  TDot // .
  TSlash // /
  TArrow // =>
  TDiamond // <>
  TLt // <
  TLtEq // <=
  TGt // >
  TGtEq // >=
  THoleStart // <{
  THoleEnd // }>
  TBang // !
  TBar // |
  TBarBar // ||
  TAmp // &
  TAmpAmp // &&
  TPlus // +
  TPlusPlus // ++
  TMinus // -
  TStar // *
  TGtGt // >>
  TLtLt // <<
  TTilde // ~
  TMinusMinus // --
  TTildeGt // ~>
  TLtTilde // <~
  TPlusEq // +=
  TMinusEq // -=
  TStarEq // *=
  TSlashEq // /=
  TDotDot // ..
  TDotDotDot // ...
  THatHat // ^^
  THat // ^
  TQuestion // ?
  // keywords
  KLet
  KTrue
  KFalse
  KVal
  KVar
  KIf
  KElse
  KWhile
  KType
  KEffect
  KInterface
  KTry
  KWith
  KCase
  KDo
  KMatch
  KDef
  KExtern
  KRecord
  KBox
  KUnbox
  KReturn
  KRegion
  KResource
  KNew
  KAnd
  KIs
  KNamespace
  KModule
  KImport
  KExport
  KInclude
  KPrivate
} derive(Eq)

///|
/// The source text of a symbol token (used for error messages).
pub fn symbol_text(kind : TokenKind) -> String {
  match kind {
    TAssign => "="
    TColonAssign => ":="
    TEqEqEq => "==="
    TNotEqEq => "!=="
    TColon => ":"
    TSemi => ";"
    TPathSep => "::"
    TAt => "@"
    TSpliceStart => "${"
    TLBrace => "{"
    TRBrace => "}"
    TSpliceEnd => "}$"
    TLParen => "("
    TRParen => ")"
    TLBracket => "["
    TRBracket => "]"
    TComma => ","
    TQuote => "'"
    TDot => "."
    TSlash => "/"
    TArrow => "=>"
    TDiamond => "<>"
    TLt => "<"
    TLtEq => "<="
    TGt => ">"
    TGtEq => ">="
    THoleStart => "<{"
    THoleEnd => "}>"
    TBang => "!"
    TBar => "|"
    TBarBar => "||"
    TAmp => "&"
    TAmpAmp => "&&"
    TPlus => "+"
    TPlusPlus => "++"
    TMinus => "-"
    TStar => "*"
    TGtGt => ">>"
    TLtLt => "<<"
    TTilde => "~"
    TMinusMinus => "--"
    TTildeGt => "~>"
    TLtTilde => "<~"
    TPlusEq => "+="
    TMinusEq => "-="
    TStarEq => "*="
    TSlashEq => "/="
    TDotDot => ".."
    TDotDotDot => "..."
    THatHat => "^^"
    THat => "^"
    TQuestion => "?"
    _ => "<not a symbol>"
  }
}

///|
/// An explanation of a token kind, used in "Expected X but got Y" errors.
pub fn TokenKind::explain(self : TokenKind) -> String {
  if self.is_keyword() {
    return "keyword \{self.keyword_text()}"
  }
  match self {
    TIdent(n) => "identifier \{n}"
    TInteger(n) => "integer \{n}"
    TFloat(d) => "float \{d}"
    TStr(_, true) => "multi-line string literal"
    TStr(s, false) => "string literal \"\{s}\""
    TChr(c) => "character literal '\{char_of_code(c)}'"
    THoleStr(_) => "natural language hole `<\" ... \">`"
    TComment(_) => "comment"
    TDocComment(_) => "doc comment"
    TNewline => "newline"
    TSpace => "space"
    TEOF => "end of file"
    TSpliceEnd => "a splice ending brace `}`"
    TError(error) => "invalid token: \{error.message()}"
    other => symbol_text(other)
  }
}

///|
fn char_of_code(c : Int32) -> Char {
  c.unsafe_to_char()
}

///|
pub fn TokenKind::keyword_text(self : TokenKind) -> String {
  match self {
    KLet => "let"
    KTrue => "true"
    KFalse => "false"
    KVal => "val"
    KVar => "var"
    KIf => "if"
    KElse => "else"
    KWhile => "while"
    KType => "type"
    KEffect => "effect"
    KInterface => "interface"
    KTry => "try"
    KWith => "with"
    KCase => "case"
    KDo => "do"
    KMatch => "match"
    KDef => "def"
    KExtern => "extern"
    KRecord => "record"
    KBox => "box"
    KUnbox => "unbox"
    KReturn => "return"
    KRegion => "region"
    KResource => "resource"
    KNew => "new"
    KAnd => "and"
    KIs => "is"
    KNamespace => "namespace"
    KModule => "module"
    KImport => "import"
    KExport => "export"
    KInclude => "include"
    KPrivate => "private"
    _ => ""
  }
}

///|
pub fn TokenKind::is_keyword(self : TokenKind) -> Bool {
  match self {
    KLet
    | KTrue
    | KFalse
    | KVal
    | KVar
    | KIf
    | KElse
    | KWhile
    | KType
    | KEffect
    | KInterface
    | KTry
    | KWith
    | KCase
    | KDo
    | KMatch
    | KDef
    | KExtern
    | KRecord
    | KBox
    | KUnbox
    | KReturn
    | KRegion
    | KResource
    | KNew
    | KAnd
    | KIs
    | KNamespace
    | KModule
    | KImport
    | KExport
    | KInclude
    | KPrivate => true
    _ => false
  }
}

///|
/// The mapping from words to keyword tokens. Everything not listed here is a
/// plain identifier (`resume`, `in`, `at`, `_`, ... are "soft" keywords).
pub fn keyword_kind(word : String) -> TokenKind? {
  match word {
    "let" => Some(KLet)
    "true" => Some(KTrue)
    "false" => Some(KFalse)
    "val" => Some(KVal)
    "var" => Some(KVar)
    "if" => Some(KIf)
    "else" => Some(KElse)
    "while" => Some(KWhile)
    "type" => Some(KType)
    "effect" => Some(KEffect)
    "interface" => Some(KInterface)
    "try" => Some(KTry)
    "with" => Some(KWith)
    "case" => Some(KCase)
    "do" => Some(KDo)
    "match" => Some(KMatch)
    "def" => Some(KDef)
    "extern" => Some(KExtern)
    "record" => Some(KRecord)
    "box" => Some(KBox)
    "unbox" => Some(KUnbox)
    "return" => Some(KReturn)
    "region" => Some(KRegion)
    "resource" => Some(KResource)
    "new" => Some(KNew)
    "and" => Some(KAnd)
    "is" => Some(KIs)
    "namespace" => Some(KNamespace)
    "module" => Some(KModule)
    "import" => Some(KImport)
    "export" => Some(KExport)
    "include" => Some(KInclude)
    "private" => Some(KPrivate)
    _ => None
  }
}

///|
/// Whitespace and comments are skipped by the parser, but are represented in
/// the token stream (needed for "semicolon insertion" and for extern bodies).
pub fn TokenKind::is_space(self : TokenKind) -> Bool {
  match self {
    TSpace | TComment(_) | TNewline => true
    _ => false
  }
}

///|
/// Soft keywords are identifiers to the lexer.
pub fn soft_keyword(word : String) -> TokenKind {
  TIdent(word)
}

///|
pub fn resume_kind() -> TokenKind {
  TIdent("resume")
}

///|
pub fn in_kind() -> TokenKind {
  TIdent("in")
}

///|
pub fn at_kind() -> TokenKind {
  TIdent("at")
}

///|
pub fn underscore_kind() -> TokenKind {
  TIdent("_")
}

///|
/// A token with *inclusive* start and end offsets (in UTF-16 code units).
pub struct Token {
  start : Int32
  end : Int32
  kind : TokenKind
}

///|
pub fn Token::new(start : Int32, end : Int32, kind : TokenKind) -> Token {
  { start, end, kind, }
}

///|
pub fn Token::is_error(self : Token) -> Bool {
  match self.kind {
    TError(_) => true
    _ => false
  }
}

///|
pub impl Show for Token with fn output(self, logger) {
  logger.write_string(self.kind.explain())
}
