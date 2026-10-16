// Names from `util` that are used unqualified throughout this package.

///|
using @util {
  type Span,
  type EffektError,
  type Message,
  type Severity,
  type Origin,
  fresh_uid,
}

///|
/// `a` if it is `Some`, otherwise compute `b`.
pub fn[T] or_else(
  a : T?,
  b : () -> T? raise EffektError,
) -> T? raise EffektError {
  match a {
    Some(_) => a
    None => b()
  }
}
