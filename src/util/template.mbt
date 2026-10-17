// String templates used by the FFI (`extern js """ ... ${x} ... """`).
//
// A template is a list of literal string fragments interleaved with
// interpolated arguments: "a" arg0 "b" arg1 "c" has strings
// ["a", "b", "c"] and args [arg0, arg1].

///|
pub(all) struct Template[T] {
  strings : Array[String]
  args : Array[T]
}

///|
pub fn[T] Template::new(
  strings : Array[String],
  args : Array[T],
) -> Template[T] {
  { strings, args, }
}

///|
pub fn[T] Template::empty() -> Template[T] {
  { strings: [], args: [], }
}

///|
pub fn[T] Template::is_empty(self : Template[T]) -> Bool {
  self.args.length() == 0 && self.strings.length() <= 1
}

///|
pub fn[T, U] Template::map(self : Template[T], f : (T) -> U) -> Template[U] {
  { strings: self.strings, args: self.args.map(f), }
}

///|
/// Renders a template where each argument is rendered by `f`.
pub fn[T] Template::render(self : Template[T], f : (T) -> String) -> String {
  let buf = StringBuilder()
  for i = 0; i < self.strings.length(); i = i + 1 {
    buf.write_string(self.strings[i])
    if i < self.args.length() {
      buf.write_string(f(self.args[i]))
    }
  }
  buf.to_string()
}

///|
/// Like `map`, but the mapping function may abort compilation.
pub fn[T, U] Template::map_raise(
  self : Template[T],
  f : (T) -> U raise EffektError,
) -> Template[U] raise EffektError {
  let args : Array[U] = []
  for a in self.args {
    args.push(f(a))
  }
  { strings: self.strings, args, }
}
