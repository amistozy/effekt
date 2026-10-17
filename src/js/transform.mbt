// Shared definitions of the JavaScript transformers.
//
// Mirrors the `Transformer` trait of `effekt/generator/js/Transformer.scala`:
// string escaping, JavaScript name generation, constructor generation and the
// smart constructors for data / codata.
//
// Deviation from the Scala original (documented on purpose): `usedIncludes`
// (the analysis needed for separate compilation / the web backend) is *not*
// ported. It walks `Module.dependencies` and the `Bindings` of a module, which
// are not part of this port's `@symbols` package, and it is only needed by
// `js.Module.virtual`, whereas `compile_cps` renders `js.Module.commonjs`.

///|
/// The feature flags supported by the JavaScript backend.
pub fn js_feature_flags() -> Array[String] {
  ["js"]
}

// ---------------------------------------------------------------------------
// Strings
// ---------------------------------------------------------------------------

///|
/// Escapes the characters that cannot appear verbatim in a JS string literal.
pub fn escape(scala_string : String) -> String {
  let buf = StringBuilder()
  for c in scala_string {
    match c {
      '\'' => buf.write_string("'")
      '"' => buf.write_string("\\\"")
      '\\' => buf.write_string("\\\\")
      '\n' => buf.write_string("\\n")
      '\t' => buf.write_string("\\t")
      '\r' => buf.write_string("\\r")
      _ => buf.write_char(c)
    }
  }
  buf.to_string()
}

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

///|
/// Words that may not be used as a JavaScript identifier.
fn reserved_words() -> Array[String] {
  [
    // reserved words
    // (https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Lexical_grammar#keywords)
    "break", "case", "catch", "class", "const", "continue", "debugger", "default",
    "delete", "do", "else", "export", "extends", "false", "finally", "for", "function",
    "if", "import", "in", "instanceof", "let", "new", "null", "return", "static",
    "super", "switch", "this", "throw", "true", "try", "typeof", "var", "void", "while",
    "with", "yield",
    // future reserved words
     "enum", "implements", "interface", "package", "private", "protected", "public",
    // identifiers with special meanings
     "get", "set", "arguments", "async", "eval",
    // special names in CommonJS module systems
     "module", "exports", "require",
    // other special names
     "window", "document", "alert", "console",
  ]
}

///|
pub fn js_escape(name : String) -> String {
  if reserved_words().contains(name) {
    "$\{name}"
  } else {
    name.replace_all(old="?", new="").replace_all(old="!", new="")
  }
}

///|
pub fn js_module_name(path : String) -> String {
  "$\{path.replace_all(old="/", new="_").replace_all(old="-", new="_")}"
}

///|
pub fn js_module_file(path : String) -> String {
  "\{path.replace_all(old="/", new="_").replace_all(old="-", new="_")}.js"
}

// Attempt to have better / shorter names: `used_names` counts the names handed
// out per base name and `generated_names` remembers the name of every symbol,
// so that a symbol is spelled the same everywhere it occurs. Upstream keeps
// these in the (singleton) `Transformer` object; here they are module globals.
// `reset_naming` makes a compilation run reproducible.

///|
let used_names : Map[String, Int32] = Map([])

///|
/// uid -> generated name
let generated_names : Map[Int32, JSName] = Map([])

///|
/// Forgets every generated name.
pub fn reset_naming() -> Unit {
  used_names.clear()
  generated_names.clear()
}

///|
fn is_js_letter(c : Char) -> Bool {
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

///|
/// The base name of a symbol: upstream
/// `baseNameRx = """([A-Za-z$]*(?:_[A-Za-z]+)*)""".r` applied with
/// `findFirstIn`, that is, the longest prefix of letters, `$` and `_word`
/// groups.
fn base_name_of(name : String) -> String {
  let chars : Array[Char] = []
  for c in name {
    chars.push(c)
  }
  let buf = StringBuilder()
  let mut i = 0
  while i < chars.length() && (is_js_letter(chars[i]) || chars[i] == '$') {
    buf.write_char(chars[i])
    i = i + 1
  }
  while i + 1 < chars.length() && chars[i] == '_' && is_js_letter(chars[i + 1]) {
    buf.write_char('_')
    i = i + 1
    while i < chars.length() && is_js_letter(chars[i]) {
      buf.write_char(chars[i])
      i = i + 1
    }
  }
  buf.to_string()
}

///|
fn unique_name_for(base : String) -> String {
  let next_id = match used_names.get(base) {
    Some(id) => id
    None => 0
  }
  used_names.set(base, next_id + 1)
  "\{base}_\{next_id}"
}

///|
fn unique_name(sym : Sym) -> JSName {
  match generated_names.get(sym.uid()) {
    Some(name) => name
    None => {
      let name = JSName::new(
        js_escape(unique_name_for(base_name_of(sym.name().name))),
      )
      generated_names.set(sym.uid(), name)
      name
    }
  }
}

///|
/// The generated name of a symbol at its definition site.
pub fn name_def(id : Sym) -> JSName {
  unique_name(id)
}

///|
/// A reference to a symbol.
pub fn name_ref(id : Sym) -> Expr {
  Variable(unique_name(id))
}

///|
/// The generated name of a field or method.
pub fn member_name_ref(id : Sym) -> JSName {
  unique_name(id)
}

///|
/// A name that is guaranteed to be fresh (used for compiler-generated
/// variables that have no symbol, e.g. the `other` of `__equals`).
pub fn fresh_name(s : String) -> JSName {
  JSName::new("\{s}\{@util.fresh_uid()}")
}

// ---------------------------------------------------------------------------
// Representation of data
// ---------------------------------------------------------------------------

///|
pub fn should_export(id : Sym) -> Bool {
  let _ = id
  true
}

///|
fn this_field(field : JSName) -> Expr {
  Member(Variable(JSName::new("this")), field)
}

///|
fn other_field(other : JSName, field : JSName) -> Expr {
  Member(Variable(other), field)
}

///|
/// `!e`
fn not_expr(e : Expr) -> Expr {
  RawExpr(["!", ""], [e])
}

///|
/// `$effekt.equals(a, b)`
fn equals_call(a : Expr, b : Expr) -> Expr {
  effekt_call("equals", [a, b])
}

///|
fn bool_literal(b : Bool) -> Expr {
  raw_expr(b.to_string())
}

///|
pub fn tag_for(
  constructor : Sym,
  declarations : @core.DeclarationContext,
) -> Expr raise EffektError {
  raw_expr(declarations.get_constructor_tag(constructor).to_string())
}

///|
/// ```
/// class Id {
///   constructor(param...) { this.param = param; ... }
///   __reflect() { return { __tag: TAG, __name: "NAME", __data: [this.param...] } }
///   __equals(other) { ... }
/// }
/// ```
pub fn generate_constructor(
  constructor : @core.Constructor,
  tag_value : Int32,
) -> Stmt {
  let fields = constructor.fields
  let tag = JSName::new("__tag")
  let data = JSName::new("__data")
  let reflect = JSName::new("__reflect")
  let equals = JSName::new("__equals")

  let params : Array[JSName] = []
  for f in fields {
    params.push(name_def(f.id))
  }

  // constructor(param...) { this.__tag = TAG; this.param = param; ... }
  let init_params : Array[Stmt] = []
  for p in params {
    init_params.push(Assign(this_field(p), Variable(p)))
  }
  let init_tag = Assign(this_field(tag), raw_expr(tag_value.to_string()))
  let js_constructor = Stmt::Function(
    JSName::new("constructor"),
    params,
    [init_tag] + init_params,
  )

  // __reflect() { return { __tag: TAG, __name: "NAME", __data: [this.param...] } }
  let reflected_data : Array[Expr] = []
  for f in fields {
    reflected_data.push(this_field(member_name_ref(f.id)))
  }
  let js_reflect = Stmt::Function(reflect, [], [
    Return(
      Object([
        ObjectProperty::new(tag, raw_expr(tag_value.to_string())),
        ObjectProperty::new(
          JSName::new("__name"),
          js_string(constructor.id.name().name),
        ),
        ObjectProperty::new(data, ArrayLiteral(reflected_data)),
      ]),
    ),
  ])

  // __equals(other) { if (!other) { return false }; if (!equals(this.__tag, other.__tag)) { return false }; ...; return true }
  let other = fresh_name("other")
  let noop = Block([])
  let abort = Return(bool_literal(false))
  let succeed = Return(bool_literal(true))

  fn compare(field : JSName) -> Expr {
    not_expr(equals_call(this_field(field), other_field(other, field)))
  }

  let other_exists = If(not_expr(Variable(other)), abort, noop)
  let compare_tags = If(compare(tag), abort, noop)
  let compare_fields : Array[Stmt] = []
  for p in params {
    compare_fields.push(If(compare(p), abort, noop))
  }
  let js_equals = Stmt::Function(
    equals,
    [other],
    [other_exists, compare_tags] + compare_fields + [succeed],
  )

  Class(name_def(constructor.id), [js_constructor, js_reflect, js_equals])
}
