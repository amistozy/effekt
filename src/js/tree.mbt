// The JavaScript syntax tree: the image of the translation from CPS.
//
// Mirrors `effekt/generator/js/Tree.scala`. `JSName` is `@symbols.JSName`.
//
// Since MoonBit has neither overloading nor varargs, the smart constructors of
// the Scala file (`Const`, `Let`, `Call`, `MethodCall`, `Lambda`, `JsString`,
// `Object`, `MaybeBlock`, `Undefined`, `RawExpr`, `RawStmt`) are provided here
// as free functions with a `js_` prefix.

///|
/// The `$effekt` runtime namespace.
pub fn effekt_namespace() -> Expr {
  Variable(JSName::new("$effekt"))
}

///|
/// `$effekt.<name>`: a reference to a runtime field.
pub fn effekt_field(name : String) -> Expr {
  Member(effekt_namespace(), JSName::new(name))
}

///|
/// `$effekt.<name>(args...)`: a call into the runtime.
pub fn effekt_call(name : String, args : Array[Expr]) -> Expr {
  method_call(effekt_namespace(), JSName::new(name), args)
}

// ---------------------------------------------------------------------------
// Imports and exports
// ---------------------------------------------------------------------------

///|
pub(all) enum Import {
  /// `import * as <name> from "<file>";`
  ImportAll(JSName, String)
  /// `import {<members>, ...} from "<file>";`
  ImportSelective(Array[JSName], String)
}

///|
pub(all) struct Export {
  name : JSName
  expr : Expr
}

///|
pub fn Export::new(name : JSName, expr : Expr) -> Export {
  { name, expr, }
}

///|
pub(all) struct Module {
  name : JSName
  imports : Array[Import]
  exports : Array[Export]
  stmts : Array[Stmt]
}

///|
pub fn Module::new(
  name : JSName,
  imports : Array[Import],
  exports : Array[Export],
  stmts : Array[Stmt],
) -> Module {
  { name, imports, exports, stmts, }
}

///|
/// Generates the JavaScript module skeleton for whole program compilation.
pub fn Module::commonjs(self : Module) -> Array[Stmt] {
  let effekt = Stmt::Const(
    PatternVariable(JSName::new("$effekt")),
    Expr::Object([]),
  )
  let import_stmts : Array[Stmt] = []
  for i in self.imports {
    match i {
      // const MOD = require(PATH)
      ImportAll(name, file) =>
        import_stmts.push(
          Stmt::Const(
            PatternVariable(name),
            call(Variable(JSName::new("require")), [js_string("./" + file)]),
          ),
        )
      // const {NAMES, ...} = require(PATH)
      ImportSelective(names, file) =>
        import_stmts.push(
          Stmt::Destruct(
            names,
            call(Variable(JSName::new("require")), [js_string("./" + file)]),
          ),
        )
    }
  }
  let export_statement = Stmt::Assign(
    Expr::RawExpr(
      [
        "(typeof module != \"undefined\" && module !== null ? module : {}).exports = " +
        self.name.name,
      ],
      [],
    ),
    Expr::Object(self.exports.map(e => ObjectProperty::new(e.name, e.expr))),
  )
  [effekt] + import_stmts + self.stmts + [export_statement]
}

///|
/// Generates the JavaScript module skeleton for virtual modules that are
/// compiled separately:
///
/// ```
/// const $effekt = {}
/// // ... contents of the module
/// module.exports = {
///   // EXPORTS...
/// }
/// ```
pub fn Module::virtual(self : Module) -> Array[Stmt] {
  let effekt = Stmt::Const(
    PatternVariable(JSName::new("$effekt")),
    Expr::Object([]),
  )
  let import_stmts : Array[Stmt] = []
  for i in self.imports {
    match i {
      // const MOD = load(PATH)
      ImportAll(name, file) =>
        import_stmts.push(
          js_const(name, call(Variable(JSName::new("load")), [js_string(file)])),
        )
      // const {NAMES, ...} = load(PATH)
      ImportSelective(names, file) =>
        import_stmts.push(
          Stmt::Destruct(
            names,
            call(Variable(JSName::new("load")), [js_string(file)]),
          ),
        )
    }
  }
  let declaration = Stmt::Const(PatternVariable(self.name), Expr::Object([]))
  let export_statement = Stmt::Assign(
    Expr::RawExpr(["module.exports"], []),
    Expr::Object(self.exports.map(e => ObjectProperty::new(e.name, e.expr))),
  )
  [effekt] + import_stmts + [declaration] + self.stmts + [export_statement]
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

///|
/// The syntax of JavaScript, as far as it is the image of our translation.
pub(all) enum Expr {
  /// e.g. `<EXPR>(<EXPR>)`
  Call(Expr, Array[Expr])
  /// e.g. `new <EXPR>(<EXPR>)`
  New(Expr, Array[Expr])
  /// e.g. `"" <EXPR> " + " <EXPR>`
  /// Raw JS splices, always start with a prefix string, then interleave the
  /// arguments. `strings.length() == args.length() + 1`.
  RawExpr(Array[String], Array[Expr])
  /// e.g. `42`. A raw JS literal, already converted to a string. Similar to
  /// `RawExpr`, but will not be parenthesized.
  RawLiteral(String)
  /// e.g. `(<EXPR> ? <EXPR> : <EXPR>)`
  IfExpr(Expr, Expr, Expr)
  /// e.g. `(x, y) => <STMT>`
  Lambda(Array[JSName], Stmt)
  /// e.g. `{ x: <EXPR>, y: <EXPR>, ... }`
  Object(Array[ObjectProperty])
  /// e.g. `<EXPR>.<NAME>`
  Member(Expr, JSName)
  /// e.g. `[<EXPR>*]` (we cannot call it "Array")
  ArrayLiteral(Array[Expr])
  /// e.g. `x`
  Variable(JSName)
}

///|
pub(all) struct ObjectProperty {
  name : JSName
  value : Expr
}

///|
pub fn ObjectProperty::new(name : JSName, value : Expr) -> ObjectProperty {
  { name, value, }
}

// ---------------------------------------------------------------------------
// Patterns and statements
// ---------------------------------------------------------------------------

///|
pub(all) enum Pattern {
  PatternVariable(JSName)
  /// `Array` is a reserved-ish word, hence `PatternArray`.
  PatternArray(Array[Pattern])
}

///|
pub(all) struct SwitchBranch {
  tag : Expr
  body : Array[Stmt]
}

///|
pub fn SwitchBranch::new(tag : Expr, body : Array[Stmt]) -> SwitchBranch {
  { tag, body, }
}

///|
pub(all) enum Stmt {
  /// e.g. `{ <STMT>* }`
  Block(Array[Stmt])
  /// e.g. `return <EXPR>`
  Return(Expr)
  /// A raw JS statement.
  RawStmt(Array[String], Array[Expr])
  /// e.g. `const x = <EXPR>`
  Const(Pattern, Expr)
  /// e.g. `let x = <EXPR>`
  Let(Pattern, Expr)
  /// e.g. `<EXPR> = <EXPR>`
  Assign(Expr, Expr)
  /// e.g. `const {x,y,z} = <EXPR>`
  Destruct(Array[JSName], Expr)
  /// e.g. `switch (sc) { case <EXPR>: <STMT>; ...; default: <STMT> }`
  Switch(Expr, Array[SwitchBranch], Array[Stmt]?)
  /// e.g. `function <NAME>(x, y) { <STMT>* }`
  Function(JSName, Array[JSName], Array[Stmt])
  /// e.g. `class <NAME> { <NAME>(x, y) { <STMT>* }... }`.
  /// The members are expected to be `Function` statements.
  Class(JSName, Array[Stmt])
  /// e.g. `if (<EXPR>) { <STMT> } else { <STMT> }`
  If(Expr, Stmt, Stmt)
  /// e.g. `try { <STMT>* } catch(x) { <STMT>* } finally { <STMT>* }`
  Try(Array[Stmt], JSName, Array[Stmt], Array[Stmt])
  /// e.g. `throw e`
  Throw(Expr)
  /// `label : while (<EXPR>) { <STMT>* }`
  While(Expr, Array[Stmt], JSName?)
  /// e.g. `break`
  Break
  /// e.g. `continue l`
  Continue(JSName?)
  /// e.g. `<EXPR>;`
  ExprStmt(Expr)
}

// ---------------------------------------------------------------------------
// Smart constructors
// ---------------------------------------------------------------------------

///|
/// `raw_expr(str)` is `RawExpr(List(str), Nil)`.
pub fn raw_expr(str : String) -> Expr {
  Expr::RawExpr([str], [])
}

///|
/// `raw_stmt(str)` is `RawStmt(List(str), Nil)`.
pub fn raw_stmt(str : String) -> Stmt {
  Stmt::RawStmt([str], [])
}

///|
/// `name = <binding>`, turning a lambda into a function declaration.
pub fn js_const(name : JSName, binding : Expr) -> Stmt {
  match binding {
    Lambda(params, Block(stmts)) => Stmt::Function(name, params, stmts)
    Lambda(params, stmt) => Stmt::Function(name, params, [stmt])
    _ => Stmt::Const(PatternVariable(name), binding)
  }
}

///|
pub fn js_let(name : JSName, binding : Expr) -> Stmt {
  Stmt::Let(PatternVariable(name), binding)
}

///|
pub fn js_let_multi(names : Array[JSName], binding : Expr) -> Stmt {
  match names.length() {
    0 => Stmt::ExprStmt(binding)
    1 => js_let(names[0], binding)
    _ => Stmt::Let(PatternArray(names.map(n => PatternVariable(n))), binding)
  }
}

///|
pub fn call(receiver : Expr, args : Array[Expr]) -> Expr {
  Expr::Call(receiver, args)
}

///|
pub fn method_call(
  receiver : Expr,
  method : JSName,
  args : Array[Expr],
) -> Expr {
  call(Member(receiver, method), args)
}

///|
/// A lambda whose body is a single returned expression.
pub fn lambda(params : Array[JSName], body : Expr) -> Expr {
  Expr::Lambda(params, Stmt::Return(body))
}

///|
/// A lambda whose body is a list of statements.
pub fn lambda_stmts(
  params : Array[JSName],
  stmts : Array[Stmt],
) -> Expr raise EffektError {
  match stmts.length() {
    0 =>
      raise EffektError::Internal(
        "Lambda should have at least one statement as body",
      )
    1 =>
      match stmts[0] {
        Return(e) => lambda(params, e)
        stmt => Expr::Lambda(params, stmt)
      }
    _ => Expr::Lambda(params, Block(stmts))
  }
}

///|
pub fn js_string(scala_string : String) -> Expr {
  Expr::RawLiteral("\"" + scala_string + "\"")
}

///|
pub fn maybe_block(stmts : Array[Stmt]) -> Stmt {
  match stmts.length() {
    1 => stmts[0]
    _ => Block(stmts)
  }
}

///|
pub fn undefined() -> Expr {
  Expr::RawLiteral("undefined")
}

// ---------------------------------------------------------------------------
// Code generation monad
// ---------------------------------------------------------------------------

///|
/// The code generation monad: a code generator producing a value of type `A`
/// given a continuation that consumes it.
pub(all) struct Binding[A] {
  run : ((A) -> Array[Stmt] raise EffektError) -> Array[Stmt] raise EffektError
}

///|
pub fn[A] pure(a : A) -> Binding[A] {
  { run: k => k(a), }
}

///|
pub fn[A, B] Binding::flat_map(
  self : Binding[A],
  rest : (A) -> Binding[B] raise EffektError,
) -> Binding[B] raise EffektError {
  {
    run: k => {
      (self.run)(a => {
        let next = rest(a)
        (next.run)(k)
      })
    },
  }
}

///|
pub fn[A, B] Binding::map(
  self : Binding[A],
  f : (A) -> B raise EffektError,
) -> Binding[B] raise EffektError {
  self.flat_map(a => pure(f(a)))
}

///|
/// The statements generated so far.
pub fn Binding::stmts(
  self : Binding[Array[Stmt]],
) -> Array[Stmt] raise EffektError {
  (self.run)(x => x)
}

///|
/// The generated statements as a single statement.
pub fn Binding::block(self : Binding[Array[Stmt]]) -> Stmt raise EffektError {
  maybe_block(self.stmts())
}

///|
/// The value of a binding, as an expression.
pub fn Binding::to_expr(self : Binding[Array[Stmt]]) -> Expr raise EffektError {
  match self.stmts() {
    [] =>
      raise EffektError::Internal(
        "Cannot convert an empty binding to an expression",
      )
    [Return(e)] => e
    stmts => call(Expr::Lambda([], Stmt::Block(stmts)), [])
  }
}

///|
pub fn[S, T] traverse(
  l : Array[S],
  f : (S) -> Binding[T] raise EffektError,
) -> Binding[Array[T]] raise EffektError {
  let mut acc : Binding[Array[T]] = pure([])
  for x in l {
    acc = acc.flat_map(xs => f(x).map(v => xs + [v]))
  }
  acc
}
