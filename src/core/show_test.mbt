// Tests for the `show` phase.
//
// The core modules are built by hand: a prelude-shaped module with
// `show`, `showBuiltin` and `infixPlusPlus` externs, a two-constructor data
// type and a call to `show`.

///|
struct ShowFixture {
  module : @core.ModuleDecl
  /// `extern def show[R](value: R): String`
  show : @symbols.Sym
  /// `extern def showBuiltin(value: Int): String`
  show_builtin : @symbols.Sym
  /// `extern def infixPlusPlus(s1: String, s2: String): String`
  concat : @symbols.Sym
  /// The symbol of the data type and of its two constructors, and the type
  /// `Tree` itself.
  tree : @symbols.Sym
  leaf : @symbols.Sym
  node : @symbols.Sym
  tree_type : @symbols.ValueType
  /// The definition that contains the call to `show`.
  entry : @symbols.Sym
  /// The `show[T](value)` call that the phase is supposed to rewrite.
  call : @core.Expr
}

///|
fn show_test_base(name : String) -> @symbols.SymBase {
  {
    uid: @util.fresh_uid(),
    name: @symbols.Name::local(name),
    decl: @util.Span::missing(),
  }
}

///|
fn show_test_extern_sym(
  name : String,
  tparams : Array[@symbols.Sym],
  vparams : Array[@core.ValueParam],
  result : @symbols.ValueType,
) -> @symbols.Sym {
  @symbols.Sym::ExternFunction({
    base: show_test_base(name),
    tparams,
    vparams: vparams.map(p => p.id),
    bparams: [],
    result,
    effects: @symbols.Effects::empty(),
    capture: [],
  })
}

///|
fn show_test_extern(
  sym : @symbols.Sym,
  tparams : Array[@symbols.Sym],
  vparams : Array[@core.ValueParam],
  result : @symbols.ValueType,
) -> @core.Extern {
  @core.ExternDef(
    sym,
    @core.QualifiedSignature::new("test::\{sym.name().name}"),
    tparams,
    [],
    vparams,
    [],
    result,
    @symbols.CaptureSetOf([]),
    @core.Unsupported(@util.EffektError::Internal("test extern")),
  )
}

///|
/// `type Tree { Leaf(v: Int); Node(l: Tree, r: Tree) }`, its declaration and
/// the symbols of its constructors.
fn show_test_tree() -> (
  @symbols.Sym,
  Array[@symbols.Sym],
  Array[@core.Constructor],
) {
  let tree = @symbols.Sym::DataType({
    base: show_test_base("Tree"),
    tparams: [],
    constructors: [],
  })
  let tree_tpe = @symbols.ValueTypeApp(tree, [])
  let leaf = @symbols.Sym::Constructor({
    base: show_test_base("Leaf"),
    tparams: [],
    fields: [],
    tpe: tree,
  })
  let node = @symbols.Sym::Constructor({
    base: show_test_base("Node"),
    tparams: [],
    fields: [],
    tpe: tree,
  })
  let field_v = @symbols.Sym::Field({
    base: show_test_base("v"),
    param: @symbols.Sym::value_param(
      @symbols.Name::local("v"),
      Some(@symbols.t_int()),
      @util.Span::missing(),
    ),
    constructor: leaf,
  })
  let field_l = @symbols.Sym::Field({
    base: show_test_base("l"),
    param: @symbols.Sym::value_param(
      @symbols.Name::local("l"),
      Some(tree_tpe),
      @util.Span::missing(),
    ),
    constructor: node,
  })
  let field_r = @symbols.Sym::Field({
    base: show_test_base("r"),
    param: @symbols.Sym::value_param(
      @symbols.Name::local("r"),
      Some(tree_tpe),
      @util.Span::missing(),
    ),
    constructor: node,
  })
  let constructors : Array[@core.Constructor] = [
    @core.Constructor::new(leaf, [], [
      @core.Field::new(field_v, @symbols.t_int()),
    ]),
    @core.Constructor::new(node, [], [
      @core.Field::new(field_l, tree_tpe),
      @core.Field::new(field_r, tree_tpe),
    ]),
  ]
  (tree, [leaf, node], constructors)
}

///|
/// A module with the prelude's show externs, a `Tree` declaration and one
/// definition whose body is `return show(args)`.
///
/// `targs_of` computes the type arguments of the call from the type `Tree` of
/// the shown value: upstream's `Show` reads the inferred type arguments, while
/// `core.transform` produces calls without any (see `show_type_argument`).
fn show_test_fixture(
  targs_of : (@symbols.ValueType) -> Array[@symbols.ValueType],
) -> ShowFixture {
  let show = show_test_extern_sym("show", [], [], @symbols.t_string())
  let show_builtin = show_test_extern_sym(
    "showBuiltin",
    [],
    [],
    @symbols.t_string(),
  )
  let concat = show_test_extern_sym(
    "infixPlusPlus",
    [],
    [],
    @symbols.t_string(),
  )
  let (tree, constructors_syms, constructors) = show_test_tree()
  let tree_type = @symbols.ValueTypeApp(tree, [])

  // extern def show[R](value: R): String
  let r = @symbols.Sym::type_param(
    @symbols.Name::local("R"),
    @util.Span::missing(),
  )
  let r_param = @core.ValueParam::new(
    @symbols.Sym::value_param(
      @symbols.Name::local("value"),
      Some(@symbols.ValueTypeRef(r)),
      @util.Span::missing(),
    ),
    @symbols.ValueTypeRef(r),
  )
  // extern def showBuiltin(value: Int): String
  let int_param = @core.ValueParam::new(
    @symbols.Sym::value_param(
      @symbols.Name::local("value"),
      Some(@symbols.t_int()),
      @util.Span::missing(),
    ),
    @symbols.t_int(),
  )
  // extern def infixPlusPlus(s1: String, s2: String): String
  let str_param = fn(name : String) {
    @core.ValueParam::new(
      @symbols.Sym::value_param(
        @symbols.Name::local(name),
        Some(@symbols.t_string()),
        @util.Span::missing(),
      ),
      @symbols.t_string(),
    )
  }
  let externs : Array[@core.Extern] = [
    show_test_extern(show, [r], [r_param], @symbols.t_string()),
    show_test_extern(show_builtin, [], [int_param], @symbols.t_string()),
    show_test_extern(
      concat,
      [],
      [str_param("s1"), str_param("s2")],
      @symbols.t_string(),
    ),
  ]

  // the argument of the show call
  let value = @symbols.Sym::value_param(
    @symbols.Name::local("t"),
    Some(tree_type),
    @util.Span::missing(),
  )
  let call = @core.PureApp(
    @core.BlockVar::new(
      show,
      @symbols.FunctionType(
        [],
        [],
        [@symbols.ValueTypeRef(r)],
        [],
        @symbols.t_string(),
        @symbols.Effects::empty(),
      ),
      @symbols.CaptureSetOf([]),
    ),
    targs_of(tree_type),
    [@core.ValueVar(value, tree_type)],
  )

  // def entry(t: Tree): String = return show(t)
  let entry = @symbols.Sym::UserFunction({
    base: show_test_base("entry"),
    tparams: [],
    vparams: [value],
    bparams: [],
    annotated_captures: None,
    annotated_result: Some(@symbols.t_string()),
    annotated_effects: None,
  })
  let entry_def = @core.ToplevelDef(
    entry,
    @core.BlockLit(
      @core.BlockLit::new(
        [],
        [],
        [@core.ValueParam::new(value, tree_type)],
        [],
        @core.Return(call),
      ),
    ),
  )
  let module = @core.ModuleDecl::new(
    "test",
    [],
    [@core.DeclarationData(tree, [], constructors)],
    externs,
    [entry_def],
    [],
  )
  {
    module,
    show,
    show_builtin,
    concat,
    tree,
    leaf: constructors_syms[0],
    node: constructors_syms[1],
    tree_type,
    entry,
    call,
  }
}

///|
/// The show instance the phase generated for a parameter of the given type.
///
/// The generated definitions are appended after the definitions of the module,
/// so the ones at the front (here: the single `entry`) are skipped.
fn show_test_instance_def(
  f : ShowFixture,
  out : @core.ModuleDecl,
  tpe : @symbols.ValueType,
) -> (@symbols.Sym, @core.BlockLit)? {
  for i = f.module.definitions.length(); i < out.definitions.length(); i = i + 1 {
    match out.definitions[i] {
      @core.ToplevelDef(id, @core.BlockLit(lit)) =>
        if lit.vparams.length() == 1 &&
          @symbols.value_type_equal(lit.vparams[0].tpe, tpe) {
          return Some((id, lit))
        }
      _ => ()
    }
  }
  None
}

///|
/// See [[show_test_instance_def]].
fn show_test_instance_for(
  f : ShowFixture,
  out : @core.ModuleDecl,
  tpe : @symbols.ValueType,
) -> @core.BlockLit {
  match show_test_instance_def(f, out, tpe) {
    Some((_, lit)) => lit
    None =>
      abort(
        "no show instance was generated for \{@core.show_core_value_type(tpe)}",
      )
  }
}

///|
/// See [[show_test_instance_def]].
fn show_test_instance_id(
  f : ShowFixture,
  out : @core.ModuleDecl,
  tpe : @symbols.ValueType,
) -> @symbols.Sym {
  match show_test_instance_def(f, out, tpe) {
    Some((id, _)) => id
    None =>
      abort(
        "no show instance was generated for \{@core.show_core_value_type(tpe)}",
      )
  }
}

///|
/// The id of the definition the call in `entry` was rewritten to.
fn show_test_callee(f : ShowFixture, out : @core.ModuleDecl) -> @symbols.Sym {
  match out.definitions[0] {
    @core.ToplevelDef(_, @core.BlockLit(lit)) =>
      match lit.body {
        @core.Val(_, @core.App(@core.BlockVar(callee), _, _, _), _) => callee.id
        other =>
          abort(
            "expected Val(_, App(show0, ...), _), got \{@core.show_core_stmt(other)}",
          )
      }
    _ => abort("expected a toplevel block definition")
  }
}

// ---------------------------------------------------------------------------
// Rewriting the call
// ---------------------------------------------------------------------------

///|
test "show phase: generates a structural instance and rewrites the call" {
  let f = show_test_fixture(fn(t) { [t] })
  let out = @core.show_phase(f.module)
  // the declarations are carried over unchanged
  assert_eq(out.declarations.length(), 1)
  assert_eq(out.declarations[0].id().uid(), f.tree.uid())
  // two definitions are appended: one for `Tree` and the one its `Leaf` field
  // needs for `Int`
  assert_eq(out.definitions.length(), f.module.definitions.length() + 2)
  let tree_id = show_test_instance_id(f, out, f.tree_type)
  let _ = show_test_instance_for(f, out, @symbols.t_int())
  // the call is rewritten to a call of the generated instance, with the
  // `showApp` binding emitted in front of the statement
  let callee = show_test_callee(f, out)
  match out.definitions[0] {
    @core.ToplevelDef(_, @core.BlockLit(lit)) =>
      match lit.body {
        @core.Val(
          _,
          @core.App(_, targs, vargs, bargs),
          @core.Return(@core.ValueVar(_, _))
        ) => {
          assert_eq(targs.length(), 0)
          assert_eq(vargs.length(), 1)
          assert_eq(bargs.length(), 0)
        }
        other =>
          abort(
            "expected Val(showApp, ...), got \{@core.show_core_stmt(other)}",
          )
      }
    _ => abort("expected a toplevel block definition")
  }
  // ... and the callee is the generated instance, not the extern
  assert_true(callee.uid() != f.show.uid())
  assert_eq(callee.uid(), tree_id.uid())
}

///|
test "show phase: the generated instance matches on the constructors" {
  let f = show_test_fixture(fn(t) { [t] })
  let out = @core.show_phase(f.module)
  let lit = show_test_instance_for(f, out, f.tree_type)
  assert_eq(lit.tparams.length(), 0)
  assert_eq(lit.vparams.length(), 1)
  match lit.body {
    @core.Match(@core.ValueVar(id, _), _, clauses, None) => {
      assert_eq(id.uid(), lit.vparams[0].id.uid())
      assert_eq(clauses.length(), 2)
      assert_eq(clauses[0].tag.uid(), f.leaf.uid())
      assert_eq(clauses[1].tag.uid(), f.node.uid())
      // `Leaf(v)` shows its field to a temporary
      assert_true(clauses[0].body.body is @core.Val(_, _, _))
    }
    other => abort("expected a match, got \{@core.show_core_stmt(other)}")
  }
  // the fields are shown with `showBuiltin` / concatenated with `infixPlusPlus`
  let rendered = @core.show_core(out)
  assert_true(rendered.contains("showBuiltin"))
  assert_true(rendered.contains("infixPlusPlus"))
  let int_lit = show_test_instance_for(f, out, @symbols.t_int())
  match int_lit.body {
    @core.ImpureApp(_, callee, _, _, _, @core.Return(_)) =>
      assert_eq(callee.id.uid(), f.show_builtin.uid())
    other =>
      abort(
        "expected an impure application of showBuiltin, got \{@core.show_core_stmt(other)}",
      )
  }
}

// ---------------------------------------------------------------------------
// Recovering the shown type
// ---------------------------------------------------------------------------

///|
test "show phase: without type arguments the shown type is recovered from the argument" {
  // `core.transform` produces calls without type arguments, because
  // `ExplicitCapabilities` rebuilds the call node and the typer's annotation is
  // keyed by uid.
  let f = show_test_fixture(fn(_t) { [] })
  let out = @core.show_phase(f.module)
  // the same instances are generated for `Tree` and its `Int` field as with
  // explicit type arguments
  assert_eq(out.definitions.length(), f.module.definitions.length() + 2)
  let callee = show_test_callee(f, out)
  assert_eq(callee.uid(), show_test_instance_id(f, out, f.tree_type).uid())
}

///|
test "show phase: a type variable is not rewritten" {
  let f = show_test_fixture(fn(_t) { [] })
  // `def entry[A](x: A): String = return show(x)`
  let a = @symbols.Sym::type_param(
    @symbols.Name::local("A"),
    @util.Span::missing(),
  )
  let polymorphic = @symbols.Sym::value_param(
    @symbols.Name::local("x"),
    Some(@symbols.ValueTypeRef(a)),
    @util.Span::missing(),
  )
  let call = @core.PureApp(
    match f.call {
      @core.PureApp(callee, _, _) => callee
      _ => abort("expected a pure application")
    },
    [],
    [@core.ValueVar(polymorphic, @symbols.ValueTypeRef(a))],
  )
  let module = @core.ModuleDecl::new(
    f.module.path,
    f.module.includes,
    f.module.declarations,
    f.module.externs,
    [
      @core.ToplevelDef(
        f.entry,
        @core.BlockLit(
          @core.BlockLit::new(
            [],
            [],
            [@core.ValueParam::new(polymorphic, @symbols.ValueTypeRef(a))],
            [],
            @core.Return(call),
          ),
        ),
      ),
    ],
    f.module.exports,
  )
  let out = @core.show_phase(module)
  // no instance can be generated, the extern call is left alone
  assert_eq(out.definitions.length(), 1)
  match out.definitions[0] {
    @core.ToplevelDef(_, @core.BlockLit(lit)) =>
      match lit.body {
        @core.Return(@core.PureApp(callee, _, vargs)) => {
          assert_eq(callee.id.uid(), f.show.uid())
          assert_eq(vargs.length(), 1)
        }
        other =>
          abort(
            "expected the extern call to be untouched, got \{@core.show_core_stmt(other)}",
          )
      }
    _ => abort("expected a toplevel block definition")
  }
}

///|
test "show phase: a call to a user function named show is not rewritten" {
  let f = show_test_fixture(fn(_t) { [] })
  // `def show(value: Int): String` — like `examples/minilib`
  let user_show = @symbols.Sym::UserFunction({
    base: show_test_base("show"),
    tparams: [],
    vparams: [],
    bparams: [],
    annotated_captures: None,
    annotated_result: Some(@symbols.t_string()),
    annotated_effects: None,
  })
  let x = @symbols.Sym::value_param(
    @symbols.Name::local("x"),
    Some(@symbols.t_int()),
    @util.Span::missing(),
  )
  let call = @core.PureApp(
    @core.BlockVar::new(
      user_show,
      @symbols.FunctionType(
        [],
        [],
        [@symbols.t_int()],
        [],
        @symbols.t_string(),
        @symbols.Effects::empty(),
      ),
      @symbols.CaptureSetOf([]),
    ),
    [],
    [@core.ValueVar(x, @symbols.t_int())],
  )
  let module = @core.ModuleDecl::new(
    f.module.path,
    f.module.includes,
    f.module.declarations,
    f.module.externs,
    [
      @core.ToplevelDef(
        f.entry,
        @core.BlockLit(
          @core.BlockLit::new(
            [],
            [],
            [@core.ValueParam::new(x, @symbols.t_int())],
            [],
            @core.Return(call),
          ),
        ),
      ),
    ],
    f.module.exports,
  )
  let out = @core.show_phase(module)
  assert_eq(out.definitions.length(), 1)
  match out.definitions[0] {
    @core.ToplevelDef(_, @core.BlockLit(lit)) =>
      match lit.body {
        @core.Return(@core.PureApp(callee, _, _)) =>
          assert_eq(callee.id.uid(), user_show.uid())
        other =>
          abort(
            "expected the user call to be untouched, got \{@core.show_core_stmt(other)}",
          )
      }
    _ => abort("expected a toplevel block definition")
  }
}

// ---------------------------------------------------------------------------
// Builtins and required names
// ---------------------------------------------------------------------------

///|
test "show phase: builtins are shown by showBuiltin" {
  let f = show_test_fixture(fn(_t) { [] })
  let x = @symbols.Sym::value_param(
    @symbols.Name::local("x"),
    Some(@symbols.t_int()),
    @util.Span::missing(),
  )
  let call = @core.PureApp(
    match f.call {
      @core.PureApp(callee, _, _) => callee
      _ => abort("expected a pure application")
    },
    [],
    [@core.ValueVar(x, @symbols.t_int())],
  )
  let module = @core.ModuleDecl::new(
    f.module.path,
    f.module.includes,
    f.module.declarations,
    f.module.externs,
    [
      @core.ToplevelDef(
        f.entry,
        @core.BlockLit(
          @core.BlockLit::new(
            [],
            [],
            [@core.ValueParam::new(x, @symbols.t_int())],
            [],
            @core.Return(call),
          ),
        ),
      ),
    ],
    f.module.exports,
  )
  let out = @core.show_phase(module)
  assert_eq(out.definitions.length(), f.module.definitions.length() + 1)
  // the instance for `Int` calls `showBuiltin`
  let lit = show_test_instance_for(f, out, @symbols.t_int())
  match lit.body {
    @core.ImpureApp(_, callee, _, _, _, @core.Return(_)) =>
      assert_eq(callee.id.uid(), f.show_builtin.uid())
    other =>
      abort(
        "expected an impure application of showBuiltin, got \{@core.show_core_stmt(other)}",
      )
  }
}

///|
test "show phase: requiredNames keeps show, showBuiltin and infixPlusPlus" {
  let f = show_test_fixture(fn(_t) { [] })
  let names = @core.required_names(f.module)
  assert_eq(names.length(), 3)
  assert_true(@symbols.sym_in(f.show, names))
  assert_true(@symbols.sym_in(f.show_builtin, names))
  assert_true(@symbols.sym_in(f.concat, names))
}
