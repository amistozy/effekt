// Names used unqualified throughout the `typer` package.
//
// The upstream type checker is a set of traits with implicit parameters
// (`using Context, Captures`, `given ErrorReporter`). In this port all of that
// is explicit state: a `Typer` value is threaded through every function,
// mirroring the `Context` / `Captures` implicits, and the unification state
// lives in the `Typer` as well.

///|
using @util {type Span, type EffektError}

///|
using @symbols {
  type Sym,
  type Name,
  type ValueType,
  type BlockType,
  type Effects,
  type Captures,
  sym_eq,
  sym_in,
  dedup_syms,
  or_else,
  interface_type_equal,
  canonical_order,
  t_unit,
  t_bool,
  t_int,
  t_double,
  t_string,
  t_top,
  t_bottom,
  constructor_tparams,
  constructor_applied_datatype,
}

///|
using @source {
  type Context,
  type Term,
  type TermKind,
  type Stmt,
  type StmtKind,
  type Def,
  type DefKind,
  type TypeTree,
  type TypeKind,
  type EffectsTree,
  type CaptureSetTree,
  type MatchPattern,
  type PatternKind,
  type MatchClause,
  type MatchGuard,
  type GuardKind,
  type ValueArg,
  type ValueParam,
  type BlockParam,
  type IdDef,
  type IdRef,
  type CallTarget,
  type Implementation,
  type Handler,
  type OpClause,
  type ModuleDecl,
  type LiteralValue,
  type ExternBody,
  mk_term,
  mk_stmt,
  mk_def,
  mk_type,
}

///|
/// The result of type checking: an inferred type together with the effects
/// that the checked tree might perform. Mirrors upstream `case class Result[+T]`
/// with `ConcreteEffects` (see `constraints.mbt` for how these are kept
/// concrete).
pub struct TyRes[T] {
  tpe : T
  effs : Effects
}

///|
pub fn[T] TyRes::new(tpe : T, effs : Effects) -> TyRes[T] {
  { tpe, effs, }
}

///|
/// A call site: everything the type checker needs to know about a `Call`,
/// `Do` or `MethodCall` node to annotate it.
pub struct CallLike {
  uid : Int32
  span : Span
  /// The name of the called thing, for error messages.
  name : String
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

///|
/// Structural equality on value types (upstream `Type` equality).
pub fn value_type_eq(a : ValueType, b : ValueType) -> Bool {
  match (a, b) {
    (@symbols.ValueType::ValueTypeRef(x), @symbols.ValueType::ValueTypeRef(y)) =>
      sym_eq(x, y)
    (
      @symbols.ValueType::ValueTypeApp(c1, args1),
      @symbols.ValueType::ValueTypeApp(c2, args2),
    ) => sym_eq(c1, c2) && value_types_eq(args1, args2)
    (
      @symbols.ValueType::BoxedType(b1, c1),
      @symbols.ValueType::BoxedType(b2, c2),
    ) => block_type_eq(b1, b2) && captures_eq(c1, c2)
    _ => false
  }
}

///|
pub fn value_types_eq(a : Array[ValueType], b : Array[ValueType]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i = 0; i < a.length(); i = i + 1 {
    if !value_type_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
/// Structural equality on block types. Unlike `@symbols.block_type_equal` this
/// also compares function types (needed by the unifier).
pub fn block_type_eq(a : BlockType, b : BlockType) -> Bool {
  match (a, b) {
    (
      @symbols.BlockType::InterfaceType(c1, args1),
      @symbols.BlockType::InterfaceType(c2, args2),
    ) => sym_eq(c1, c2) && value_types_eq(args1, args2)
    (
      @symbols.BlockType::FunctionType(cps1, capts1, vps1, bps1, ret1, effs1),
      @symbols.BlockType::FunctionType(cps2, capts2, vps2, bps2, ret2, effs2),
    ) =>
      syms_eq(cps1, cps2) &&
      captures_list_eq(capts1, capts2) &&
      value_types_eq(vps1, vps2) &&
      block_types_eq(bps1, bps2) &&
      value_type_eq(ret1, ret2) &&
      effects_eq(effs1, effs2)
    _ => false
  }
}

///|
pub fn block_types_eq(a : Array[BlockType], b : Array[BlockType]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i = 0; i < a.length(); i = i + 1 {
    if !block_type_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
pub fn syms_eq(a : Array[Sym], b : Array[Sym]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i = 0; i < a.length(); i = i + 1 {
    if !sym_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
/// Equality on capture sets. Only meaningful once all unification variables
/// have been solved.
pub fn captures_eq(a : Captures, b : Captures) -> Bool {
  match (a, b) {
    (@symbols.Captures::CaptureSetOf(xs), @symbols.Captures::CaptureSetOf(ys)) =>
      xs.all(x => sym_in(x, ys)) && ys.all(y => sym_in(y, xs))
    (@symbols.Captures::CaptVar(x), @symbols.Captures::CaptVar(y)) =>
      sym_eq(x, y)
    _ => false
  }
}

///|
pub fn captures_list_eq(a : Array[Captures], b : Array[Captures]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i = 0; i < a.length(); i = i + 1 {
    if !captures_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
pub fn effects_eq(a : Effects, b : Effects) -> Bool {
  let xs = a.distinct().effects
  let ys = b.distinct().effects
  if xs.length() != ys.length() {
    return false
  }
  xs.all(x => ys.any(y => interface_type_equal(x, y)))
}

// ---------------------------------------------------------------------------
// Function types
// ---------------------------------------------------------------------------

///|
/// In this port, `BlockType::FunctionType` has the shape
///
///     FunctionType(tparams, captures, vparams, bparams, result, effects)
///
/// where `captures` holds one capture set per block parameter and one per
/// effect (see `Sym::annotated_type`). These helpers extract the *capture
/// parameter* of such a slot, which is what instantiation substitutes.
pub fn capture_param_of(c : Captures) -> Sym? {
  match c {
    @symbols.Captures::CaptureSetOf(cs) =>
      if cs.length() == 1 {
        Some(cs[0])
      } else {
        None
      }
    @symbols.Captures::CaptVar(_) => None
  }
}

///|
pub fn capture_params_of(capts : Array[Captures]) -> Array[Sym] {
  let out : Array[Sym] = []
  for c in capts {
    match capture_param_of(c) {
      Some(x) => out.push(x)
      None => ()
    }
  }
  out
}

///|
pub fn captures_of_params(params : Array[Sym]) -> Array[Captures] {
  params.map(p => @symbols.Captures::CaptureSetOf([p]))
}

// ---------------------------------------------------------------------------
// Effects
// ---------------------------------------------------------------------------

///|
pub fn effects_of(effs : Array[BlockType]) -> Effects {
  Effects::new(effs)
}

///|
/// Union of two effect sets, keeping the result duplicate free.
pub fn eff_union(a : Effects, b : Effects) -> Effects {
  a.union(b).distinct()
}

///|
pub fn eff_union_of(effs : Array[Effects]) -> Effects {
  let out : Array[BlockType] = []
  for e in effs {
    for x in e.effects {
      if !out.any(y => interface_type_equal(x, y)) {
        out.push(x)
      }
    }
  }
  Effects::new(out)
}

///|
/// Set difference on effects.
pub fn eff_diff(a : Effects, b : Effects) -> Effects {
  a.filter_not(x => b.exists(y => interface_type_equal(x, y)))
}

///|
pub fn eff_contains(a : Effects, x : BlockType) -> Bool {
  a.exists(y => interface_type_equal(x, y))
}

///|
pub fn show_effects(effs : Effects) -> String {
  let names : Array[String] = []
  for e in effs.distinct().effects {
    names.push(show_block_type(e))
  }
  if names.length() == 0 {
    "{}"
  } else {
    "{" + names.join(", ") + "}"
  }
}

///|
/// A minimal type printer. Upstream has a full `TypePrinter`; the error
/// messages produced here only need to be readable.
pub fn show_value_type(t : ValueType) -> String {
  match t {
    @symbols.ValueType::ValueTypeRef(s) => s.name().qualified_name()
    @symbols.ValueType::ValueTypeApp(c, args) =>
      if args.length() == 0 {
        c.name().qualified_name()
      } else {
        c.name().qualified_name() +
        "[" +
        args.map(show_value_type).join(", ") +
        "]"
      }
    @symbols.ValueType::BoxedType(b, c) =>
      "box " + show_block_type(b) + " at " + show_captures(c)
  }
}

///|
pub fn show_block_type(t : BlockType) -> String {
  match t {
    @symbols.BlockType::InterfaceType(c, args) =>
      if args.length() == 0 {
        c.name().qualified_name()
      } else {
        c.name().qualified_name() +
        "[" +
        args.map(show_value_type).join(", ") +
        "]"
      }
    @symbols.BlockType::FunctionType(_, _, vps, bps, ret, effs) => {
      let all : Array[String] = vps.map(show_value_type)
      for b in bps {
        all.push("{" + show_block_type(b) + "}")
      }
      "(" +
      all.join(", ") +
      ") => " +
      show_value_type(ret) +
      " / " +
      show_effects(effs)
    }
  }
}

///|
pub fn show_captures(c : Captures) -> String {
  match c {
    @symbols.Captures::CaptureSetOf(cs) =>
      "{" + cs.map(s => s.name().qualified_name()).join(", ") + "}"
    @symbols.Captures::CaptVar(x) => "?" + x.name().qualified_name()
  }
}
