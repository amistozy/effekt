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
  dedup_syms,
  interface_type_equal,
  canonical_order,
  t_unit,
  t_bool,
  t_int,
  value_type_equal,
  t_top,
  t_bottom,
  constructor_tparams,
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
  type CaptureSetTree,
  type MatchPattern,
  type MatchClause,
  type MatchGuard,
  type ValueArg,
  type IdDef,
  type IdRef,
  type CallTarget,
  type Implementation,
  type Handler,
  type OpClause,
  type ModuleDecl,
  mk_term,
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
