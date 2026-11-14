// Core's type language (upstream `core/Type.scala`).
//
// Core has its own types, separate from the source language of `@symbols`:
//
//   ─ [[ Type ]]
//     │─ [[ ValueType ]]  Var | Data | Boxed
//     │─ [[ BlockType ]]  Function | Interface | Prompt | Resume
//
// Two things the source language cannot express are needed by the prompt/shift
// encoding that the transformer produces and the optimizer removes: a function
// type has a *list* of results (a prompt answers with several values), and a
// shift continuation has the resumption type `(result) ~> (answer)` rather than
// a function type — telling the two apart is exactly what `DirectStyle` matches
// on.
//
// Captures stay `@symbols.Captures` (a set of capture symbols): upstream core
// stores a `Set[Symbol]` and the port's capture sets are the same thing with the
// "singleton set for one id" encoding used everywhere else.

///|
/// A core value type (upstream `ValueType`).
#derive(Eq)
pub(all) enum ValueType {
  /// A type variable (upstream `ValueType.Var`).
  ValueVar(Sym)
  /// A data type applied to type arguments (upstream `ValueType.Data`).
  ValueData(Sym, Array[ValueType])
  /// A first-class block together with its captures (upstream `ValueType.Boxed`).
  ValueBoxed(BlockType, Captures)
}

///|
/// A core block type (upstream `BlockType`).
#derive(Eq)
pub(all) enum BlockType {
  /// `[tparams](cparams)(vparams){bparams} => (result)`.
  ///
  /// `cparams` holds one capture per block parameter, as everywhere in the port.
  FunctionType(
    Array[Sym],
    Array[Captures],
    Array[ValueType],
    Array[BlockType],
    Array[ValueType]
  )
  /// An effect / capability type, e.g. `State[Int]` (upstream `Interface`).
  InterfaceType(Sym, Array[ValueType])
  /// `Prompt[(answer)]`, the type of the prompt that a `reset` binds.
  PromptType(Array[ValueType])
  /// `(result) ~> (answer)`, the type of a shift continuation.
  ResumeType(Array[ValueType], Array[ValueType])
}

// ---------------------------------------------------------------------------
// The built-in types (upstream `Type.TUnit` and friends)
// ---------------------------------------------------------------------------

///|
pub fn t_unit() -> ValueType {
  ValueData(@symbols.unit_type_sym(), [])
}

///|
pub fn t_bool() -> ValueType {
  ValueData(@symbols.bool_type_sym(), [])
}

///|
pub fn t_int() -> ValueType {
  ValueData(@symbols.int_type_sym(), [])
}

///|
pub fn t_double() -> ValueType {
  ValueData(@symbols.double_type_sym(), [])
}

///|
pub fn t_string() -> ValueType {
  ValueData(@symbols.string_type_sym(), [])
}

///|
pub fn t_char() -> ValueType {
  ValueData(@symbols.char_type_sym(), [])
}

///|
pub fn t_byte() -> ValueType {
  ValueData(@symbols.byte_type_sym(), [])
}

///|
/// `Any` (upstream `TTop`).
pub fn t_top() -> ValueType {
  ValueData(@symbols.top_type_sym(), [])
}

///|
/// `Nothing` (upstream `TBottom`), the type of a call that never returns.
pub fn t_bottom() -> ValueType {
  ValueData(@symbols.bottom_type_sym(), [])
}

///|
/// `Region` (upstream `TRegion`).
pub fn t_region() -> BlockType {
  InterfaceType(@symbols.region_type_sym(), [])
}

///|
/// `State[tpe]` (upstream `Type.TState`).
pub fn t_state(tpe : ValueType) -> BlockType {
  InterfaceType(@symbols.state_effect_sym(), [tpe])
}

///|
/// The `tpe` of `State[tpe]`, if this is one (upstream `Type.TState.unapply`).
pub fn t_state_extract(tpe : BlockType) -> ValueType? {
  match tpe {
    InterfaceType(sym, [arg]) =>
      if sym == @symbols.state_effect_sym() {
        Some(arg)
      } else {
        None
      }
    _ => None
  }
}

// ---------------------------------------------------------------------------
// Structural equality and printing
// ---------------------------------------------------------------------------

///|
/// The surface rendering of a type application: `Name` or `Name[A, B]`.
fn show_type_application(name : Name, args : Array[ValueType]) -> String {
  if args.length() == 0 {
    name.name
  } else {
    "\{name.name}[\{args.map(a => "\{a}").join(", ")}]"
  }
}

///|
/// A parenthesized type list, `(A, B)`; a single type prints bare.
fn show_type_list(tpes : Array[ValueType]) -> String {
  tpes.map(t => "\{t}").join(", ")
}

///|
/// Core types print like the source ones (`@symbols`' `Show`), plus the two
/// constructors core has in addition.
pub impl Show for ValueType with fn output(self, logger) {
  match self {
    ValueVar(sym) => logger.write_string(sym.name().name)
    ValueData(sym, args) =>
      logger.write_string(show_type_application(sym.name(), args))
    ValueBoxed(tpe, capt) => logger.write_string("\{tpe} at \{capt}")
  }
}

///|
pub impl Show for BlockType with fn output(self, logger) {
  match self {
    InterfaceType(sym, args) =>
      logger.write_string(show_type_application(sym.name(), args))
    PromptType(answer) =>
      logger.write_string("Prompt[(\{show_type_list(answer)})]")
    ResumeType(result, answer) =>
      logger.write_string(
        "(\{show_type_list(result)}) ~> (\{show_type_list(answer)})",
      )
    FunctionType(tparams, _, vps, bps, result) => {
      // Same layout as `@symbols`' `Show` for function types: a single value
      // parameter prints without parentheses unless the function binds type
      // parameters, and block parameters follow in braces.
      let params = if vps.length() == 0 && bps.length() == 0 {
        "()"
      } else if bps.length() == 0 && vps.length() == 1 {
        if tparams.length() == 0 {
          "\{vps[0]}"
        } else {
          "(\{vps[0]})"
        }
      } else {
        let value_params = if vps.length() == 0 {
          ""
        } else {
          "(\{vps.map(v => "\{v}").join(", ")})"
        }
        let block_params = bps.map(b => "{\{b}}").join("")
        "\{value_params}\{block_params}"
      }
      let results = if result.length() == 1 {
        "\{result[0]}"
      } else {
        "(\{show_type_list(result)})"
      }
      let type_params = if tparams.length() == 0 {
        ""
      } else {
        "[\{tparams.map(t => t.name().name).join(", ")}]"
      }
      logger.write_string("\{type_params}\{params} => \{results}")
    }
  }
}

// ---------------------------------------------------------------------------
// Operations on types (upstream `Type.*`)
// ---------------------------------------------------------------------------

///|
/// Upstream `Type.single`: expressions (and thus FFI calls) produce exactly one
/// value.
pub fn single(tpes : Array[ValueType]) -> ValueType raise EffektError {
  if tpes.length() == 1 {
    return tpes[0]
  }
  raise EffektError::Internal(
    "Expected exactly one value, but got: \{show_type_list(tpes)}",
  )
}

///|
/// Upstream `Type.instantiate`: substitutes the type and capture arguments of a
/// function type and drops the parameters, which the arguments have bound.
pub fn instantiate(
  tpe : BlockType,
  targs : Array[ValueType],
  cargs : Array[Captures],
) -> BlockType raise EffektError {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result) => {
      if targs.length() != tparams.length() {
        raise EffektError::Internal(
          "Wrong number of type arguments: expected \{tparams.length()}, got \{targs.length()}",
        )
      }
      if cargs.length() != cparams.length() {
        raise EffektError::Internal(
          "Wrong number of capture arguments: expected \{cparams.length()}, got \{cargs.length()}",
        )
      }
      let tsubst : Map[Int32, ValueType] = Map([])
      for i = 0; i < tparams.length(); i = i + 1 {
        tsubst.set(tparams[i].uid(), targs[i])
      }
      let csubst : Map[Int32, Captures] = Map([])
      for i = 0; i < cparams.length(); i = i + 1 {
        // A capture parameter is a (usually singleton) capture set here, while
        // upstream stores the id directly.
        for c in cparams[i].to_array() {
          csubst.set(c.uid(), cargs[i])
        }
      }
      FunctionType(
        [],
        [],
        vparams.map(t => substitute_value_type_with(t, tsubst, Map([]))),
        bparams.map(t => substitute_block_type_with(t, tsubst, Map([]))),
        result.map(t => substitute_value_type_with(t, tsubst, csubst)),
      )
    }
    _ =>
      raise EffektError::Internal("Expected a function type, but got: \{tpe}")
  }
}

///|
/// The ids occurring in a list of capture sets. In `@symbols` the capture
/// parameters of a function type are stored as (singleton) capture sets, while
/// upstream core stores the ids directly.
fn capture_ids(cs : Array[Captures]) -> Array[Sym] {
  let out : Array[Sym] = []
  for c in cs {
    for x in c.to_array() {
      out.push(x)
    }
  }
  out
}

///|
/// Upstream `Type.substitute` on value types.
pub fn substitute_value_type_with(
  tpe : ValueType,
  vsubst : Map[Int32, ValueType],
  csubst : Map[Int32, Captures],
) -> ValueType {
  match tpe {
    ValueVar(sym) =>
      match vsubst.get(sym.uid()) {
        Some(replacement) => replacement
        None => tpe
      }
    ValueData(sym, targs) =>
      ValueData(
        sym,
        targs.map(t => substitute_value_type_with(t, vsubst, csubst)),
      )
    ValueBoxed(block, capt) =>
      ValueBoxed(
        substitute_block_type_with(block, vsubst, csubst),
        substitute_captures_with(capt, csubst),
      )
  }
}

///|
/// Upstream `Type.substitute` on block types.
pub fn substitute_block_type_with(
  tpe : BlockType,
  vsubst : Map[Int32, ValueType],
  csubst : Map[Int32, Captures],
) -> BlockType {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result) => {
      // Names are unique symbols, so shadowing should NOT take place; we still
      // subtract to be safe.
      let vsubst_local = shadowed(vsubst, tparams)
      let csubst_local = shadowed(csubst, capture_ids(cparams))
      FunctionType(
        tparams,
        cparams,
        // technically, in the source, cparams are not bound in value arguments
        vparams.map(t => substitute_value_type_with(t, vsubst_local, csubst)),
        bparams.map(t => {
          substitute_block_type_with(t, vsubst_local, csubst_local)
        }),
        result.map(t => {
          substitute_value_type_with(t, vsubst_local, csubst_local)
        }),
      )
    }
    InterfaceType(sym, targs) =>
      InterfaceType(
        sym,
        targs.map(t => substitute_value_type_with(t, vsubst, csubst)),
      )
    PromptType(answer) =>
      PromptType(answer.map(t => substitute_value_type_with(t, vsubst, csubst)))
    ResumeType(result, answer) =>
      ResumeType(
        result.map(t => substitute_value_type_with(t, vsubst, csubst)),
        answer.map(t => substitute_value_type_with(t, vsubst, csubst)),
      )
  }
}
