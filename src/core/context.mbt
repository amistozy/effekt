// Context for transformations of a core module.
//
// Mirrors `effekt/core/DeclarationContext.scala`: provides the declarations of
// the module being transformed. The `find*` methods return `Option`, the `get*`
// methods raise `EffektError` when no matching declaration can be found.
//
// Upstream lazily caches all declarations in maps; since MoonBit maps are
// mutable, we build them eagerly in `DeclarationContext`.

///|
pub(all) struct ConstructorRef {
  /// The data declaration this constructor belongs to.
  data : Declaration
  constructor : Constructor
}

///|
pub(all) struct DeclarationContext {
  declarations : Array[Declaration]
  externs : Array[Extern]
  /// uid -> index into `declarations`
  datas : Map[Int32, Int32]
  /// uid -> constructor
  constructors : Map[Int32, ConstructorRef]
  /// uid -> index into `externs`
  extern_defs : Map[Int32, Int32]
  /// "name(t1, t2)" -> index into `externs`
  extern_defs_by_name : Map[String, Int32]
}

///|
fn extern_def_key(name : String, params : ArrayView[ValueType]) -> String {
  let rendered : Array[String] = params.map(show_core_value_type)
  "\{name}(\{rendered.join(", ")})"
}

///|
pub fn DeclarationContext::DeclarationContext(
  declarations : Array[Declaration],
  externs : Array[Extern],
) -> DeclarationContext {
  let datas : Map[Int32, Int32] = Map([])
  let constructors : Map[Int32, ConstructorRef] = Map([])
  for i, d in declarations {
    if d is DeclarationData(id, _, ctors) {
      datas.set(id.uid(), i)
      for c in ctors {
        constructors.set(c.id.uid(), { data: d, constructor: c, })
      }
    }
  }
  let extern_defs : Map[Int32, Int32] = Map([])
  let extern_defs_by_name : Map[String, Int32] = Map([])
  for i, e in externs {
    match e {
      ExternDef(id, _, _, _, vparams, _, _, _, _) => {
        extern_defs.set(id.uid(), i)
        extern_defs_by_name.set(
          extern_def_key(id.name().name, vparams.map(p => p.tpe)),
          i,
        )
      }
      _ => ()
    }
  }
  {
    declarations,
    externs,
    datas,
    constructors,
    extern_defs,
    extern_defs_by_name,
  }
}

///|
/// Raises an internal error; the polymorphic result type lets it stand in for
/// any expected value (upstream's `Context.panic`).
fn[T] panic(msg : String) -> T raise EffektError {
  raise EffektError::Internal(msg)
}

// Lookups
// -------

///|
fn DeclarationContext::find_data(
  self : DeclarationContext,
  id : Sym,
) -> Declaration? {
  self.datas.get(id.uid()).map(i => self.declarations[i])
}

///|
fn DeclarationContext::find_constructor(
  self : DeclarationContext,
  id : Sym,
) -> Constructor? {
  self.constructors.get(id.uid()).map(ref => ref.constructor)
}

///|
fn DeclarationContext::find_constructor_tag(
  self : DeclarationContext,
  id : Sym,
) -> Int32? {
  self.constructors
  .get(id.uid())
  .bind(ref => {
    match ref.data {
      DeclarationData(_, _, ctors) =>
        ctors.search_by(c => c.id.uid() == ref.constructor.id.uid())
      _ => None
    }
  })
}

///|
fn DeclarationContext::find_extern_def_by_name(
  self : DeclarationContext,
  name : String,
  params : ArrayView[ValueType],
) -> Extern? {
  self.extern_defs_by_name
  .get(extern_def_key(name, params))
  .map(i => self.externs[i])
}

// Panicking lookups
// -----------------

///|
pub fn DeclarationContext::get_constructor(
  self : DeclarationContext,
  id : Sym,
) -> Constructor raise EffektError {
  match self.find_constructor(id) {
    Some(c) => c
    None => panic("No declaration found for constructor \{id.name().name}.")
  }
}

///|
pub fn DeclarationContext::get_constructor_tag(
  self : DeclarationContext,
  id : Sym,
) -> Int32 raise EffektError {
  match self.find_constructor_tag(id) {
    Some(tag) => tag
    None => panic("No declaration found for constructor \{id.name().name}.")
  }
}

// Qualified signatures
// --------------------

///|
/// Builds the qualified signature of an extern function, e.g.
/// `mymodule::externFun[Int](Int, String){Int}`.
fn QualifiedSignature::from_extern_function(
  module_name : String,
  f : Sym,
) -> QualifiedSignature {
  let callable = f.as_callable()
  match callable {
    None => QualifiedSignature("\{module_name}::\{f.name().name}")
    Some(c) => {
      let tps = if c.tparams.is_empty() {
        ""
      } else {
        "[\{c.tparams.map(t => show_core_value_type(ValueVar(t))).join(", ")}]"
      }
      let value_params = c.vparams.map(p => "\{value_param_type(p)}").join(", ")
      let vps = if value_params == "" { "" } else { "(\{value_params})" }
      let bps = c.bparams.map(b => "{\{block_param_type(b)}}").join("")
      let ps = if vps == "" && bps == "" { "()" } else { vps + bps }
      QualifiedSignature("\{module_name}::\{f.name().name}\{tps}\{ps}")
    }
  }
}

///|
/// The *source* type annotated on a value parameter, for the signature string
/// (which is printed as written, not as a core type).
fn value_param_type(p : Sym) -> @symbols.ValueType {
  match p {
    ValueParam(vp) =>
      match vp.tpe {
        Some(t) => t
        None => @symbols.t_top()
      }
    _ => @symbols.t_top()
  }
}

///|
fn block_param_type(p : Sym) -> @symbols.BlockType {
  match p {
    BlockParam(bp) =>
      match bp.tpe {
        Some(t) => t
        None => @symbols.t_io()
      }
    _ => @symbols.t_io()
  }
}
