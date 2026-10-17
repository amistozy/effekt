// Context for transformations of a core module.
//
// Mirrors `effekt/core/DeclarationContext.scala`: provides the declarations of
// the module being transformed. The `find*` methods return `Option`, the `get*`
// methods raise `EffektError` when no matching declaration can be found.
//
// Upstream lazily caches all declarations in maps; since MoonBit maps are
// mutable, we build them eagerly in `DeclarationContext::new`.

///|
pub(all) struct ConstructorRef {
  /// The data declaration this constructor belongs to.
  data : Declaration
  constructor_ : Constructor
}

///|
pub(all) struct FieldRef {
  constructor_ref : ConstructorRef
  field : Field
}

///|
pub(all) struct PropertyRef {
  /// The interface declaration this property belongs to.
  interface : Declaration
  property : Property
}

///|
pub(all) struct DeclarationContext {
  declarations : Array[Declaration]
  externs : Array[Extern]
  /// uid -> index into `declarations`
  datas : Map[Int32, Int32]
  /// uid -> index into `declarations`
  interfaces : Map[Int32, Int32]
  /// uid -> constructor
  constructors : Map[Int32, ConstructorRef]
  /// uid -> field
  fields : Map[Int32, FieldRef]
  /// uid -> property
  properties : Map[Int32, PropertyRef]
  /// uid -> index into `externs`
  extern_defs : Map[Int32, Int32]
  /// uid -> index into `externs`
  extern_datas : Map[Int32, Int32]
  /// "name(t1, t2)" -> index into `externs`
  extern_defs_by_name : Map[String, Int32]
}

///|
fn extern_def_key(name : String, params : Array[ValueType]) -> String {
  let rendered : Array[String] = params.map(show_core_value_type)
  "\{name}(\{rendered.join(", ")})"
}

///|
pub fn DeclarationContext::new(
  declarations : Array[Declaration],
  externs : Array[Extern],
) -> DeclarationContext {
  let datas : Map[Int32, Int32] = Map([])
  let interfaces : Map[Int32, Int32] = Map([])
  let constructors : Map[Int32, ConstructorRef] = Map([])
  let fields : Map[Int32, FieldRef] = Map([])
  let properties : Map[Int32, PropertyRef] = Map([])
  for i = 0; i < declarations.length(); i = i + 1 {
    match declarations[i] {
      DeclarationData(id, _, ctors) => {
        datas.set(id.uid(), i)
        for c in ctors {
          let ref_ = { data: declarations[i], constructor_: c, }
          constructors.set(c.id.uid(), ref_)
          for f in c.fields {
            fields.set(f.id.uid(), { constructor_ref: ref_, field: f, })
          }
        }
      }
      DeclarationInterface(id, _, props) => {
        interfaces.set(id.uid(), i)
        for p in props {
          properties.set(p.id.uid(), {
            interface: declarations[i],
            property: p,
          })
        }
      }
    }
  }
  let extern_defs : Map[Int32, Int32] = Map([])
  let extern_datas : Map[Int32, Int32] = Map([])
  let extern_defs_by_name : Map[String, Int32] = Map([])
  for i = 0; i < externs.length(); i = i + 1 {
    match externs[i] {
      ExternDef(id, _, _, _, vparams, _, _, _, _) => {
        extern_defs.set(id.uid(), i)
        extern_defs_by_name.set(
          extern_def_key(id.name().name, vparams.map(p => p.tpe)),
          i,
        )
      }
      ExternData(id, _, _) => extern_datas.set(id.uid(), i)
      _ => ()
    }
  }
  {
    declarations,
    externs,
    datas,
    interfaces,
    constructors,
    fields,
    properties,
    extern_defs,
    extern_datas,
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
pub fn DeclarationContext::find_declaration(
  self : DeclarationContext,
  id : Sym,
) -> Declaration? {
  for d in self.declarations {
    if d.id().uid() == id.uid() {
      return Some(d)
    }
  }
  None
}

///|
pub fn DeclarationContext::find_data(
  self : DeclarationContext,
  id : Sym,
) -> Declaration? {
  match self.datas.get(id.uid()) {
    Some(i) => Some(self.declarations[i])
    None => None
  }
}

///|
pub fn DeclarationContext::find_data_of_constructor(
  self : DeclarationContext,
  constructor_ : Constructor,
) -> Declaration? {
  match self.constructors.get(constructor_.id.uid()) {
    Some(ref_) => Some(ref_.data)
    None => None
  }
}

///|
pub fn DeclarationContext::find_data_of_field(
  self : DeclarationContext,
  field : Field,
) -> Declaration? {
  match self.fields.get(field.id.uid()) {
    Some(ref_) => Some(ref_.constructor_ref.data)
    None => None
  }
}

///|
pub fn DeclarationContext::find_interface(
  self : DeclarationContext,
  id : Sym,
) -> Declaration? {
  match self.interfaces.get(id.uid()) {
    Some(i) => Some(self.declarations[i])
    None => None
  }
}

///|
pub fn DeclarationContext::find_interface_of_property(
  self : DeclarationContext,
  property : Property,
) -> Declaration? {
  match self.properties.get(property.id.uid()) {
    Some(ref_) => Some(ref_.interface)
    None => None
  }
}

///|
pub fn DeclarationContext::find_constructor(
  self : DeclarationContext,
  id : Sym,
) -> Constructor? {
  match self.constructors.get(id.uid()) {
    Some(ref_) => Some(ref_.constructor_)
    None => None
  }
}

///|
pub fn DeclarationContext::find_constructor_of_field(
  self : DeclarationContext,
  field : Field,
) -> Constructor? {
  match self.fields.get(field.id.uid()) {
    Some(ref_) => Some(ref_.constructor_ref.constructor_)
    None => None
  }
}

///|
pub fn DeclarationContext::find_constructor_tag(
  self : DeclarationContext,
  id : Sym,
) -> Int32? {
  match self.constructors.get(id.uid()) {
    Some(ref_) =>
      match ref_.data {
        DeclarationData(_, _, ctors) => {
          for i = 0; i < ctors.length(); i = i + 1 {
            if ctors[i].id.uid() == ref_.constructor_.id.uid() {
              return Some(i)
            }
          }
          None
        }
        _ => None
      }
    None => None
  }
}

///|
pub fn DeclarationContext::find_field(
  self : DeclarationContext,
  id : Sym,
) -> Field? {
  match self.fields.get(id.uid()) {
    Some(ref_) => Some(ref_.field)
    None => None
  }
}

///|
pub fn DeclarationContext::find_property(
  self : DeclarationContext,
  id : Sym,
) -> Property? {
  match self.properties.get(id.uid()) {
    Some(ref_) => Some(ref_.property)
    None => None
  }
}

///|
pub fn DeclarationContext::find_property_tag(
  self : DeclarationContext,
  id : Sym,
) -> Int32? {
  match self.properties.get(id.uid()) {
    Some(ref_) =>
      match ref_.interface {
        DeclarationInterface(_, _, props) => {
          for i = 0; i < props.length(); i = i + 1 {
            if props[i].id.uid() == ref_.property.id.uid() {
              return Some(i)
            }
          }
          None
        }
        _ => None
      }
    None => None
  }
}

///|
pub fn DeclarationContext::find_extern_def(
  self : DeclarationContext,
  id : Sym,
) -> Extern? {
  match self.extern_defs.get(id.uid()) {
    Some(i) => Some(self.externs[i])
    None => None
  }
}

///|
pub fn DeclarationContext::find_extern_def_by_name(
  self : DeclarationContext,
  name : String,
  params : Array[ValueType],
) -> Extern? {
  match self.extern_defs_by_name.get(extern_def_key(name, params)) {
    Some(i) => Some(self.externs[i])
    None => None
  }
}

///|
pub fn DeclarationContext::find_extern_data(
  self : DeclarationContext,
  id : Sym,
) -> Extern? {
  match self.extern_datas.get(id.uid()) {
    Some(i) => Some(self.externs[i])
    None => None
  }
}

// Panicking lookups
// -----------------

///|
pub fn DeclarationContext::get_declaration(
  self : DeclarationContext,
  id : Sym,
) -> Declaration raise EffektError {
  match self.find_declaration(id) {
    Some(d) => d
    None => panic("No declaration found for \{show_core_stmt_hint(id)}.")
  }
}

///|
fn show_core_stmt_hint(id : Sym) -> String {
  id.name().name
}

///|
pub fn DeclarationContext::get_data(
  self : DeclarationContext,
  id : Sym,
) -> Declaration raise EffektError {
  match self.find_data(id) {
    Some(d) => d
    None => panic("No declaration found for data type \{id.name().name}.")
  }
}

///|
pub fn DeclarationContext::get_interface(
  self : DeclarationContext,
  id : Sym,
) -> Declaration raise EffektError {
  match self.find_interface(id) {
    Some(d) => d
    None => panic("No declaration found for interface \{id.name().name}.")
  }
}

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

///|
pub fn DeclarationContext::get_field(
  self : DeclarationContext,
  id : Sym,
) -> Field raise EffektError {
  match self.find_field(id) {
    Some(f) => f
    None => panic("No declaration found for field \{id.name().name}.")
  }
}

///|
pub fn DeclarationContext::get_property(
  self : DeclarationContext,
  id : Sym,
) -> Property raise EffektError {
  match self.find_property(id) {
    Some(p) => p
    None => panic("No declaration found for property \{id.name().name}.")
  }
}

///|
pub fn DeclarationContext::get_property_tag(
  self : DeclarationContext,
  id : Sym,
) -> Int32 raise EffektError {
  match self.find_property_tag(id) {
    Some(tag) => tag
    None => panic("No declaration found for property \{id.name().name}.")
  }
}

///|
pub fn DeclarationContext::get_extern_def(
  self : DeclarationContext,
  id : Sym,
) -> Extern raise EffektError {
  match self.find_extern_def(id) {
    Some(d) => d
    None => panic("No extern definition found for \{id.name().name}.")
  }
}

///|
pub fn DeclarationContext::get_extern_data(
  self : DeclarationContext,
  id : Sym,
) -> Extern raise EffektError {
  match self.find_extern_data(id) {
    Some(d) => d
    None => panic("No extern data found for \{id.name().name}.")
  }
}

// Qualified signatures
// --------------------

///|
/// Builds the qualified signature of an extern function, e.g.
/// `mymodule::externFun[Int](Int, String){Int}`.
pub fn QualifiedSignature::from_extern_function(
  module_name : String,
  f : Sym,
) -> QualifiedSignature {
  let callable = f.as_callable()
  match callable {
    None => QualifiedSignature::new("\{module_name}::\{f.name().name}")
    Some(c) => {
      let tps = if c.tparams.length() == 0 {
        ""
      } else {
        "[\{c.tparams.map(t => show_core_value_type(ValueTypeRef(t))).join(", ")}]"
      }
      let value_params = c.vparams
        .map(p => show_core_value_type(value_param_type(p)))
        .join(", ")
      let vps = if value_params == "" { "" } else { "(\{value_params})" }
      let bps = c.bparams
        .map(b => "{\{show_core_block_type(block_param_type(b))}}")
        .join("")
      let ps = if vps == "" && bps == "" { "()" } else { vps + bps }
      QualifiedSignature::new("\{module_name}::\{f.name().name}\{tps}\{ps}")
    }
  }
}

///|
fn value_param_type(p : Sym) -> ValueType {
  match p {
    ValueParam(vp) =>
      match vp.tpe {
        Some(t) => t
        None => unknown_value_type()
      }
    _ => unknown_value_type()
  }
}

///|
fn block_param_type(p : Sym) -> BlockType {
  match p {
    BlockParam(bp) =>
      match bp.tpe {
        Some(t) => t
        None => unknown_block_type()
      }
    _ => unknown_block_type()
  }
}
