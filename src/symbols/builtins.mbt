// Built-in types and capabilities.
//
// Mirrors `effekt/symbols/builtins.scala`.

///|
fn builtin_name(s : String) -> Name {
  Name::qualified(["effekt"], s)
}

///|
fn builtin_extern_type(s : String) -> Sym {
  ExternType({
    base: { uid: fresh_uid(), name: builtin_name(s), decl: Span::missing(), },
    tparams: [],
  })
}

///|
fn builtin_data_type(s : String) -> Sym {
  DataType({
    base: { uid: fresh_uid(), name: builtin_name(s), decl: Span::missing(), },
    tparams: [],
    constructors: [],
  })
}

///|
let unit_symbol : Sym = builtin_extern_type("Unit")

///|
let boolean_symbol : Sym = builtin_extern_type("Bool")

///|
let int_symbol : Sym = builtin_extern_type("Int")

///|
let double_symbol : Sym = builtin_extern_type("Double")

///|
let string_symbol : Sym = builtin_extern_type("String")

///|
let char_symbol : Sym = builtin_extern_type("Char")

///|
let byte_symbol : Sym = builtin_extern_type("Byte")

///|
let top_symbol : Sym = builtin_data_type("Any")

///|
let bottom_symbol : Sym = builtin_data_type("Nothing")

///|
let io_symbol : Sym = Interface({
  base: { uid: fresh_uid(), name: Name::local("IO"), decl: Span::missing(), },
  tparams: [],
  operations: [],
})

///|
let async_symbol : Sym = Interface({
  base: { uid: fresh_uid(), name: Name::local("Async"), decl: Span::missing(), },
  tparams: [],
  operations: [],
})

///|
let global_symbol : Sym = Interface({
  base: {
    uid: fresh_uid(),
    name: Name::local("Global"),
    decl: Span::missing(),
  },
  tparams: [],
  operations: [],
})

///|
let region_symbol : Sym = Interface({
  base: {
    uid: fresh_uid(),
    name: Name::local("Region"),
    decl: Span::missing(),
  },
  tparams: [],
  operations: [],
})

///|
let io_capability : Sym = ExternResource({
  base: { uid: fresh_uid(), name: Name::local("io"), decl: Span::missing(), },
  tpe: InterfaceType(io_symbol, []),
  capture: Sym::resource(Name::local("io")),
})

///|
let async_capability : Sym = ExternResource({
  base: { uid: fresh_uid(), name: Name::local("async"), decl: Span::missing(), },
  tpe: InterfaceType(async_symbol, []),
  capture: Sym::resource(Name::local("async")),
})

///|
let global_capability : Sym = ExternResource({
  base: {
    uid: fresh_uid(),
    name: Name::local("global"),
    decl: Span::missing(),
  },
  tpe: InterfaceType(global_symbol, []),
  capture: Sym::resource(Name::local("global")),
})

///|
pub fn t_unit() -> ValueType {
  ValueTypeApp(unit_symbol, [])
}

///|
pub fn t_bool() -> ValueType {
  ValueTypeApp(boolean_symbol, [])
}

///|
pub fn t_int() -> ValueType {
  ValueTypeApp(int_symbol, [])
}

///|
pub fn t_double() -> ValueType {
  ValueTypeApp(double_symbol, [])
}

///|
pub fn t_string() -> ValueType {
  ValueTypeApp(string_symbol, [])
}

///|
pub fn t_char() -> ValueType {
  ValueTypeApp(char_symbol, [])
}

///|
pub fn t_byte() -> ValueType {
  ValueTypeApp(byte_symbol, [])
}

///|
pub fn t_top() -> ValueType {
  ValueTypeApp(top_symbol, [])
}

///|
pub fn t_bottom() -> ValueType {
  ValueTypeApp(bottom_symbol, [])
}

///|
pub fn t_region() -> BlockType {
  InterfaceType(region_symbol, [])
}

///|
pub fn t_io() -> BlockType {
  InterfaceType(io_symbol, [])
}

///|
pub fn io_capability_sym() -> Sym {
  io_capability
}

///|
pub fn async_capability_sym() -> Sym {
  async_capability
}

///|
pub fn global_capability_sym() -> Sym {
  global_capability
}

///|
pub fn io_capture() -> Sym {
  match io_capability {
    ExternResource(r) => r.capture
    _ => Sym::resource(Name::local("io"))
  }
}

///|
pub fn async_capture() -> Sym {
  match async_capability {
    ExternResource(r) => r.capture
    _ => Sym::resource(Name::local("async"))
  }
}

///|
pub fn global_capture() -> Sym {
  match global_capability {
    ExternResource(r) => r.capture
    _ => Sym::resource(Name::local("global"))
  }
}

///|
/// The built-in mutable reference effect `Ref[S]`.
pub(all) struct StateEffect {
  state_param : Sym
  interface : Sym
  get : Sym
  put : Sym
}

///|
fn make_state_effect() -> StateEffect {
  let s = Sym::type_param(Name::local("S"), Span::missing())
  let iface = Interface({
    base: { uid: fresh_uid(), name: Name::local("Ref"), decl: Span::missing(), },
    tparams: [s],
    operations: [],
  })
  let get = Operation({
    base: {
      uid: fresh_uid(),
      name: builtin_name("get"),
      decl: Span::missing(),
    },
    tparams: [s],
    vparams: [],
    bparams: [],
    result_type: ValueTypeRef(s),
    effects: Effects::empty(),
    interface: iface,
  })
  let put = Operation({
    base: {
      uid: fresh_uid(),
      name: builtin_name("put"),
      decl: Span::missing(),
    },
    tparams: [s],
    vparams: [
      Sym::value_param(Name::local("s"), Some(ValueTypeRef(s)), Span::missing()),
    ],
    bparams: [],
    result_type: t_unit(),
    effects: Effects::empty(),
    interface: iface,
  })
  match iface {
    Interface(i) => i.operations = [get, put]
    _ => ()
  }
  { state_param: s, interface: iface, get, put, }
}

///|
let state_effect : StateEffect = make_state_effect()

///|
pub fn t_state(state_type : ValueType) -> BlockType {
  InterfaceType(state_effect.interface, [state_type])
}

///|
pub fn state_effect_sym() -> Sym {
  state_effect.interface
}

///|
pub fn t_state_extract(s : BlockType) -> ValueType raise EffektError {
  match s {
    InterfaceType(i, args) =>
      if i.uid() == state_effect.interface.uid() && args.length() == 1 {
        args[0]
      } else {
        raise EffektError::Internal(
          "Expected builtin state, but got " + "state",
        )
      }
    _ => raise EffektError::Internal("Expected builtin state")
  }
}

///|
/// The built-in map of names visible in every module.
pub fn root_bindings() -> Bindings {
  let types : Map[String, Sym] = {
    "Unit": unit_symbol,
    "Bool": boolean_symbol,
    "Int": int_symbol,
    "Double": double_symbol,
    "String": string_symbol,
    "Char": char_symbol,
    "Byte": byte_symbol,
    "Any": top_symbol,
    "Nothing": bottom_symbol,
    "IO": io_symbol,
    "Region": region_symbol,
    "Ref": state_effect.interface,
  }
  let captures : Map[String, Sym] = {
    "io": io_capture(),
    "async": async_capture(),
    "global": global_capture(),
  }
  let inner : Bindings = {
    terms: Map([]),
    types,
    captures,
    namespaces: Map([]),
  }
  let namespaces : Map[String, Bindings] = { "effekt": inner }
  { terms: Map([]), types, captures, namespaces, }
}

///|
/// The names that are also available at the core level.
pub fn core_builtins() -> Map[String, Sym] {
  {
    "Unit": unit_symbol,
    "Bool": boolean_symbol,
    "Int": int_symbol,
    "Double": double_symbol,
    "String": string_symbol,
    "Char": char_symbol,
    "Byte": byte_symbol,
    "Any": top_symbol,
    "Nothing": bottom_symbol,
    "IO": io_symbol,
    "Region": region_symbol,
    "io": io_capture(),
    "async": async_capture(),
    "global": global_capture(),
    "Ref": state_effect.interface,
  }
}

///|
pub fn is_core_builtin(s : Sym) -> Bool {
  match core_builtins().get(s.name().name) {
    Some(other) => other.uid() == s.uid()
    None => false
  }
}

///|
pub fn core_builtin_to_string(s : Sym) -> String? {
  if is_core_builtin(s) {
    Some(s.name().name)
  } else {
    None
  }
}
