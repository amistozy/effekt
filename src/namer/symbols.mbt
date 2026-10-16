// Construction and inspection of the symbols the namer creates.
//
// Upstream builds symbols with case-class constructors (`UserFunction(...)`,
// `DataType(...)`, ...); in this port a `Sym` is one variant of a single enum
// carrying a plain struct, so all construction happens here. Keeping it in one
// place also means the traversal in `namer.mbt` reads like the upstream code.

///|
fn mk_base(name : Name, decl : Span) -> @symbols.SymBase {
  { uid: fresh_uid(), name, decl, }
}

///|
/// A unique copy of an identifier, mirroring upstream's `Id.clone`: the same
/// path, name and span, but a fresh `uid`. Used when one tree node gives rise
/// to two symbols (e.g. a record and its constructor).
fn clone_id_def(id : IdDef) -> IdDef {
  { uid: fresh_uid(), path: id.path, name: id.name, span: id.span, }
}

///|
/// The name of an identifier in binding position, *without* the surrounding
/// namespace path. Mirrors upstream's `Name(id)`.
fn name_of_id(id : IdDef) -> Name {
  if id.path.length() == 0 {
    Name::local(id.name)
  } else {
    Name::qualified(id.path, id.name)
  }
}

///|
/// Renders an identifier in use position, including its path, for diagnostics.
fn id_text(id : IdRef) -> String {
  if id.path.length() == 0 {
    id.name
  } else {
    id.path.join("::") + "::" + id.name
  }
}

///|
/// Structural equality of names. (`Name` has an `impl Eq`, but it is not
/// exported from the `symbols` package.)
fn name_eq(a : Name, b : Name) -> Bool {
  a.name == b.name && a.path == b.path
}

// Values
// ------

///|
fn mk_value_param(
  name : Name,
  tpe : ValueType?,
  is_implicit : Bool,
  decl : Span,
) -> Sym {
  @symbols.Sym::ValueParam({ base: mk_base(name, decl), tpe, is_implicit, })
}

///|
fn mk_val_binder(name : Name, tpe : ValueType?, decl : Span) -> Sym {
  @symbols.Sym::ValBinder({ base: mk_base(name, decl), tpe, })
}

///|
fn mk_var_binder(
  name : Name,
  tpe : ValueType?,
  capture : Sym,
  decl : Span,
) -> Sym {
  @symbols.Sym::VarBinder({ base: mk_base(name, decl), tpe, capture, })
}

///|
fn mk_reg_binder(
  name : Name,
  tpe : ValueType?,
  region : Sym,
  decl : Span,
) -> Sym {
  @symbols.Sym::RegBinder({ base: mk_base(name, decl), tpe, region, })
}

///|
fn mk_hole(name : Name, decl : Span) -> Sym {
  @symbols.Sym::Hole({
    base: mk_base(name, decl),
    expected_type: None,
    arg_types: [],
  })
}

// Blocks
// ------

///|
fn mk_block_param(
  name : Name,
  tpe : BlockType?,
  capture : Sym,
  is_implicit : Bool,
  decl : Span,
) -> Sym {
  @symbols.Sym::BlockParam({
    base: mk_base(name, decl),
    tpe,
    capture,
    is_implicit,
  })
}

///|
fn mk_def_binder(
  name : Name,
  caps : Array[Sym]?,
  tpe : BlockType?,
  decl : Span,
) -> Sym {
  @symbols.Sym::DefBinder({ base: mk_base(name, decl), caps, tpe, })
}

///|
fn mk_user_function(
  name : Name,
  tparams : Array[Sym],
  vparams : Array[Sym],
  bparams : Array[Sym],
  annotated_captures : Array[Sym]?,
  annotated_result : ValueType?,
  annotated_effects : Effects?,
  decl : Span,
) -> Sym {
  @symbols.Sym::UserFunction({
    base: mk_base(name, decl),
    tparams,
    vparams,
    bparams,
    annotated_captures,
    annotated_result,
    annotated_effects,
  })
}

///|
fn mk_extern_function(
  name : Name,
  tparams : Array[Sym],
  vparams : Array[Sym],
  bparams : Array[Sym],
  result : ValueType,
  effects : Effects,
  capture : Array[Sym],
  decl : Span,
) -> Sym {
  @symbols.Sym::ExternFunction({
    base: mk_base(name, decl),
    tparams,
    vparams,
    bparams,
    result,
    effects,
    capture,
  })
}

///|
fn mk_extern_resource(
  name : Name,
  tpe : BlockType,
  capture : Sym,
  decl : Span,
) -> Sym {
  @symbols.Sym::ExternResource({ base: mk_base(name, decl), tpe, capture, })
}

///|
fn mk_operation(
  name : Name,
  tparams : Array[Sym],
  vparams : Array[Sym],
  bparams : Array[Sym],
  result : ValueType,
  effects : Effects,
  interface : Sym,
  decl : Span,
) -> Sym {
  @symbols.Sym::Operation({
    base: mk_base(name, decl),
    tparams,
    vparams,
    bparams,
    result_type: result,
    effects,
    interface,
  })
}

///|
fn mk_constructor(
  name : Name,
  tparams : Array[Sym],
  tpe : Sym,
  decl : Span,
) -> Sym {
  @symbols.Sym::Constructor({
    base: mk_base(name, decl),
    tparams,
    fields: [],
    tpe,
  })
}

///|
fn mk_field(name : Name, param : Sym, constructor : Sym, decl : Span) -> Sym {
  @symbols.Sym::Field({ base: mk_base(name, decl), param, constructor, })
}

// Types
// -----

///|
fn mk_interface(name : Name, tparams : Array[Sym], decl : Span) -> Sym {
  @symbols.Sym::Interface({
    base: mk_base(name, decl),
    tparams,
    operations: [],
  })
}

///|
fn mk_extern_interface(name : Name, tparams : Array[Sym], decl : Span) -> Sym {
  @symbols.Sym::ExternInterface({ base: mk_base(name, decl), tparams, })
}

///|
fn mk_extern_type(name : Name, tparams : Array[Sym], decl : Span) -> Sym {
  @symbols.Sym::ExternType({ base: mk_base(name, decl), tparams, })
}

///|
fn mk_data_type(name : Name, tparams : Array[Sym], decl : Span) -> Sym {
  @symbols.Sym::DataType({
    base: mk_base(name, decl),
    tparams,
    constructors: [],
  })
}

///|
/// Record symbols need their constructor; upstream passes `null` and fills it
/// in while resolving the body, which we emulate with a placeholder.
fn mk_record(name : Name, tparams : Array[Sym], decl : Span) -> Sym {
  @symbols.Sym::Record({
    base: mk_base(name, decl),
    tparams,
    constructor: @symbols.Sym::wildcard(),
  })
}

///|
fn mk_type_alias(
  name : Name,
  tparams : Array[Sym],
  tpe : ValueType,
  decl : Span,
) -> Sym {
  @symbols.Sym::TypeAlias({ base: mk_base(name, decl), tparams, tpe, })
}

///|
fn mk_effect_alias(
  name : Name,
  tparams : Array[Sym],
  effs : Effects,
  decl : Span,
) -> Sym {
  @symbols.Sym::EffectAlias({ base: mk_base(name, decl), tparams, effs, })
}

// Inspection and mutation of symbols
// ----------------------------------

///|
/// The capture parameter of a tracked block (block parameter, mutable variable
/// or extern resource).
fn capture_of(sym : Sym) -> Sym {
  match sym {
    @symbols.Sym::BlockParam(p) => p.capture
    @symbols.Sym::ExternResource(r) => r.capture
    @symbols.Sym::VarBinder(v) => v.capture
    _ => @symbols.Sym::wildcard()
  }
}

///|
fn interface_tparams(sym : Sym) -> Array[Sym] {
  match sym {
    @symbols.Sym::Interface(i) => i.tparams
    @symbols.Sym::ExternInterface(i) => i.tparams
    _ => []
  }
}

///|
fn interface_operations(sym : Sym) -> Array[Sym] {
  match sym {
    @symbols.Sym::Interface(i) => i.operations
    _ => []
  }
}

///|
fn set_interface_operations(sym : Sym, ops : Array[Sym]) -> Unit {
  match sym {
    @symbols.Sym::Interface(i) => i.operations = ops
    _ => ()
  }
}

///|
fn data_tparams(sym : Sym) -> Array[Sym] {
  match sym {
    @symbols.Sym::DataType(d) => d.tparams
    @symbols.Sym::Record(r) => r.tparams
    _ => []
  }
}

///|
fn set_data_constructors(sym : Sym, ctors : Array[Sym]) -> Unit {
  match sym {
    @symbols.Sym::DataType(d) => d.constructors = ctors
    _ => ()
  }
}

///|
fn set_constructor_fields(sym : Sym, fields : Array[Sym]) -> Unit {
  match sym {
    @symbols.Sym::Constructor(c) => c.fields = fields
    _ => ()
  }
}

///|
fn set_record_constructor(sym : Sym, ctor : Sym) -> Unit {
  match sym {
    @symbols.Sym::Record(r) => r.constructor = ctor
    _ => ()
  }
}

///|
fn operation_interface(sym : Sym) -> Sym {
  match sym {
    @symbols.Sym::Operation(o) => o.interface
    _ => @symbols.Sym::wildcard()
  }
}

///|
/// The type a constructor constructs, rendered for diagnostics.
fn constructor_type_text(sym : Sym) -> String {
  match sym {
    @symbols.Sym::Constructor(c) => c.tpe.name().qualified_name()
    _ => "?"
  }
}

///|
/// Removes duplicates from a nested array of symbols, preserving order.
fn flatten_syms(xs : Array[Array[Sym]]) -> Array[Sym] {
  @symbols.dedup_syms(xs.flatten())
}
