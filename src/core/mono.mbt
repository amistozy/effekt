// Monomorphization: specializes polymorphic data types and functions for the
// instantiations a program actually uses (`effekt/core/Mono.scala`).
//
// Upstream runs it before `core.Show` (`JavaScript.scala`: `Mono andThen Show`),
// because the structural `show` instances it generates only make sense once the
// data declarations have concrete field types. That is why the port needs it
// too: without it `show` of a generic data type has to look through type
// variables, and `Show` can only treat those as opaque.
//
// The phase is a small flow analysis followed by a specialization:
//
//   1. `preprocess` elaborates polymorphic block parameters into interface
//      values: a parameter of type `[A](A) => A` becomes a value of a
//      `Poly[A] { def apply(method: (A) => A): ... }` interface, and a call
//      `f(x)` becomes `f.apply(x)`. Alpha-equivalent block schemas share one
//      interface, so a module gets one `Poly` per *shape*.
//   2. `collect` gathers, for every flow variable (a definition, a local
//      function, a constructor, an operation), the vector of type arguments it
//      is used with, and how those arguments flow into one another.
//   3. `solve` propagates the arguments through those dependencies to a fixed
//      point, keeping only ground vectors (no free type variables).
//   4. `specialize` rewrites the tree: every polymorphic definition is copied
//      once per variant, every data type gets one declaration per instantiation
//      (`Option` + `Int` becomes `Option_Int`), and type arguments disappear
//      from applications.
//
// A module that is already monomorphic is left (almost) untouched: no data type
// has an instance, and every `tparams` list is empty, so the pass degenerates to
// a type-preserving traversal.

// ---------------------------------------------------------------------------
// Monomorphized types
// ---------------------------------------------------------------------------

///|
/// A value type of a flow variable and the position its owner supplies: the
/// flow analysis works with types that still mention *where* a type argument
/// comes from (`Request[?f.0]`).
#derive(Eq)
pub(all) struct MonoProjection {
  owner : Sym
  position : Int32
}

///|
/// A capture in a monomorphized type: either a binder of an enclosing
/// signature (by De Bruijn level and position) or a named capture.
#derive(Eq)
pub(all) enum MonoCapture {
  MonoCaptureBound(Int32, Int32)
  MonoCaptureNamed(Sym)
}

///|
/// A value type, parameterized over what a free variable is: `MonoProjection`
/// while the flows are collected, `Unit` once the type is ground (a ground type
/// has no variable by construction).
#derive(Eq)
pub(all) enum MonoValueType[V] {
  MonoValueVar(V)
  MonoValueBound(Int32, Int32)
  MonoValueData(Sym, Array[MonoValueType[V]])
  MonoValueBoxed(MonoBlockType[V], Array[MonoCapture])
}

///|
/// A block type, similarly parameterized. The arities are explicit because a
/// `FunctionType`'s binders are not part of the encoded shape (they are
/// positions, not names).
#derive(Eq)
pub(all) enum MonoBlockType[V] {
  MonoFunction(
    Int32,
    Int32,
    Array[MonoValueType[V]],
    Array[MonoBlockType[V]],
    Array[MonoValueType[V]],
  )
  MonoInterface(Sym, Array[MonoValueType[V]])
  MonoPrompt(Array[MonoValueType[V]])
  MonoResume(Array[MonoValueType[V]], Array[MonoValueType[V]])
}

// ---------------------------------------------------------------------------
// Rendering keys
// ---------------------------------------------------------------------------
//
// Types are compared and keyed by a rendered string, like upstream's
// `typeKey`/`blockTypeKey`: MoonBit's `Map` needs a hashable key and the
// structural equality of the enums above is not hashable, and the rendered key
// is what the specialized names are built from anyway.

///|
fn[V] mono_value_type_key(
  t : MonoValueType[V],
  var_key : (V) -> String,
) -> String {
  match t {
    MonoValueVar(v) => var_key(v)
    MonoValueBound(level, position) => "V\{level}.\{position}"
    MonoValueData(name, targs) => {
      let arguments = targs.map(x => mono_value_type_key(x, var_key)).join(",")
      "D\{name.name().name}[\{arguments}]"
    }
    MonoValueBoxed(tpe, captures) => {
      let block = mono_block_type_key(tpe, var_key)
      let captures = mono_captures_key(captures)
      "B\{block}@\{captures}"
    }
  }
}

///|
fn[V] mono_block_type_key(
  t : MonoBlockType[V],
  var_key : (V) -> String,
) -> String {
  match t {
    MonoFunction(tarity, carity, vparams, bparams, result) => {
      let vps = vparams.map(x => mono_value_type_key(x, var_key)).join(",")
      let bps = bparams.map(x => mono_block_type_key(x, var_key)).join(",")
      let ret = result.map(x => mono_value_type_key(x, var_key)).join(",")
      "[\{tarity},\{carity}](\{vps})<\{bps}>:\{ret}"
    }
    MonoInterface(name, targs) => {
      let arguments = targs.map(x => mono_value_type_key(x, var_key)).join(",")
      "\{name.name().name}[\{arguments}]"
    }
    MonoPrompt(answer) => {
      let answers = answer.map(x => mono_value_type_key(x, var_key)).join(",")
      "Prompt[\{answers}]"
    }
    MonoResume(result, answer) => {
      let results = result.map(x => mono_value_type_key(x, var_key)).join(",")
      let answers = answer.map(x => mono_value_type_key(x, var_key)).join(",")
      "(\{results})~>(\{answers})"
    }
  }
}

///|
fn mono_captures_key(captures : Array[MonoCapture]) -> String {
  let parts : Array[String] = captures.map(c => {
    match c {
      MonoCaptureBound(level, position) => "\{level}.\{position}"
      MonoCaptureNamed(id) => id.name().name
    }
  })
  parts.mut_view().stable_sort_by((a, b) => a.lexical_compare(b))
  parts.join(",")
}

// ---------------------------------------------------------------------------
// Binders
// ---------------------------------------------------------------------------

///|
/// The index of `id` in a stack of binder lists: (De Bruijn level, position).
fn mono_binder_index(
  id : Sym,
  binders : ArrayView[Array[Sym]],
) -> (Int32, Int32)? {
  for level, bindings in binders {
    for position, binding in bindings {
      if binding.uid() == id.uid() {
        return Some((level, position))
      }
    }
  }
  None
}

///|
fn mono_key(id : Sym, variant : ArrayView[MonoValueType[Unit]]) -> String {
  "\{id.uid()}|\{variant.map(t => mono_value_type_key(t, _ => "")).join(",")}"
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

///|
/// `flatMap` over an array (upstream's `List.flatMap`): `Array` has no `flat_map`,
/// and the call sites are shorter with this than with `map` and `flatten`.
fn[T, A] mono_flat_map(xs : Array[A], f : (A) -> Array[T]) -> Array[T] {
  xs.map(x => f(x)).flatten()
}

// ---------------------------------------------------------------------------
// Preprocessing: polymorphic block parameters become interface values
// ---------------------------------------------------------------------------

///|
/// The symbols of a list of capture parameters (the port's core has capture
/// *sets* there, upstream has one id per parameter).
fn mono_capture_params(cparams : ArrayView[Captures]) -> Array[Sym] {
  let out : Array[Sym] = []
  for captures in cparams {
    match captures {
      CaptureSetOf(cs) =>
        for c in cs {
          out.push(c)
        }
      CaptVar(c) => out.push(c)
    }
  }
  out
}

///|
/// De Bruijn encoding of a block type: the free type and capture variables are
/// *positions* in the enclosing signature, so alpha-equivalent schemas get the
/// same key and share one interface.
priv struct MonoDebruijn {
  type_binders : Array[Array[Sym]]
  capture_binders : Array[Array[Sym]]
}

///|
fn MonoDebruijn::for_outer(outer : Array[Sym]) -> MonoDebruijn {
  { type_binders: [outer], capture_binders: [[]], }
}

///|
fn MonoDebruijn::enter(
  self : MonoDebruijn,
  tparams : Array[Sym],
  cparams : Array[Captures],
) -> MonoDebruijn {
  {
    type_binders: [tparams] + self.type_binders,
    capture_binders: [mono_capture_params(cparams)] + self.capture_binders,
  }
}

///|
fn MonoDebruijn::type_index(self : MonoDebruijn, id : Sym) -> (Int32, Int32)? {
  mono_binder_index(id, self.type_binders)
}

///|
fn MonoDebruijn::capture_index(
  self : MonoDebruijn,
  id : Sym,
) -> (Int32, Int32)? {
  mono_binder_index(id, self.capture_binders)
}

///|
/// Encodes a block type: its binders become positions, its free variables must
/// be bound by the enclosing signature (see [[MonoDebruijn::for_outer]]).
fn MonoDebruijn::block_type(
  self : MonoDebruijn,
  tpe : BlockType,
) -> MonoBlockType[Unit] raise EffektError {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result) => {
      let local = self.enter(tparams, cparams)
      MonoFunction(
        tparams.length(),
        cparams.length(),
        vparams.map(x => local.value_type(x)),
        bparams.map(x => local.block_type(x)),
        result.map(x => local.value_type(x)),
      )
    }
    InterfaceType(name, targs) =>
      MonoInterface(name, targs.map(x => self.value_type(x)))
    PromptType(answer) => MonoPrompt(answer.map(x => self.value_type(x)))
    ResumeType(result, answer) =>
      MonoResume(
        result.map(x => self.value_type(x)),
        answer.map(x => self.value_type(x)),
      )
  }
}

///|
fn MonoDebruijn::value_type(
  self : MonoDebruijn,
  tpe : ValueType,
) -> MonoValueType[Unit] raise EffektError {
  match tpe {
    ValueVar(id) =>
      match self.type_index(id) {
        Some((level, position)) => MonoValueBound(level, position)
        None =>
          raise EffektError::Fatal(
            "Unbound type variable '\{id.name().name}' while encoding a polymorphic block",
          )
      }
    ValueData(name, targs) =>
      MonoValueData(name, targs.map(x => self.value_type(x)))
    ValueBoxed(tpe, captures) => {
      let mono_captures : Array[MonoCapture] = []
      match captures {
        CaptureSetOf(cs) =>
          for c in cs {
            mono_captures.push(self.capture(c))
          }
        CaptVar(c) => mono_captures.push(self.capture(c))
      }
      MonoValueBoxed(self.block_type(tpe), mono_captures)
    }
  }
}

///|
fn MonoDebruijn::capture(self : MonoDebruijn, id : Sym) -> MonoCapture {
  match self.capture_index(id) {
    Some((level, position)) => MonoCaptureBound(level, position)
    None => MonoCaptureNamed(id)
  }
}

///|
/// The free type variables of a block type, in first-occurrence order.
fn mono_free_type_variables(tpe : BlockType) -> Array[Sym] {
  let out : Array[Sym] = []
  mono_free_types_block(tpe, [], out)
  out
}

///|
fn mono_free_types_value(
  tpe : ValueType,
  bound : Array[Sym],
  out : Array[Sym],
) -> Unit {
  match tpe {
    ValueVar(id) =>
      if !bound.any(b => b.uid() == id.uid()) &&
        !out.any(x => x.uid() == id.uid()) {
        out.push(id)
      }
    ValueData(_, targs) =>
      for t in targs {
        mono_free_types_value(t, bound, out)
      }
    ValueBoxed(inner, _) => mono_free_types_block(inner, bound, out)
  }
}

///|
fn mono_free_types_block(
  tpe : BlockType,
  bound : Array[Sym],
  out : Array[Sym],
) -> Unit {
  match tpe {
    FunctionType(tparams, _, vparams, bparams, result) => {
      let local = bound + tparams
      for t in vparams {
        mono_free_types_value(t, local, out)
      }
      for t in bparams {
        mono_free_types_block(t, local, out)
      }
      for t in result {
        mono_free_types_value(t, local, out)
      }
    }
    InterfaceType(_, targs) =>
      for t in targs {
        mono_free_types_value(t, bound, out)
      }
    PromptType(answer) =>
      for t in answer {
        mono_free_types_value(t, bound, out)
      }
    ResumeType(result, answer) => {
      for t in result {
        mono_free_types_value(t, bound, out)
      }
      for t in answer {
        mono_free_types_value(t, bound, out)
      }
    }
  }
}

///|
/// The free capture variables of a block type (ignoring the ones bound by the
/// type itself).
fn mono_free_capture_variables(tpe : BlockType) -> Array[Sym] {
  let out : Array[Sym] = []
  mono_free_captures_block(tpe, [], out)
  out
}

///|
fn mono_free_captures_value(
  tpe : ValueType,
  bound : Array[Sym],
  out : Array[Sym],
) -> Unit {
  match tpe {
    ValueVar(_) => ()
    ValueData(_, targs) =>
      for t in targs {
        mono_free_captures_value(t, bound, out)
      }
    ValueBoxed(inner, captures) => {
      mono_free_captures_of(captures, bound, out)
      mono_free_captures_block(inner, bound, out)
    }
  }
}

///|
fn mono_free_captures_of(
  captures : Captures,
  bound : Array[Sym],
  out : Array[Sym],
) -> Unit {
  let add : (Sym) -> Unit = id => {
    if !bound.any(b => b.uid() == id.uid()) &&
      !out.any(x => x.uid() == id.uid()) {
      out.push(id)
    }
  }
  match captures {
    CaptureSetOf(cs) =>
      for c in cs {
        add(c)
      }
    CaptVar(c) => add(c)
  }
}

///|
fn mono_free_captures_block(
  tpe : BlockType,
  bound : Array[Sym],
  out : Array[Sym],
) -> Unit {
  match tpe {
    FunctionType(_, cparams, vparams, bparams, result) => {
      let local = bound + mono_capture_params(cparams)
      for t in vparams {
        mono_free_captures_value(t, local, out)
      }
      for t in bparams {
        mono_free_captures_block(t, local, out)
      }
      for t in result {
        mono_free_captures_value(t, local, out)
      }
    }
    InterfaceType(_, targs) =>
      for t in targs {
        mono_free_captures_value(t, bound, out)
      }
    PromptType(answer) =>
      for t in answer {
        mono_free_captures_value(t, bound, out)
      }
    ResumeType(result, answer) => {
      for t in result {
        mono_free_captures_value(t, bound, out)
      }
      for t in answer {
        mono_free_captures_value(t, bound, out)
      }
    }
  }
}

///|
/// One `Poly` interface: `interface` with the single operation `method`.
priv struct MonoEncoding {
  interface : Sym
  method : Sym
}

///|
/// The encoding of a polymorphic schema, together with the type variables that
/// it closes over.
priv struct MonoEncoded {
  encoding : MonoEncoding
  outer : Array[Sym]
}

///|
fn MonoEncoded::interface(
  self : MonoEncoded,
  arguments : ArrayView[ValueType],
) -> BlockType {
  InterfaceType(self.encoding.interface, arguments.to_owned())
}

///|
fn MonoEncoded::open_interface(self : MonoEncoded) -> BlockType {
  self.interface(self.outer.map(id => ValueType::ValueVar(id)))
}

///|
priv struct MonoScope {
  type_params : Array[Sym]
  capture_params : Array[Sym]
  blocks : Map[Int32, MonoEncoded]
}

///|
fn MonoScope::empty() -> MonoScope {
  { type_params: [], capture_params: [], blocks: Map([]), }
}

///|
fn MonoScope::bind_params(
  self : MonoScope,
  tparams : ArrayView[Sym],
  cparams : ArrayView[Captures],
) -> MonoScope {
  self.bind_syms(tparams, mono_capture_params(cparams))
}

///|
/// Binds parameters that are already plain symbols: a `BlockLit` and an
/// `Operation` hold their capture parameters as ids, a signature as one capture
/// set per block parameter.
fn MonoScope::bind_syms(
  self : MonoScope,
  tparams : ArrayView[Sym],
  cparams : ArrayView[Sym],
) -> MonoScope {
  {
    type_params: self.type_params + tparams.to_owned(),
    capture_params: self.capture_params + cparams.to_owned(),
    blocks: self.blocks,
  }
}

///|
fn MonoScope::bind_blocks(
  self : MonoScope,
  blocks : Map[Int32, MonoEncoded],
) -> MonoScope {
  // upstream `copy(blocks = this.blocks ++ blocks)`: the encodings of the
  // enclosing scopes stay visible, otherwise a block parameter of an enclosing
  // function is no longer recognized inside a nested block (a `reset`, say) and
  // its call is left as an `App`
  let merged = self.blocks.copy()
  for id, encoded in blocks {
    merged.set(id, encoded)
  }
  {
    type_params: self.type_params,
    capture_params: self.capture_params,
    blocks: merged,
  }
}

///|
/// The state of the pre-pass: the interfaces generated so far, keyed by the
/// encoded schema.
priv struct MonoState {
  interfaces : Array[Declaration]
  encodings : Map[String, MonoEncoding]
}

///|
fn MonoState::MonoState() -> MonoState {
  { interfaces: [], encodings: Map([]), }
}

///|
fn MonoState::encode(
  self : MonoState,
  tpe : BlockType,
  scope : MonoScope,
) -> MonoEncoded raise EffektError {
  let outer = mono_free_type_variables(tpe)
  for id in outer {
    if !scope.type_params.any(p => p.uid() == id.uid()) {
      raise EffektError::Fatal(
        "Unbound type variable while encoding a polymorphic block: \{id.name().name}",
      )
    }
  }
  let free_captures = mono_free_capture_variables(tpe)
  for id in free_captures {
    if scope.capture_params.any(p => p.uid() == id.uid()) {
      raise EffektError::Fatal(
        "Cannot encode a polymorphic block with free capture parameters: \{id.name().name}",
      )
    }
  }
  let key = mono_block_type_key(
    MonoDebruijn::for_outer(outer).block_type(tpe),
    _ => "",
  )
  match self.encodings.get(key) {
    Some(encoding) => MonoEncoded::{ encoding, outer, }
    None => {
      let interface = Sym::id(Name::local("Poly"))
      let method = Sym::id(Name::local("apply"))
      let fresh_params : Array[Sym] = outer.map(p => {
        Sym::type_param(Name::local(p.name().name), Span::missing())
      })
      let vtypes : Map[Int32, ValueType] = Map([])
      for i, old in outer {
        vtypes.set(old.uid(), ValueVar(fresh_params[i]))
      }
      let subst : Substitution = Substitution::Substitution(
        vtypes,
        Map([]),
        Map([]),
        Map([]),
      )
      let method_type = substitute_block_type(tpe, subst)
      self.interfaces.push(
        DeclarationInterface(interface, fresh_params, [
          Property::{ id: method, tpe: method_type, },
        ]),
      )
      let fresh : MonoEncoding = { interface, method, }
      self.encodings.set(key, fresh)
      MonoEncoded::{ encoding: fresh, outer, }
    }
  }
}

// ---------------------------------------------------------------------------
// The elaborator
// ---------------------------------------------------------------------------

///|
priv struct MonoElaborator {
  state : MonoState
}

///|
fn MonoElaborator::MonoElaborator(state : MonoState) -> MonoElaborator {
  { state, }
}

///|
fn MonoElaborator::declaration(
  self : MonoElaborator,
  decl : Declaration,
  scope : MonoScope,
) -> Declaration raise EffektError {
  match decl {
    DeclarationInterface(id, tparams, properties) => {
      let local = scope.bind_params(tparams, [])
      DeclarationInterface(
        id,
        tparams,
        properties.map(p => Property::{
          id: p.id,
          tpe: self.block_type(p.tpe, local),
        }),
      )
    }
    DeclarationData(id, tparams, constructors) => {
      let local = scope.bind_params(tparams, [])
      DeclarationData(
        id,
        tparams,
        constructors.map(c => {
          let ctor_scope = local.bind_params(c.tparams, [])
          Constructor::{
            id: c.id,
            tparams: c.tparams,
            fields: c.fields.map(f => Field::{
              id: f.id,
              tpe: self.value_type(f.tpe, ctor_scope),
            }),
          }
        }),
      )
    }
  }
}

///|
fn MonoElaborator::operation(
  self : MonoElaborator,
  op : Operation,
  scope : MonoScope,
) -> Operation raise EffektError {
  let local = scope.bind_syms(op.tparams, op.cparams)
  let (bparams, encoded) = self.rewrite_parameters(op.bparams, local)
  Operation::{
    name: op.name,
    tparams: op.tparams,
    cparams: op.cparams,
    vparams: op.vparams.map(p => ValueParam::{
      id: p.id,
      tpe: self.value_type(p.tpe, local),
    }),
    bparams,
    body: self.stmt(op.body, local.bind_blocks(encoded)),
  }
}

///|
fn MonoElaborator::block_lit(
  self : MonoElaborator,
  block : BlockLit,
  scope : MonoScope,
) -> BlockLit raise EffektError {
  let local = scope.bind_syms(block.tparams, block.cparams)
  let (bparams, encoded) = self.rewrite_parameters(block.bparams, local)
  BlockLit::{
    tparams: block.tparams,
    cparams: block.cparams,
    vparams: block.vparams.map(p => ValueParam::{
      id: p.id,
      tpe: self.value_type(p.tpe, local),
    }),
    bparams,
    body: self.stmt(block.body, local.bind_blocks(encoded)),
  }
}

///|
/// Polymorphic block parameters become values of the interface that encodes
/// their schema (`Poly.apply`); every other parameter is rewritten in place.
fn MonoElaborator::rewrite_parameters(
  self : MonoElaborator,
  params : Array[BlockParam],
  scope : MonoScope,
) -> (Array[BlockParam], Map[Int32, MonoEncoded]) raise EffektError {
  let encoded : Map[Int32, MonoEncoded] = Map([])
  let rewritten : Array[BlockParam] = []
  for p in params {
    match p.tpe {
      FunctionType(tparams, _, _, _, _) if !tparams.is_empty() => {
        let replacement = self.state.encode(p.tpe, scope)
        encoded.set(p.id.uid(), replacement)
        rewritten.push(BlockParam::{
          id: p.id,
          tpe: replacement.open_interface(),
          capt: p.capt,
        })
      }
      _ =>
        rewritten.push(BlockParam::{
          id: p.id,
          tpe: self.block_type(p.tpe, scope),
          capt: p.capt,
        })
    }
  }
  (rewritten, encoded)
}

///|
fn MonoElaborator::value_type(
  self : MonoElaborator,
  tpe : ValueType,
  scope : MonoScope,
) -> ValueType raise EffektError {
  match tpe {
    ValueVar(id) => ValueVar(id)
    ValueData(name, targs) =>
      ValueData(name, targs.map(t => self.value_type(t, scope)))
    ValueBoxed(inner, captures) =>
      ValueBoxed(self.block_type(inner, scope), captures)
  }
}

///|
fn MonoElaborator::block_type(
  self : MonoElaborator,
  tpe : BlockType,
  scope : MonoScope,
) -> BlockType raise EffektError {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result) => {
      let local = scope.bind_params(tparams, cparams)
      FunctionType(
        tparams,
        cparams,
        vparams.map(t => self.value_type(t, local)),
        bparams.map(b => {
          match b {
            FunctionType(inner_tparams, _, _, _, _) if !inner_tparams.is_empty() =>
              self.state.encode(b, local).open_interface()
            _ => self.block_type(b, local)
          }
        }),
        result.map(t => self.value_type(t, local)),
      )
    }
    InterfaceType(name, targs) =>
      InterfaceType(name, targs.map(t => self.value_type(t, scope)))
    PromptType(answer) => PromptType(answer.map(t => self.value_type(t, scope)))
    ResumeType(result, answer) =>
      ResumeType(
        result.map(t => self.value_type(t, scope)),
        answer.map(t => self.value_type(t, scope)),
      )
  }
}

///|
fn MonoElaborator::block_var(
  self : MonoElaborator,
  block : BlockVar,
  scope : MonoScope,
) -> BlockVar raise EffektError {
  match scope.blocks.get(block.id.uid()) {
    Some(encoded) =>
      BlockVar::{
        id: block.id,
        annotated_tpe: encoded.open_interface(),
        annotated_capt: block.annotated_capt,
      }
    None =>
      BlockVar::{
        id: block.id,
        annotated_tpe: self.block_type(block.annotated_tpe, scope),
        annotated_capt: block.annotated_capt,
      }
  }
}

///|
fn MonoElaborator::block(
  self : MonoElaborator,
  block : Block,
  scope : MonoScope,
) -> Block raise EffektError {
  match block {
    BlockVar(bv) => BlockVar(self.block_var(bv, scope))
    BlockLit(lit) => BlockLit(self.block_lit(lit, scope))
    Unbox(expr) => Unbox(self.expr(expr, scope))
    New(implementation) => New(self.implementation(implementation, scope))
  }
}

///|
fn MonoElaborator::implementation(
  self : MonoElaborator,
  implementation : Implementation,
  scope : MonoScope,
) -> Implementation raise EffektError {
  Implementation::{
    interface: self.block_type(implementation.interface, scope),
    operations: implementation.operations.map(op => self.operation(op, scope)),
  }
}

///|
fn MonoElaborator::expr(
  self : MonoElaborator,
  expr : Expr,
  scope : MonoScope,
) -> Expr raise EffektError {
  match expr {
    ValueVar(id, tpe) => ValueVar(id, self.value_type(tpe, scope))
    Literal(value, tpe) => Literal(value, self.value_type(tpe, scope))
    PureApp(callee, targs, vargs) =>
      PureApp(
        self.block_var(callee, scope),
        targs.map(t => self.value_type(t, scope)),
        vargs.map(v => self.expr(v, scope)),
      )
    Make(data, tag, targs, vargs) =>
      Make(
        self.value_type(data, scope),
        tag,
        targs.map(t => self.value_type(t, scope)),
        vargs.map(v => self.expr(v, scope)),
      )
    Box(inner, captures) => Box(self.block(inner, scope), captures)
  }
}

///|
fn MonoElaborator::stmt(
  self : MonoElaborator,
  stmt : Stmt,
  scope : MonoScope,
) -> Stmt raise EffektError {
  match stmt {
    Def(id, block, body) =>
      Def(id, self.block(block, scope), self.stmt(body, scope))
    Let(id, binding, body) =>
      Let(id, self.expr(binding, scope), self.stmt(body, scope))
    ImpureApp(id, callee, targs, vargs, bargs, body) => {
      let rewritten_targs = targs.map(t => self.value_type(t, scope))
      ImpureApp(
        id,
        self.block_var(callee, scope),
        rewritten_targs,
        vargs.map(v => self.expr(v, scope)),
        self.arguments(bargs, callee.annotated_tpe, rewritten_targs, scope),
        self.stmt(body, scope),
      )
    }
    Return(exprs) => Return(exprs.map(e => self.expr(e, scope)))
    Val(ids, binding, body) =>
      Val(ids, self.stmt(binding, scope), self.stmt(body, scope))
    App(callee, targs, vargs, bargs) => {
      let rewritten_targs = targs.map(t => self.value_type(t, scope))
      match callee {
        BlockVar(bv) =>
          match scope.blocks.get(bv.id.uid()) {
            Some(encoded) => {
              let rewritten_vargs = vargs.map(v => self.expr(v, scope))
              let rewritten_bargs = self.arguments(
                bargs,
                bv.annotated_tpe,
                rewritten_targs,
                scope,
              )
              Invoke(
                BlockVar(self.block_var(bv, scope)),
                encoded.encoding.method,
                self.block_type(bv.annotated_tpe, scope),
                rewritten_targs,
                rewritten_vargs,
                rewritten_bargs,
              )
            }
            None =>
              App(
                BlockVar(self.block_var(bv, scope)),
                rewritten_targs,
                vargs.map(v => self.expr(v, scope)),
                self.arguments(bargs, bv.annotated_tpe, rewritten_targs, scope),
              )
          }
        _ =>
          App(
            self.block(callee, scope),
            rewritten_targs,
            vargs.map(v => self.expr(v, scope)),
            self.arguments(bargs, callee.infer_type(), rewritten_targs, scope),
          )
      }
    }
    Invoke(callee, method, method_tpe, targs, vargs, bargs) => {
      let rewritten_targs = targs.map(t => self.value_type(t, scope))
      Invoke(
        self.block(callee, scope),
        method,
        self.block_type(method_tpe, scope),
        rewritten_targs,
        vargs.map(v => self.expr(v, scope)),
        self.arguments(bargs, method_tpe, rewritten_targs, scope),
      )
    }
    If(cond, thn, els) =>
      If(self.expr(cond, scope), self.stmt(thn, scope), self.stmt(els, scope))
    Match(scrutinee, result, clauses, default) =>
      Match(
        self.expr(scrutinee, scope),
        result.map(t => self.value_type(t, scope)),
        clauses.map(c => Clause::{
          tag: c.tag,
          body: self.block_lit(c.body, scope),
        }),
        default.map(s => self.stmt(s, scope)),
      )
    Region(body) => Region(self.block_lit(body, scope))
    Alloc(id, init, region, body) =>
      Alloc(id, self.expr(init, scope), region, self.stmt(body, scope))
    Var(id, init, capture, body) =>
      Var(id, self.expr(init, scope), capture, self.stmt(body, scope))
    Get(id, tpe, ref, capt, body) =>
      Get(id, self.value_type(tpe, scope), ref, capt, self.stmt(body, scope))
    Put(ref, capt, value, body) =>
      Put(ref, capt, self.expr(value, scope), self.stmt(body, scope))
    Reset(body) => Reset(self.block_lit(body, scope))
    Shift(prompt, continuation, body) =>
      Shift(
        self.block_var(prompt, scope),
        BlockParam::{
          id: continuation.id,
          tpe: self.block_type(continuation.tpe, scope),
          capt: continuation.capt,
        },
        self.stmt(body, scope),
      )
    Resume(continuation, body) =>
      Resume(self.block_var(continuation, scope), self.stmt(body, scope))
    Hole(tpes, span) => Hole(tpes.map(t => self.value_type(t, scope)), span)
  }
}

///|
/// The arguments of a call: a polymorphic block argument is wrapped into the
/// implementation of its encoding interface (`rewriteArguments`).
fn MonoElaborator::arguments(
  self : MonoElaborator,
  arguments : Array[Block],
  function : BlockType,
  targs : Array[ValueType],
  scope : MonoScope,
) -> Array[Block] raise EffektError {
  let (tparams, cparams, bparams) = match function {
    FunctionType(tparams, cparams, _, bparams, _) => (tparams, cparams, bparams)
    _ => ([], [], [])
  }
  let signature_scope = scope.bind_params(tparams, cparams)
  let out : Array[Block] = []
  for i, argument in arguments {
    let poly = if i < bparams.length() {
      match bparams[i] {
        FunctionType(inner, _, _, _, _) => !inner.is_empty()
        _ => false
      }
    } else {
      false
    }
    if poly {
      let btype = match bparams[i] {
        FunctionType(_, _, _, _, _) as f => f
        _ => bparams[i]
      }
      let encoded = self.state.encode(btype, signature_scope)
      let interface_args : Array[ValueType] = encoded.outer.map(id => {
        match
          mono_index_where(targs, t => {
            match t {
              ValueType::ValueVar(sym) => sym.uid() == id.uid()
              _ => false
            }
          }) {
          Some(index) => targs[index]
          None => ValueType::ValueVar(id)
        }
      })
      out.push(
        self.rewrite_block(
          self.block(argument, scope),
          encoded.interface(interface_args),
          encoded.encoding,
        ),
      )
    } else {
      out.push(self.block(argument, scope))
    }
  }
  out
}

///|
/// Wraps a block into the implementation of an encoding interface.
fn MonoElaborator::rewrite_block(
  self : MonoElaborator,
  block : Block,
  target : BlockType,
  encoding : MonoEncoding,
) -> Block raise EffektError {
  match block {
    BlockLit(lit) =>
      New(Implementation::{
        interface: target,
        operations: [
          Operation::{
            name: encoding.method,
            tparams: lit.tparams,
            cparams: lit.cparams,
            vparams: lit.vparams,
            bparams: lit.bparams,
            body: lit.body,
          },
        ],
      })
    BlockVar(bv) =>
      match bv.annotated_tpe {
        InterfaceType(name, _) if name.uid() == interface_name(target) =>
          BlockVar(bv)
        _ => self.rewrite_block_eta(block, target, encoding)
      }
    New(implementation) =>
      match implementation.interface {
        InterfaceType(name, _) if name.uid() == interface_name(target) =>
          New(implementation)
        _ => self.rewrite_block_eta(block, target, encoding)
      }
    _ => self.rewrite_block_eta(block, target, encoding)
  }
}

///|
fn interface_name(tpe : BlockType) -> Int32 {
  match tpe {
    InterfaceType(name, _) => name.uid()
    _ => -1
  }
}

///|
fn MonoElaborator::rewrite_block_eta(
  self : MonoElaborator,
  block : Block,
  target : BlockType,
  encoding : MonoEncoding,
) -> Block raise EffektError {
  match block.infer_type() {
    FunctionType(tparams, _, _, _, _) if !tparams.is_empty() =>
      self.rewrite_block(
        BlockLit(mono_eta_expand(block, block.infer_type())),
        target,
        encoding,
      )
    _ =>
      raise EffektError::Fatal(
        "Expected a polymorphic block literal, but found '\{show_core_block_type(block.infer_type())}'",
      )
  }
}

///|
/// `etaExpand` (`Mono.scala`): `f` becomes `{ [A](x: T) => f[A](x) }`.
fn mono_eta_expand(
  block : Block,
  function : BlockType,
) -> BlockLit raise EffektError {
  let (tparams, cparams, vparam_types, bparam_types, _) = match function {
    FunctionType(tparams, cparams, vparams, bparams, result) =>
      (tparams, cparams, vparams, bparams, result)
    _ => raise EffektError::Fatal("Expected a function type.")
  }
  if cparams.length() != bparam_types.length() {
    raise EffektError::Fatal("Expected as many capture parameters as blocks.")
  }
  let fresh_tparams : Array[Sym] = tparams.map(t => {
    Sym::type_param(Name::local(t.name().name), Span::missing())
  })
  let fresh_cparams : Array[Sym] = cparams.map(_ => {
    Sym::capture_param(Name::local("c"))
  })
  let vtypes : Map[Int32, ValueType] = Map([])
  for i, old in tparams {
    vtypes.set(old.uid(), ValueVar(fresh_tparams[i]))
  }
  // A capture parameter is a *set* in the port's core, so every id of the set
  // maps to the fresh parameter of the block it belongs to (upstream has one id
  // per parameter).
  let captures : Map[Int32, Captures] = Map([])
  for i, param in cparams {
    for old in mono_capture_params([param]) {
      captures.set(old.uid(), CaptureSetOf([fresh_cparams[i]]))
    }
  }
  let subst : Substitution = Substitution::Substitution(
    vtypes,
    captures,
    Map([]),
    Map([]),
  )
  let vparams : Array[ValueParam] = vparam_types.mapi((index, t) => ValueParam::{
    id: Sym::value_param(Name::local("x\{index}"), None, Span::missing()),
    tpe: substitute_value_type(t, subst),
  })
  let bparams : Array[BlockParam] = bparam_types.mapi((index, t) => BlockParam::{
    id: Sym::block_param(
      Name::local("f\{index}"),
      None,
      fresh_cparams[index],
      false,
      Span::missing(),
    ),
    tpe: substitute_block_type(t, subst),
    capt: CaptureSetOf([fresh_cparams[index]]),
  })
  let body = App(
    block,
    fresh_tparams.map(id => ValueType::ValueVar(id)),
    vparams.map(p => ValueVar(p.id, p.tpe)),
    bparams.map(p => {
      BlockVar(BlockVar::{
        id: p.id,
        annotated_tpe: p.tpe,
        annotated_capt: p.capt,
      })
    }),
  )
  BlockLit::{
    tparams: fresh_tparams,
    cparams: fresh_cparams,
    vparams,
    bparams,
    body,
  }
}

// ---------------------------------------------------------------------------
// Collecting the flows
// ---------------------------------------------------------------------------
//
// A flow is "the type arguments a usage site supplies to a flow variable":
// `Flow([Int], Option)` says `Option` is used with `Int` somewhere, and the
// arguments themselves may still mention other flow variables (a projection),
// which `solve` then resolves.

///|
priv struct MonoFlow {
  from : Array[MonoValueType[MonoProjection]]
  to : Sym
}

///|
fn MonoFlow::MonoFlow(
  from : Array[MonoValueType[MonoProjection]],
  to : Sym,
) -> MonoFlow {
  { from, to, }
}

///|
priv struct MonoEnvironment {
  variables : Map[Int32, MonoProjection]
  type_binders : Array[Array[Sym]]
  capture_binders : Array[Array[Sym]]
}

///|
fn MonoEnvironment::MonoEnvironment() -> MonoEnvironment {
  { variables: Map([]), type_binders: [], capture_binders: [], }
}

///|
fn MonoEnvironment::bind(
  self : MonoEnvironment,
  owner : Sym,
  params : ArrayView[Sym],
  offset : Int32,
) -> MonoEnvironment {
  let variables = self.variables
  for i, param in params {
    variables.set(param.uid(), { owner, position: offset + i, })
  }
  {
    variables,
    type_binders: self.type_binders,
    capture_binders: self.capture_binders,
  }
}

///|
fn MonoEnvironment::enter(
  self : MonoEnvironment,
  tparams : ArrayView[Sym],
  cparams : ArrayView[Captures],
) -> MonoEnvironment {
  {
    variables: self.variables,
    type_binders: [tparams.to_owned()] + self.type_binders,
    capture_binders: [mono_capture_params(cparams)] + self.capture_binders,
  }
}

///|
fn MonoEnvironment::type_variable(
  self : MonoEnvironment,
  id : Sym,
) -> MonoValueType[MonoProjection] raise EffektError {
  match mono_binder_index(id, self.type_binders) {
    Some((level, position)) => MonoValueBound(level, position)
    None =>
      match self.variables.get(id.uid()) {
        Some(projection) => MonoValueVar(projection)
        None =>
          raise EffektError::Fatal(
            "Unbound type variable '\{id.name().name}' while collecting monomorphization flows",
          )
      }
  }
}

///|
fn MonoEnvironment::capture(self : MonoEnvironment, id : Sym) -> MonoCapture {
  match mono_binder_index(id, self.capture_binders) {
    Some((level, position)) => MonoCaptureBound(level, position)
    None => MonoCaptureNamed(id)
  }
}

///|
fn mono_collect(module : ModuleDecl) -> Array[MonoFlow] raise EffektError {
  let env = MonoEnvironment::MonoEnvironment()
  let out : Array[MonoFlow] = []
  for decl in module.declarations {
    mono_collect_declaration(decl, env, out)
  }
  for external in module.externs {
    mono_collect_extern(external, env, out)
  }
  for definition in module.definitions {
    mono_collect_toplevel(definition, env, out)
  }
  out
}

///|
fn mono_collect_toplevel(
  definition : Toplevel,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  match definition {
    ToplevelDef(id, BlockLit(lit)) =>
      mono_collect_function(id, 0, lit, env, out)
    ToplevelDef(_, block) => mono_collect_block(block, env, out)
    ToplevelVal(_, binding) => mono_collect_stmt(binding, env, out)
  }
}

///|
fn mono_collect_declaration(
  decl : Declaration,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  match decl {
    DeclarationData(id, tparams, constructors) => {
      let data_env = env.bind(id, tparams, 0)
      let outer_arity = tparams.length()
      for constructor in constructors {
        if outer_arity > 0 {
          let from : Array[MonoValueType[MonoProjection]] = []
          for i in 0..<outer_arity {
            from.push(MonoValueVar({ owner: constructor.id, position: i, }))
          }
          out.push(MonoFlow::MonoFlow(from, id))
        }
        let ctor_env = data_env.bind(
          constructor.id,
          constructor.tparams,
          outer_arity,
        )
        for field in constructor.fields {
          ignore(mono_collect_value_type(field.tpe, ctor_env, out))
        }
      }
    }
    DeclarationInterface(id, tparams, properties) => {
      let interface_env = env.bind(id, tparams, 0)
      let outer_arity = tparams.length()
      for property in properties {
        if outer_arity > 0 {
          let from : Array[MonoValueType[MonoProjection]] = []
          for i in 0..<outer_arity {
            from.push(MonoValueVar({ owner: property.id, position: i, }))
          }
          out.push(MonoFlow::MonoFlow(from, id))
        }
        match property.tpe {
          FunctionType(_, _, _, _, _) =>
            mono_collect_function_tpe(
              property.id,
              outer_arity,
              property.tpe,
              interface_env,
              out,
            )
          other => ignore(mono_collect_block_type(other, interface_env, out))
        }
      }
    }
  }
}

///|
fn mono_collect_extern(
  external : Extern,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  guard external
    is ExternDef(id, _, tparams, _, vparams, bparams, result, _, body) else {
    return
  }
  let local = env.bind(id, tparams, 0)
  for param in vparams {
    ignore(mono_collect_value_type(param.tpe, local, out))
  }
  for param in bparams {
    ignore(mono_collect_block_type(param.tpe, local, out))
  }
  ignore(mono_collect_value_type(result, local, out))
  if body is StringExternBody(_, template) {
    for argument in template.args {
      mono_collect_expr(argument, local, out)
    }
  }
}

///|
fn mono_collect_function(
  owner : Sym,
  offset : Int32,
  lit : BlockLit,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  let local = env.bind(owner, lit.tparams, offset)
  mono_collect_parameters(lit.vparams, lit.bparams, local, out)
  mono_collect_stmt(lit.body, local, out)
}

///|
fn mono_collect_function_tpe(
  owner : Sym,
  offset : Int32,
  tpe : BlockType,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  match tpe {
    FunctionType(tparams, _, vparams, bparams, result) => {
      let local = env.bind(owner, tparams, offset)
      for param in vparams {
        ignore(mono_collect_value_type(param, local, out))
      }
      for param in bparams {
        ignore(mono_collect_block_type(param, local, out))
      }
      for r in result {
        ignore(mono_collect_value_type(r, local, out))
      }
    }
    other => ignore(mono_collect_block_type(other, env, out))
  }
}

///|
fn mono_collect_parameters(
  vparams : Array[ValueParam],
  bparams : Array[BlockParam],
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  for param in vparams {
    ignore(mono_collect_value_type(param.tpe, env, out))
  }
  for param in bparams {
    ignore(mono_collect_block_type(param.tpe, env, out))
  }
}

///|
fn mono_collect_block(
  block : Block,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  match block {
    BlockVar(bv) =>
      match bv.annotated_tpe {
        FunctionType(_, _, _, _, _) =>
          mono_collect_function_tpe(bv.id, 0, bv.annotated_tpe, env, out)
        other => ignore(mono_collect_block_type(other, env, out))
      }
    BlockLit(lit) => {
      if !lit.tparams.is_empty() {
        raise EffektError::Fatal(
          "Anonymous polymorphic block reached monomorphization: \{show_core_block_type(lit.infer_type())}",
        )
      }
      mono_collect_parameters(lit.vparams, lit.bparams, env, out)
      mono_collect_stmt(lit.body, env, out)
    }
    Unbox(expr) => mono_collect_expr(expr, env, out)
    New(implementation) => mono_collect_implementation(implementation, env, out)
  }
}

///|
fn mono_collect_implementation(
  implementation : Implementation,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  ignore(mono_collect_block_type(implementation.interface, env, out))
  let offset = match implementation.interface {
    InterfaceType(_, targs) => targs.length()
    _ => 0
  }
  for operation in implementation.operations {
    mono_collect_operation(operation, offset, env, out)
  }
}

///|
fn mono_collect_operation(
  op : Operation,
  offset : Int32,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  let local = env.bind(op.name, op.tparams, offset)
  mono_collect_parameters(op.vparams, op.bparams, local, out)
  mono_collect_stmt(op.body, local, out)
}

///|
fn mono_collect_stmt(
  stmt : Stmt,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  match stmt {
    Def(id, BlockLit(lit), body) => {
      mono_collect_function(id, 0, lit, env, out)
      mono_collect_stmt(body, env, out)
    }
    Def(_, block, body) => {
      mono_collect_block(block, env, out)
      mono_collect_stmt(body, env, out)
    }
    Let(_, binding, body) => {
      mono_collect_expr(binding, env, out)
      mono_collect_stmt(body, env, out)
    }
    ImpureApp(_, callee, targs, vargs, bargs, body) => {
      mono_collect_application(callee, targs, vargs, bargs, env, out)
      mono_collect_stmt(body, env, out)
    }
    Return(exprs) =>
      for expr in exprs {
        mono_collect_expr(expr, env, out)
      }
    Val(_, binding, body) => {
      mono_collect_stmt(binding, env, out)
      mono_collect_stmt(body, env, out)
    }
    App(callee, targs, vargs, bargs) =>
      mono_collect_application_block(callee, targs, vargs, bargs, env, out)
    Invoke(callee, method, method_tpe, targs, vargs, bargs) => {
      let receiver_targs = match callee.infer_type() {
        BlockType::InterfaceType(_, arguments) => arguments
        other =>
          raise EffektError::Fatal(
            "Expected an interface receiver, but found '\{show_core_block_type(other)}'",
          )
      }
      let combined = receiver_targs + targs
      let from = mono_collect_value_types(combined, env, out)
      out.push(MonoFlow::MonoFlow(from, method))
      match method_tpe {
        FunctionType(_, _, _, _, _) =>
          mono_collect_function_tpe(
            method,
            receiver_targs.length(),
            method_tpe,
            env,
            out,
          )
        other => ignore(mono_collect_block_type(other, env, out))
      }
      mono_collect_block(callee, env, out)
      for varg in vargs {
        mono_collect_expr(varg, env, out)
      }
      for barg in bargs {
        mono_collect_block(barg, env, out)
      }
    }
    If(cond, thn, els) => {
      mono_collect_expr(cond, env, out)
      mono_collect_stmt(thn, env, out)
      mono_collect_stmt(els, env, out)
    }
    Match(scrutinee, result, clauses, default) => {
      let outer_arity = match scrutinee.infer_type() {
        ValueData(_, targs) => targs.length()
        _ => 0
      }
      mono_collect_expr(scrutinee, env, out)
      for r in result {
        ignore(mono_collect_value_type(r, env, out))
      }
      for clause in clauses {
        let local = env.bind(clause.tag, clause.body.tparams, outer_arity)
        mono_collect_parameters(
          clause.body.vparams,
          clause.body.bparams,
          local,
          out,
        )
        mono_collect_stmt(clause.body.body, local, out)
      }
      if default is Some(s) {
        mono_collect_stmt(s, env, out)
      }
    }
    Region(body) => mono_collect_block(BlockLit(body), env, out)
    Alloc(_, init, _, body) => {
      mono_collect_expr(init, env, out)
      mono_collect_stmt(body, env, out)
    }
    Var(_, init, _, body) => {
      mono_collect_expr(init, env, out)
      mono_collect_stmt(body, env, out)
    }
    Get(_, tpe, _, _, body) => {
      ignore(mono_collect_value_type(tpe, env, out))
      mono_collect_stmt(body, env, out)
    }
    Put(_, _, value, body) => {
      mono_collect_expr(value, env, out)
      mono_collect_stmt(body, env, out)
    }
    Reset(body) => mono_collect_block(BlockLit(body), env, out)
    Shift(prompt, continuation, body) => {
      mono_collect_block(BlockVar(prompt), env, out)
      ignore(mono_collect_block_type(continuation.tpe, env, out))
      mono_collect_stmt(body, env, out)
    }
    Resume(continuation, body) => {
      mono_collect_block(BlockVar(continuation), env, out)
      mono_collect_stmt(body, env, out)
    }
    Hole(tpes, _) =>
      for tpe in tpes {
        ignore(mono_collect_value_type(tpe, env, out))
      }
  }
}

///|
/// The flows of an application whose callee is a block (not a `BlockVar`).
fn mono_collect_application_block(
  callee : Block,
  targs : Array[ValueType],
  vargs : Array[Expr],
  bargs : Array[Block],
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  match callee {
    BlockVar(bv) => mono_collect_application(bv, targs, vargs, bargs, env, out)
    _ => {
      if !targs.is_empty() {
        raise EffektError::Fatal(
          "Polymorphic application has no stable flow variable",
        )
      }
      mono_collect_block(callee, env, out)
      for varg in vargs {
        mono_collect_expr(varg, env, out)
      }
      for barg in bargs {
        mono_collect_block(barg, env, out)
      }
    }
  }
}

///|
fn mono_collect_application(
  callee : BlockVar,
  targs : Array[ValueType],
  vargs : Array[Expr],
  bargs : Array[Block],
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  let arguments = mono_collect_value_types(targs, env, out)
  match callee.annotated_tpe {
    FunctionType(_, _, _, _, _) =>
      mono_collect_function_tpe(callee.id, 0, callee.annotated_tpe, env, out)
    other => ignore(mono_collect_block_type(other, env, out))
  }
  out.push(MonoFlow::MonoFlow(arguments, callee.id))
  for varg in vargs {
    mono_collect_expr(varg, env, out)
  }
  for barg in bargs {
    mono_collect_block(barg, env, out)
  }
}

///|
fn mono_collect_expr(
  expr : Expr,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Unit raise EffektError {
  match expr {
    PureApp(callee, targs, vargs) => {
      let arguments = mono_collect_value_types(targs, env, out)
      match callee.annotated_tpe {
        FunctionType(_, _, _, _, _) =>
          mono_collect_function_tpe(
            callee.id,
            0,
            callee.annotated_tpe,
            env,
            out,
          )
        other => ignore(mono_collect_block_type(other, env, out))
      }
      out.push(MonoFlow::MonoFlow(arguments, callee.id))
      for varg in vargs {
        mono_collect_expr(varg, env, out)
      }
    }
    ValueVar(_, tpe) => ignore(mono_collect_value_type(tpe, env, out))
    Literal(_, tpe) => ignore(mono_collect_value_type(tpe, env, out))
    Make(data, tag, targs, vargs) => {
      ignore(mono_collect_value_type(data, env, out))
      let data_targs = match data {
        ValueData(_, targs) => targs
        _ => []
      }
      let arguments = mono_collect_value_types(data_targs + targs, env, out)
      if data is ValueData(name, _) && data_targs.is_empty() {
        out.push(MonoFlow::MonoFlow([], name))
      }
      out.push(MonoFlow::MonoFlow(arguments, tag))
      for varg in vargs {
        mono_collect_expr(varg, env, out)
      }
    }
    Box(block, _) => mono_collect_block(block, env, out)
  }
}

///|
fn mono_collect_value_types(
  tpes : ArrayView[ValueType],
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> Array[MonoValueType[MonoProjection]] raise EffektError {
  let result : Array[MonoValueType[MonoProjection]] = []
  for tpe in tpes {
    result.push(mono_collect_value_type(tpe, env, out))
  }
  result
}

///|
fn mono_collect_value_type(
  tpe : ValueType,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> MonoValueType[MonoProjection] raise EffektError {
  match tpe {
    ValueVar(id) => env.type_variable(id)
    ValueData(name, targs) => {
      let arguments = mono_collect_value_types(targs, env, out)
      if !arguments.is_empty() {
        out.push(MonoFlow::MonoFlow(arguments, name))
      }
      MonoValueData(name, arguments)
    }
    ValueBoxed(inner, captures) => {
      let boxed = mono_collect_block_type(inner, env, out)
      MonoValueBoxed(boxed, captures.to_array().map(c => env.capture(c)))
    }
  }
}

///|
fn mono_collect_block_type(
  tpe : BlockType,
  env : MonoEnvironment,
  out : Array[MonoFlow],
) -> MonoBlockType[MonoProjection] raise EffektError {
  match tpe {
    InterfaceType(name, targs) => {
      let arguments = mono_collect_value_types(targs, env, out)
      out.push(MonoFlow::MonoFlow(arguments, name))
      MonoInterface(name, arguments)
    }
    PromptType(answer) => {
      let answers = mono_collect_value_types(answer, env, out)
      MonoPrompt(answers)
    }
    ResumeType(result, answer) => {
      let results = mono_collect_value_types(result, env, out)
      let answers = mono_collect_value_types(answer, env, out)
      MonoResume(results, answers)
    }
    FunctionType(tparams, cparams, vparams, bparams, result) => {
      let local = env.enter(tparams, cparams)
      let vparam_types : Array[MonoValueType[MonoProjection]] = []
      for param in vparams {
        vparam_types.push(mono_collect_value_type(param, local, out))
      }
      let bparam_types : Array[MonoBlockType[MonoProjection]] = []
      for param in bparams {
        bparam_types.push(mono_collect_block_type(param, local, out))
      }
      let result_types = mono_collect_value_types(result, local, out)
      MonoFunction(
        tparams.length(),
        cparams.length(),
        vparam_types,
        bparam_types,
        result_types,
      )
    }
  }
}

// ---------------------------------------------------------------------------
// Solving the flows
// ---------------------------------------------------------------------------

///|
/// One variant of a flow variable: the type arguments of one instantiation,
/// still mentioning the projections of the variables they came from.
type MonoVariant = Array[MonoValueType[MonoProjection]]

///|
/// A solution maps every flow variable to the ground variants it is used with.
type MonoSolution = Map[Int32, Array[Array[MonoValueType[Unit]]]]

///|
fn mono_ground_variant_key(variant : ArrayView[MonoValueType[Unit]]) -> String {
  variant.map(t => mono_value_type_key(t, _ => "")).join(",")
}

///|
/// `Array::search_by`, which the standard library does not have: the index of
/// the first element that satisfies `pred`.
fn[T] mono_index_where(xs : ArrayView[T], pred : (T) -> Bool) -> Int32? {
  for i, x in xs {
    if pred(x) {
      return Some(i)
    }
  }
  None
}

///|
/// Pushes `value` unless an element that is equal to it is already there.
fn[T : Eq] mono_push_unique(xs : Array[T], value : T) -> Unit {
  if !xs.any(x => x == value) {
    xs.push(value)
  }
}

///|
fn mono_bounds_equal(
  a : Map[Int32, Array[MonoVariant]],
  b : Map[Int32, Array[MonoVariant]],
) -> Bool {
  guard a.length() == b.length() else { return false }
  for uid, variants in a {
    match b.get(uid) {
      Some(other) => {
        guard variants.length() == other.length() else { return false }
        for i in 0..<variants.length() {
          if variants[i] != other[i] {
            return false
          }
        }
      }
      None => return false
    }
  }
  true
}

///|
fn mono_solve(constraints : Array[MonoFlow]) -> MonoSolution raise EffektError {
  let initial : Map[Int32, Array[MonoVariant]] = Map([])
  for flow in constraints {
    match initial.get(flow.to.uid()) {
      Some(variants) => mono_push_unique(variants, flow.from)
      None => initial.set(flow.to.uid(), [flow.from])
    }
  }
  let bounds = mono_fixed_point(initial)
  let solution : MonoSolution = Map([])
  for uid, variants in bounds {
    let ground : Array[Array[MonoValueType[Unit]]] = []
    for variant in variants {
      if mono_ground_variant(variant, [], []) is Some(g) {
        mono_push_unique(ground, g)
      }
    }
    if !ground.is_empty() {
      solution.set(uid, ground)
    }
  }
  solution
}

///|
fn mono_fixed_point(
  bounds : Map[Int32, Array[MonoVariant]],
) -> Map[Int32, Array[MonoVariant]] raise EffektError {
  let next : Map[Int32, Array[MonoVariant]] = Map([])
  for owner, variants in bounds {
    next.set(owner, mono_propagate(owner, variants, bounds))
  }
  if mono_bounds_equal(next, bounds) {
    bounds
  } else {
    mono_fixed_point(next)
  }
}

///|
fn mono_propagate(
  owner : Int32,
  variants : Array[MonoVariant],
  bounds : Map[Int32, Array[MonoVariant]],
) -> Array[MonoVariant] raise EffektError {
  let result : Array[MonoVariant] = []
  for variant in variants {
    // the dependencies of this variant: the flow variables mentioned in it
    let dependencies : Array[Sym] = []
    for tpe in variant {
      for dependency in mono_dependencies_value(tpe) {
        if !dependencies.any(d => d.uid() == dependency.uid()) {
          dependencies.push(dependency)
        }
      }
    }
    // all combinations of the alternatives of those dependencies
    let substitutions : Array[Map[Int32, MonoVariant]] = [Map([])]
    for dependency in dependencies {
      let alternatives = bounds.get(dependency.uid()).unwrap_or([])
      let next : Array[Map[Int32, MonoVariant]] = []
      for substitution in substitutions {
        for alternative in alternatives {
          let extended = substitution.copy()
          extended.set(dependency.uid(), alternative)
          next.push(extended)
        }
      }
      substitutions.clear()
      substitutions.append(next)
    }
    for substitution in substitutions {
      let substituted : MonoVariant = variant.map(t => {
        mono_substitute_value(t, substitution)
      })
      mono_push_unique(result, substituted)
    }
  }
  mono_reject_growing_recursion(owner, result)
  result
}

///|
fn mono_substitute_value(
  tpe : MonoValueType[MonoProjection],
  substitution : Map[Int32, MonoVariant],
) -> MonoValueType[MonoProjection] {
  match tpe {
    MonoValueVar(projection) =>
      match substitution.get(projection.owner.uid()) {
        Some(variant) => variant[projection.position]
        None => tpe
      }
    MonoValueBound(_, _) => tpe
    MonoValueData(name, targs) =>
      MonoValueData(
        name,
        targs.map(t => mono_substitute_value(t, substitution)),
      )
    MonoValueBoxed(inner, captures) =>
      MonoValueBoxed(mono_substitute_block(inner, substitution), captures)
  }
}

///|
fn mono_substitute_block(
  tpe : MonoBlockType[MonoProjection],
  substitution : Map[Int32, MonoVariant],
) -> MonoBlockType[MonoProjection] {
  match tpe {
    MonoFunction(tarity, carity, vparams, bparams, result) =>
      MonoFunction(
        tarity,
        carity,
        vparams.map(t => mono_substitute_value(t, substitution)),
        bparams.map(t => mono_substitute_block(t, substitution)),
        result.map(t => mono_substitute_value(t, substitution)),
      )
    MonoInterface(name, targs) =>
      MonoInterface(
        name,
        targs.map(t => mono_substitute_value(t, substitution)),
      )
    MonoPrompt(answer) =>
      MonoPrompt(answer.map(t => mono_substitute_value(t, substitution)))
    MonoResume(result, answer) =>
      MonoResume(
        result.map(t => mono_substitute_value(t, substitution)),
        answer.map(t => mono_substitute_value(t, substitution)),
      )
  }
}

///|
fn mono_dependencies_value(tpe : MonoValueType[MonoProjection]) -> Array[Sym] {
  match tpe {
    MonoValueVar(projection) => [projection.owner]
    MonoValueBound(_, _) => []
    MonoValueData(_, targs) =>
      mono_flat_map(targs, t => mono_dependencies_value(t))
    MonoValueBoxed(inner, _) => mono_dependencies_block(inner)
  }
}

///|
fn mono_dependencies_block(tpe : MonoBlockType[MonoProjection]) -> Array[Sym] {
  match tpe {
    MonoFunction(_, _, vparams, bparams, result) =>
      mono_flat_map(vparams, t => mono_dependencies_value(t)) +
      mono_flat_map(bparams, t => mono_dependencies_block(t)) +
      mono_flat_map(result, t => mono_dependencies_value(t))
    MonoInterface(_, targs) =>
      mono_flat_map(targs, t => mono_dependencies_value(t))
    MonoPrompt(answer) => mono_flat_map(answer, t => mono_dependencies_value(t))
    MonoResume(result, answer) =>
      mono_flat_map(result, t => mono_dependencies_value(t)) +
      mono_flat_map(answer, t => mono_dependencies_value(t))
  }
}

///|
/// A recursive definition whose own variant appears under a type constructor
/// (`f[A]` calls `f[List[A]]`) has no finite set of instances.
fn mono_reject_growing_recursion(
  owner : Int32,
  variants : Array[MonoVariant],
) -> Unit raise EffektError {
  for variant in variants {
    for tpe in variant {
      if mono_grows(owner, tpe, false) {
        raise EffektError::Fatal(
          "Detected polymorphic recursion for '\{owner}'",
        )
      }
    }
  }
}

///|
fn mono_grows(
  owner : Int32,
  tpe : MonoValueType[MonoProjection],
  guarded : Bool,
) -> Bool {
  match tpe {
    MonoValueVar(projection) => guarded && projection.owner.uid() == owner
    MonoValueBound(_, _) => false
    MonoValueData(_, targs) => targs.any(t => mono_grows(owner, t, true))
    MonoValueBoxed(inner, _) => mono_grows_block(owner, inner)
  }
}

///|
fn mono_grows_block(owner : Int32, tpe : MonoBlockType[MonoProjection]) -> Bool {
  match tpe {
    MonoFunction(_, _, vparams, bparams, result) =>
      vparams.any(t => mono_grows(owner, t, true)) ||
      bparams.any(t => mono_grows_block(owner, t)) ||
      result.any(t => mono_grows(owner, t, true))
    MonoInterface(_, targs) => targs.any(t => mono_grows(owner, t, true))
    MonoPrompt(answer) => answer.any(t => mono_grows(owner, t, true))
    MonoResume(result, answer) =>
      result.any(t => mono_grows(owner, t, true)) ||
      answer.any(t => mono_grows(owner, t, true))
  }
}

///|
/// Grounds a variant: `None` if it still mentions a flow variable or a bound
/// type parameter that the surrounding binders do not bind.
fn mono_ground_variant(
  variant : ArrayView[MonoValueType[MonoProjection]],
  type_binders : Array[Int32],
  capture_binders : Array[Int32],
) -> Array[MonoValueType[Unit]]? {
  let out : Array[MonoValueType[Unit]] = []
  for tpe in variant {
    match mono_ground_value_type(tpe, type_binders, capture_binders) {
      Some(ground) => out.push(ground)
      None => return None
    }
  }
  Some(out)
}

///|
fn mono_ground_value_type(
  tpe : MonoValueType[MonoProjection],
  type_binders : Array[Int32],
  capture_binders : Array[Int32],
) -> MonoValueType[Unit]? {
  match tpe {
    MonoValueVar(_) => None
    MonoValueBound(level, position) =>
      if mono_is_bound(level, position, type_binders) {
        Some(MonoValueBound(level, position))
      } else {
        None
      }
    MonoValueData(name, targs) => {
      let out : Array[MonoValueType[Unit]] = []
      for t in targs {
        match mono_ground_value_type(t, type_binders, capture_binders) {
          Some(ground) => out.push(ground)
          None => return None
        }
      }
      Some(MonoValueData(name, out))
    }
    MonoValueBoxed(inner, captures) =>
      mono_ground_block_type(inner, type_binders, capture_binders)
      .map(ground => MonoValueBoxed(ground, captures))
      .filter(_ => {
        // a box is ground only if every capture in it is bound here
        captures.all(c => {
          match c {
            MonoCaptureBound(level, position) =>
              mono_is_bound(level, position, capture_binders)
            MonoCaptureNamed(_) => true
          }
        })
      })
  }
}

///|
fn mono_ground_block_type(
  tpe : MonoBlockType[MonoProjection],
  type_binders : Array[Int32],
  capture_binders : Array[Int32],
) -> MonoBlockType[Unit]? {
  match tpe {
    MonoFunction(tarity, carity, vparams, bparams, result) => {
      let local_types = [tarity] + type_binders
      let local_captures = [carity] + capture_binders
      let ground_vparams : Array[MonoValueType[Unit]] = []
      for param in vparams {
        match mono_ground_value_type(param, local_types, local_captures) {
          Some(ground) => ground_vparams.push(ground)
          None => return None
        }
      }
      let ground_bparams : Array[MonoBlockType[Unit]] = []
      for param in bparams {
        match mono_ground_block_type(param, local_types, local_captures) {
          Some(ground) => ground_bparams.push(ground)
          None => return None
        }
      }
      let ground_result : Array[MonoValueType[Unit]] = []
      for r in result {
        match mono_ground_value_type(r, local_types, local_captures) {
          Some(ground) => ground_result.push(ground)
          None => return None
        }
      }
      Some(
        MonoFunction(
          tarity, carity, ground_vparams, ground_bparams, ground_result,
        ),
      )
    }
    MonoInterface(name, targs) => {
      let ground : Array[MonoValueType[Unit]] = []
      for t in targs {
        match mono_ground_value_type(t, type_binders, capture_binders) {
          Some(g) => ground.push(g)
          None => return None
        }
      }
      Some(MonoInterface(name, ground))
    }
    MonoPrompt(answer) => {
      let ground : Array[MonoValueType[Unit]] = []
      for t in answer {
        match mono_ground_value_type(t, type_binders, capture_binders) {
          Some(g) => ground.push(g)
          None => return None
        }
      }
      Some(MonoPrompt(ground))
    }
    MonoResume(result, answer) => {
      let ground_result : Array[MonoValueType[Unit]] = []
      for t in result {
        match mono_ground_value_type(t, type_binders, capture_binders) {
          Some(g) => ground_result.push(g)
          None => return None
        }
      }
      let ground_answer : Array[MonoValueType[Unit]] = []
      for t in answer {
        match mono_ground_value_type(t, type_binders, capture_binders) {
          Some(g) => ground_answer.push(g)
          None => return None
        }
      }
      Some(MonoResume(ground_result, ground_answer))
    }
  }
}

///|
fn mono_is_bound(
  level : Int32,
  position : Int32,
  binders : Array[Int32],
) -> Bool {
  guard level >= 0 && position >= 0 else { return false }
  binders.get(level) is Some(arity) && position < arity
}
// ---------------------------------------------------------------------------
// Specializing the tree
// ---------------------------------------------------------------------------

///|
priv struct MonoSpecialize {
  solution : MonoSolution
  owners : Map[Int32, Sym]
  fun_names : Map[String, Sym]
  tpe_names : Map[String, ValueType]
  /// The inverse of `tpe_names`: the monomorphized data name to the variant it
  /// stands for (`Match` needs it to know which case belongs to which variant).
  tpe_names_inverse : Map[Int32, (Sym, Array[MonoValueType[Unit]])]
  poly_extern_defs : Map[Int32, Bool]
  substitution : Map[Int32, MonoValueType[Unit]]
}

///|
fn MonoSpecialize::MonoSpecialize(
  solution : MonoSolution,
  owners : Map[Int32, Sym],
) -> MonoSpecialize {
  {
    solution,
    owners,
    fun_names: Map([]),
    tpe_names: Map([]),
    tpe_names_inverse: Map([]),
    poly_extern_defs: Map([]),
    substitution: Map([]),
  }
}

///|
fn MonoSpecialize::bind(
  self : MonoSpecialize,
  tparams : ArrayView[Sym],
  targs : ArrayView[MonoValueType[Unit]],
) -> MonoSpecialize {
  // A variant can be longer than the parameters it is bound to: the constructor
  // `None` of `Option[A]` has no parameters of its own, but its variant carries
  // the arguments of the data type. Upstream zips the two lists, and its arity
  // assertion (`util.assert`) is compiled out of release builds, so the extra
  // arguments are simply dropped.
  let substitution = self.substitution.copy()
  for i, param in tparams {
    guard i < targs.length() else { break }
    substitution.set(param.uid(), targs[i])
  }
  {
    solution: self.solution,
    owners: self.owners,
    fun_names: self.fun_names,
    tpe_names: self.tpe_names,
    tpe_names_inverse: self.tpe_names_inverse,
    poly_extern_defs: self.poly_extern_defs,
    substitution,
  }
}

///|
fn MonoSpecialize::variants(
  self : MonoSpecialize,
  id : Sym,
) -> Array[Array[MonoValueType[Unit]]] {
  let variants = self.solution.get(id.uid()).unwrap_or([])
  let sorted = variants.copy()
  sorted
  .mut_view()
  .stable_sort_by((a, b) => {
    mono_ground_variant_key(a).lexical_compare(mono_ground_variant_key(b))
  })
  sorted
}

///|
fn MonoSpecialize::fun_name(
  self : MonoSpecialize,
  id : Sym,
  variant : ArrayView[MonoValueType[Unit]],
) -> Sym raise EffektError {
  match self.fun_names.get(mono_key(id, variant)) {
    Some(name) => name
    None =>
      raise EffektError::Fatal(
        "No monomorphized name for '\{id.name().name}' with variant \{mono_ground_variant_key(variant)}",
      )
  }
}

///|
fn MonoSpecialize::tpe_name(
  self : MonoSpecialize,
  id : Sym,
  variant : ArrayView[MonoValueType[Unit]],
) -> ValueType raise EffektError {
  match self.tpe_names.get(mono_key(id, variant)) {
    Some(name) => name
    None =>
      raise EffektError::Fatal(
        "No monomorphized data type for '\{id.name().name}' with variant \{mono_ground_variant_key(variant)}",
      )
  }
}

///|
fn mono_is_extern_def(dctx : DeclarationContext, id : Sym) -> Bool {
  dctx.extern_defs.contains(id.uid())
}

///|
fn mono_is_data(dctx : DeclarationContext, id : Sym) -> Bool {
  dctx.datas.contains(id.uid())
}

///|
/// `id is ExternInterface` (`Mono.scala`): an interface that the backends
/// implement by hand keeps its name, so that calls still resolve to it.
fn mono_is_extern_interface(dctx : DeclarationContext, id : Sym) -> Bool {
  dctx.externs.any(e => {
    match e {
      ExternInterface(sym, _, _) => sym.uid() == id.uid()
      ExternData(sym, _, _) => sym.uid() == id.uid()
      _ => false
    }
  })
}

///|
/// `preferredMonoName` / `freshMonoTypeName`: upstream appends the type
/// arguments to the declared name, but only in debug builds
/// (`util.debug(...)("")` in `Mono.scala`), so a normal build names an instance
/// like its declaration (`Cons`, not `Cons_Int`).
///
/// The *fresh* symbol is what matters: `Id.apply` wraps the name in a new
/// symbol, so every instance is a symbol of its own — that is how the backends
/// give each one a distinct JS name. A fresh symbol with the same name is the
/// port's equivalent (a `Sym` carries a uid); reusing the original would make
/// two instances look like one definition.
fn MonoSpecialize::fresh_data_name(
  self : MonoSpecialize,
  data : Sym,
  variant : ArrayView[MonoValueType[Unit]],
) -> ValueType {
  let key = mono_key(data, variant)
  match self.tpe_names.get(key) {
    Some(name) => name
    None => {
      let name = Sym::id(Name::local(data.name().name))
      let result = ValueData(name, [])
      self.tpe_names.set(key, result)
      self.tpe_names_inverse.set(name.uid(), (data, variant.to_owned()))
      result
    }
  }
}

///|
fn mono_specialize(
  module : ModuleDecl,
  solution : MonoSolution,
  owners : Map[Int32, Sym],
) -> ModuleDecl raise EffektError {
  let dctx = DeclarationContext::DeclarationContext(
    module.declarations,
    module.externs,
  )
  let state = MonoSpecialize::MonoSpecialize(solution, owners)

  // collect the owners, sorted by name so that fresh names are deterministic
  let uids : Array[Int32] = []
  for uid, _ in solution {
    uids.push(uid)
  }
  uids
  .mut_view()
  .stable_sort_by((a, b) => {
    let an = match owners.get(a) {
      Some(sym) => sym.name().name
      None => ""
    }
    let bn = match owners.get(b) {
      Some(sym) => sym.name().name
      None => ""
    }
    an.lexical_compare(bn)
  })
  for uid in uids {
    match owners.get(uid) {
      Some(id) => {
        let variants = state.variants(id)
        if mono_is_extern_def(dctx, id) {
          for variant in variants {
            state.fun_names.set(mono_key(id, variant), id)
          }
        } else if mono_is_data(dctx, id) {
          for variant in variants {
            ignore(state.fresh_data_name(id, variant))
          }
        } else {
          for variant in variants {
            // `if variant.isEmpty || id is ExternInterface then id else
            // fresh(preferredMonoName(id, variant))`: an instance is a fresh
            // symbol of the same name, but the name is not mangled outside of
            // debug builds (see `fresh_data_name`).
            let name = if variant.is_empty() ||
              mono_is_extern_interface(dctx, id) {
              id
            } else {
              Sym::id(Name::local(id.name().name))
            }
            state.fun_names.set(mono_key(id, variant), name)
          }
        }
      }
      None => ()
    }
  }
  // declarations that are already monomorphic: no instance, but the name is
  // still what the specialized tree refers to
  for decl in module.declarations {
    match decl {
      DeclarationData(id, tparams, _) =>
        if tparams.is_empty() {
          state.tpe_names.set(mono_key(id, []), ValueData(id, []))
        }
      DeclarationInterface(id, tparams, _) =>
        if tparams.is_empty() {
          state.fun_names.set(mono_key(id, []), id)
        }
    }
  }
  for external in module.externs {
    if external is ExternDef(id, _, tparams, _, _, _, _, _, _) &&
      !tparams.is_empty() {
      state.poly_extern_defs.set(id.uid(), true)
    }
  }

  let declarations : Array[Declaration] = []
  for decl in module.declarations {
    declarations.append(mono_monomorphize_declaration(state, dctx, decl))
  }
  let definitions : Array[Toplevel] = []
  for definition in module.definitions {
    definitions.append(mono_monomorphize_toplevel(state, dctx, definition))
  }
  ModuleDecl::{
    path: module.path,
    includes: module.includes,
    declarations,
    externs: module.externs,
    definitions,
    exports: module.exports,
  }
}

///|
/// The binder stack of a ground type: its free variables are De Bruijn
/// positions in the surrounding signatures.
priv struct MonoBinders {
  types : Array[Array[Sym]]
  captures : Array[Array[Sym]]
}

///|
fn MonoBinders::empty() -> MonoBinders {
  { types: [], captures: [], }
}

///|
fn MonoBinders::enter(
  self : MonoBinders,
  tparams : Array[Sym],
  cparams : Array[Sym],
) -> MonoBinders {
  { types: [tparams] + self.types, captures: [cparams] + self.captures, }
}

///|
fn MonoBinders::type_index(self : MonoBinders, id : Sym) -> (Int32, Int32)? {
  mono_binder_index(id, self.types)
}

///|
fn MonoBinders::capture_index(self : MonoBinders, id : Sym) -> (Int32, Int32)? {
  mono_binder_index(id, self.captures)
}

///|
fn MonoBinders::type_binder(
  self : MonoBinders,
  level : Int32,
  position : Int32,
) -> Sym {
  self.types[level][position]
}

///|
fn MonoBinders::capture_binder(
  self : MonoBinders,
  level : Int32,
  position : Int32,
) -> Sym {
  self.captures[level][position]
}

///|
fn mono_starts_with(
  variant : ArrayView[MonoValueType[Unit]],
  prefix : ArrayView[MonoValueType[Unit]],
) -> Bool {
  guard prefix.length() <= variant.length() else { return false }
  for i in 0..<prefix.length() {
    if variant[i] != prefix[i] {
      return false
    }
  }
  true
}

///|
/// The instances of `id` whose variant starts with `prefix`, each with the state
/// that binds the remaining arguments to `tparams`.
fn mono_instances(
  state : MonoSpecialize,
  id : Sym,
  prefix : ArrayView[MonoValueType[Unit]],
  tparams : ArrayView[Sym],
) -> Array[(Array[MonoValueType[Unit]], MonoSpecialize)] {
  let out : Array[(Array[MonoValueType[Unit]], MonoSpecialize)] = []
  for variant in state.variants(id) {
    if mono_starts_with(variant, prefix) {
      let rest = variant[prefix.length():].to_owned()
      out.push((variant, state.bind(tparams, rest)))
    }
  }
  out
}

///|
fn mono_to_ground_value(
  state : MonoSpecialize,
  tpe : ValueType,
) -> MonoValueType[Unit] raise EffektError {
  mono_to_ground_value_b(state, MonoBinders::empty(), tpe)
}

///|
fn mono_to_ground_value_b(
  state : MonoSpecialize,
  binders : MonoBinders,
  tpe : ValueType,
) -> MonoValueType[Unit] raise EffektError {
  match tpe {
    ValueVar(name) =>
      match binders.type_index(name) {
        Some((level, position)) => MonoValueBound(level, position)
        None =>
          match state.substitution.get(name.uid()) {
            Some(ground) => ground
            None =>
              raise EffektError::Fatal(
                "Unbound type variable '\{name.name().name}' in a monomorphized type",
              )
          }
      }
    ValueData(name, targs) =>
      MonoValueData(
        name,
        targs.map(t => mono_to_ground_value_b(state, binders, t)),
      )
    ValueBoxed(inner, captures) =>
      MonoValueBoxed(
        mono_to_ground_block_b(state, binders, inner),
        captures
        .to_array()
        .map(id => {
          match binders.capture_index(id) {
            Some((level, position)) => MonoCaptureBound(level, position)
            None => MonoCaptureNamed(id)
          }
        }),
      )
  }
}

///|
fn mono_to_ground_block_b(
  state : MonoSpecialize,
  binders : MonoBinders,
  tpe : BlockType,
) -> MonoBlockType[Unit] raise EffektError {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result) => {
      let local = binders.enter(tparams, mono_capture_params(cparams))
      MonoFunction(
        tparams.length(),
        cparams.length(),
        vparams.map(t => mono_to_ground_value_b(state, local, t)),
        bparams.map(t => mono_to_ground_block_b(state, local, t)),
        result.map(t => mono_to_ground_value_b(state, local, t)),
      )
    }
    InterfaceType(name, targs) =>
      MonoInterface(
        name,
        targs.map(t => mono_to_ground_value_b(state, binders, t)),
      )
    PromptType(answer) =>
      MonoPrompt(answer.map(t => mono_to_ground_value_b(state, binders, t)))
    ResumeType(result, answer) =>
      MonoResume(
        result.map(t => mono_to_ground_value_b(state, binders, t)),
        answer.map(t => mono_to_ground_value_b(state, binders, t)),
      )
  }
}

///|
fn mono_contains_bound_value(tpe : MonoValueType[Unit]) -> Bool {
  match tpe {
    MonoValueVar(_) => false
    MonoValueBound(_, _) => true
    MonoValueData(_, targs) => targs.any(mono_contains_bound_value)
    MonoValueBoxed(inner, _) => mono_contains_bound_block(inner)
  }
}

///|
fn mono_contains_bound_block(tpe : MonoBlockType[Unit]) -> Bool {
  match tpe {
    MonoFunction(_, _, vparams, bparams, result) =>
      vparams.any(mono_contains_bound_value) ||
      bparams.any(mono_contains_bound_block) ||
      result.any(mono_contains_bound_value)
    MonoInterface(_, targs) => targs.any(mono_contains_bound_value)
    MonoPrompt(answer) => answer.any(mono_contains_bound_value)
    MonoResume(result, answer) =>
      result.any(mono_contains_bound_value) ||
      answer.any(mono_contains_bound_value)
  }
}

///|
fn mono_monomorphize_ground_value(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  tpe : MonoValueType[Unit],
  binders : MonoBinders,
) -> ValueType raise EffektError {
  match tpe {
    MonoValueVar(_) =>
      raise EffektError::Fatal("A ground type has no flow variable")
    MonoValueBound(level, position) =>
      ValueVar(binders.type_binder(level, position))
    MonoValueData(name, targs) =>
      if mono_contains_bound_value(tpe) {
        ValueData(
          name,
          targs.map(t => mono_monomorphize_ground_value(state, dctx, t, binders)),
        )
      } else {
        mono_replacement_data_ground(state, dctx, name, targs)
      }
    MonoValueBoxed(inner, captures) =>
      ValueBoxed(
        mono_monomorphize_ground_block(state, dctx, inner, binders),
        CaptureSetOf(
          captures.map(c => {
            match c {
              MonoCaptureBound(level, position) =>
                binders.capture_binder(level, position)
              MonoCaptureNamed(id) => id
            }
          }),
        ),
      )
  }
}

///|
fn mono_monomorphize_ground_block(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  tpe : MonoBlockType[Unit],
  binders : MonoBinders,
) -> BlockType raise EffektError {
  match tpe {
    MonoFunction(tarity, carity, vparams, bparams, result) => {
      let tparams : Array[Sym] = []
      for i in 0..<tarity {
        tparams.push(Sym::type_param(Name::local("A\{i}"), Span::missing()))
      }
      let cparams : Array[Sym] = []
      for i in 0..<carity {
        cparams.push(Sym::capture_param(Name::local("c\{i}")))
      }
      let local = binders.enter(tparams, cparams)
      FunctionType(
        tparams,
        cparams.map(c => CaptureSetOf([c])),
        vparams.map(t => mono_monomorphize_ground_value(state, dctx, t, local)),
        bparams.map(t => mono_monomorphize_ground_block(state, dctx, t, local)),
        result.map(t => mono_monomorphize_ground_value(state, dctx, t, local)),
      )
    }
    MonoInterface(name, targs) =>
      if targs.any(mono_contains_bound_value) {
        InterfaceType(
          name,
          targs.map(t => mono_monomorphize_ground_value(state, dctx, t, binders)),
        )
      } else {
        let variant = targs.map(t => {
          mono_monomorphize_ground_value(state, dctx, t, binders)
        })
        let replacement = mono_lookup_fun_name(state, name, targs)
        match replacement {
          Some(fun) =>
            if fun.uid() != name.uid() {
              InterfaceType(fun, [])
            } else {
              InterfaceType(name, variant)
            }
          None => InterfaceType(name, variant)
        }
      }
    MonoPrompt(answer) =>
      PromptType(
        answer.map(t => mono_monomorphize_ground_value(state, dctx, t, binders)),
      )
    MonoResume(result, answer) =>
      ResumeType(
        result.map(t => mono_monomorphize_ground_value(state, dctx, t, binders)),
        answer.map(t => mono_monomorphize_ground_value(state, dctx, t, binders)),
      )
  }
}

///|
/// `funNames.getOrElse((name, targs), name)`: the monomorphized name of an
/// interface, if the solution has one for this variant.
fn mono_lookup_fun_name(
  state : MonoSpecialize,
  name : Sym,
  targs : ArrayView[MonoValueType[Unit]],
) -> Sym? {
  state.fun_names.get(mono_key(name, targs))
}

///|
/// The monomorphized name of a data type applied to ground arguments (upstream
/// `replacementData(id, Vector[GroundType])`): a declared type becomes the
/// declaration of its instance, while an extern type (`Array`, `Ref`) keeps its
/// symbol and has its arguments monomorphized in place. Dropping them would leave
/// a bare `Array` behind, and every phase that reads the type's arity — arity
/// raising looks for `Array[A]` at an extern boundary — then misreads it.
fn mono_replacement_data_ground(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  id : Sym,
  targs : ArrayView[MonoValueType[Unit]],
) -> ValueType raise EffektError {
  guard !targs.is_empty() else { return ValueData(id, []) }
  match mono_lookup_extern_data(dctx, id) {
    Some(_) =>
      ValueData(
        id,
        targs.map(t => {
          mono_monomorphize_ground_value(state, dctx, t, MonoBinders::empty())
        }),
      )
    None =>
      state.tpe_names.get(mono_key(id, targs)).unwrap_or(ValueData(id, []))
  }
}

///|
fn mono_lookup_extern_data(dctx : DeclarationContext, id : Sym) -> Sym? {
  for external in dctx.externs {
    if external is ExternData(sym, _, _) && sym.uid() == id.uid() {
      return Some(sym)
    }
  }
  None
}

///|
fn mono_monomorphize_value_type(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  tpe : ValueType,
) -> ValueType raise EffektError {
  match tpe {
    ValueVar(name) =>
      match state.substitution.get(name.uid()) {
        Some(ground) =>
          mono_monomorphize_ground_value(
            state,
            dctx,
            ground,
            MonoBinders::empty(),
          )
        None =>
          raise EffektError::Fatal(
            "No monomorphized instance for type variable '\{name.name().name}'",
          )
      }
    ValueData(name, targs) => mono_replacement_data(state, dctx, name, targs)
    ValueBoxed(inner, captures) => {
      let ground = mono_to_ground_block_b(state, MonoBinders::empty(), inner)
      mono_monomorphize_ground_value(
        state,
        dctx,
        MonoValueBoxed(
          ground,
          captures.to_array().map(c => MonoCaptureNamed(c)),
        ),
        MonoBinders::empty(),
      )
    }
  }
}

///|
fn mono_replacement_data(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  id : Sym,
  targs : Array[ValueType],
) -> ValueType raise EffektError {
  match mono_lookup_extern_data(dctx, id) {
    Some(_) =>
      ValueData(
        id,
        targs.map(t => mono_monomorphize_value_type(state, dctx, t)),
      )
    None => {
      let variant = targs.map(t => mono_to_ground_value(state, t))
      mono_replacement_data_ground(state, dctx, id, variant)
    }
  }
}

///|
fn mono_monomorphize_block_type(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  tpe : BlockType,
) -> BlockType raise EffektError {
  match tpe {
    FunctionType(_, cparams, vparams, bparams, result) =>
      FunctionType(
        [],
        cparams,
        vparams.map(t => mono_monomorphize_value_type(state, dctx, t)),
        bparams.map(t => mono_monomorphize_block_type(state, dctx, t)),
        result.map(t => mono_monomorphize_value_type(state, dctx, t)),
      )
    InterfaceType(name, targs) => {
      let variant = targs.map(t => mono_to_ground_value(state, t))
      let replacement = mono_lookup_fun_name(state, name, variant)
      match replacement {
        Some(fun) =>
          if fun.uid() == name.uid() {
            InterfaceType(
              name,
              targs.map(t => mono_monomorphize_value_type(state, dctx, t)),
            )
          } else {
            InterfaceType(fun, [])
          }
        None =>
          InterfaceType(
            name,
            targs.map(t => mono_monomorphize_value_type(state, dctx, t)),
          )
      }
    }
    PromptType(answer) =>
      PromptType(answer.map(t => mono_monomorphize_value_type(state, dctx, t)))
    ResumeType(result, answer) =>
      ResumeType(
        result.map(t => mono_monomorphize_value_type(state, dctx, t)),
        answer.map(t => mono_monomorphize_value_type(state, dctx, t)),
      )
  }
}

///|
fn mono_monomorphize_value_param(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  param : ValueParam,
) -> ValueParam raise EffektError {
  ValueParam::{
    id: param.id,
    tpe: mono_monomorphize_value_type(state, dctx, param.tpe),
  }
}

///|
fn mono_monomorphize_block_param(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  param : BlockParam,
) -> BlockParam raise EffektError {
  BlockParam::{
    id: param.id,
    tpe: mono_monomorphize_block_type(state, dctx, param.tpe),
    capt: param.capt,
  }
}

///|
fn mono_monomorphize_block_var(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  bv : BlockVar,
) -> BlockVar raise EffektError {
  BlockVar::{
    id: bv.id,
    annotated_tpe: mono_monomorphize_block_type(state, dctx, bv.annotated_tpe),
    annotated_capt: bv.annotated_capt,
  }
}

///|
fn mono_monomorphize_block_lit(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  lit : BlockLit,
) -> BlockLit raise EffektError {
  BlockLit::{
    tparams: [],
    cparams: lit.cparams,
    vparams: lit.vparams.map(p => mono_monomorphize_value_param(state, dctx, p)),
    bparams: lit.bparams.map(p => mono_monomorphize_block_param(state, dctx, p)),
    body: mono_monomorphize_stmt(state, dctx, lit.body),
  }
}

///|
fn mono_monomorphize_block(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  block : Block,
) -> Block raise EffektError {
  match block {
    BlockVar(bv) => BlockVar(mono_monomorphize_block_var(state, dctx, bv))
    BlockLit(lit) => BlockLit(mono_monomorphize_block_lit(state, dctx, lit))
    Unbox(expr) => Unbox(mono_monomorphize_expr(state, dctx, expr))
    New(implementation) =>
      New(mono_monomorphize_implementation(state, dctx, implementation))
  }
}

///|
/// `operations.flatMap(rewrite(_))`: one operation can expand into several,
/// because its polymorphic parameters are specialized per instance.
fn mono_monomorphize_operations(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  operations : ArrayView[Operation],
  variant : ArrayView[MonoValueType[Unit]],
) -> Array[Operation] raise EffektError {
  let out : Array[Operation] = []
  for op in operations {
    out.append(mono_monomorphize_operation(state, dctx, op, variant))
  }
  out
}

///|
fn mono_monomorphize_implementation(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  implementation : Implementation,
) -> Implementation raise EffektError {
  match implementation.interface {
    InterfaceType(name, targs) => {
      let variant = targs.map(t => mono_to_ground_value(state, t))
      Implementation::{
        interface: InterfaceType(mono_replacement_fun(state, name, targs), []),
        operations: mono_monomorphize_operations(
          state,
          dctx,
          implementation.operations,
          variant,
        ),
      }
    }
    other =>
      Implementation::{
        interface: mono_monomorphize_block_type(state, dctx, other),
        operations: mono_monomorphize_operations(
          state,
          dctx,
          implementation.operations,
          [],
        ),
      }
  }
}

///|
fn mono_replacement_fun(
  state : MonoSpecialize,
  id : Sym,
  targs : ArrayView[ValueType],
) -> Sym raise EffektError {
  guard !targs.is_empty() else { return id }
  let variant = targs.map(t => mono_to_ground_value(state, t))
  state.fun_name(id, variant)
}

///|
fn mono_monomorphize_operation(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  op : Operation,
  variant : ArrayView[MonoValueType[Unit]],
) -> Array[Operation] raise EffektError {
  let out : Array[Operation] = []
  let instances = mono_instances(state, op.name, variant, op.tparams)
  for (base_types, local) in instances {
    out.push(Operation::{
      name: local.fun_name(op.name, base_types),
      tparams: [],
      cparams: op.cparams,
      vparams: op.vparams.map(p => mono_monomorphize_value_param(local, dctx, p)),
      bparams: op.bparams.map(p => mono_monomorphize_block_param(local, dctx, p)),
      body: mono_monomorphize_stmt(local, dctx, op.body),
    })
  }
  out
}

///|
fn mono_monomorphize_clause(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  clause : Clause,
  variant : ArrayView[MonoValueType[Unit]],
) -> Array[Clause] raise EffektError {
  let out : Array[Clause] = []
  let instances = mono_instances(
    state,
    clause.tag,
    variant,
    clause.body.tparams,
  )

  for (base_types, local) in instances {
    out.push(Clause::{
      tag: local.fun_name(clause.tag, base_types),
      body: mono_monomorphize_block_lit(local, dctx, clause.body),
    })
  }
  out
}

///|
fn mono_monomorphize_field(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  field : Field,
) -> Field raise EffektError {
  // Upstream freshens the field symbol per instance (`Field(Id(id), ...)`:
  // "fields of different instances are distinct, backends like Chez define one
  // accessor per field"). The JavaScript backend resolves a field by looking it
  // up in the declaration of the constructor it matches on, so keeping the
  // symbol means every instance of a data type spells its fields the same way —
  // which is what makes a `Match` whose scrutinee type is not known (see
  // [[mono_monomorphize_clause]]) still read the right member.
  Field::{
    id: field.id,
    tpe: mono_monomorphize_value_type(state, dctx, field.tpe),
  }
}

///|
fn mono_monomorphize_constructor(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  ctor : Constructor,
  variant : ArrayView[MonoValueType[Unit]],
) -> Array[Constructor] raise EffektError {
  mono_instances(state, ctor.id, variant, ctor.tparams).map(instance => {
    let (base_types, local) = instance
    Constructor::{
      id: local.fun_name(ctor.id, base_types),
      tparams: [],
      fields: ctor.fields.map(f => mono_monomorphize_field(local, dctx, f)),
    }
  })
}

///|
fn mono_monomorphize_property(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  property : Property,
  variant : ArrayView[MonoValueType[Unit]],
) -> Array[Property] raise EffektError {
  match property.tpe {
    FunctionType(tparams, _, _, _, _) => {
      let out : Array[Property] = []
      let instances = mono_instances(state, property.id, variant, tparams)
      for (base_types, local) in instances {
        out.push(Property::{
          id: local.fun_name(property.id, base_types),
          tpe: mono_monomorphize_block_type(local, dctx, property.tpe),
        })
      }
      out
    }
    other =>
      [
        Property::{
          id: property.id,
          tpe: mono_monomorphize_block_type(state, dctx, other),
        },
      ]
  }
}

///|
fn mono_specialize_call(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  callee : BlockVar,
  targs : Array[ValueType],
) -> (BlockVar, Array[ValueType]) raise EffektError {
  if state.poly_extern_defs.contains(callee.id.uid()) {
    (callee, targs.map(t => mono_monomorphize_value_type(state, dctx, t)))
  } else {
    let function = callee.annotated_tpe
    let tparams = match function {
      FunctionType(tparams, _, _, _, _) => tparams
      _ => []
    }
    let local = state.bind(
      tparams,
      targs.map(t => mono_to_ground_value(state, t)),
    )
    let replacement = mono_replacement_fun(local, callee.id, targs)
    (
      BlockVar::{
        id: replacement,
        annotated_tpe: mono_monomorphize_block_type(local, dctx, function),
        annotated_capt: callee.annotated_capt,
      },
      [],
    )
  }
}

///|
fn mono_nest_defs(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  id : Sym,
  lit : BlockLit,
  variants : ArrayView[Array[MonoValueType[Unit]]],
  index : Int32,
  body : Stmt,
) -> Stmt raise EffektError {
  guard index < variants.length() else {
    return mono_monomorphize_stmt(state, dctx, body)
  }
  let variant = variants[index]
  let local = state.bind(lit.tparams, variant)
  let name = local.fun_name(id, variant)
  let mono_lit = BlockLit::{
    tparams: [],
    cparams: lit.cparams,
    vparams: lit.vparams.map(p => mono_monomorphize_value_param(local, dctx, p)),
    bparams: lit.bparams.map(p => mono_monomorphize_block_param(local, dctx, p)),
    body: mono_monomorphize_stmt(local, dctx, lit.body),
  }
  Def(
    name,
    BlockLit(mono_lit),
    mono_nest_defs(state, dctx, id, lit, variants, index + 1, body),
  )
}

///|
fn mono_monomorphize_stmt(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  stmt : Stmt,
) -> Stmt raise EffektError {
  match stmt {
    Return(exprs) =>
      Return(exprs.map(e => mono_monomorphize_expr(state, dctx, e)))
    Val(ids, binding, body) =>
      Val(
        ids,
        mono_monomorphize_stmt(state, dctx, binding),
        mono_monomorphize_stmt(state, dctx, body),
      )
    Var(ref, init, capture, body) =>
      Var(
        ref,
        mono_monomorphize_expr(state, dctx, init),
        capture,
        mono_monomorphize_stmt(state, dctx, body),
      )
    ImpureApp(id, callee, targs, vargs, bargs, body) => {
      let (mono_callee, mono_targs) = mono_specialize_call(
        state, dctx, callee, targs,
      )
      ImpureApp(
        id,
        mono_callee,
        mono_targs,
        vargs.map(e => mono_monomorphize_expr(state, dctx, e)),
        bargs.map(b => mono_monomorphize_block(state, dctx, b)),
        mono_monomorphize_stmt(state, dctx, body),
      )
    }
    App(BlockVar(bv), targs, vargs, bargs) => {
      let (mono_callee, mono_targs) = mono_specialize_call(
        state, dctx, bv, targs,
      )
      App(
        BlockVar(mono_callee),
        mono_targs,
        vargs.map(e => mono_monomorphize_expr(state, dctx, e)),
        bargs.map(b => mono_monomorphize_block(state, dctx, b)),
      )
    }
    App(callee, targs, vargs, bargs) =>
      match callee {
        Unbox(
          ValueVar(
            id,
            ValueBoxed(FunctionType(tparams, _, _, _, _) as function, captures),
          ),
        ) if !targs.is_empty() => {
          let local = state.bind(
            tparams,
            targs.map(t => mono_to_ground_value(state, t)),
          )
          let mono_type = ValueBoxed(
            mono_monomorphize_block_type(local, dctx, function),
            captures,
          )
          App(
            Unbox(ValueVar(id, mono_type)),
            [],
            vargs.map(e => mono_monomorphize_expr(state, dctx, e)),
            bargs.map(b => mono_monomorphize_block(state, dctx, b)),
          )
        }
        _ => {
          if !targs.is_empty() {
            raise EffektError::Fatal(
              "Polymorphic application has no stable flow variable",
            )
          }
          App(
            mono_monomorphize_block(state, dctx, callee),
            [],
            vargs.map(e => mono_monomorphize_expr(state, dctx, e)),
            bargs.map(b => mono_monomorphize_block(state, dctx, b)),
          )
        }
      }
    Let(id, binding, body) =>
      Let(
        id,
        mono_monomorphize_expr(state, dctx, binding),
        mono_monomorphize_stmt(state, dctx, body),
      )
    If(cond, thn, els) =>
      If(
        mono_monomorphize_expr(state, dctx, cond),
        mono_monomorphize_stmt(state, dctx, thn),
        mono_monomorphize_stmt(state, dctx, els),
      )
    Invoke(callee, method, method_tpe, targs, vargs, bargs) => {
      let receiver_targs = match callee.infer_type() {
        InterfaceType(_, arguments) => arguments
        other =>
          raise EffektError::Fatal(
            "Expected an interface receiver, but found '\{show_core_block_type(other)}'",
          )
      }
      let combined = receiver_targs + targs
      let replacement = mono_replacement_fun(state, method, combined)
      let tparams = match method_tpe {
        FunctionType(tparams, _, _, _, _) => tparams
        _ => raise EffektError::Fatal("Expected a function method type")
      }

      let local = state.bind(
        tparams,
        targs.map(t => mono_to_ground_value(state, t)),
      )
      Invoke(
        mono_monomorphize_block(state, dctx, callee),
        replacement,
        mono_monomorphize_block_type(local, dctx, method_tpe),
        [],
        vargs.map(e => mono_monomorphize_expr(state, dctx, e)),
        bargs.map(b => mono_monomorphize_block(state, dctx, b)),
      )
    }
    Resume(continuation, body) =>
      Resume(
        mono_monomorphize_block_var(state, dctx, continuation),
        mono_monomorphize_stmt(state, dctx, body),
      )
    Reset(body) => Reset(mono_monomorphize_block_lit(state, dctx, body))
    Def(id, BlockLit(lit), body) =>
      if lit.tparams.is_empty() {
        Def(
          id,
          BlockLit(mono_monomorphize_block_lit(state, dctx, lit)),
          mono_monomorphize_stmt(state, dctx, body),
        )
      } else {
        mono_nest_defs(state, dctx, id, lit, state.variants(id), 0, body)
      }
    Def(id, block, body) =>
      Def(
        id,
        mono_monomorphize_block(state, dctx, block),
        mono_monomorphize_stmt(state, dctx, body),
      )
    Shift(prompt, continuation, body) =>
      Shift(
        mono_monomorphize_block_var(state, dctx, prompt),
        BlockParam::{
          id: continuation.id,
          tpe: mono_monomorphize_block_type(state, dctx, continuation.tpe),
          capt: continuation.capt,
        },
        mono_monomorphize_stmt(state, dctx, body),
      )
    Match(scrutinee, result, clauses, default) => {
      let mono_scrutinee = mono_monomorphize_expr(state, dctx, scrutinee)
      let variant = match mono_scrutinee.infer_type() {
        ValueData(name, _) =>
          match state.tpe_names_inverse.get(name.uid()) {
            Some((_, variant)) => variant
            None => []
          }
        _ => []
      }

      let mono_clauses : Array[Clause] = []
      for clause in clauses {
        mono_clauses.append(
          mono_monomorphize_clause(state, dctx, clause, variant),
        )
      }
      Match(
        mono_scrutinee,
        result.map(t => mono_monomorphize_value_type(state, dctx, t)),
        mono_clauses,
        default.map(s => mono_monomorphize_stmt(state, dctx, s)),
      )
    }
    Get(id, tpe, ref, capt, body) =>
      Get(
        id,
        mono_monomorphize_value_type(state, dctx, tpe),
        ref,
        capt,
        mono_monomorphize_stmt(state, dctx, body),
      )
    Put(ref, capt, value, body) =>
      Put(
        ref,
        capt,
        mono_monomorphize_expr(state, dctx, value),
        mono_monomorphize_stmt(state, dctx, body),
      )
    Alloc(id, init, region, body) =>
      Alloc(
        id,
        mono_monomorphize_expr(state, dctx, init),
        region,
        mono_monomorphize_stmt(state, dctx, body),
      )
    Region(body) => Region(mono_monomorphize_block_lit(state, dctx, body))
    Hole(tpes, span) =>
      Hole(tpes.map(t => mono_monomorphize_value_type(state, dctx, t)), span)
  }
}

///|
fn mono_monomorphize_expr(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  expr : Expr,
) -> Expr raise EffektError {
  match expr {
    ValueVar(id, tpe) =>
      ValueVar(id, mono_monomorphize_value_type(state, dctx, tpe))
    Literal(value, tpe) =>
      Literal(value, mono_monomorphize_value_type(state, dctx, tpe))
    PureApp(callee, targs, vargs) => {
      let (mono_callee, mono_targs) = mono_specialize_call(
        state, dctx, callee, targs,
      )
      PureApp(
        mono_callee,
        mono_targs,
        vargs.map(e => mono_monomorphize_expr(state, dctx, e)),
      )
    }
    Make(data, tag, targs, vargs) => {
      let data_targs = match data {
        ValueData(_, targs) => targs
        _ => []
      }
      let combined = data_targs + targs
      let replacement_tag = mono_replacement_fun(state, tag, combined)
      let replacement_data = match data {
        ValueData(name, _) =>
          mono_replacement_data(state, dctx, name, data_targs)
        _ => data
      }
      Make(
        replacement_data,
        replacement_tag,
        [],
        vargs.map(e => mono_monomorphize_expr(state, dctx, e)),
      )
    }
    Box(block, capt) => Box(mono_monomorphize_block(state, dctx, block), capt)
  }
}

///|
fn mono_monomorphize_toplevel(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  definition : Toplevel,
) -> Array[Toplevel] raise EffektError {
  match definition {
    ToplevelDef(id, BlockLit(lit)) =>
      if lit.tparams.is_empty() {
        [
          ToplevelDef(
            id,
            BlockLit({
              tparams: [],
              cparams: lit.cparams,
              vparams: lit.vparams.map(p => {
                mono_monomorphize_value_param(state, dctx, p)
              }),
              bparams: lit.bparams.map(p => {
                mono_monomorphize_block_param(state, dctx, p)
              }),
              body: mono_monomorphize_stmt(state, dctx, lit.body),
            }),
          ),
        ]
      } else {
        let out : Array[Toplevel] = []
        for variant in state.variants(id) {
          let local = state.bind(lit.tparams, variant)
          let name = local.fun_name(id, variant)
          let mono_lit = BlockLit::{
            tparams: [],
            cparams: lit.cparams,
            vparams: lit.vparams.map(p => {
              mono_monomorphize_value_param(local, dctx, p)
            }),
            bparams: lit.bparams.map(p => {
              mono_monomorphize_block_param(local, dctx, p)
            }),
            body: mono_monomorphize_stmt(local, dctx, lit.body),
          }
          let (renamed, _) = rename_block_lit(mono_lit)
          out.push(ToplevelDef(name, BlockLit(renamed)))
        }
        out
      }
    ToplevelDef(id, block) =>
      [ToplevelDef(id, mono_monomorphize_block(state, dctx, block))]
    ToplevelVal(id, stmt) =>
      [ToplevelVal(id, mono_monomorphize_stmt(state, dctx, stmt))]
  }
}

///|
fn mono_monomorphize_declaration(
  state : MonoSpecialize,
  dctx : DeclarationContext,
  decl : Declaration,
) -> Array[Declaration] raise EffektError {
  match decl {
    DeclarationData(id, tparams, constructors) => {
      let variants = state.variants(id)
      if variants.is_empty() && !tparams.is_empty() {
        []
      } else if variants.is_empty() {
        let mono_constructors : Array[Constructor] = []
        for ctor in constructors {
          mono_constructors.append(
            mono_monomorphize_constructor(state, dctx, ctor, []),
          )
        }
        [DeclarationData(id, tparams, mono_constructors)]
      } else {
        let out : Array[Declaration] = []
        for variant in variants {
          let local = state.bind(tparams, variant)
          let name = match local.tpe_name(id, variant) {
            ValueData(name, _) => name
            _ => id
          }
          let mono_constructors : Array[Constructor] = []
          for ctor in constructors {
            mono_constructors.append(
              mono_monomorphize_constructor(local, dctx, ctor, variant),
            )
          }
          out.push(DeclarationData(name, [], mono_constructors))
        }
        out
      }
    }
    DeclarationInterface(id, tparams, properties) => {
      let variants = state.variants(id)
      if variants.is_empty() {
        let mono_properties : Array[Property] = []
        for property in properties {
          mono_properties.append(
            mono_monomorphize_property(state, dctx, property, []),
          )
        }
        [DeclarationInterface(id, tparams, mono_properties)]
      } else {
        let out : Array[Declaration] = []
        for variant in variants {
          let local = state.bind(tparams, variant)
          let name = local.fun_name(id, variant)
          let mono_properties : Array[Property] = []
          for property in properties {
            mono_properties.append(
              mono_monomorphize_property(local, dctx, property, variant),
            )
          }
          if name.uid() == id.uid() {
            out.push(DeclarationInterface(name, tparams, mono_properties))
          } else {
            out.push(DeclarationInterface(name, [], mono_properties))
          }
        }
        out
      }
    }
  }
}

///|
fn mono_elaborate_toplevel(
  elaborator : MonoElaborator,
  definition : Toplevel,
  scope : MonoScope,
) -> Toplevel raise EffektError {
  match definition {
    ToplevelDef(id, block) => ToplevelDef(id, elaborator.block(block, scope))
    ToplevelVal(id, stmt) => ToplevelVal(id, elaborator.stmt(stmt, scope))
  }
}

///|
fn mono_preprocess(module : ModuleDecl) -> ModuleDecl raise EffektError {
  let state = MonoState::MonoState()
  let elaborator = MonoElaborator::MonoElaborator(state)
  let initial = MonoScope::empty()
  let declarations : Array[Declaration] = []
  for decl in module.declarations {
    declarations.push(elaborator.declaration(decl, initial))
  }
  let definitions : Array[Toplevel] = []
  for definition in module.definitions {
    definitions.push(mono_elaborate_toplevel(elaborator, definition, initial))
  }
  let mut index = 0
  while index < state.interfaces.length() {
    state.interfaces[index] = elaborator.declaration(
      state.interfaces[index],
      initial,
    )
    index += 1
  }
  ModuleDecl::{
    path: module.path,
    includes: module.includes,
    declarations: declarations + state.interfaces,
    externs: module.externs,
    definitions,
    exports: module.exports,
  }
}

///|
/// Monomorphization: `bindSubexpressions`, `preprocess`, `collect`, `solve`,
/// `specialize` (`effekt/core/Mono.scala`). Upstream runs it between `Deadcode`
/// and `core.Show`; see the module comment.
pub fn mono_phase(module : ModuleDecl) -> ModuleDecl raise EffektError {
  let bound = bind_subexpressions(module)
  let preprocessed = mono_preprocess(bound)
  let constraints = mono_collect(preprocessed)
  let solution = mono_solve(constraints)
  let owners : Map[Int32, Sym] = Map([])
  for flow in constraints {
    owners.set(flow.to.uid(), flow.to)
    for tpe in flow.from {
      for owner in mono_dependencies_value(tpe) {
        owners.set(owner.uid(), owner)
      }
    }
  }
  mono_specialize(preprocessed, solution, owners)
}
