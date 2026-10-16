// Wellformedness of inferred types.
//
// Mirrors the parts of `effekt/typer/Wellformedness.scala` that matter for the
// JavaScript backend: capabilities and regions must not escape through the
// type of a value that outlives them.
//
// Upstream tracks a `WFContext` of types and captures in scope while
// traversing the already type checked tree. We check the same property
// *locally* at the places where an escape would be observable (the return type
// of a handled statement, of a function body, of a block literal body and of a
// region body), which gives the same diagnostics for the common cases.
//
// Not implemented (see the report): scope extrusion of type parameters of
// existentials / higher-rank functions, and the exhaustivity-related parts
// (those live in `exhaustivity.mbt`).

///|
/// The free captures of a capture set: capture parameters and lexical regions
/// are free, resources (`io`, `global`, ...) are not — like upstream.
pub fn free_captures(c : Captures) -> Array[Sym] {
  match c {
    @symbols.Captures::CaptureSetOf(cs) => cs.filter(s => is_free_capture(s))
    @symbols.Captures::CaptVar(x) => [x]
  }
}

///|
fn is_free_capture(s : Sym) -> Bool {
  match s {
    @symbols.Sym::CaptureParam(_) => true
    @symbols.Sym::LexicalRegion(_) => true
    @symbols.Sym::CaptUnificationVar(_) => true
    _ => false
  }
}

///|
pub fn free_captures_value(t : ValueType) -> Array[Sym] {
  match t {
    @symbols.ValueType::ValueTypeRef(_) => []
    @symbols.ValueType::ValueTypeApp(_, args) => {
      let out : Array[Sym] = []
      for a in args {
        push_new(out, free_captures_value(a))
      }
      out
    }
    @symbols.ValueType::BoxedType(b, c) => {
      let out = free_captures_block(b)
      push_new(out, free_captures(c))
      out
    }
  }
}

///|
pub fn free_captures_block(t : BlockType) -> Array[Sym] {
  match t {
    @symbols.BlockType::InterfaceType(_, args) => {
      let out : Array[Sym] = []
      for a in args {
        push_new(out, free_captures_value(a))
      }
      out
    }
    @symbols.BlockType::FunctionType(_, capts, vps, bps, ret, effs) => {
      let bound = capture_params_of(capts)
      let out : Array[Sym] = []
      for v in vps {
        push_new(out, free_captures_value(v))
      }
      for b in bps {
        push_new(out, free_captures_block(b))
      }
      for e in effs.effects {
        push_new(out, free_captures_block(e))
      }
      for c in capts {
        push_new(out, free_captures(c))
      }
      push_new(out, free_captures_value(ret))
      out.filter(c => !sym_in(c, bound))
    }
  }
}

///|
/// The free type parameters of a value type.
pub fn free_types_value(t : ValueType, bound : Array[Sym]) -> Array[Sym] {
  match t {
    @symbols.ValueType::ValueTypeRef(x) =>
      if sym_in(x, bound) {
        []
      } else {
        match x {
          @symbols.Sym::TypeParam(_) => [x]
          _ => []
        }
      }
    @symbols.ValueType::ValueTypeApp(_, args) => {
      let out : Array[Sym] = []
      for a in args {
        push_new(out, free_types_value(a, bound))
      }
      out
    }
    @symbols.ValueType::BoxedType(b, _) => free_types_block(b, bound)
  }
}

///|
pub fn free_types_block(t : BlockType, bound : Array[Sym]) -> Array[Sym] {
  match t {
    @symbols.BlockType::InterfaceType(_, args) => {
      let out : Array[Sym] = []
      for a in args {
        push_new(out, free_types_value(a, bound))
      }
      out
    }
    @symbols.BlockType::FunctionType(tparams, _, vps, bps, ret, effs) => {
      let inner = bound + tparams
      let out : Array[Sym] = []
      for v in vps {
        push_new(out, free_types_value(v, inner))
      }
      for b in bps {
        push_new(out, free_types_block(b, inner))
      }
      for e in effs.effects {
        push_new(out, free_types_block(e, inner))
      }
      push_new(out, free_types_value(ret, inner))
      out
    }
  }
}

///|
fn push_new(out : Array[Sym], xs : Array[Sym]) -> Unit {
  for x in xs {
    if !sym_in(x, out) {
      out.push(x)
    }
  }
}

///|
/// Checks that the captures bound by a handler / function / region do not
/// escape through an inferred type.
pub fn Typer::check_no_capture_escape(
  self : Typer,
  bound : Array[Sym],
  free : Array[Sym],
  span : Span,
  msg : String,
) -> Unit {
  let escaping = free.filter(c => sym_in(c, bound))
  if escaping.length() > 0 {
    self.error(
      span,
      "\{msg} Escaping: \{show_captures(@symbols.Captures::CaptureSetOf(escaping))}",
    )
  }
}
