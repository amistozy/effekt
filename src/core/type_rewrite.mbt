// The congruence of the type language, shared by the passes that rewrite
// symbols.
//
// `Rewrite` hooks a symbol rewrite and a capture rewrite (`on_id`,
// `on_captures`); `Renamer` looks both up in the scope it is freshening. What
// they then do to a `ValueType` / `BlockType` is the same tree walk, so the walk
// lives here once, generic over the two operations a type can mention. The trait
// is private: it exists to parameterise this walk, not to be a public capability.
//
// Generic here is the zero-cost form: both instantiations are monomorphised, so
// the walk calls the pass's own `rewrite_id`/`rewrite_captures` directly, exactly
// as the two copies did.

///|
/// The two operations a type mentions: a symbol and a capture set.
priv trait TypeRewrite {
  fn rewrite_type_id(Self, Sym) -> Sym
  fn rewrite_type_captures(Self, Captures) -> Captures
}

///|
fn[T : TypeRewrite] rewrite_type(tpe : ValueType, rw : T) -> ValueType {
  match tpe {
    ValueVar(sym) => ValueVar(rw.rewrite_type_id(sym))
    ValueData(sym, targs) =>
      ValueData(rw.rewrite_type_id(sym), targs.map(t => rewrite_type(t, rw)))
    ValueBoxed(block, capt) =>
      ValueBoxed(rewrite_block_type(block, rw), rw.rewrite_type_captures(capt))
  }
}

///|
fn[T : TypeRewrite] rewrite_block_type(tpe : BlockType, rw : T) -> BlockType {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result) =>
      FunctionType(
        tparams.map(t => rw.rewrite_type_id(t)),
        cparams.map(c => rw.rewrite_type_captures(c)),
        vparams.map(t => rewrite_type(t, rw)),
        bparams.map(t => rewrite_block_type(t, rw)),
        result.map(t => rewrite_type(t, rw)),
      )
    InterfaceType(sym, targs) =>
      InterfaceType(
        rw.rewrite_type_id(sym),
        targs.map(t => rewrite_type(t, rw)),
      )
    PromptType(answer) => PromptType(answer.map(t => rewrite_type(t, rw)))
    ResumeType(result, answer) =>
      ResumeType(
        result.map(t => rewrite_type(t, rw)),
        answer.map(t => rewrite_type(t, rw)),
      )
  }
}

///|
impl TypeRewrite for Rewrite with fn rewrite_type_id(self, id) {
  self.rewrite_id(id)
}

///|
impl TypeRewrite for Rewrite with fn rewrite_type_captures(self, capt) {
  self.rewrite_captures(capt)
}

///|
impl TypeRewrite for Renamer with fn rewrite_type_id(self, id) {
  self.rewrite_id(id)
}

///|
impl TypeRewrite for Renamer with fn rewrite_type_captures(self, capt) {
  self.rewrite_captures(capt)
}
