// Static resumptions: reduce delimited control whose context is static.
//
// Mirrors `effekt/core/optimizer/StaticResumptions.scala`:
//
//   [[ reset { p => E[ shift(p) { {k} => b } ] } ]]
//     ~> b[ resume(k){s} := reset { p => E[s] } ]
//
// When `E` is syntactically known, the continuation is known and the call is
// performed in place: reused where it stands (`reuse`) when the shift is its
// last use, or copied as a join point (`joinpoint`) as long as whatever it
// captures it captures privately. Afterwards `Deadcode` drops a `reset` that
// nothing shifts to anymore, and the inliner works with the join points.
//
// The rules run the body of a shift where the shift stood, so its prompt stays
// installed. That is only sound when the body cannot resume another
// continuation to the same prompt — the machine does not allow a prompt twice on
// the stack (upstream #1510) — so `blocked_prompts` collects the prompts that
// have to be left alone:
//
//   - some shift to it lets its continuation escape, also through a block that
//     closes over it,
//   - it occurs other than as the prompt of a shift, or
//   - it is a parameter, since we do not know which `reset` it stands for.

// ---------------------------------------------------------------------------
// Sets of symbols and the captures of a type
// ---------------------------------------------------------------------------

///|
/// A set of symbols, keyed by `uid` (MoonBit maps need `Hash`, `Sym` has none).
fn sym_set(ids : Array[Sym]) -> Map[Int32, Sym] {
  let out : Map[Int32, Sym] = Map([])
  for id in ids {
    out.set(id.uid(), id)
  }
  out
}

///|
fn sym_set_union(a : Map[Int32, Sym], b : Map[Int32, Sym]) -> Map[Int32, Sym] {
  let out = a.copy()
  for uid, id in b {
    out.set(uid, id)
  }
  out
}

///|
/// The captures occurring in a type (upstream `StaticResumptions.captures`).
fn captures_of_value_type(tpe : ValueType) -> Captures {
  match tpe {
    ValueVar(_) => Captures::empty()
    ValueData(_, targs) => captures_of_value_types(targs)
    ValueBoxed(block, capt) => capt.union(captures_of_block_type(block))
  }
}

///|
fn captures_of_value_types(tpes : Array[ValueType]) -> Captures {
  let mut out = Captures::empty()
  for tpe in tpes {
    out = out.union(captures_of_value_type(tpe))
  }
  out
}

///|
fn captures_of_block_types(tpes : Array[BlockType]) -> Captures {
  let mut out = Captures::empty()
  for tpe in tpes {
    out = out.union(captures_of_block_type(tpe))
  }
  out
}

///|
fn captures_of_block_type(tpe : BlockType) -> Captures {
  match tpe {
    FunctionType(_, cparams, vparams, bparams, result) =>
      captures_of_value_types(vparams)
      .union(captures_of_block_types(bparams))
      .union(captures_of_value_types(result))
      .diff(CaptureSetOf(capture_ids(cparams)))
    InterfaceType(_, targs) => captures_of_value_types(targs)
    PromptType(answer) => captures_of_value_types(answer)
    ResumeType(result, answer) =>
      captures_of_value_types(result).union(captures_of_value_types(answer))
  }
}

///|
/// Whether one of the symbols of `set` occurs in `capt`.
fn captures_any_in(capt : Captures, set : Map[Int32, Sym]) -> Bool {
  capt.to_array().any(c => set.contains(c.uid()))
}

// ---------------------------------------------------------------------------
// Bailing out of a rule
// ---------------------------------------------------------------------------

///|
/// The non-local exit of upstream's `boundary { break(None) }`: a rule that finds
/// its preconditions unmet sets `aborted`, and every caller checks the flag
/// before it uses what the aborted call returned.
priv struct Bail {
  mut aborted : Bool
}

///|
fn Bail::Bail() -> Bail {
  { aborted: false, }
}

///|
fn Bail::abort(self : Bail) -> Unit {
  self.aborted = true
}

// ---------------------------------------------------------------------------
// A shift, analysed
// ---------------------------------------------------------------------------

///|
/// A `Stmt::Shift` together with what the rules need: the resumption `k` it
/// binds and the `result` values that `k` resumes with (upstream
/// `StaticResumptions.Shift`).
priv struct ShiftInfo {
  shift : Stmt
  k : Sym
  result : Array[ValueType]
}

///|
/// Reads a `Stmt::Shift` whose continuation has a resumption type.
fn shift_info_of(s : Stmt) -> ShiftInfo? {
  match s {
    Shift(_, k, _) =>
      match k.tpe {
        ResumeType(result, _) => Some({ shift: s, k: k.id, result, })
        _ => None
      }
    _ => None
  }
}

///|
fn ShiftInfo::body(self : ShiftInfo) -> Stmt {
  match self.shift {
    Shift(_, _, body) => body
    _ => Return([])
  }
}

///|
fn ShiftInfo::with_body(self : ShiftInfo, body : Stmt) -> ShiftInfo {
  match self.shift {
    Shift(prompt, k, _) => { ..self, shift: Shift(prompt, k, body), }
    _ => self
  }
}

///|
/// `resume(k){s}`, if this statement is one.
fn ShiftInfo::resume_of(self : ShiftInfo, s : Stmt) -> Stmt? {
  match s {
    Resume(k_var, resumed) =>
      if k_var.id.uid() == self.k.uid() {
        Some(resumed)
      } else {
        None
      }
    _ => None
  }
}

///|
/// `[[ resume(k){s} ]] = by(s)`, everywhere in `s`.
fn ShiftInfo::replace_resumptions_in(
  self : ShiftInfo,
  s : Stmt,
  by : (Stmt) -> Stmt raise EffektError,
) -> Stmt raise EffektError {
  let rewrite = Rewrite(
    Some((rewrite, stmt) => {
      match self.resume_of(stmt) {
        Some(resumed) => Some(by(rewrite.rewrite_stmt(resumed)))
        None => None
      }
    }),
    None,
    None,
    None,
  )
  rewrite.rewrite_stmt(s)
}

///|
fn ShiftInfo::replace_resumptions(
  self : ShiftInfo,
  by : (Stmt) -> Stmt raise EffektError,
) -> Stmt raise EffektError {
  self.replace_resumptions_in(self.body(), by)
}

///|
/// Whether `k` occurs only as the callee of a `resume(k){...}`: dropping the
/// resumptions must leave no occurrence of it.
fn ShiftInfo::resumes_only(self : ShiftInfo) -> Bool raise EffektError {
  let stripped = self.replace_resumptions(resumed => resumed)
  !stripped.free().contains(self.k)
}

///|
/// Whether every `resume(k){s}` resumes with a value, i.e. not bidirectionally.
fn ShiftInfo::resumes_with_values(self : ShiftInfo) -> Bool raise EffektError {
  let mut with_values = true
  let _ = self.replace_resumptions(resumed => {
    if !(resumed is Return(_)) {
      with_values = false
    }
    resumed
  })
  with_values
}

///|
/// Whether resuming `k` with `s` lets a shift observe a frame known by `names`.
fn ShiftInfo::observes(
  self : ShiftInfo,
  names : Map[Int32, Sym],
  s : Stmt,
) -> Bool raise EffektError {
  let mut observed = false
  let _ = self.replace_resumptions_in(s, resumed => {
    if captures_any_in(resumed.infer_capt(), names) {
      observed = true
    }
    resumed
  })
  observed
}

// ---------------------------------------------------------------------------
// A prompt
// ---------------------------------------------------------------------------

///|
/// The prompt a `reset` binds: its parameter, the capture parameter that stands
/// for it, and the answer types it promises.
priv struct Prompt {
  param : BlockParam
  capture : Sym
  answer : Array[ValueType]
}

///|
/// The names a copy of this prompt renames, and that must not escape into such a
/// copy.
fn Prompt::names(self : Prompt) -> Map[Int32, Sym] {
  sym_set([self.param.id, self.capture])
}

///|
/// A shift to this prompt (upstream `Prompt.Shift`).
fn Prompt::shift_of(self : Prompt, s : Stmt) -> ShiftInfo? {
  match s {
    Shift(prompt_var, _, _) =>
      if prompt_var.id.uid() == self.param.id.uid() {
        shift_info_of(s)
      } else {
        None
      }
    _ => None
  }
}

// ---------------------------------------------------------------------------
// Frames: a `var`, a `region` or a nested `reset`
// ---------------------------------------------------------------------------

///|
/// A statement that pushes exactly one frame, which the answer pops.
///
/// `names` are what can observe it: a `var` by its capture, a region or prompt by
/// its id *and* its capture. `before` is what it evaluates before its body.
priv struct Frame {
  names : Map[Int32, Sym]
  before : Free
  body : Stmt
  rebuild_with : (Stmt) -> Stmt
  is_delimiter : Bool
}

///|
/// The same frame around a different body.
fn Frame::rebuild(self : Frame, body : Stmt) -> Stmt {
  (self.rebuild_with)(body)
}

///|
fn frame_of(s : Stmt) -> Frame? {
  match s {
    Var(ref, init, capture, body) =>
      Some({
        names: sym_set([capture]),
        before: init.free(),
        body,
        rebuild_with: b => Var(ref, init, capture, b),
        is_delimiter: false,
      })
    Region(lit) =>
      if lit.bparams.length() == 1 {
        Some({
          names: sym_set(lit.cparams + [lit.bparams[0].id]),
          before: Free::empty(),
          body: lit.body,
          rebuild_with: b => Region({ ..lit, body: b, }),
          is_delimiter: false,
        })
      } else {
        None
      }
    Reset(lit) =>
      if lit.bparams.length() == 1 {
        Some({
          names: sym_set(lit.cparams + [lit.bparams[0].id]),
          before: Free::empty(),
          body: lit.body,
          rebuild_with: b => Reset({ ..lit, body: b, }),
          is_delimiter: true,
        })
      } else {
        None
      }
    _ => None
  }
}

// ---------------------------------------------------------------------------
// The part of a continuation a join point re-creates
// ---------------------------------------------------------------------------

///|
/// `reset { p => val y = hole; rest }`, or `reset { p => hole }` when the
/// continuation ends at the prompt.
priv struct Continuation {
  prompt : Prompt
  /// the `val` frame `val y = []; rest`, if the continuation stands below one
  binder : (Array[Sym], Stmt)?
}

///|
fn Continuation::Continuation(
  prompt : Prompt,
  binder : (Array[Sym], Stmt)?,
) -> Continuation {
  { prompt, binder, }
}

///|
fn Continuation::fill(self : Continuation, filling : Stmt) -> Stmt {
  let body = match self.binder {
    Some((ys, rest)) => Val(ys, filling, rest)
    None => filling
  }
  Reset(
    BlockLit::BlockLit([], [self.prompt.capture], [], [self.prompt.param], body),
  )
}

// ---------------------------------------------------------------------------
// Tail positions
// ---------------------------------------------------------------------------

///|
/// A statement with a hole in its tail positions (upstream
/// `StaticResumptions.TailPositions`): applying `rewrite` to a function `f`
/// rebuilds it with `f` applied to every tail.
///
/// `before` is what is evaluated on the way, so an occurrence there is not in tail
/// position; `transparents` are the blocks only ever tail-called from here, whose
/// tail positions are ours too.
priv struct TailPositions {
  apply_tails : ((Stmt) -> Stmt raise EffektError) -> Stmt raise EffektError
  before : Free
  transparents : Array[Sym]
}

///|
/// Applies `f` to every tail position and rebuilds the statement around them.
fn TailPositions::rewrite(
  self : TailPositions,
  f : (Stmt) -> Stmt raise EffektError,
) -> Stmt raise EffektError {
  (self.apply_tails)(f)
}

///|
fn TailPositions::tails(self : TailPositions) -> Array[Stmt] raise EffektError {
  let found : Array[Stmt] = []
  let _ = self.rewrite(child => {
    found.push(child)
    child
  })
  found
}

///|
fn TailPositions::all(
  self : TailPositions,
  p : (Stmt) -> Bool raise EffektError,
) -> Bool raise EffektError {
  self.tails().all(child => p(child))
}

///|
/// The tail positions of `s`, if nothing is pushed on the stack on the way to
/// them: bindings, `if` and `match` push nothing, nor does a call to a block that
/// is only ever tail-called.
fn tail_positions(s : Stmt) -> TailPositions? raise EffektError {
  match s {
    // a block that is only ever tail-called adds no frame
    Def(id, Block::BlockLit(lit), body) =>
      if tail_called_only(id, body) && tail_called_only(id, lit.body) {
        Some({
          apply_tails: f => {
            Def(id, Block::BlockLit({ ..lit, body: f(lit.body), }), f(body))
          },
          before: Free::empty(),
          transparents: [id],
        })
      } else {
        None
      }
    Val(ids, binding, body) =>
      Some({
        apply_tails: f => Val(ids, binding, f(body)),
        before: binding.free(),
        transparents: [],
      })
    Let(id, binding, body) =>
      Some({
        apply_tails: f => Let(id, binding, f(body)),
        before: binding.free(),
        transparents: [],
      })
    ImpureApp(id, callee, targs, vargs, bargs, body) =>
      Some({
        apply_tails: f => ImpureApp(id, callee, targs, vargs, bargs, f(body)),
        before: {
          let mut out = Block::BlockVar(callee).free()
          for v in vargs {
            out = out.union(v.free())
          }
          for b in bargs {
            out = out.union(b.free())
          }
          out
        },
        transparents: [],
      })
    Def(id, block, body) =>
      Some({
        apply_tails: f => Def(id, block, f(body)),
        before: block.free(),
        transparents: [],
      })
    Alloc(id, init, region, body) =>
      Some({
        apply_tails: f => Alloc(id, init, region, f(body)),
        before: init.free(),
        transparents: [],
      })
    Get(id, tpe, ref, capt, body) =>
      Some({
        apply_tails: f => Get(id, tpe, ref, capt, f(body)),
        before: Free::empty(),
        transparents: [],
      })
    Put(ref, capt, value, body) =>
      Some({
        apply_tails: f => Put(ref, capt, value, f(body)),
        before: value.free(),
        transparents: [],
      })
    If(cond, thn, els) =>
      Some({
        apply_tails: f => If(cond, f(thn), f(els)),
        before: cond.free(),
        transparents: [],
      })
    Match(scrutinee, tpe, clauses, default) =>
      Some({
        apply_tails: f => {
          let rewritten = clauses.map(clause => {
            Clause(clause.tag, { ..clause.body, body: f(clause.body.body), })
          })
          let default = match default {
            Some(body) => Some(f(body))
            None => None
          }
          Match(scrutinee, tpe, rewritten, default)
        },
        before: scrutinee.free(),
        transparents: [],
      })
    _ => None
  }
}

///|
/// Whether every use of `id` in `s` is a call to it in tail position.
fn tail_called_only(id : Sym, s : Stmt) -> Bool raise EffektError {
  match tail_positions(s) {
    Some(positions) =>
      !positions.before.contains(id) &&
      positions.all(child => tail_called_only(id, child))
    None =>
      match frame_of(s) {
        // a `var` or a region is popped by the answer, so a call under one is
        // still a tail call
        Some(frame) =>
          if frame.is_delimiter {
            !s.free().contains(id)
          } else {
            !frame.before.contains(id) && tail_called_only(id, frame.body)
          }
        None =>
          match s {
            // the only permitted occurrence: a tail call, whose arguments must
            // not mention it again
            App(Block::BlockVar(callee), _, vargs, bargs) =>
              if callee.id.uid() == id.uid() {
                !vargs.any(v => v.free().contains(id)) &&
                !bargs.any(b => b.free().contains(id))
              } else {
                !s.free().contains(id)
              }
            other => !other.free().contains(id)
          }
      }
  }
}

// ---------------------------------------------------------------------------
// Blocked prompts
// ---------------------------------------------------------------------------

///|
/// A local definition, as `escapes` needs it.
priv struct LocalDefinition {
  id : Sym
  block : Block
}

///|
fn collect_definitions(
  s : Stmt,
  out : Map[Int32, LocalDefinition],
) -> Unit raise EffektError {
  match s {
    Def(id, block, rest) => {
      out.set(id.uid(), { id, block, })
      collect_definitions_block(block, out)
      collect_definitions(rest, out)
    }
    Let(_, binding, body) => {
      collect_definitions_expr(binding, out)
      collect_definitions(body, out)
    }
    ImpureApp(_, _, _, vargs, bargs, body) => {
      for v in vargs {
        collect_definitions_expr(v, out)
      }
      for b in bargs {
        collect_definitions_block(b, out)
      }
      collect_definitions(body, out)
    }
    Return(exprs) =>
      for e in exprs {
        collect_definitions_expr(e, out)
      }
    Val(_, binding, body) => {
      collect_definitions(binding, out)
      collect_definitions(body, out)
    }
    App(callee, _, vargs, bargs) => {
      collect_definitions_block(callee, out)
      for v in vargs {
        collect_definitions_expr(v, out)
      }
      for b in bargs {
        collect_definitions_block(b, out)
      }
    }
    Invoke(callee, _, _, _, vargs, bargs) => {
      collect_definitions_block(callee, out)
      for v in vargs {
        collect_definitions_expr(v, out)
      }
      for b in bargs {
        collect_definitions_block(b, out)
      }
    }
    If(cond, thn, els) => {
      collect_definitions_expr(cond, out)
      collect_definitions(thn, out)
      collect_definitions(els, out)
    }
    Match(scrutinee, _, clauses, default) => {
      collect_definitions_expr(scrutinee, out)
      for clause in clauses {
        collect_definitions(clause.body.body, out)
      }
      if default is Some(body) {
        collect_definitions(body, out)
      }
    }
    Region(lit) => collect_definitions(lit.body, out)
    Alloc(_, init, _, body) => {
      collect_definitions_expr(init, out)
      collect_definitions(body, out)
    }
    Var(_, init, _, body) => {
      collect_definitions_expr(init, out)
      collect_definitions(body, out)
    }
    Get(_, _, _, _, body) => collect_definitions(body, out)
    Put(_, _, value, body) => {
      collect_definitions_expr(value, out)
      collect_definitions(body, out)
    }
    Reset(lit) => collect_definitions(lit.body, out)
    Shift(_, _, body) => collect_definitions(body, out)
    Resume(_, body) => collect_definitions(body, out)
    Hole(_, _) => ()
  }
}

///|
fn collect_definitions_block(
  b : Block,
  out : Map[Int32, LocalDefinition],
) -> Unit raise EffektError {
  match b {
    BlockVar(_) => ()
    BlockLit(lit) => collect_definitions(lit.body, out)
    Unbox(e) => collect_definitions_expr(e, out)
    New(implementation) =>
      for op in implementation.operations {
        collect_definitions(op.body, out)
      }
  }
}

///|
fn collect_definitions_expr(
  e : Expr,
  out : Map[Int32, LocalDefinition],
) -> Unit raise EffektError {
  match e {
    ValueVar(_, _) | Literal(_, _) => ()
    PureApp(_, _, vargs) =>
      for v in vargs {
        collect_definitions_expr(v, out)
      }
    Make(_, _, _, vargs) =>
      for v in vargs {
        collect_definitions_expr(v, out)
      }
    Box(b, _) => collect_definitions_block(b, out)
  }
}

///|
/// Whether `k` escapes from `s`: it, or a local definition closing over it,
/// occurs other than as the callee of a call, or in a block that is not bound by a
/// definition.
fn escapes(k : Sym, s : Stmt) -> Bool raise EffektError {
  let defined : Map[Int32, LocalDefinition] = Map([])
  collect_definitions(s, defined)
  // the definitions that close over k, directly or through one that does
  let closed = sym_set([k])
  let mut changed = true
  while changed {
    changed = false
    for uid, def in defined {
      if !closed.contains(uid) &&
        def.block.free().free_ids().any(id => closed.contains(id.uid())) {
        closed.set(uid, def.id)
        changed = true
      }
    }
  }
  escaping_stmt(closed, s)
}

///|
fn escaping_stmt(closed : Map[Int32, Sym], s : Stmt) -> Bool raise EffektError {
  match s {
    Def(_, Block::BlockLit(lit), rest) =>
      escaping_stmt(closed, lit.body) || escaping_stmt(closed, rest)
    App(Block::BlockVar(_), _, vargs, bargs) =>
      exprs_escape(closed, vargs) || blocks_escape(closed, bargs)
    Resume(_, resumed) => escaping_stmt(closed, resumed)
    Reset(lit) => escaping_stmt(closed, lit.body)
    Region(lit) => escaping_stmt(closed, lit.body)
    // the congruence
    Def(_, block, rest) =>
      escaping_block(closed, block) || escaping_stmt(closed, rest)
    Let(_, binding, body) =>
      escaping_expr(closed, binding) || escaping_stmt(closed, body)
    ImpureApp(_, callee, _, vargs, bargs, body) =>
      escaping_block_var(closed, callee) ||
      exprs_escape(closed, vargs) ||
      blocks_escape(closed, bargs) ||
      escaping_stmt(closed, body)
    Return(exprs) => exprs_escape(closed, exprs)
    Val(_, binding, body) =>
      escaping_stmt(closed, binding) || escaping_stmt(closed, body)
    App(callee, _, vargs, bargs) =>
      escaping_block(closed, callee) ||
      exprs_escape(closed, vargs) ||
      blocks_escape(closed, bargs)
    Invoke(callee, _, _, _, vargs, bargs) =>
      escaping_block(closed, callee) ||
      exprs_escape(closed, vargs) ||
      blocks_escape(closed, bargs)
    If(cond, thn, els) =>
      escaping_expr(closed, cond) ||
      escaping_stmt(closed, thn) ||
      escaping_stmt(closed, els)
    Match(scrutinee, _, clauses, default) =>
      escaping_expr(closed, scrutinee) ||
      clauses.any(clause => escaping_stmt(closed, clause.body.body)) ||
      (match default {
        Some(body) => escaping_stmt(closed, body)
        None => false
      })
    Alloc(_, init, _, body) =>
      escaping_expr(closed, init) || escaping_stmt(closed, body)
    Var(_, init, _, body) =>
      escaping_expr(closed, init) || escaping_stmt(closed, body)
    Get(_, _, _, _, body) => escaping_stmt(closed, body)
    Put(_, _, value, body) =>
      escaping_expr(closed, value) || escaping_stmt(closed, body)
    Shift(prompt, _, body) =>
      escaping_block_var(closed, prompt) || escaping_stmt(closed, body)
    Hole(_, _) => false
  }
}

///|
fn escaping_block(
  closed : Map[Int32, Sym],
  b : Block,
) -> Bool raise EffektError {
  match b {
    BlockVar(v) => closed.contains(v.id.uid())
    BlockLit(lit) => lit.free().free_ids().any(id => closed.contains(id.uid()))
    Unbox(e) => escaping_expr(closed, e)
    New(implementation) =>
      implementation.free().free_ids().any(id => closed.contains(id.uid()))
  }
}

///|
fn escaping_block_var(closed : Map[Int32, Sym], v : BlockVar) -> Bool {
  closed.contains(v.id.uid())
}

///|
fn escaping_expr(closed : Map[Int32, Sym], e : Expr) -> Bool raise EffektError {
  match e {
    ValueVar(_, _) | Literal(_, _) => false
    PureApp(callee, _, vargs) =>
      escaping_block_var(closed, callee) || exprs_escape(closed, vargs)
    Make(_, _, _, vargs) => exprs_escape(closed, vargs)
    Box(b, _) => escaping_block(closed, b)
  }
}

///|
fn exprs_escape(
  closed : Map[Int32, Sym],
  exprs : Array[Expr],
) -> Bool raise EffektError {
  exprs.any(e => escaping_expr(closed, e))
}

///|
fn blocks_escape(
  closed : Map[Int32, Sym],
  blocks : Array[Block],
) -> Bool raise EffektError {
  blocks.any(b => escaping_block(closed, b))
}

///|
/// The prompts that have to be left alone; see the module comment.
fn blocked_prompts(module : ModuleDecl) -> Map[Int32, Sym] raise EffektError {
  let out : Map[Int32, Sym] = Map([])
  let on_stmt = (s : Stmt) => {
    match s {
      Shift(prompt, _, _) =>
        if shift_info_of(s) is Some(shift) {
          if !(shift.resumes_only() && !escapes(shift.k, shift.body())) {
            out.set(prompt.id.uid(), prompt.id)
          }
        }
      _ => ()
    }
  }
  let rewrite = Rewrite(
    Some((_rewrite, s) => {
      on_stmt(s)
      None
    }),
    None,
    None,
    Some((_rewrite, b) => {
      match b {
        BlockVar(v) =>
          match v.annotated_tpe {
            PromptType(_) => out.set(v.id.uid(), v.id)
            _ => ()
          }
        BlockLit(lit) =>
          for param in lit.bparams {
            match param.tpe {
              PromptType(_) => out.set(param.id.uid(), param.id)
              _ => ()
            }
          }
        _ => ()
      }
      None
    }),
  )
  let _ = rewrite.rewrite_module(module)
  out
}

// ---------------------------------------------------------------------------
// The rules
// ---------------------------------------------------------------------------

///|
/// [[ shift(p) { {k} => B[resume(k){s}] } ]] ~> B[s]
///
/// Sound iff every use of `k` is a tail shift, reached only through segments that
/// no shift observes, and every exit is one too (unless the shift is
/// `at_prompt`, where any exit is the answer already).
fn reuse(shift : ShiftInfo, at_prompt : Bool) -> Stmt? raise EffektError {
  reuse_go(shift, at_prompt, shift.body(), Map([]))
}

///|
fn reuse_go(
  shift : ShiftInfo,
  at_prompt : Bool,
  s : Stmt,
  transparents : Map[Int32, Sym],
) -> Stmt? raise EffektError {
  match tail_positions(s) {
    Some(positions) => {
      // `k` escapes into a binding
      if positions.before.contains(shift.k) {
        return None
      }
      let extended = sym_set_union(
        transparents,
        sym_set(positions.transparents),
      )
      let bail = Bail()
      let rewritten = positions.rewrite(child => {
        match reuse_go(shift, at_prompt, child, extended) {
          Some(result) => result
          None => {
            bail.abort()
            child
          }
        }
      })
      if bail.aborted {
        None
      } else {
        Some(retype_answer(rewritten, shift.result))
      }
    }
    None =>
      match shift.resume_of(s) {
        // [[ resume(k){s} ]] = s
        Some(resumed) =>
          if !resumed.free().contains(shift.k) {
            Some(resumed)
          } else {
            None
          }
        None =>
          match frame_of(s) {
            // a `var` or a region is popped by the answer, so it stands above; a
            // nested `reset` only at the prompt, since an abort to it is an exit
            Some(frame) =>
              if (!frame.is_delimiter || at_prompt) &&
                !frame.before.contains(shift.k) &&
                !shift.observes(frame.names, frame.body) {
                match reuse_go(shift, at_prompt, frame.body, transparents) {
                  Some(result) => Some(frame.rebuild(result))
                  None => None
                }
              } else if s.free().contains(shift.k) {
                None
              } else {
                reuse_leaf(shift, at_prompt, s, transparents)
              }
            None =>
              if s.free().contains(shift.k) {
                None
              } else {
                reuse_leaf(shift, at_prompt, s, transparents)
              }
          }
      }
  }
}

///|
/// The exits of a shift body that are not covered by the congruences of `reuse`.
fn reuse_leaf(
  shift : ShiftInfo,
  at_prompt : Bool,
  s : Stmt,
  transparents : Map[Int32, Sym],
) -> Stmt? raise EffektError {
  match s {
    App(Block::BlockVar(f), targs, vargs, bargs) =>
      // a tail call to a block that is only ever tail-called
      if transparents.contains(f.id.uid()) {
        match f.annotated_tpe {
          FunctionType(tps, cps, vps, bps, _) =>
            Some(
              App(
                Block::BlockVar({
                  ..f,
                  annotated_tpe: FunctionType(tps, cps, vps, bps, shift.result),
                }),
                targs,
                vargs,
                bargs,
              ),
            )
          _ => None
        }
      } else {
        None
      }
    Hole(_, _) => Some(retype_answer(s, shift.result))
    _ =>
      // an exit that never returns is no exit
      if at_prompt || s.infer_type().contains(t_bottom()) {
        Some(retype_answer(s, shift.result))
      } else {
        None
      }
  }
}

///|
/// [[ shift(p) { {k} => b } ]] ~> def j(y) = reset { p' => return y };
///                               b[ resume(k){return e} := j(e) ]
/// if `k` is only resumed.
fn copy(
  continuation : Continuation,
  shift : ShiftInfo,
  blocked : Map[Int32, Sym],
) -> Stmt? raise EffektError {
  if shift.resumes_only() {
    joinpoint(continuation, shift.result, [shift], blocked, jump => {
      shift.replace_resumptions(jump)
    })
  } else {
    None
  }
}

///|
/// Binds `def j(y) = [[continuation]].fill(return y)` around `scope(j)`, with the
/// prompt renamed, or the thunked form when a resumption does not resume with a
/// value.
///
/// The machine reinstalls the *same* prompt on resume, a join point only a fresh
/// one: nothing other than the renamed binders may know the old name, neither
/// inside the join point nor in what is passed to it. Renaming would hide that, so
/// it is checked on the free variables before renaming.
fn joinpoint(
  continuation : Continuation,
  result : Array[ValueType],
  shifts : Array[ShiftInfo],
  blocked : Map[Int32, Sym],
  scope : ((Stmt) -> Stmt raise EffektError) -> Stmt raise EffektError,
) -> Stmt? raise EffektError {
  let bail = Bail()
  let fresh : Map[Int32, Sym] = Map([])
  for _, id in continuation.prompt.names() {
    fresh.set(id.uid(), Sym::id(id.name()))
  }
  let renaming = Rewrite(
    None,
    Some(id => {
      match fresh.get(id.uid()) {
        Some(f) => f
        None => id
      }
    }),
    None,
    None,
  )
  let knows_old_name = (s : Stmt) => {
    let free = s.free()
    free
    .free_blocks()
    .any(fb => {
      !fresh.contains(fb.id.uid()) &&
      captures_any_in(fb.capt.union(captures_of_block_type(fb.tpe)), fresh)
    }) ||
    free
    .free_values()
    .any(fv => {
      !fresh.contains(fv.id.uid()) &&
      captures_any_in(captures_of_value_type(fv.tpe), fresh)
    })
  }
  if captures_any_in(captures_of_value_types(result), fresh) {
    return None
  }
  let j = Sym::tmp_block("j")

  // the join point's body: the continuation's frames, around `filled`
  let frames = (filled : Stmt) => {
    let code = continuation.fill(filled)
    if knows_old_name(code) {
      None
    } else {
      Some(reduce_rewriter(blocked).rewrite_stmt(renaming.rewrite_stmt(code)))
    }
  }

  // nothing may enter the join point carrying a name the copy renamed
  let entering = (s : Stmt) => {
    !(captures_any_in(s.infer_capt(), fresh) || knows_old_name(s))
  }

  let taking_a_value = () => {
    let ys : Array[ValueParam] = result.map(tpe => {
      ValueParam(Sym::tmp_value("y"), tpe)
    })
    let results = Return(ys.map(y => Expr::ValueVar(y.id, y.tpe)))
    match frames(results) {
      None => None
      Some(body) => {
        let j_def = BlockLit::BlockLit([], [], ys, [], body)
        let j_var = Block::BlockVar(
          BlockVar::BlockVar(j, j_def.infer_type(), j_def.infer_capt()),
        )
        let scoped = scope((s : Stmt) => {
          match s {
            Return(exprs) =>
              if entering(s) {
                App(j_var, [], exprs, [])
              } else {
                bail.abort()
                Return([])
              }
            _ => {
              bail.abort()
              Return([])
            }
          }
        })
        if bail.aborted {
          None
        } else {
          Some(Def(j, Block::BlockLit(j_def), scoped))
        }
      }
    }
  }

  let taking_a_computation = () => {
    let s = Sym::tmp_block("s")
    let s_capt = Sym::tmp_block("sCapt")
    let s_param = BlockParam(
      s,
      FunctionType([], [], [], [], result),
      CaptureSetOf([s_capt]),
    )
    let callee = Block::BlockVar(
      BlockVar::BlockVar(s, s_param.tpe, CaptureSetOf([s_capt])),
    )
    match frames(App(callee, [], [], [])) {
      None => None
      Some(body) => {
        let j_def = BlockLit::BlockLit([], [s_capt], [], [s_param], body)
        let j_var = Block::BlockVar(
          BlockVar::BlockVar(j, j_def.infer_type(), j_def.infer_capt()),
        )
        let scoped = scope((stmt : Stmt) => {
          if !entering(stmt) {
            bail.abort()
          }
          App(j_var, [], [], [
            Block::BlockLit(BlockLit::BlockLit([], [], [], [], stmt)),
          ])
        })
        if bail.aborted {
          None
        } else {
          Some(Def(j, Block::BlockLit(j_def), scoped))
        }
      }
    }
  }

  let mut with_values = true
  for shift in shifts {
    if !shift.resumes_with_values() {
      with_values = false
    }
  }
  if with_values {
    taking_a_value()
  } else {
    taking_a_computation()
  }
}

///|
/// The binding of a joined `val`, now standing at the prompt: every exit jumps to
/// the join point.
///
///   [[ shift(p) { {k} => b } ]] = b[ resume(k){s} := jump(s) ]
///   [[ l ]]                     = jump(l)   any other leaf, an untreatable shift
///                                           included
fn jumps_to_join(
  prompt : Prompt,
  s : Stmt,
  jump : (Stmt) -> Stmt raise EffektError,
  transparents : Map[Int32, Sym],
) -> Stmt raise EffektError {
  match tail_positions(s) {
    Some(positions) => {
      let extended = sym_set_union(
        transparents,
        sym_set(positions.transparents),
      )
      retype_answer(
        positions.rewrite(child => jumps_to_join(prompt, child, jump, extended)),
        prompt.answer,
      )
    }
    None => {
      if prompt.shift_of(s) is Some(shift) {
        if shift.resumes_only() {
          return shift.replace_resumptions(jump)
        }
      }
      match s {
        // [[ f(…) ]] = f(…), a tail call to a block only ever tail-called
        App(Block::BlockVar(f), targs, vargs, bargs) if transparents.contains(
            f.id.uid(),
          ) =>
          match f.annotated_tpe {
            FunctionType(tps, cps, vps, bps, _) =>
              App(
                Block::BlockVar({
                  ..f,
                  annotated_tpe: FunctionType(tps, cps, vps, bps, prompt.answer),
                }),
                targs,
                vargs,
                bargs,
              )
            _ => jumps_to_join_leaf(prompt, s, jump)
          }
        _ => jumps_to_join_leaf(prompt, s, jump)
      }
    }
  }
}

///|
/// A leaf of the binding of a joined `val`: it produces the frame's value where
/// it stands, so it jumps with that value — the frames moved into the join point,
/// the leaf did not.
fn jumps_to_join_leaf(
  prompt : Prompt,
  leaf : Stmt,
  jump : (Stmt) -> Stmt raise EffektError,
) -> Stmt raise EffektError {
  let result_types = leaf.infer_type()
  // an exit that never returns is no exit
  if result_types.contains(t_bottom()) {
    return retype_answer(leaf, prompt.answer)
  }
  match leaf {
    Return(_) => jump(leaf)
    _ => {
      let ys : Array[Sym] = result_types.map(_ => Sym::tmp_value("y"))
      let results : Array[Expr] = []
      for i in 0..<ys.length() {
        results.push(Expr::ValueVar(ys[i], result_types[i]))
      }
      Val(ys, leaf, jump(Return(results)))
    }
  }
}

///|
/// The statements `k` is resumed with in `s`.
fn resumed_statements(k : Sym, s : Stmt) -> Array[Stmt] raise EffektError {
  let out : Array[Stmt] = []
  let rewrite = Rewrite(
    Some((rewrite, stmt) => {
      match stmt {
        Resume(k_var, resumed) =>
          if k_var.id.uid() == k.uid() {
            out.push(resumed)
          }
        _ => ()
      }
      match stmt {
        Def(_, block, rest) => {
          let _ = rewrite.rewrite_block(block)
          let _ = rewrite.rewrite_stmt(rest)
        }
        Let(_, binding, body) => {
          let _ = rewrite.rewrite_expr(binding)
          let _ = rewrite.rewrite_stmt(body)
        }
        ImpureApp(_, _, _, vargs, bargs, body) => {
          for v in vargs {
            let _ = rewrite.rewrite_expr(v)
          }
          for b in bargs {
            let _ = rewrite.rewrite_block(b)
          }
          let _ = rewrite.rewrite_stmt(body)
        }
        Return(exprs) =>
          for e in exprs {
            let _ = rewrite.rewrite_expr(e)
          }
        Val(_, binding, body) => {
          let _ = rewrite.rewrite_stmt(binding)
          let _ = rewrite.rewrite_stmt(body)
        }
        App(callee, _, vargs, bargs) => {
          let _ = rewrite.rewrite_block(callee)
          for v in vargs {
            let _ = rewrite.rewrite_expr(v)
          }
          for b in bargs {
            let _ = rewrite.rewrite_block(b)
          }
        }
        Invoke(callee, _, _, _, vargs, bargs) => {
          let _ = rewrite.rewrite_block(callee)
          for v in vargs {
            let _ = rewrite.rewrite_expr(v)
          }
          for b in bargs {
            let _ = rewrite.rewrite_block(b)
          }
        }
        If(cond, thn, els) => {
          let _ = rewrite.rewrite_expr(cond)
          let _ = rewrite.rewrite_stmt(thn)
          let _ = rewrite.rewrite_stmt(els)
        }
        Match(scrutinee, _, clauses, default) => {
          let _ = rewrite.rewrite_expr(scrutinee)
          for clause in clauses {
            let _ = rewrite.rewrite_block_lit(clause.body)
          }
          if default is Some(body) {
            let _ = rewrite.rewrite_stmt(body)
          }
        }
        Region(lit) => {
          let _ = rewrite.rewrite_block_lit(lit)
        }
        Alloc(_, init, _, body) => {
          let _ = rewrite.rewrite_expr(init)
          let _ = rewrite.rewrite_stmt(body)
        }
        Var(_, init, _, body) => {
          let _ = rewrite.rewrite_expr(init)
          let _ = rewrite.rewrite_stmt(body)
        }
        Get(_, _, _, _, body) => {
          let _ = rewrite.rewrite_stmt(body)
        }
        Put(_, _, value, body) => {
          let _ = rewrite.rewrite_expr(value)
          let _ = rewrite.rewrite_stmt(body)
        }
        Reset(lit) => {
          let _ = rewrite.rewrite_block_lit(lit)
        }
        Shift(_, _, body) => {
          let _ = rewrite.rewrite_stmt(body)
        }
        Resume(_, body) => {
          let _ = rewrite.rewrite_stmt(body)
        }
        Hole(_, _) => ()
      }
      None
    }),
    None,
    None,
    None,
  )
  let _ = rewrite.rewrite_stmt(s)
  out
}

///|
/// [[ T[s₁, …, sₙ] ]] ~> T[ [[ s₁ ]], …, [[ sₙ] ]] for the tail positions of `s`.
fn reduce_shifts(
  prompt : Prompt,
  s : Stmt,
  joinable : Bool,
  blocked : Map[Int32, Sym],
) -> Stmt raise EffektError {
  // 1) a shift to `prompt`, with nothing left between it and the prompt
  if prompt.shift_of(s) is Some(shift) {
    // 1a) in place, since any exit is the answer already
    return match reuse(shift, true) {
      Some(result) => result
      None =>
        // 1b) copied into a join point, if no `var` or a region lies above
        if joinable {
          match copy(Continuation(prompt, None), shift, blocked) {
            Some(result) => result
            // 1c) else left alone
            None => s
          }
        } else {
          s
        }
    }
  }
  // 2) a `val` frame over a shift to `prompt`, with no `var` or a region above
  if val_with_shifts(prompt, s) is Some((ys, binding, rest, shifts)) {
    if joinable {
      let continuation = Continuation(prompt, Some((ys, rest)))
      return match
        joinpoint(continuation, binding.infer_type(), shifts, blocked, jump => {
          reduce_shifts(
            prompt,
            jumps_to_join(prompt, binding, jump, Map([])),
            true,
            blocked,
          )
        }) {
        Some(result) => result
        None => Val(ys, binding, reduce_shifts(prompt, rest, joinable, blocked))
      }
    }
  }
  // 3) a `var` or a region is popped by the answer, so the shifts below it still
  // stand at the prompt; but it cannot be copied, so from here only 1a) applies
  if frame_of(s) is Some(frame) {
    if !frame.is_delimiter {
      return frame.rebuild(reduce_shifts(prompt, frame.body, false, blocked))
    }
  }
  // 4) anything else pushes nothing, so continue into its tail positions
  match tail_positions(s) {
    Some(positions) =>
      positions.rewrite(child => reduce_shifts(prompt, child, joinable, blocked))
    None => s
  }
}

///|
/// `val ys = E[shift(p){...}]; rest` where `E` stands under `val` frames only.
fn val_with_shifts(
  prompt : Prompt,
  s : Stmt,
) -> (Array[Sym], Stmt, Stmt, Array[ShiftInfo])? raise EffektError {
  match s {
    Val(ys, binding, rest) => {
      let shifts = shifts_to(prompt, binding)
      if !shifts.is_empty() {
        Some((ys, binding, rest, shifts))
      } else {
        None
      }
    }
    _ => None
  }
}

///|
/// The shifts to `prompt` that can be joined, standing in `s` under `val` frames
/// only.
fn shifts_to(prompt : Prompt, s : Stmt) -> Array[ShiftInfo] raise EffektError {
  match prompt.shift_of(s) {
    Some(shift) => if shift.resumes_only() { [shift] } else { [] }
    None =>
      match s {
        Val(_, binding, body) =>
          shifts_to(prompt, binding) + shifts_to(prompt, body)
        _ =>
          match tail_positions(s) {
            Some(positions) => {
              let out : Array[ShiftInfo] = []
              for child in positions.tails() {
                for shift in shifts_to(prompt, child) {
                  out.push(shift)
                }
              }
              out
            }
            None => []
          }
      }
  }
}

///|
fn retype_answer(s : Stmt, tpe : Array[ValueType]) -> Stmt {
  match s {
    Match(scrutinee, _, clauses, default) =>
      Match(scrutinee, tpe, clauses, default)
    Hole(_, span) => Hole(tpe, span)
    other => other
  }
}

///|
/// The rewrite of the pass: a shift whose context is unknown, and the statements
/// around a `reset` whose prompt is not blocked.
fn reduce_rewriter(blocked : Map[Int32, Sym]) -> Rewrite {
  Rewrite(
    Some((rewrite, s) => {
      match s {
        // 0) a shift whose context is unknown (inside a call or a closure),
        //    inner shifts first:
        //    [[ shift(p) { {k} => B[resume(k){s}] } ]] ~> B[s] if every exit resumes
        Shift(prompt, _, _) =>
          match shift_info_of(s) {
            Some(shift) =>
              if blocked.contains(prompt.id.uid()) {
                None
              } else {
                let inner = shift.with_body(rewrite.rewrite_stmt(shift.body()))
                match reuse(inner, false) {
                  Some(result) => Some(result)
                  None => Some(inner.shift)
                }
              }
            None => None
          }
        Reset(lit) =>
          match lit.bparams {
            [param] =>
              match param.tpe {
                PromptType(answer) =>
                  if blocked.contains(param.id.uid()) {
                    None
                  } else {
                    let capture = if !lit.cparams.is_empty() {
                      lit.cparams[0]
                    } else {
                      Sym::tmp_block("promptCapt")
                    }
                    let prompt = { param, capture, answer, }
                    let body = rewrite.rewrite_stmt(lit.body)
                    Some(
                      Reset({
                        ..lit,
                        body: reduce_shifts(prompt, body, true, blocked),
                      }),
                    )
                  }
                _ => None
              }
            _ => None
          }
        _ => None
      }
    }),
    None,
    None,
    None,
  )
}

///|
/// `StaticResumptions.apply`: reduce the static resumptions of the module, after
/// collecting the prompts that have to be left alone.
pub fn static_resumptions(module : ModuleDecl) -> ModuleDecl raise EffektError {
  let blocked = blocked_prompts(module)
  reduce_rewriter(blocked).rewrite_module(module)
}
