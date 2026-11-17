// Whitebox tests for the two passes that consume the normal form: `DirectStyle`
// (`direct_style.mbt`) and `StaticResumptions` (`static_resumptions.mbt`).
//
// The trees are built by hand and compared as printed code, so a test pins the
// shape of the rewrite. A whitebox test file does not inherit the `using`
// declarations of `prelude.mbt`, so the types are spelled out.

///|
fn owb_value(name : String) -> @symbols.Sym {
  @symbols.Sym::value_param(
    @symbols.Name::local(name),
    None,
    @util.Span::missing(),
  )
}

///|
fn owb_bool(name : String) -> @symbols.Sym {
  @symbols.Sym::value_param(
    @symbols.Name::local(name),
    Some(@symbols.t_bool()),
    @util.Span::missing(),
  )
}

///|
fn owb_block(
  name : String,
  tpe : BlockType,
  capt : @symbols.Captures,
) -> BlockVar {
  BlockVar::BlockVar(@symbols.Sym::tmp_block(name), tpe, capt)
}

///|
fn owb_main(body : Stmt) -> ModuleDecl {
  ModuleDecl(
    "test",
    [],
    [],
    [],
    [
      ToplevelDef(
        @symbols.Sym::tmp_block("main"),
        BlockLit(BlockLit::BlockLit([], [], [], [], body)),
      ),
    ],
    [],
  )
}

// ---------------------------------------------------------------------------
// DirectStyle
// ---------------------------------------------------------------------------

///|
test "direct style: a binding that returns becomes a join point" {
  let x = owb_value("x")
  // def main = { () => val x = return 42; return x }
  let stmt = Val(
    [x],
    Return([Literal(@source.LInt(42), t_int())]),
    Return([Expr::ValueVar(x, t_int())]),
  )
  let out = direct_style(owb_main(stmt))
  match out.definitions[0] {
    ToplevelDef(_, BlockLit(lit)) =>
      match lit.body {
        // def l(x) = { return x }; l(42)
        Def(_, BlockLit(joinpoint), App(BlockVar(callee), _, [arg], _)) => {
          assert_eq(joinpoint.vparams.length(), 1)
          assert_eq(joinpoint.vparams[0].id.uid(), x.uid())
          assert_not_eq(callee.id.uid(), x.uid())
          assert_true(arg is Literal(_, _))
        }
        other => abort("expected a join point, got \{show_core_stmt(other)}")
      }
    _ => abort("expected a toplevel definition")
  }
}

///|
test "direct style: a binding that does not return is kept" {
  let x = owb_value("x")
  let f = owb_block(
    "f",
    FunctionType([], [], [], [], [t_int()]),
    @symbols.Captures::empty(),
  )
  // def main = { () => val x = f(); return x }
  let stmt = Val(
    [x],
    App(Block::BlockVar(f), [], [], []),
    Return([Expr::ValueVar(x, t_int())]),
  )
  match direct_style(owb_main(stmt)).definitions[0] {
    ToplevelDef(_, BlockLit(lit)) => assert_true(lit.body is Val(_, _, _))
    _ => abort("expected a toplevel definition")
  }
}

// ---------------------------------------------------------------------------
// StaticResumptions
// ---------------------------------------------------------------------------

///|
/// `reset { [pCapt]{p: Prompt[Int]} => body }`
fn owb_reset(
  body : Stmt,
  prompt_capt : @symbols.Sym,
  prompt : BlockParam,
) -> Stmt {
  Reset(BlockLit::BlockLit([], [prompt_capt], [], [prompt], body))
}

///|
test "static resumptions: an aborting shift at its prompt becomes what it aborts with" {
  let b = owb_bool("b")
  let prompt_capt = @symbols.Sym::tmp_block("pCapt")
  let prompt_id = @symbols.Sym::tmp_block("p")
  let prompt = BlockParam(
    prompt_id,
    PromptType([t_int()]),
    @symbols.Captures::CaptureSetOf([prompt_capt]),
  )
  let k_capt = @symbols.Sym::tmp_block("kCapt")
  let k = BlockParam(
    @symbols.Sym::tmp_block("k"),
    ResumeType([t_int()], [t_int()]),
    @symbols.Captures::CaptureSetOf([k_capt]),
  )
  // if (b) { return 1 } else { shift p { k => return 2 } }
  let body = If(
    Expr::ValueVar(b, t_bool()),
    Return([Literal(@source.LInt(1), t_int())]),
    Shift(
      BlockVar::BlockVar(
        prompt_id,
        PromptType([t_int()]),
        @symbols.Captures::CaptureSetOf([prompt_capt]),
      ),
      k,
      Return([Literal(@source.LInt(2), t_int())]),
    ),
  )
  let out = static_resumptions(owb_main(owb_reset(body, prompt_capt, prompt)))
  let rendered = show_core_toplevel(out.definitions[0])
  // the shift is gone: every exit of the branch is the answer already
  assert_false(rendered.contains("shift"))
  assert_true(rendered.contains("return 2"))
}
