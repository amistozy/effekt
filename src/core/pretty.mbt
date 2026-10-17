// A pretty printer for the core representation.
//
// Mirrors `effekt/core/PrettyPrinter.scala` (this port implements the
// human-readable mode only, i.e. `HumanReadablePrettyPrinter`, which is what
// the `--show-core` flag uses). Barendregt ids are not printed: names alone
// keep the output stable and readable.

///|
/// Renders a whole module.
pub fn show_core(m : ModuleDecl) -> String {
  render_width(d_module(m), 80)
}

///|
/// Renders a list of toplevel definitions.
pub fn show_core_toplevels(definitions : Array[Toplevel]) -> String {
  render_width(d_toplevels(definitions), 60)
}

///|
pub fn show_core_toplevel(d : Toplevel) -> String {
  render_width(d_toplevel(d), 60)
}

///|
pub fn show_core_stmt(s : Stmt) -> String {
  render_width(d_stmts(s), 60)
}

///|
pub fn show_core_expr(e : Expr) -> String {
  render_width(d_expr(e), 60)
}

///|
pub fn show_core_block(b : Block) -> String {
  render_width(d_block(b), 60)
}

///|
pub fn show_core_implementation(i : Implementation) -> String {
  render_width(d_implementation(i), 60)
}

///|
pub fn show_core_value_type(t : ValueType) -> String {
  render_width(d_value_type(t), 60)
}

///|
pub fn show_core_block_type(t : BlockType) -> String {
  render_width(d_block_type(t), 60)
}

///|
pub fn show_core_captures(c : Captures) -> String {
  render_width(d_captures(c), 60)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

///|
fn d_id(id : Sym) -> Doc {
  match core_builtin_to_string(id) {
    Some(name) => text(name)
    None => text(id.name().name)
  }
}

///|
/// `emptyline` upstream: two line breaks.
fn emptyline() -> Doc {
  doc_cat(doc_line(), doc_line())
}

///|
fn parens_list(docs : Array[Doc]) -> Doc {
  parens_inner(punctuate(docs, comma()))
}

///|
fn braces_list(docs : Array[Doc]) -> Doc {
  braces_inner(punctuate(docs, comma()))
}

///|
fn brackets_list(docs : Array[Doc]) -> Doc {
  brackets_inner(punctuate(docs, comma()))
}

///|
/// `block(content) = "{" <> nest(line <> content) <> line <> "}"`.
fn braced_block(content : Doc) -> Doc {
  braces_inner(doc_cat(doc_nest(2, doc_cat(doc_line(), content)), doc_line()))
}

///|
fn escape_string(s : String) -> String {
  let buf = StringBuilder()
  for c in s {
    match c {
      '\\' => buf.write_string("\\\\")
      '"' => buf.write_string("\\\"")
      '\r' => buf.write_string("\\r")
      '\t' => buf.write_string("\\t")
      '\n' => buf.write_string("\\n")
      _ => buf.write_char(c)
    }
  }
  buf.to_string()
}

///|
fn must_escape(s : String) -> Bool {
  s.contains("\"") || s.contains("\r") || s.contains("\t")
}

///|
fn string_literal(s : String) -> Doc {
  if must_escape(s) {
    doc_cat(text("\""), doc_cat(text(escape_string(s)), text("\"")))
  } else {
    doc_cat(text("\"\"\""), doc_cat(text(s), text("\"\"\"")))
  }
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

///|
fn d_value_type(t : ValueType) -> Doc {
  match t {
    ValueTypeRef(id) => doc_cat(text("'"), d_id(id))
    ValueTypeApp(symbol, targs) =>
      if targs.length() == 0 {
        d_id(symbol)
      } else {
        doc_cat(d_id(symbol), brackets_list(targs.map(d_value_type)))
      }
    BoxedType(tpe, capt) =>
      doc_spacecat(
        d_block_type(tpe),
        doc_spacecat(text("at"), d_captures(capt)),
      )
  }
}

///|
fn d_effects(effs : Effects) -> Doc {
  let docs = effs.to_list().map(d_block_type)
  braces_list(docs)
}

///|
fn d_block_type(t : BlockType) -> Doc {
  match t {
    FunctionType(tparams, cparams, vparams, bparams, result, effects) => {
      let tps = d_type_params(tparams)
      let vps = parens_list(vparams.map(d_value_type))
      let n = if cparams.length() < bparams.length() {
        cparams.length()
      } else {
        bparams.length()
      }
      let bps : Array[Doc] = []
      for i = 0; i < n; i = i + 1 {
        bps.push(
          braces_inner(
            doc_cat(
              d_captures(cparams[i]),
              doc_spacecat(text(":"), d_block_type(bparams[i])),
            ),
          ),
        )
      }
      // After `=>` the grammar expects a primValueType, so boxed results are
      // parenthesized.
      let res = match result {
        BoxedType(_, _) => parens_inner(d_value_type(result))
        _ => d_value_type(result)
      }
      let base = doc_spacecat(
        doc_spacecat(doc_cat(tps, doc_cat(vps, hsep(bps))), text("=>")),
        res,
      )
      if effects.is_empty() {
        base
      } else {
        doc_spacecat(doc_spacecat(base, text("/")), d_effects(effects))
      }
    }
    InterfaceType(symbol, targs) =>
      if targs.length() == 0 {
        d_id(symbol)
      } else {
        doc_cat(d_id(symbol), brackets_list(targs.map(d_value_type)))
      }
  }
}

///|
fn d_captures(capt : Captures) -> Doc {
  let syms = dedup_syms(capt.to_array())
  let sorted = syms.copy()
  sorted.sort_by((a, b) => {
    let an = a.name().name
    let bn = b.name().name
    if an < bn {
      -1
    } else if an > bn {
      1
    } else {
      0
    }
  })
  braces_list(sorted.map(d_id))
}

///|
fn d_type_params(tps : Array[Sym]) -> Doc {
  if tps.length() == 0 {
    empty_doc()
  } else {
    brackets_list(tps.map(tp => doc_cat(text("'"), d_id(tp))))
  }
}

// ---------------------------------------------------------------------------
// Blocks and parameters
// ---------------------------------------------------------------------------

///|
fn d_params(
  tps : Array[Sym],
  cps : Array[Sym],
  vps : Array[ValueParam],
  bps : Array[BlockParam],
) -> Doc {
  let tps_doc = d_type_params(tps)
  let vps_doc = parens_list(vps.map(d_value_param))
  let bps_doc = if bps.length() == 0 {
    empty_doc()
  } else {
    let docs : Array[Doc] = []
    for i = 0; i < bps.length(); i = i + 1 {
      let cp = if i < cps.length() { Some(cps[i]) } else { None }
      docs.push(d_block_param_with_capture(bps[i], cp))
    }
    hsep(docs)
  }
  doc_cat(tps_doc, doc_cat(vps_doc, bps_doc))
}

///|
fn d_value_param(p : ValueParam) -> Doc {
  doc_cat(d_id(p.id), doc_spacecat(text(":"), d_value_type(p.tpe)))
}

///|
fn d_block_param(p : BlockParam) -> Doc {
  braces_inner(
    doc_cat(d_id(p.id), doc_spacecat(text(":"), d_block_type(p.tpe))),
  )
}

///|
fn d_block_param_with_capture(p : BlockParam, cparam : Sym?) -> Doc {
  match cparam {
    Some(cp) =>
      braces_inner(
        doc_cat(
          doc_spacecat(doc_spacecat(d_id(p.id), text("@")), d_id(cp)),
          doc_spacecat(text(":"), d_block_type(p.tpe)),
        ),
      )
    None => d_block_param(p)
  }
}

///|
fn d_args(
  targs : Array[ValueType],
  vargs : Array[Expr],
  bargs : Array[Block],
) -> Doc {
  let targs_doc = if targs.length() == 0 {
    empty_doc()
  } else {
    brackets_list(targs.map(d_value_type))
  }
  let vargs_doc = parens_list(vargs.map(d_expr))
  let bargs_doc = if bargs.length() == 0 {
    empty_doc()
  } else {
    hsep(bargs.map(b => braces_inner(d_block_no_braces(b))))
  }
  doc_cat(targs_doc, doc_cat(vargs_doc, bargs_doc))
}

///|
fn d_block(b : Block) -> Doc {
  d_block_with(b, false)
}

///|
fn d_block_no_braces(b : Block) -> Doc {
  d_block_with(b, true)
}

///|
fn d_block_with(b : Block, prevent_braces : Bool) -> Doc {
  match b {
    BlockVar(bv) => d_id(bv.id)
    BlockLit(lit) => {
      let doc = doc_cat(
        doc_spacecat(
          doc_cat(
            doc_space(),
            d_params(lit.tparams, lit.cparams, lit.vparams, lit.bparams),
          ),
          text("=>"),
        ),
        doc_cat(nested(d_stmts(lit.body)), doc_line()),
      )
      if prevent_braces {
        doc
      } else {
        braces_inner(doc)
      }
    }
    Unbox(e) => parens_inner(doc_spacecat(text("unbox"), d_expr(e)))
    New(implementation) =>
      doc_spacecat(text("new"), d_implementation(implementation))
  }
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

///|
fn hex_byte(b : Int32) -> String {
  let digits = "0123456789ABCDEF"
  let v = b & 0xFF
  let hi = (v >> 4) & 0xF
  let lo = v & 0xF
  "0x\{digits[hi:hi + 1].to_owned()}\{digits[lo:lo + 1].to_owned()}"
}

///|
fn d_literal(value : LiteralValue) -> Doc {
  match value {
    @source.LUnit => text("()")
    @source.LBool(b) => text(if b { "true" } else { "false" })
    @source.LInt(n) => text(n.to_string())
    @source.LDouble(d) => text(d.to_string())
    @source.LString(s) => string_literal(s)
    @source.LChar(c) => text("'\\" + c.to_string() + "'")
    @source.LByte(b) => text(hex_byte(b))
  }
}

///|
fn d_expr(e : Expr) -> Doc {
  match e {
    Literal(value, _) => d_literal(value)
    ValueVar(id, _) => d_id(id)
    PureApp(callee, targs, vargs) =>
      doc_cat(d_id(callee.id), d_args(targs, vargs, []))
    Make(_, tag, targs, vargs) =>
      doc_spacecat(text("make"), doc_cat(d_id(tag), d_args(targs, vargs, [])))
    Box(b, capt) =>
      doc_spacecat(text("box"), doc_spacecat(d_captures(capt), d_block(b)))
  }
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
fn d_stmt(s : Stmt) -> Doc {
  match s {
    // requires a block to be readable
    Def(_, _, _)
    | Let(_, _, _)
    | Val(_, _, _)
    | Alloc(_, _, _, _)
    | Var(_, _, _, _)
    | Get(_, _, _, _, _)
    | Put(_, _, _, _) => braced_block(d_stmts(s))
    _ => d_stmts(s)
  }
}

///|
fn d_optional_stmt(body : Stmt?) -> Doc {
  match body {
    Some(b) => doc_spacecat(text("else"), braces_inner(nested(d_stmts(b))))
    None => empty_doc()
  }
}

///|
fn d_stmts(s : Stmt) -> Doc {
  match s {
    Def(id, block, rest) =>
      match block {
        BlockLit(lit) =>
          doc_cat(
            doc_spacecat(
              doc_spacecat(text("def"), d_id(id)),
              doc_cat(
                d_params(lit.tparams, lit.cparams, lit.vparams, lit.bparams),
                doc_spacecat(text("="), braced_block(d_stmts(lit.body))),
              ),
            ),
            doc_cat(doc_line(), d_stmts(rest)),
          )
        _ =>
          doc_cat(
            doc_spacecat(
              doc_spacecat(text("def"), d_id(id)),
              doc_spacecat(text("="), d_block(block)),
            ),
            doc_cat(doc_line(), d_stmts(rest)),
          )
      }
    Let(id, binding, rest) =>
      doc_cat(
        doc_spacecat(
          doc_spacecat(text("let"), d_id(id)),
          doc_spacecat(text("="), d_expr(binding)),
        ),
        doc_cat(doc_line(), d_stmts(rest)),
      )
    ImpureApp(id, callee, targs, vargs, bargs, rest) =>
      doc_cat(
        doc_spacecat(
          doc_spacecat(doc_spacecat(text("let"), text("!")), d_id(id)),
          doc_spacecat(
            text("="),
            doc_cat(d_id(callee.id), d_args(targs, vargs, bargs)),
          ),
        ),
        doc_cat(doc_line(), d_stmts(rest)),
      )
    Return(e) => doc_spacecat(text("return"), d_expr(e))
    // the most common case: binding the result of a single statement
    Val(id, binding, body) =>
      match binding {
        App(_, _, _, _)
        | Hole(_, _)
        | Resume(_, _)
        | Shift(_, _, _)
        | Reset(_)
        | Region(_)
        | Match(_, _, _, _)
        | If(_, _, _)
        | Invoke(_, _, _, _, _, _)
        | Return(_) =>
          doc_cat(
            doc_spacecat(
              doc_spacecat(text("val"), d_id(id)),
              doc_spacecat(text("="), doc_cat(d_stmt(binding), text(";"))),
            ),
            doc_cat(doc_line(), d_stmts(body)),
          )
        // the remaining cases are "intrinsic lists", so we need to wrap them
        _ =>
          doc_cat(
            doc_spacecat(
              doc_spacecat(text("val"), d_id(id)),
              doc_spacecat(
                text("="),
                doc_cat(braced_block(d_stmts(binding)), text(";")),
              ),
            ),
            doc_cat(doc_line(), d_stmts(body)),
          )
      }
    App(b, targs, vargs, bargs) =>
      doc_cat(d_block(b), d_args(targs, vargs, bargs))
    Invoke(b, method_, _, targs, vargs, bargs) =>
      doc_cat(
        doc_cat(d_block(b), doc_cat(text("."), d_id(method_))),
        d_args(targs, vargs, bargs),
      )
    If(cond, thn, els) =>
      doc_spacecat(
        doc_spacecat(
          doc_spacecat(text("if"), parens_inner(d_expr(cond))),
          braced_block(d_stmts(thn)),
        ),
        doc_spacecat(text("else"), braced_block(d_stmts(els))),
      )
    Reset(body) => doc_spacecat(text("reset"), d_block_lit(body))
    Shift(prompt, k, body) =>
      doc_spacecat(
        doc_cat(text("shift"), parens_inner(d_id(prompt.id))),
        braces_inner(
          doc_cat(
            doc_spacecat(d_block_param(k), text("=>")),
            doc_cat(nested(d_stmts(body)), doc_line()),
          ),
        ),
      )
    Resume(k, body) =>
      doc_spacecat(
        doc_cat(text("resume"), parens_inner(d_id(k.id))),
        braced_block(d_stmts(body)),
      )
    Alloc(id, init, region, body) =>
      doc_cat(
        doc_spacecat(
          doc_spacecat(
            doc_spacecat(text("var"), d_id(id)),
            doc_spacecat(text("in"), d_id(region)),
          ),
          doc_spacecat(text("="), doc_cat(d_expr(init), text(";"))),
        ),
        doc_cat(doc_line(), d_stmts(body)),
      )
    Var(ref_id, init, _, body) =>
      doc_cat(
        doc_spacecat(
          doc_spacecat(text("var"), d_id(ref_id)),
          doc_spacecat(text("="), doc_cat(d_expr(init), text(";"))),
        ),
        doc_cat(doc_line(), d_stmts(body)),
      )
    Get(id, _, ref_id, _, body) =>
      doc_cat(
        doc_spacecat(
          doc_spacecat(text("get"), d_id(id)),
          doc_spacecat(
            text("="),
            doc_cat(doc_spacecat(text("!"), d_id(ref_id)), text(";")),
          ),
        ),
        doc_cat(doc_line(), d_stmts(body)),
      )
    Put(ref_id, _, value, body) =>
      doc_cat(
        doc_spacecat(
          doc_spacecat(text("put"), d_id(ref_id)),
          doc_spacecat(text("="), doc_cat(d_expr(value), text(";"))),
        ),
        doc_cat(doc_line(), d_stmts(body)),
      )
    Region(body) => doc_spacecat(text("region"), d_block_lit(body))
    Match(scrutinee, tpe, clauses, default) =>
      doc_spacecat(
        doc_spacecat(
          d_expr(scrutinee),
          doc_spacecat(
            doc_cat(text("match"), brackets_list([d_value_type(tpe)])),
            d_match_clauses(clauses),
          ),
        ),
        d_optional_stmt(default),
      )
    Hole(tpe, span) =>
      doc_spacecat(
        doc_cat(text("<>"), doc_spacecat(text(":"), d_value_type(tpe))),
        text("@ \"\{span.source.name}\":\{span.start}:\{span.end}"),
      )
  }
}

///|
fn d_block_lit(lit : BlockLit) -> Doc {
  d_block(BlockLit(lit))
}

///|
fn d_match_clauses(clauses : Array[Clause]) -> Doc {
  if clauses.length() == 0 {
    text("{}")
  } else {
    let docs : Array[Doc] = []
    for c in clauses {
      docs.push(
        doc_spacecat(doc_cat(d_id(c.tag), text(":")), d_block_lit(c.body)),
      )
    }
    braces_inner(
      doc_cat(doc_nest(2, doc_cat(doc_line(), vsep(docs))), doc_line()),
    )
  }
}

// ---------------------------------------------------------------------------
// Declarations, externs, toplevel
// ---------------------------------------------------------------------------

///|
fn d_declaration(d : Declaration) -> Doc {
  match d {
    DeclarationData(id, tparams, ctors) =>
      d_type_template(text("type"), id, tparams, ctors.map(d_constructor))
    DeclarationInterface(id, tparams, properties) =>
      d_type_template(
        text("interface"),
        id,
        tparams,
        properties.map(d_property),
      )
  }
}

///|
fn d_type_template(
  kind : Doc,
  id : Sym,
  tparams : Array[Sym],
  decls : Array[Doc],
) -> Doc {
  let tps = d_type_params(tparams)
  let body = if decls.length() == 0 {
    text("{}")
  } else {
    braced_block(vsep(decls))
  }
  doc_spacecat(doc_cat(kind, doc_cat(d_id(id), tps)), body)
}

///|
fn d_constructor(c : Constructor) -> Doc {
  doc_cat(
    doc_cat(d_id(c.id), d_type_params(c.tparams)),
    parens_list(c.fields.map(d_field)),
  )
}

///|
fn d_field(f : Field) -> Doc {
  doc_cat(d_id(f.id), doc_spacecat(text(":"), d_value_type(f.tpe)))
}

///|
fn d_property(p : Property) -> Doc {
  doc_cat(d_id(p.id), doc_spacecat(text(":"), d_block_type(p.tpe)))
}

///|
fn d_flag(ff : FeatureFlag) -> Doc {
  match ff {
    @source.NamedFeatureFlag(name) => text(name)
    @source.Default => text("default")
  }
}

///|
fn d_template(t : Template[Expr]) -> Doc {
  let head = if t.strings.length() == 0 {
    text("\"\"\"\"\"\"")
  } else {
    string_literal(t.strings[0])
  }
  let mut doc = head
  for i = 0; i < t.args.length(); i = i + 1 {
    let s = if i + 1 < t.strings.length() { t.strings[i + 1] } else { "" }
    doc = doc_cat(
      doc,
      doc_cat(
        doc_space(),
        doc_cat(
          text("++"),
          doc_cat(
            doc_spacecat(d_expr(t.args[i]), text("++")),
            doc_cat(doc_space(), string_literal(s)),
          ),
        ),
      ),
    )
  }
  doc
}

///|
fn d_error(err : EffektError) -> String {
  match err {
    @util.Fatal(msg) => msg
    @util.Internal(msg) => "Internal compiler error: \{msg}"
  }
}

///|
fn d_extern_body(body : ExternBody[Expr]) -> Doc {
  match body {
    StringExternBody(ff, contents) =>
      doc_spacecat(d_flag(ff), d_template(contents))
    Unsupported(err) => doc_spacecat(text("<unsupported>"), text(d_error(err)))
  }
}

///|
fn d_extern(e : Extern) -> Doc {
  match e {
    ExternDef(id, _, tps, cps, vps, bps, ret, capt, bodies) =>
      doc_spacecat(
        doc_spacecat(
          doc_cat(
            doc_spacecat(text("extern"), d_captures(capt)),
            doc_spacecat(text("def"), d_id(id)),
          ),
          doc_cat(
            doc_cat(d_params(tps, cps, vps, bps), text(":")),
            doc_spacecat(d_value_type(ret), text("=")),
          ),
        ),
        d_extern_body(bodies),
      )
    ExternInclude(ff, contents) =>
      doc_spacecat(
        text("extern"),
        doc_spacecat(d_flag(ff), string_literal(contents)),
      )
    ExternData(id, tps, body) =>
      doc_cat(
        doc_spacecat(text("extern type"), doc_cat(d_id(id), d_type_params(tps))),
        d_extern_body(body),
      )
    ExternInterface(id, tps, body) =>
      doc_cat(
        doc_spacecat(
          text("extern interface"),
          doc_cat(d_id(id), d_type_params(tps)),
        ),
        d_extern_body(body),
      )
  }
}

///|
fn d_implementation(implementation : Implementation) -> Doc {
  let clauses : Array[Doc] = []
  for op in implementation.operations {
    clauses.push(
      doc_spacecat(
        doc_cat(
          doc_spacecat(text("def"), d_id(op.name)),
          d_params(op.tparams, op.cparams, op.vparams, op.bparams),
        ),
        doc_spacecat(text("="), braced_block(d_stmts(op.body))),
      ),
    )
  }
  doc_spacecat(
    d_block_type(implementation.interface),
    braced_block(vsep(clauses)),
  )
}

///|
fn d_toplevel(d : Toplevel) -> Doc {
  match d {
    ToplevelDef(id, block) =>
      match block {
        BlockLit(lit) =>
          doc_spacecat(
            doc_cat(
              doc_spacecat(text("def"), d_id(id)),
              d_params(lit.tparams, lit.cparams, lit.vparams, lit.bparams),
            ),
            doc_spacecat(text("="), braced_block(d_stmts(lit.body))),
          )
        _ =>
          doc_spacecat(
            doc_spacecat(text("def"), d_id(id)),
            doc_spacecat(text("="), d_block(block)),
          )
      }
    ToplevelVal(id, binding) =>
      doc_spacecat(
        doc_spacecat(text("val"), d_id(id)),
        doc_spacecat(text("="), d_stmt(binding)),
      )
  }
}

///|
fn d_toplevels(definitions : Array[Toplevel]) -> Doc {
  vsep(definitions.map(d_toplevel))
}

///|
fn d_module(m : ModuleDecl) -> Doc {
  let includes = vsep(
    m.includes.map(im => doc_spacecat(text("import"), text(im))),
  )
  let decls = vsep(m.declarations.map(d_declaration))
  let externs = vsep(m.externs.map(d_extern))
  let defs = d_toplevels(m.definitions)
  let exports = vsep(
    m.exports.map(id => doc_spacecat(text("export"), d_id(id))),
  )
  let tail = if m.exports.length() == 0 {
    empty_doc()
  } else {
    doc_cat(emptyline(), exports)
  }
  doc_cat(
    doc_spacecat(text("module"), text(m.path)),
    doc_cat(
      emptyline(),
      doc_cat(
        includes,
        doc_cat(
          emptyline(),
          doc_cat(
            decls,
            doc_cat(
              emptyline(),
              doc_cat(externs, doc_cat(emptyline(), doc_cat(defs, tail))),
            ),
          ),
        ),
      ),
    ),
  )
}
