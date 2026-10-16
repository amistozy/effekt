// Pretty printer for the JavaScript backend.
//
// Mirrors `effekt/generator/js/PrettyPrinter.scala`.
//
// Deviations from the Scala original (documented on purpose):
//   * an *empty* block/object is printed as `{}` instead of `{  }` (kiama
//     flattens the two soft lines of `jsBlock` to two spaces);
//   * `Lambda(params, Return(obj: Object))` prints the object, upstream
//     re-prints the whole lambda, which does not terminate.

///|
/// Renders a list of statements, one per line.
pub fn show_stmts(stmts : Array[Stmt]) -> String {
  render_width(vsep(stmts.map(d_stmt)), 80)
}

///|
/// Renders the statements of a module.
pub fn show_module(m : Module) -> String {
  show_stmts(m.stmts)
}

///|
pub fn show_stmt(s : Stmt) -> String {
  render_width(d_stmt(s), 80)
}

///|
pub fn show_expr(e : Expr) -> String {
  render_width(d_expr(e), 80)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

///|
fn d_name(name : JSName) -> Doc {
  text(name.name)
}

///|
fn parens_list(docs : Array[Doc]) -> Doc {
  parens_inner(punctuate(docs, comma()))
}

///|
fn brackets_list(docs : Array[Doc]) -> Doc {
  brackets_inner(punctuate(docs, comma()))
}

///|
fn braces_list(docs : Array[Doc]) -> Doc {
  braces_inner(punctuate(docs, comma()))
}

///|
/// `jsBlock(content) = "{" <> nest(line <> content) <> line <> "}"`.
fn js_block(content : Doc) -> Doc {
  braces_inner(doc_cat(doc_nest(2, doc_cat(doc_line(), content)), doc_line()))
}

///|
/// `jsBlock(docs)`. An empty block is printed as `{}`.
fn js_block_docs(docs : Array[Doc]) -> Doc {
  if docs.length() == 0 {
    text("{}")
  } else {
    js_block(vcat(docs))
  }
}

///|
/// `jsBlock(vsep(docs, sep))`: the documents are interleaved with `sep`.
fn js_block_sep(docs : Array[Doc]) -> Doc {
  if docs.length() == 0 {
    text("{}")
  } else {
    js_block(punctuate(docs, comma()))
  }
}

///|
/// Upstream effekt's `util.intercalate(a, b)`: `a[0], b[0], a[1], b[1], ...`.
/// (The `intercalate` of our `@util` package has a different shape, so the JS
/// printer uses this local version.)
fn interleave(strings : Array[String], docs : Array[Doc]) -> Array[Doc] {
  let out : Array[Doc] = []
  for i = 0; i < strings.length(); i = i + 1 {
    out.push(text(strings[i]))
    if i < docs.length() {
      out.push(docs[i])
    }
  }
  out
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

///|
/// To be used in low precedence positions.
fn d_expr_parens(e : Expr) -> Doc {
  match e {
    IfExpr(_, _, _) | Lambda(_, _) | Object(_) => parens_inner(d_expr(e))
    _ => d_expr(e)
  }
}

///|
/// To be used in really low precedence positions.
fn d_expr_atom(e : Expr) -> Doc {
  match e {
    Variable(_) | ArrayLiteral(_) | RawLiteral(_) => d_expr(e)
    _ => parens_inner(d_expr(e))
  }
}

///|
fn d_raw(strings : Array[String], args : Array[Expr]) -> Doc {
  hcat(interleave(strings, args.map(d_expr_atom)))
}

///|
fn d_expr(e : Expr) -> Doc {
  match e {
    Call(callee, args) =>
      doc_cat(d_expr_parens(callee), parens_list(args.map(d_expr)))
    New(callee, args) =>
      doc_cat(
        doc_spacecat(text("new"), d_expr_parens(callee)),
        parens_list(args.map(d_expr)),
      )
    RawExpr(strings, args) => d_raw(strings, args)
    RawLiteral(content) => text(content)
    Member(callee, selection) =>
      doc_cat(d_expr_parens(callee), doc_cat(text("."), d_name(selection)))
    IfExpr(cond, thn, els) =>
      doc_spacecat(
        doc_spacecat(
          doc_spacecat(parens_inner(d_expr(cond)), text("?")),
          doc_spacecat(d_expr(thn), text(":")),
        ),
        d_expr(els),
      )
    Lambda(params, body) =>
      match body {
        Return(Object(properties)) =>
          // Upstream re-prints the whole lambda here, which does not terminate;
          // we print the returned object, which is clearly the intent.
          doc_cat(
            doc_spacecat(parens_list(params.map(d_name)), text("=>")),
            nested(parens_inner(d_expr(Object(properties)))),
          )
        Return(expr) =>
          doc_cat(
            doc_spacecat(parens_list(params.map(d_name)), text("=>")),
            nested(d_expr(expr)),
          )
        Block(stmts) =>
          doc_spacecat(
            doc_spacecat(parens_list(params.map(d_name)), text("=>")),
            js_block_docs(stmts.map(d_stmt)),
          )
        stmt =>
          doc_spacecat(
            doc_spacecat(parens_list(params.map(d_name)), text("=>")),
            js_block_docs([d_stmt(stmt)]),
          )
      }
    Object(properties) =>
      doc_group(
        js_block_sep(
          properties.map(p => {
            doc_cat(d_name(p.name), doc_spacecat(text(":"), d_expr(p.value)))
          }),
        ),
      )
    ArrayLiteral(elements) => brackets_list(elements.map(d_expr))
    Variable(name) => d_name(name)
  }
}

// ---------------------------------------------------------------------------
// Patterns and statements
// ---------------------------------------------------------------------------

///|
fn d_pattern(p : Pattern) -> Doc {
  match p {
    PatternVariable(name) => d_name(name)
    PatternArray(ps) => brackets_list(ps.map(d_pattern))
  }
}

///|
/// `toDocBlock`: statements that are printed without an extra layer of braces.
fn d_stmt_block(s : Stmt) -> Doc {
  match s {
    Block(_) | If(_, _, _) => d_stmt(s)
    _ => js_block_docs([d_stmt(s)])
  }
}

///|
fn d_method(f : Stmt) -> Doc {
  match f {
    Function(name, params, stmts) =>
      doc_spacecat(
        doc_cat(d_name(name), parens_list(params.map(d_name))),
        js_block_docs(stmts.map(d_stmt)),
      )
    _ => d_stmt(f)
  }
}

///|
fn d_stmt(s : Stmt) -> Doc {
  match s {
    RawStmt(strings, args) => d_raw(strings, args)
    Block(stmts) => js_block_docs(stmts.map(d_stmt))
    Return(expr) =>
      doc_cat(doc_spacecat(text("return"), d_expr(expr)), text(";"))
    ExprStmt(expr) => doc_cat(d_expr(expr), text(";"))
    Const(id, expr) =>
      doc_cat(
        doc_spacecat(
          doc_spacecat(text("const"), d_pattern(id)),
          doc_spacecat(text("="), d_expr(expr)),
        ),
        text(";"),
      )
    Let(id, expr) =>
      doc_cat(
        doc_spacecat(
          doc_spacecat(text("let"), d_pattern(id)),
          doc_spacecat(text("="), d_expr(expr)),
        ),
        text(";"),
      )
    Destruct(ids, expr) =>
      doc_cat(
        doc_spacecat(
          doc_spacecat(
            text("const"),
            braces_inner(punctuate(ids.map(d_name), comma())),
          ),
          doc_spacecat(text("="), d_expr(expr)),
        ),
        text(";"),
      )
    Assign(target, value) =>
      doc_cat(
        doc_spacecat(d_expr(target), doc_spacecat(text("="), d_expr(value))),
        text(";"),
      )
    Function(name, params, stmts) =>
      doc_spacecat(
        doc_cat(
          doc_spacecat(text("function"), d_name(name)),
          parens_list(params.map(d_name)),
        ),
        js_block_docs(stmts.map(d_stmt)),
      )
    Class(name, methods) =>
      doc_spacecat(
        doc_spacecat(text("class"), d_name(name)),
        js_block_docs(methods.map(d_method)),
      )
    If(cond, thn, Block([])) =>
      doc_spacecat(
        doc_spacecat(text("if"), parens_inner(d_expr(cond))),
        d_stmt_block(thn),
      )
    If(cond, thn, els) =>
      doc_spacecat(
        doc_spacecat(
          doc_spacecat(text("if"), parens_inner(d_expr(cond))),
          d_stmt_block(thn),
        ),
        doc_spacecat(text("else"), d_stmt_block(els)),
      )
    Try(prog, id, handler, []) =>
      doc_spacecat(
        doc_spacecat(
          doc_spacecat(text("try"), js_block_docs(prog.map(d_stmt))),
          doc_spacecat(text("catch"), parens_inner(d_name(id))),
        ),
        js_block_docs(handler.map(d_stmt)),
      )
    Try(prog, id, handler, fin) =>
      doc_spacecat(
        doc_spacecat(
          doc_spacecat(
            doc_spacecat(
              doc_spacecat(text("try"), js_block_docs(prog.map(d_stmt))),
              doc_spacecat(text("catch"), parens_inner(d_name(id))),
            ),
            js_block_docs(handler.map(d_stmt)),
          ),
          text("finally"),
        ),
        js_block_docs(fin.map(d_stmt)),
      )
    Throw(expr) => doc_cat(doc_spacecat(text("throw"), d_expr(expr)), text(";"))
    Break => text("break;")
    Continue(label) =>
      match label {
        Some(l) => doc_cat(doc_spacecat(text("continue"), d_name(l)), text(";"))
        None => text("continue;")
      }
    While(cond, stmts, label) => {
      let head = match label {
        Some(l) => doc_cat(doc_cat(d_name(l), text(":")), doc_space())
        None => empty_doc()
      }
      doc_cat(
        doc_spacecat(
          doc_cat(head, doc_spacecat(text("while"), parens_inner(d_expr(cond)))),
          js_block_docs(stmts.map(d_stmt)),
        ),
        empty_doc(),
      )
    }
    Switch(scrutinee, branches, default) => {
      let docs : Array[Doc] = []
      for b in branches {
        docs.push(
          doc_cat(
            doc_cat(doc_spacecat(text("case"), d_expr(b.tag)), text(":")),
            nested(vcat(b.body.map(d_stmt))),
          ),
        )
      }
      match default {
        Some(stmts) =>
          docs.push(doc_cat(text("default:"), nested(vcat(stmts.map(d_stmt)))))
        None => ()
      }
      doc_spacecat(
        doc_spacecat(text("switch"), parens_inner(d_expr(scrutinee))),
        js_block_docs(docs),
      )
    }
  }
}
