// Establishes a normal form in which every subexpression is explicitly named
// and aliasing (`val x = y`) is removed.
//
// Mirrors `effekt/core/optimizer/BindSubexpressions.scala`:
//
//     let x = Cons(1, Cons(2, Cons(3, Nil())))
//  ->
//     let x1 = Nil()
//     let x2 = Cons(3, x1)
//     let x3 = Cons(2, x2)
//     let x  = Cons(1, x3)
//
// Like upstream, the pass only renames *references*: a `let` / `def` binder
// keeps its id and the alias environment is extended for the body, so an
// aliased binder does not survive in the rewritten tree. Every other rewrite
// is a congruence, which makes the pass semantics preserving.
//
// Two differences to upstream, both because the core type language of this
// port is the one of the source language (see `README.mbt.md`, "Differences
// from upstream"): `BlockType.Prompt` and `BlockType.Resume` do not exist, so
// only `FunctionType` / `InterfaceType` are traversed, and a function's
// `Effects` are kept as they are.

///|
/// The alias environment of the rewrite: references to `from` become
/// references to the (transitively resolved) `to`.
priv struct Aliases {
  aliases : Map[Int32, Sym]
}

///|
fn Aliases::empty() -> Aliases {
  { aliases: Map([]), }
}

///|
fn Aliases::resolve(self : Aliases, id : Sym) -> Sym {
  match self.aliases.get(id.uid()) {
    Some(other) => other
    None => id
  }
}

///|
/// `alias(from, to, env) = env + (from -> env.getOrElse(to, to))`.
fn Aliases::alias(self : Aliases, from : Sym, to : Sym) -> Aliases {
  let aliases = self.aliases.copy()
  aliases.set(from.uid(), self.resolve(to))
  { aliases, }
}

///|
/// Names every subexpression and removes aliasing, see the note at the top.
pub fn bind_subexpressions(module : ModuleDecl) -> ModuleDecl raise EffektError {
  let env = Aliases::empty()
  ModuleDecl(
    module.path,
    module.includes,
    module.declarations,
    module.externs,
    transform_toplevels(module.definitions, env),
    module.exports,
  )
}

///|
fn transform_toplevels(
  definitions : Array[Toplevel],
  env : Aliases,
) -> Array[Toplevel] raise EffektError {
  let out : Array[Toplevel] = []
  for def in definitions {
    match def {
      ToplevelDef(id, block) => {
        let transformed = transform_block(block, env)
        // upstream `bindings.map(Binding.toToplevel)`: the emitted bindings of
        // a toplevel block are `def`s again -- a `let` / `val` there is a `???`
        for binding in transformed.bindings {
          match binding {
            BindingDef(id, block) => out.push(ToplevelDef(id, block))
            _ =>
              raise EffektError::Internal(
                "Binding.\{binding.kind_name()} is not allowed on the toplevel.",
              )
          }
        }
        out.push(ToplevelDef(id, transformed.value))
      }
      ToplevelVal(id, binding) =>
        out.push(ToplevelVal(id, transform_stmt(binding, env)))
    }
  }
  out
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

///|
fn transform_stmt(s : Stmt, env : Aliases) -> Stmt {
  match s {
    Def(id, block, body) => {
      let transformed = transform_block(block, env)
      match transformed.value {
        // `def id = other; body` aliases `id` to the block variable
        BlockVar(bv) =>
          bindings_to_stmt(
            transformed.bindings,
            transform_stmt(body, env.alias(id, bv.id)),
          )
        other =>
          bindings_to_stmt(
            transformed.bindings,
            Def(id, other, transform_stmt(body, env)),
          )
      }
    }
    Let(id, binding, body) => {
      let transformed = transform_expr(binding, env)
      match transformed.value {
        // `let id = other; body` aliases `id` to the variable
        ValueVar(rhs, _) =>
          bindings_to_stmt(
            transformed.bindings,
            transform_stmt(body, env.alias(id, rhs)),
          )
        other =>
          bindings_to_stmt(
            transformed.bindings,
            Let(id, other, transform_stmt(body, env)),
          )
      }
    }
    ImpureApp(id, callee, targs, vargs, bargs, body) =>
      Bind::delimit(
        transform_exprs(vargs, env).flat_map(vs => {
          transform_blocks(bargs, env).flat_map(bs => {
            Bind::pure(
              ImpureApp(
                id,
                transform_block_var(callee, env),
                targs.map(t => transform_value_type(t, env)),
                vs,
                bs,
                transform_stmt(body, env),
              ),
            )
          })
        }),
      )
    App(callee, targs, vargs, bargs) =>
      Bind::delimit(
        transform_block(callee, env).flat_map(c => {
          transform_exprs(vargs, env).flat_map(vs => {
            transform_blocks(bargs, env).flat_map(bs => {
              Bind::pure(
                App(c, targs.map(t => transform_value_type(t, env)), vs, bs),
              )
            })
          })
        }),
      )
    Invoke(callee, method, method_tpe, targs, vargs, bargs) =>
      Bind::delimit(
        transform_block(callee, env).flat_map(c => {
          transform_exprs(vargs, env).flat_map(vs => {
            transform_blocks(bargs, env).flat_map(bs => {
              Bind::pure(
                Invoke(
                  c,
                  method,
                  transform_block_type(method_tpe, env),
                  targs.map(t => transform_value_type(t, env)),
                  vs,
                  bs,
                ),
              )
            })
          })
        }),
      )
    Return(exprs) => transform_exprs(exprs, env).run(values => Return(values))
    Alloc(id, init, region, body) =>
      transform_expr(init, env).run(value => {
        Alloc(id, value, transform_id(region, env), transform_stmt(body, env))
      })
    Var(ref, init, capture, body) =>
      transform_expr(init, env).run(value => {
        Var(ref, value, transform_id(capture, env), transform_stmt(body, env))
      })
    Get(id, tpe, ref, capt, body) =>
      // upstream keeps `ref` untouched here (and in `Put`), even though
      // `Alloc` / `Var` do de-alias their region / capture
      Get(
        id,
        transform_value_type(tpe, env),
        ref,
        transform_captures(capt, env),
        transform_stmt(body, env),
      )
    Put(ref, capt, value, body) =>
      transform_expr(value, env).run(value2 => {
        Put(
          ref,
          transform_captures(capt, env),
          value2,
          transform_stmt(body, env),
        )
      })
    If(cond, thn, els) =>
      transform_expr(cond, env).run(c => {
        If(c, transform_stmt(thn, env), transform_stmt(els, env))
      })
    Match(scrutinee, tpe, clauses, default) =>
      transform_expr(scrutinee, env).run(sc => {
        Match(
          sc,
          tpe,
          clauses.map(clause => {
            Clause(clause.tag, transform_block_lit(clause.body, env))
          }),
          match default {
            Some(body) => Some(transform_stmt(body, env))
            None => None
          },
        )
      })
    // congruences
    Region(body) => Region(transform_block_lit(body, env))
    Val(ids, binding, body) =>
      Val(ids, transform_stmt(binding, env), transform_stmt(body, env))
    Reset(body) => Reset(transform_block_lit(body, env))
    Shift(prompt, k, body) =>
      Shift(transform_block_var(prompt, env), k, transform_stmt(body, env))
    Resume(k, body) =>
      Resume(transform_block_var(k, env), transform_stmt(body, env))
    Hole(tpe, span) => Hole(transform_value_type(tpe, env), span)
  }
}

// ---------------------------------------------------------------------------
// Expressions and blocks
// ---------------------------------------------------------------------------

///|
fn transform_expr(e : Expr, env : Aliases) -> Bind[Expr] {
  match e {
    ValueVar(id, tpe) =>
      Bind::pure(
        ValueVar(transform_id(id, env), transform_value_type(tpe, env)),
      )
    Literal(value, tpe) =>
      Bind::pure(Literal(value, transform_value_type(tpe, env)))
    // upstream does not de-alias the type arguments of a `make`
    Make(data, tag, targs, vargs) =>
      transform_exprs(vargs, env).flat_map(vs => {
        Bind::bind_expr(Make(data, tag, targs, vs))
      })
    // ... nor the callee of a pure application
    PureApp(f, targs, vargs) =>
      transform_exprs(vargs, env).flat_map(vs => {
        Bind::bind_expr(
          PureApp(f, targs.map(t => transform_value_type(t, env)), vs),
        )
      })
    Box(block, capt) =>
      transform_block(block, env).flat_map(b => {
        Bind::bind_expr(Box(b, transform_captures(capt, env)))
      })
  }
}

///|
fn transform_exprs(exprs : Array[Expr], env : Aliases) -> Bind[Array[Expr]] {
  Bind::traverse(exprs, e => transform_expr(e, env))
}

///|
fn transform_block(b : Block, env : Aliases) -> Bind[Block] {
  match b {
    BlockVar(bv) => Bind::pure(BlockVar(transform_block_var(bv, env)))
    BlockLit(lit) => Bind::pure(BlockLit(transform_block_lit(lit, env)))
    New(implementation) =>
      Bind::pure(New(transform_implementation(implementation, env)))
    Unbox(pure) =>
      transform_expr(pure, env).flat_map(v => Bind::bind_block(Unbox(v)))
  }
}

///|
fn transform_blocks(blocks : Array[Block], env : Aliases) -> Bind[Array[Block]] {
  Bind::traverse(blocks, b => transform_block(b, env))
}

///|
fn transform_block_lit(lit : BlockLit, env : Aliases) -> BlockLit {
  BlockLit::new(
    lit.tparams,
    lit.cparams,
    lit.vparams.map(p => transform_value_param(p, env)),
    lit.bparams.map(p => transform_block_param(p, env)),
    transform_stmt(lit.body, env),
  )
}

///|
fn transform_block_var(bv : BlockVar, env : Aliases) -> BlockVar {
  BlockVar::new(
    transform_id(bv.id, env),
    transform_block_type(bv.annotated_tpe, env),
    transform_captures(bv.annotated_capt, env),
  )
}

///|
fn transform_implementation(
  implementation : Implementation,
  env : Aliases,
) -> Implementation {
  Implementation(
    transform_block_type(implementation.interface, env),
    implementation.operations.map(op => {
      Operation(
        op.name,
        op.tparams,
        op.cparams,
        op.vparams.map(p => transform_value_param(p, env)),
        op.bparams.map(p => transform_block_param(p, env)),
        transform_stmt(op.body, env),
      )
    }),
  )
}

///|
fn transform_value_param(p : ValueParam, env : Aliases) -> ValueParam {
  ValueParam::ValueParam(p.id, transform_value_type(p.tpe, env))
}

///|
fn transform_block_param(p : BlockParam, env : Aliases) -> BlockParam {
  BlockParam::BlockParam(
    p.id,
    transform_block_type(p.tpe, env),
    transform_captures(p.capt, env),
  )
}

// ---------------------------------------------------------------------------
// Types: captures mention ids, so dealiasing renames them too
// ---------------------------------------------------------------------------

///|
fn transform_id(id : Sym, env : Aliases) -> Sym {
  env.resolve(id)
}

///|
fn transform_value_type(tpe : ValueType, env : Aliases) -> ValueType {
  match tpe {
    ValueTypeRef(name) => ValueTypeRef(transform_id(name, env))
    ValueTypeApp(name, targs) =>
      ValueTypeApp(name, targs.map(t => transform_value_type(t, env)))
    BoxedType(block, capt) =>
      BoxedType(transform_block_type(block, env), transform_captures(capt, env))
  }
}

///|
fn transform_block_type(tpe : BlockType, env : Aliases) -> BlockType {
  match tpe {
    FunctionType(tparams, cparams, vparams, bparams, result, effects) =>
      FunctionType(
        tparams,
        cparams,
        vparams.map(t => transform_value_type(t, env)),
        bparams.map(t => transform_block_type(t, env)),
        transform_value_type(result, env),
        effects,
      )
    InterfaceType(name, targs) =>
      InterfaceType(name, targs.map(t => transform_value_type(t, env)))
  }
}

///|
fn transform_captures(capt : Captures, env : Aliases) -> Captures {
  match capt {
    CaptureSetOf(ids) => CaptureSetOf(ids.map(id => transform_id(id, env)))
    CaptVar(id) => CaptVar(transform_id(id, env))
  }
}
