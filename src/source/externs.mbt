// Resolving `extern` definitions for the current backend.
//
// Mirrors `effekt/source/ResolveExternDefs.scala`. An extern definition may
// carry several bodies, each guarded by a feature flag (e.g. `js`, `chez`,
// `llvm`, or `default`). Here we pick the body that matches the current
// backend and drop extern includes that target other backends.

///|
/// The feature flags supported by the current backend, most specific first.
pub fn supported_flags(ctx : Context) -> Array[String] {
  ctx.config.feature_flags
}

///|
/// Picks the body whose feature flag matches, preferring the earliest entry in
/// the supported list. Returns `None` if no body is applicable.
pub fn find_preferred(bodies : Array[ExternBody], ctx : Context) -> ExternBody? {
  let supported = supported_flags(ctx)
  let mut best : ExternBody? = None
  let mut best_rank = supported.length() + 1
  for b in bodies {
    match b.flag() {
      NamedFeatureFlag(name) =>
        match index_of(supported, name) {
          Some(i) =>
            if i < best_rank {
              best = Some(b)
              best_rank = i
            }
          None => ()
        }
      Default =>
        if best_rank > supported.length() {
          best = Some(b)
          best_rank = supported.length()
        }
    }
  }
  best
}

///|
pub fn index_of(xs : Array[String], x : String) -> Int32? {
  for i = 0; i < xs.length(); i = i + 1 {
    if xs[i] == x {
      return Some(i)
    }
  }
  None
}

///|
fn unsupported_error(bodies : Array[ExternBody], ctx : Context) -> ExternBody {
  let flags : Array[String] = bodies.map(b => b.flag().to_string())
  let supported = supported_flags(ctx).join(", ")
  Unsupported(
    "Extern definition is not supported as it is only defined for feature flags \{flags.join(", ")}, but the current backend only supports \{supported}.",
  )
}

///|
/// Rewrites the module, selecting the extern body that applies to this backend.
pub fn resolve_extern_defs(
  module : ModuleDecl,
  ctx : Context,
) -> ModuleDecl raise EffektError {
  let defs : Array[Def] = []
  for d in module.defs {
    defs.append(resolve_extern_def(d, ctx))
  }
  { ..module, defs, }
}

///|
fn resolve_extern_def(d : Def, ctx : Context) -> Array[Def] raise EffektError {
  match d.kind {
    ExternDef(id, tparams, vparams, bparams, captures, ret, bodies) =>
      match find_preferred(bodies, ctx) {
        Some(StringExternBody(flag, template)) => {
          warn_default_flag(flag, id, ctx)
          [
            copy_def(
              d,
              ExternDef(id, tparams, vparams, bparams, captures, ret, [
                StringExternBody(flag, template),
              ]),
              ctx,
            ),
          ]
        }
        Some(EffektExternBody(_, body)) => {
          // An Effekt-implemented extern becomes an ordinary function.
          let d2 = copy_def(
            d,
            FunDef(
              id,
              tparams,
              vparams,
              bparams,
              Some(captures),
              Some(ret),
              body,
            ),
            ctx,
          )
          ctx.assign_bound_capabilities(d2.uid, [])
          [d2]
        }
        Some(Unsupported(msg)) =>
          [
            copy_def(
              d,
              ExternDef(id, tparams, vparams, bparams, captures, ret, [
                Unsupported(msg),
              ]),
              ctx,
            ),
          ]
        None =>
          [
            copy_def(
              d,
              ExternDef(id, tparams, vparams, bparams, captures, ret, [
                unsupported_error(bodies, ctx),
              ]),
              ctx,
            ),
          ]
      }
    ExternType(id, tparams, bodies) =>
      match find_preferred(bodies, ctx) {
        Some(StringExternBody(flag, template)) => {
          warn_default_flag(flag, id, ctx)
          [
            copy_def(
              d,
              ExternType(id, tparams, [StringExternBody(flag, template)]),
              ctx,
            ),
          ]
        }
        Some(Unsupported(msg)) =>
          [copy_def(d, ExternType(id, tparams, [Unsupported(msg)]), ctx)]
        _ =>
          [
            copy_def(
              d,
              ExternType(id, tparams, [unsupported_error(bodies, ctx)]),
              ctx,
            ),
          ]
      }
    ExternInterface(id, tparams, bodies) =>
      match find_preferred(bodies, ctx) {
        Some(StringExternBody(flag, template)) => {
          warn_default_flag(flag, id, ctx)
          [
            copy_def(
              d,
              ExternInterface(id, tparams, [StringExternBody(flag, template)]),
              ctx,
            ),
          ]
        }
        Some(Unsupported(msg)) =>
          [copy_def(d, ExternInterface(id, tparams, [Unsupported(msg)]), ctx)]
        _ =>
          [
            copy_def(
              d,
              ExternInterface(id, tparams, [unsupported_error(bodies, ctx)]),
              ctx,
            ),
          ]
      }
    ExternInclude(flag, _path, _contents) =>
      if flag.matches_any(supported_flags(ctx)) {
        match flag {
          Default =>
            ctx.warning(
              d.span,
              "Found extern include without feature flag. It is likely that this will fail in other backends, please annotate it with a feature flag (Supported in current backend: \{supported_flags(ctx).join(", ")})",
            )
          _ => ()
        }
        [d]
      } else {
        []
      }
    NamespaceDef(id, defs) => {
      let inner : Array[Def] = []
      for sub in defs {
        inner.append(resolve_extern_def(sub, ctx))
      }
      [copy_def(d, NamespaceDef(id, inner), ctx)]
    }
    _ => [d]
  }
}

///|
fn copy_def(from : Def, kind : DefKind, ctx : Context) -> Def {
  let to = mk_def(from.span, from.info, kind)
  ctx.copy_annotations(from.uid, to.uid)
  to
}

///|
fn warn_default_flag(flag : FeatureFlag, id : IdDef, ctx : Context) -> Unit {
  match flag {
    Default =>
      ctx.warning(
        id.span,
        "Extern definition \{id.name} contains extern string without feature flag. This will likely not work in other backends, please annotate it with a feature flag (Supported by the current backend: \{supported_flags(ctx).join(", ")})",
      )
    _ => ()
  }
}
