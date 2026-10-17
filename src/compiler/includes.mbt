// Resolving `extern include` directives.
//
// Upstream performs this in the `Namer` (which has access to the module DB).
// Here the namer is free of file IO, so the driver walks the parsed tree and
// fills in the contents of every `extern include` before name resolution runs.

///|
/// Reads the contents of every `extern include` in `tree`, resolving the path
/// relative to `source`'s file.
pub fn resolve_includes(
  tree : ModuleDecl,
  source : Source,
  ctx : Context,
) -> ModuleDecl {
  { ..tree, defs: tree.defs.map(d => resolve_includes_def(d, source, ctx)), }
}

///|
fn resolve_includes_def(d : Def, source : Source, ctx : Context) -> Def {
  let kind = match d.kind {
    @source.ExternInclude(flag, path, contents) =>
      match contents {
        Some(_) => d.kind
        None =>
          // Only load the include when it is needed by the current backend
          // (upstream `Namer`: `if (ff matches supportedFeatureFlags)`), so that
          // e.g. a Chez-only include does not have to exist for the JS backend.
          if !flag.matches_any(@source.supported_flags(ctx)) {
            d.kind
          } else {
            let base = dirname(source.name)
            let full = join_path(base, path)
            let loaded = read_file(full)
            if loaded is None {
              ctx.error(
                d.span,
                "Cannot find extern include '\{path}' (looked at \{full}).",
              )
            }
            @source.ExternInclude(flag, path, loaded)
          }
      }
    @source.NamespaceDef(id, defs) =>
      @source.NamespaceDef(
        id,
        defs.map(sub => resolve_includes_def(sub, source, ctx)),
      )
    _ => d.kind
  }
  { ..d, kind, }
}
