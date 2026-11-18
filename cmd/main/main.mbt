// The `effekt` command line compiler.
//
// Usage: effekt [options] <input.effekt>

///|
/// Writes the generated module and the runner script next to it, returning an
/// error message when either of them could not be written.
fn write_output(out : String, js : String) -> String? {
  match @compiler.write_file(out, js) {
    Some(message) => Some(message)
    None =>
      @compiler.write_file(
        @compiler.runner_path(out),
        @compiler.runner_contents(out),
      )
  }
}

///|
fn run(args : Array[String]) -> Int32 {
  let (opts, arg_errors) = @compiler.parse_args(args)
  // No argument at all is a request for the usage, like `--help`.
  if opts.show_help || args.is_empty() {
    println(@compiler.usage())
    return 0
  }
  if !arg_errors.is_empty() {
    // argparse renders the message together with the usage and the option
    // list; report it on stderr like every other diagnostic.
    for e in arg_errors {
      @compiler.eprintln(e)
    }
    return 1
  }
  let mut core_dump : String? = None
  let pipeline : @compiler.Pipeline = {
    parse: @source.parse_module_decl,
    resolve: (tree, ctx, deps) => @namer.resolve_module(tree, ctx, deps),
    typecheck: (tree, ctx) => {
      // `typecheck` runs `unbox_inference` itself and replaces the module's
      // definitions with the desugared ones in place (upstream's
      // `ParserUntilTyper` pipeline), so the tree handed back to the later
      // phases is the rewritten one. Running it here as well would report every
      // unbox diagnostic twice.
      @typer.typecheck(tree, ctx)
      tree
    },
    emit: (trees, ctx) => {
      if opts.show_core {
        // `--show-core` is a dump mode: the middle-end runs, but no code is
        // generated and no file is written.
        core_dump = Some(@backend.show_core(trees, ctx))
        ""
      } else {
        @backend.emit(trees, ctx)
      }
    },
  }
  let result = @compiler.compile_file(opts, pipeline, @source.Config::default())
  // Diagnostics go to stderr: stdout carries the program's own output when
  // `--run` is used (and the generated JavaScript with `--show-js`).
  let diagnostics = @compiler.render_messages(result.messages)
  if diagnostics != "" {
    @compiler.eprintln(diagnostics.trim_end().to_owned())
  }
  if opts.show_core {
    if core_dump is Some(ir) {
      println(ir)
    }
    return if result.failed { 1 } else { 0 }
  }
  guard result.output is Some(js) else {
    return if result.failed { 1 } else { 0 }
  }
  if opts.show_js {
    println(js)
    return 0
  }
  let out = opts.output.unwrap_or_else(() => {
    @compiler.default_output(opts.input)
  })
  if write_output(out, js) is Some(message) {
    @compiler.eprintln(message)
    return 1
  }
  @compiler.eprintln("Wrote \{out}")
  // The generated module only *exports* `main`; like the upstream runner, we
  // also wrote a tiny script that invokes it.
  if opts.run {
    @compiler.run_node(@compiler.runner_path(out))
  } else {
    0
  }
}

///|
fn main {
  let args = @compiler.command_line_args()
  let code = run(args)
  @compiler.exit(code)
}
