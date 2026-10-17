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
  if opts.show_help || (args.length() == 0 && !opts.show_help) {
    println(@compiler.usage())
    return 0
  }
  if arg_errors.length() > 0 {
    // argparse renders the message together with the usage and the option
    // list; report it on stderr like every other diagnostic.
    for e in arg_errors {
      @compiler.eprintln(e)
    }
    return 1
  }
  let pipeline : @compiler.Pipeline = {
    parse: @source.parse_module_decl,
    resolve: fn(tree, ctx, deps) raise @util.EffektError {
      @namer.resolve_module(tree, ctx, deps)
    },
    typecheck: fn(tree, ctx) raise @util.EffektError {
      // `unbox_inference` desugars uniform function calls (`x.f` becomes
      // `f(x)`) before typing, mirroring upstream's `ParserUntilTyper`.
      let desugared = @typer.unbox_inference(tree, ctx)
      @typer.typecheck(desugared, ctx)
      desugared
    },
    emit: @backend.emit,
  }
  let result = @compiler.compile_file(opts, pipeline, @source.Config::default())
  // Diagnostics go to stderr: stdout carries the program's own output when
  // `--run` is used (and the generated JavaScript with `--show-js`).
  let diagnostics = @compiler.render_messages(result.messages)
  if diagnostics != "" {
    @compiler.eprintln(diagnostics.trim_end().to_owned())
  }
  match result.output {
    None => if result.failed { 1 } else { 0 }
    Some(js) =>
      if opts.show_js {
        println(js)
        0
      } else {
        let out = match opts.output {
          Some(o) => o
          None => @compiler.default_output(opts.input)
        }
        match write_output(out, js) {
          Some(message) => {
            @compiler.eprintln(message)
            1
          }
          None => {
            @compiler.eprintln("Wrote \{out}")
            // The generated module only *exports* `main`; like the upstream
            // runner, we also wrote a tiny script that invokes it.
            let driver = @compiler.runner_path(out)
            if opts.run {
              @compiler.run_node(driver)
            } else {
              0
            }
          }
        }
      }
  }
}

///|
fn main {
  let args = @compiler.command_line_args()
  let code = run(args)
  @compiler.exit(code)
}
