// The `effekt` command line compiler.
//
// Usage: effekt [options] <input.effekt>

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
      @compiler.info(e)
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
  let result = @compiler.compile_file(opts, pipeline, @source.Config::default()) catch {
    _ => {
      println("internal compiler error")
      return 2
    }
  }
  // Diagnostics go to stderr: stdout carries the program's own output when
  // `--run` is used (and the generated JavaScript with `--show-js`).
  let diagnostics = @compiler.render_messages(result.messages)
  if diagnostics != "" {
    @compiler.info(diagnostics.trim_end().to_owned())
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
        @compiler.write_file(out, js)
        @compiler.info("Wrote \{out}")
        // The generated module only *exports* `main`; like the upstream
        // runner, we also write a tiny script that invokes it.
        let driver = @compiler.runner_path(out)
        @compiler.write_file(driver, @compiler.runner_contents(out))
        if opts.run {
          let code = @compiler.run_node(driver)
          return code
        }
        0
      }
  }
}

///|
fn main {
  let args = @compiler.command_line_args()
  let code = run(args)
  @compiler.exit(code)
}
