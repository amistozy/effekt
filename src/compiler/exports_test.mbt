// Tests for the contract between the namer and the driver.
//
// `ResolvedModule.module.exports` must contain the toplevel terms *and* types
// of a module (so that importers can open it), and the driver must hand the
// backend every module of the dependency closure, dependencies first.

///|
/// Compiles a file far enough to inspect what the backend would receive.
fn closure_of(input : String, messages : Array[@util.Message]) -> Array[String] {
  let opts : @compiler.Options = {
    input,
    output: None,
    include_paths: [],
    lib_path: "libraries",
    show_help: false,
    show_core: false,
    show_cps: false,
    show_js: false,
    run: false,
  }
  let paths : Ref[Array[String]] = Ref([])
  let pipeline : @compiler.Pipeline = {
    parse: @source.parse_module_decl,
    resolve: fn(tree, ctx, deps) raise @util.EffektError {
      @namer.resolve_module(tree, ctx, deps)
    },
    typecheck: fn(tree, ctx) raise @util.EffektError {
      let desugared = @typer.unbox_inference(tree, ctx)
      @typer.typecheck(desugared, ctx)
      desugared
    },
    emit: fn(modules, _ctx) raise @util.EffektError {
      let seen : Array[String] = []
      for m in modules {
        seen.push(m.module.path)
      }
      paths.val = seen
      ""
    },
  }
  let result = @compiler.compile_file(opts, pipeline, @source.Config::default()) catch {
    _ => {
      messages.push(@util.Message::info("the driver aborted"))
      return []
    }
  }
  for m in result.messages {
    messages.push(m)
  }
  paths.val
}

///|
test "the exception module exports its interface as a type" {
  let ctx = @source.Context::new(@source.Config::default())
  let opts : @compiler.Options = {
    input: "libraries/common/exception.effekt",
    output: None,
    include_paths: [],
    lib_path: "libraries",
    show_help: false,
    show_core: false,
    show_cps: false,
    show_js: false,
    run: false,
  }
  let loader = @compiler.Loader::new(@compiler.search_paths(opts.input, opts))
  let prelude_tree = loader.load_tree("effekt", ctx, @source.parse_module_decl)
  let prelude = @namer.resolve_module(prelude_tree, ctx, Map([]))
  let deps : Map[String, @namer.ResolvedModule] = { "effekt": prelude }
  let tree = loader.load_tree("exception", ctx, @source.parse_module_decl)
  let resolved = @namer.resolve_module(tree, ctx, deps)
  let type_names : Array[String] = []
  for name, _ in resolved.module.exports.types {
    type_names.push(name)
  }
  let term_names : Array[String] = []
  for name, _ in resolved.module.exports.terms {
    term_names.push(name)
  }
  assert_true(type_names.any(n => n == "Exception"))
  assert_true(term_names.any(n => n == "raise"))
}

///|
test "the driver hands the dependency closure to the backend" {
  let messages : Array[@util.Message] = []
  let paths = closure_of("examples/import_handler.effekt", messages)
  for m in messages {
    println(m.render())
  }
  assert_eq(messages.filter(m => m.severity == @util.Error).length(), 0)
  assert_true(paths.any(p => p == "effekt"))
  assert_true(paths.any(p => p == "exception"))
  assert_eq(paths[paths.length() - 1], "import_handler")
}
