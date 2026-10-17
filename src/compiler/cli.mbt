// Command-line interface helpers and diagnostics rendering.

///|
/// Options parsed from the command line.
pub(all) struct Options {
  mut input : String
  mut output : String?
  /// Directories searched for `import`ed Effekt modules.
  mut include_paths : Array[String]
  /// Directory containing the Effekt standard library (the prelude is found in
  /// `<lib>/common`).
  mut lib_path : String
  mut show_help : Bool
  mut show_core : Bool
  mut show_js : Bool
  mut run : Bool
}

///|
pub fn Options::default() -> Options {
  {
    input: "",
    output: None,
    include_paths: [],
    lib_path: "libraries",
    show_help: false,
    show_core: false,
    show_js: false,
    run: false,
  }
}

///|
/// The command line of `effekt`, declared for `moonbitlang/core/argparse`.
///
/// The built-in help flag is turned off and `-h`/`--help` is declared as an
/// ordinary flag instead, so that the help text stays under our control and
/// goes through the same stdout path as everything else: argparse's own help
/// action prints and then calls `process.exit`, which can truncate buffered
/// output (see `compiler.exit`).
fn command() -> @argparse.Command {
  @argparse.Command(
    "effekt",
    about="The Effekt language compiler (MoonBit implementation)",
    disable_help_flag=true,
    options=[
      @argparse.OptionArg(
        "output",
        short='o',
        about="Write the generated JavaScript to <file> (default: alongside the input, with .js extension)",
      ),
      @argparse.OptionArg(
        "include",
        short='I',
        action=Append,
        about="Add <dir> to the module search path (repeatable)",
      ),
      @argparse.OptionArg(
        "lib",
        default_values=["libraries"],
        about="Directory containing the Effekt standard library (default: ./libraries)",
      ),
    ],
    flags=[
      @argparse.FlagArg("help", short='h', about="Show this message"),
      @argparse.FlagArg(
        "show-core",
        about="Print the core IR instead of compiling",
      ),
      @argparse.FlagArg(
        "show-js",
        about="Print the generated JavaScript to stdout",
      ),
      @argparse.FlagArg(
        "run",
        about="Run the program with node after compiling",
      ),
    ],
    positionals=[
      @argparse.PositionArg(
        "input",
        about="The Effekt source file to compile",
        num_args=@argparse.ValueRange(lower=0, upper=1),
      ),
    ],
  )
}

///|
/// The help text, rendered by argparse from [[command]].
pub fn usage() -> String {
  // `render_help` ends with a newline; the caller prints it with `println`.
  command().render_help().trim_end().to_owned()
}

///|
fn flag(matches : @argparse.Matches, name : String) -> Bool {
  match matches.flags.get(name) {
    Some(value) => value
    None => false
  }
}

///|
/// The first value of an option, if it was given.
fn option(matches : @argparse.Matches, name : String) -> String? {
  match matches.values.get(name) {
    Some(values) => if values.length() > 0 { Some(values[0]) } else { None }
    None => None
  }
}

///|
/// All values of an option (used by the repeatable `-I`/`--include`).
fn option_values(matches : @argparse.Matches, name : String) -> Array[String] {
  match matches.values.get(name) {
    Some(values) => values
    None => []
  }
}

///|
/// Parses command line arguments. Diagnostics about malformed arguments are
/// returned as strings so that the caller can decide how to report them;
/// argparse renders them with the full usage text already.
pub fn parse_args(args : Array[String]) -> (Options, Array[String]) {
  let opts = Options::default()
  // Everything after the program name is handed to argparse; `env` is empty so
  // that the environment cannot silently provide values.
  let matches = command().parse(argv=args[:], env=Map([])) catch {
    err => return (opts, [err.to_string()])
  }
  opts.show_help = flag(matches, "help")
  opts.show_core = flag(matches, "show-core")
  opts.show_js = flag(matches, "show-js")
  opts.run = flag(matches, "run")
  opts.output = option(matches, "output")
  opts.include_paths = option_values(matches, "include")
  match option(matches, "lib") {
    Some(path) => opts.lib_path = path
    None => ()
  }
  match option(matches, "input") {
    Some(input) => opts.input = input
    None => ()
  }
  (opts, [])
}
