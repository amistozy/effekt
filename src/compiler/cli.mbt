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
  mut show_cps : Bool
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
    show_cps: false,
    show_js: false,
    run: false,
  }
}

///|
pub fn usage() -> String {
  let usage_text =
    #|effekt - the Effekt language compiler (MoonBit implementation)
    #|
    #|Usage: effekt [options] <input.effekt>
    #|
    #|Options:
    #|  -o, --output <file>   Write the generated JavaScript to <file>
    #|                        (default: alongside the input, with .js extension)
    #|  -I, --include <dir>   Add <dir> to the module search path (repeatable)
    #|  --lib <dir>           Directory containing the Effekt standard library
    #|                        (default: ./libraries)
    #|  --show-core           Print the core IR instead of compiling
    #|  --show-cps            Print the contified CPS IR instead of compiling
    #|  --show-js             Print the generated JavaScript to stdout
    #|      --run             Run the program with node after compiling
    #|  -h, --help            Show this message
    #|
  usage_text
}

///|
/// Parses command line arguments. Diagnostics about malformed arguments are
/// returned as strings so that the caller can decide how to report them.
pub fn parse_args(args : Array[String]) -> (Options, Array[String]) {
  let opts = Options::default()
  let errors : Array[String] = []
  let mut i = 0
  while i < args.length() {
    let arg = args[i]
    match arg {
      "-h" | "--help" => opts.show_help = true
      "-o" | "--output" =>
        if i + 1 < args.length() {
          opts.output = Some(args[i + 1])
          i = i + 1
        } else {
          errors.push("Missing argument for \{arg}")
        }
      "-I" | "--include" =>
        if i + 1 < args.length() {
          opts.include_paths.push(args[i + 1])
          i = i + 1
        } else {
          errors.push("Missing argument for \{arg}")
        }
      "--lib" =>
        if i + 1 < args.length() {
          opts.lib_path = args[i + 1]
          i = i + 1
        } else {
          errors.push("Missing argument for \{arg}")
        }
      "--show-core" => opts.show_core = true
      "--show-cps" => opts.show_cps = true
      "--show-js" => opts.show_js = true
      "--run" => opts.run = true
      _ =>
        if arg.has_prefix("-") && arg.length() > 1 {
          errors.push("Unknown option \{arg}")
        } else if opts.input == "" {
          opts.input = arg
        } else {
          errors.push("Unexpected argument \{arg}")
        }
    }
    i = i + 1
  }
  (opts, errors)
}
