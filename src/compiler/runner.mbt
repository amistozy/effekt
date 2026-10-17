// Generating and running the "executable" script for a compiled module.
//
// Mirrors `effekt/Runner.scala`'s JSRunner: the generated `.js` file only
// exports `main`; a second tiny script requires it and calls `main()`.
//
// `run_node` and `eprintln` live in `node.mbt`, next to the Node.js externs
// they need.

///|
/// The path of the runner script for the given output file.
pub fn runner_path(output : String) -> String {
  if output.has_suffix(".js") {
    "\{output[0:output.length() - 3].to_owned()}__main.js"
  } else {
    "\{output}__main.js"
  }
}

///|
/// The contents of the runner script: `require('./<module>').main()`.
///
/// The generated module is written verbatim to the output path (normally with
/// a `.js` extension, but `-o` accepts anything), so the runner requires
/// exactly that file name.
pub fn runner_contents(output : String) -> String {
  let normalized = normalize_separators(output)
  let segments = normalized.split("/").map(s => s.to_owned()).collect()
  let base = if segments.length() == 0 {
    normalized
  } else {
    segments[segments.length() - 1]
  }
  "require(\"./\{base}\").main()\n"
}
