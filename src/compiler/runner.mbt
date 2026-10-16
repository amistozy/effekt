// Generating and running the "executable" script for a compiled module.
//
// Mirrors `effekt/Runner.scala`'s JSRunner: the generated `.js` file only
// exports `main`; a second tiny script requires it and calls `main()`.

///|
/// The path of the runner script for the given output file.
pub fn runner_path(output : String) -> String {
  if output.has_suffix(".js") {
    output[0:output.length() - 3].to_owned() + "__main.js"
  } else {
    output + "__main.js"
  }
}

///|
/// The contents of the runner script: `require('./<module>.js').main()`.
pub fn runner_contents(output : String) -> String {
  let normalized = normalize_separators(output)
  let segments = normalized.split("/").map(s => s.to_owned()).collect()
  let base = if segments.length() == 0 {
    normalized
  } else {
    segments[segments.length() - 1]
  }
  let module_file = if base.has_suffix(".js") {
    base[0:base.length() - 3].to_owned()
  } else {
    base
  }
  "require(\"./" + module_file + ".js\").main()\n"
}

///|
/// Executes a generated script with `node`, returning its exit code.
pub fn run_node(path : String) -> Int32 {
  js_run_node(path)
}

///|
/// Writes a progress message to stderr, keeping stdout clean for the program's
/// own output when `--run` is used.
pub fn info(message : String) -> Unit {
  js_eprintln(message)
}

///|
extern "js" fn js_eprintln(message : String) -> Unit =
  #| (message) => { if (typeof process !== "undefined") process.stderr.write(message + "\n"); }

///|
extern "js" fn js_run_node(path : String) -> Int32 =
  #| (path) => {
  #|   const cp = require("node:child_process");
  #|   try {
  #|     cp.execFileSync(process.execPath, [path], { stdio: "inherit" });
  #|     return 0;
  #|   } catch (e) {
  #|     if (typeof e.status === "number") return e.status;
  #|     console.error(String(e.message || e));
  #|     return 1;
  #|   }
  #| }
