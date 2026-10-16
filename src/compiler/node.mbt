// What the driver needs from the process it runs in.
//
// The command line comes from `moonbitlang/core/env`; the three `extern "js"`
// functions below are the whole of the hand-written JavaScript left in the
// project, because the standard library does not offer them:
//
//   - the process *exit code*: `moonbitlang/x/sys`'s `exit` calls
//     `process.exit()`, which can truncate buffered output when stdout is a
//     pipe — exactly how the CLI is usually invoked,
//   - stderr: the standard library only prints to stdout,
//   - running a generated script with `node` (`child_process`).

///|
/// Sets the process exit code.
///
/// Deliberately does *not* call `process.exit()`: see the note above.
extern "js" fn node_set_exit_code(code : Int32) -> Unit =
  #| (code) => { process.exitCode = code; }

///|
extern "js" fn node_eprintln(message : String) -> Unit =
  #| (message) => { process.stderr.write(message + "\n"); }

///|
extern "js" fn node_run(path : String) -> Int32 =
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

///|
/// The arguments the compiler was invoked with, without the interpreter and
/// the script itself: on JavaScript `@env.args()` is the raw `process.argv`.
pub fn command_line_args() -> Array[String] {
  let args = @env.args()
  if args.length() <= 2 {
    []
  } else {
    args[2:].to_owned()
  }
}

///|
/// Sets the exit code the CLI finishes with.
pub fn exit(code : Int32) -> Unit {
  node_set_exit_code(code)
}

///|
/// Writes a message to stderr, keeping stdout for the program's own output
/// when `--run` is used (and for the generated JavaScript with `--show-js`).
pub fn eprintln(message : String) -> Unit {
  node_eprintln(message)
}

///|
/// Executes a generated script with `node`, returning its exit code.
pub fn run_node(path : String) -> Int32 {
  node_run(path)
}
