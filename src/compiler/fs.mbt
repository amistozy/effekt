// File-system access for the driver.
//
// The compiler itself never touches the file system: it receives `Source`
// values. Loading them (and writing the output) is the driver's job, and this
// is the only place that talks to Node.js.

///|
extern "js" fn js_read_file(path : String) -> String =
  #| (path) => {
  #|   const fs = typeof require !== "undefined" ? require("node:fs") : null;
  #|   if (fs === null) return "";
  #|   try { return fs.readFileSync(path, "utf8"); } catch (e) { return ""; }
  #| }

///|
extern "js" fn js_file_exists(path : String) -> Bool =
  #| (path) => {
  #|   const fs = typeof require !== "undefined" ? require("node:fs") : null;
  #|   if (fs === null) return false;
  #|   try { return fs.statSync(path).isFile(); } catch (e) { return false; }
  #| }

///|
extern "js" fn js_write_file(path : String, contents : String) -> Unit =
  #| (path, contents) => {
  #|   const fs = require("node:fs");
  #|   const p = require("node:path");
  #|   fs.mkdirSync(p.dirname(path), { recursive: true });
  #|   fs.writeFileSync(path, contents, "utf8");
  #| }

///|
extern "js" fn js_argv() -> Array[String] =
  #| () => (typeof process !== "undefined" ? process.argv.slice(2) : [])

///|
/// Sets the process exit code.
///
/// Deliberately does *not* call `process.exit()`: that can truncate buffered
/// output when stdout is a pipe (which is exactly how the CLI is usually
/// invoked).
extern "js" fn js_exit(code : Int32) -> Unit =
  #| (code) => { if (typeof process !== "undefined") process.exitCode = code; }

///|
extern "js" fn js_dirname(path : String) -> String =
  #| (path) => {
  #|   const p = require("node:path");
  #|   return p.dirname(path);
  #| }

///|
extern "js" fn js_join(a : String, b : String) -> String =
  #| (a, b) => {
  #|   const p = require("node:path");
  #|   return p.join(a, b);
  #| }

///|
extern "js" fn js_resolve(path : String) -> String =
  #| (path) => {
  #|   const p = require("node:path");
  #|   return p.resolve(path);
  #| }

///|
/// Reads a file, returning `None` when it does not exist.
pub fn read_file(path : String) -> String? {
  if js_file_exists(path) {
    Some(js_read_file(path))
  } else {
    None
  }
}

///|
pub fn file_exists(path : String) -> Bool {
  js_file_exists(path)
}

///|
pub fn write_file(path : String, contents : String) -> Unit {
  js_write_file(path, contents)
}

///|
pub fn command_line_args() -> Array[String] {
  js_argv()
}

///|
pub fn exit(code : Int32) -> Unit {
  js_exit(code)
}

///|
pub fn dirname(path : String) -> String {
  js_dirname(path)
}

///|
pub fn join_path(a : String, b : String) -> String {
  js_join(a, b)
}

///|
pub fn resolve_path(path : String) -> String {
  js_resolve(path)
}
