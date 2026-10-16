// File-system and path access for the driver.
//
// The compiler itself never touches the file system: it receives `Source`
// values. Loading them (and writing the output) is the driver's job, and this
// is the only place that talks to the host.
//
// It is built on `moonbitlang/x/fs` and `moonbitlang/x/path` instead of on
// hand-written JavaScript. `moonbitlang/x/path` implements `node:path`
// semantics and picks its Win32 or POSIX flavour at run time (`is_windows`),
// so the paths the driver computes are the same ones `require("node:path")`
// would produce on the host it runs on.

///|
/// Reads a file, returning `None` when there is no readable file at `path`.
pub fn read_file(path : String) -> String? {
  if file_exists(path) {
    Some(@fs.read_file_to_string(path)) catch {
      _ => None
    }
  } else {
    None
  }
}

///|
/// Is there a file (as opposed to a directory) at `path`?
pub fn file_exists(path : String) -> Bool {
  @fs.is_file(path) catch {
    _ => false
  }
}

///|
/// Writes `contents` to `path`, creating the parent directory if necessary.
///
/// Returns a message when the file could not be written; the caller reports it
/// and fails the compilation.
pub fn write_file(path : String, contents : String) -> String? {
  // Best effort: when the directory cannot be created, the write below fails
  // with a message that names the file, which is more useful than this one.
  @fs.create_dir(dirname(path)) catch {
    _ => ()
  }
  try {
    @fs.write_string_to_file(path, contents)
    None
  } catch {
    @fs.IOError(message) => Some("Cannot write \{path}: \{message}")
  }
}

///|
/// The directory part of `path`, following `node:path`'s `dirname`.
pub fn dirname(path : String) -> String {
  @path.Path(path).dirname().0
}

///|
/// Joins two path segments, following `node:path`'s `join`.
pub fn join_path(a : String, b : String) -> String {
  @path.Path(a).join(@path.Path(b)).0
}

///|
/// Makes `path` absolute, following `node:path`'s `resolve`.
pub fn resolve_path(path : String) -> String {
  @path.Path(path).resolve().0
}
