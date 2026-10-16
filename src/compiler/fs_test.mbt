// Tests for the driver's host layer: `fs.mbt` (files and paths) and
// `node.mbt` (the command line and the other process services).
//
// They use `_build/` for their scratch files, which is where the build output
// goes anyway and is not tracked by git.

///|
fn remove_dir_if_present(path : String) -> Unit {
  @fs.remove_dir(path) catch {
    _ => ()
  }
}

///|
test "write_file creates the parent directory and read_file reads it back" {
  let dir = "_build/tmp/fs_test"
  remove_dir_if_present(dir)
  let file = "\{dir}/nested/notes.txt"
  assert_eq(@compiler.write_file(file, "one\ntwo"), None)
  assert_true(@compiler.file_exists(file))
  assert_eq(@compiler.read_file(file), Some("one\ntwo"))
  // A directory exists, but it is not a file and has no contents.
  assert_false(@compiler.file_exists(dir))
  assert_eq(@compiler.read_file("\{dir}/missing.txt"), None)
  remove_dir_if_present(dir)
}

///|
test "write_file reports the path it could not write" {
  let dir = "_build/tmp/fs_test_report"
  remove_dir_if_present(dir)
  assert_eq(@compiler.write_file("\{dir}/sub/ok.txt", "x"), None)
  // Writing *onto a directory* fails, and the message names the path.
  match @compiler.write_file("\{dir}/sub", "x") {
    Some(message) => assert_true(message.has_prefix("Cannot write \{dir}/sub"))
    None => fail("expected write_file to report the failing path")
  }
  remove_dir_if_present(dir)
}

///|
test "the path helpers follow the host's path rules" {
  assert_eq(
    @compiler.normalize_separators(@compiler.join_path("a", "b")),
    "a/b",
  )
  assert_eq(
    @compiler.normalize_separators(@compiler.dirname("a/b/c.effekt")),
    "a/b",
  )
  // `resolve_path` is absolute, and agrees with joining onto the current
  // directory — which is what the module loader relies on.
  let cwd = @compiler.resolve_path(".")
  assert_eq(
    @compiler.resolve_path("libraries"),
    @compiler.join_path(cwd, "libraries"),
  )
  assert_eq(@compiler.dirname(@compiler.resolve_path("libraries")), cwd)
}
