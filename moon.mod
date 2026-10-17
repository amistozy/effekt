// Effekt: a MoonBit reimplementation of the Effekt language compiler.
//
// Upstream Effekt is implemented in Scala (see .reference/effekt for the
// original sources). This port targets the JavaScript backend only.
name = "amistozy/effekt"

version = "0.1.0"

readme = "README.mbt.md"

repository = "https://github.com/amistozy/effekt"

license = "Apache-2.0"

keywords = [ "effekt", "compiler", "effects", "javascript" ]

preferred_target = "js"

description = "An implementation of the Effekt language in MoonBit, compiling to JavaScript."

// Warnings suppressed for every package (a package-level `warnings =` extends
// this default). Each entry hides a class of diagnostics this port produces on
// purpose; everything else is expected to be clean, and `moon check -d`
// (warnings as errors) is part of the pre-commit gate.
//
//   reserved_keyword           `module` is used as a field/parameter name in
//                              the AST, mirroring upstream's `Module` record
//                              (~480 sites).
//   unused_value               definitions ported for fidelity to the Scala
//   unused_type_declaration    sources that the JavaScript backend does not
//   unused_error_type          consume, plus symbols kept for unported backends.
//   implicit_impl_as_method    `impl Eq/Debug/Show` methods are implicitly
//                              promoted to methods; the promotion is triggered
//                              even by `derive(Eq, Debug)` and nothing here
//                              calls the promoted methods, so declaring a
//                              `pub extend` for each would add API for nothing.

warnings = "-reserved_keyword-unused_value-unused_type_declaration-unused_error_type-implicit_impl_as_method"

import {
  "moonbitlang/x@0.5.5",
}
