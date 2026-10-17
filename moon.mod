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
//   implicit_impl_as_method    `impl Eq/Show/Debug` methods are implicitly
//                              promoted to regular methods; the 20 sites are
//                              `pub impl`s and `derive`s on public types.
//                              Writing the `pub extend` the checker asks for
//                              would put those methods into the public
//                              interface (.mbti) although nothing here calls
//                              them as methods.

warnings = "-implicit_impl_as_method"

import {
  "moonbitlang/x@0.5.5",
}
