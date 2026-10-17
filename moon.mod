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
//   reserved_keyword           The port keeps Effekt's own vocabulary for AST
//                              fields, constructors and binders (`module`,
//                              `local`, `ref`, `constructor`, `method`,
//                              `resume`, `alias`, `use`, `namespace`, `final`,
//                              `member`, `virtual`; 481 sites) so that a source
//                              file can still be read next to `.reference`.
//                              Renaming would break that mapping; when MoonBit
//                              actually reserves the words the rename is
//                              mechanical, but it has to happen at once.
//   unused_error_type          22 signatures still carry the upstream Scala
//                              `raise EffektError` although the port reports
//                              through `messages` instead. Dropping it is a
//                              real API change (every `?`/`try` at a call site
//                              has to go too), tracked as its own task.
//   implicit_impl_as_method    `impl Eq/Show/Debug` methods are implicitly
//                              promoted to regular methods; the 20 sites are
//                              `pub impl`s and `derive`s on public types.
//                              Writing the `pub extend` the checker asks for
//                              would put those methods into the public
//                              interface (.mbti) although nothing here calls
//                              them as methods.

warnings = "-reserved_keyword-unused_error_type-implicit_impl_as_method"

import {
  "moonbitlang/x@0.5.5",
}
