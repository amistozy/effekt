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

warnings = "-implicit_impl_as_method-redundant_modifier-unused_value-unused_constructor"

import {
  "moonbitlang/x@0.5.5",
}
