// Names of symbols: either local or qualified by a module/namespace path.
//
// Mirrors `effekt/symbols/Name.scala`.

///|
pub(all) struct Name {
  path : Array[String]
  name : String
}

///|
pub fn Name::local_(name : String) -> Name {
  { path: [], name, }
}

///|
pub fn Name::qualified(prefix : Array[String], name : String) -> Name {
  { path: prefix, name, }
}

///|
pub fn Name::anon() -> Name {
  { path: [], name: "__anon", }
}

///|
pub fn Name::is_anon(self : Name) -> Bool {
  self.path.length() == 0 && self.name == "__anon"
}

///|
pub fn Name::rename(self : Name, f : (String) -> String) -> Name {
  { path: self.path, name: f(self.name), }
}

///|
pub fn Name::qualified_name(self : Name) -> String {
  if self.path.length() == 0 {
    self.name
  } else {
    "\{self.path.join("::")}::\{self.name}"
  }
}

///|
impl Eq for Name with fn equal(self, other) {
  self.name == other.name && self.path == other.path
}

///|
pub impl Show for Name with fn output(self, logger) {
  if self.path.length() == 0 {
    logger.write_string(self.name)
  } else {
    for segment in self.path {
      logger.write_string(segment)
      logger.write_string("::")
    }
    logger.write_string(self.name)
  }
}

///|
/// The name of a generated JavaScript identifier.
pub(all) struct JSName {
  name : String
}

///|
pub fn JSName::new(name : String) -> JSName {
  { name, }
}
