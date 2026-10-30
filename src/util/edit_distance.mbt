// Levenshtein distance with a limit, mirroring `effekt/util/EditDistance.scala`.
//
// Used for "Did you mean ...?" suggestions: only *close* names are interesting,
// so the distance is only computed while it can still stay below `limit`.

///|
/// The code units of a string. Names are compared character-wise, so the
/// conversions up front keep the dynamic program simple.
fn chars_of(s : String) -> Array[Char] {
  let out : Array[Char] = []
  for c in s {
    out.push(c)
  }
  out
}

///|
/// The lower-case ASCII code of a character, so that type names can be compared
/// case-insensitively (`Mytype` vs `MyType`) without a Unicode case table.
fn lower_code(c : Char) -> Int32 {
  let code = c.to_int()
  if code >= 65 && code <= 90 {
    code + 32
  } else {
    code
  }
}

///|
/// The edit distance between `a` and `b`, or `None` when it exceeds `limit`.
///
/// The common prefix and suffix are stripped first (like upstream), which makes
/// the dynamic program tiny for the typos that actually occur in practice.
pub fn edit_distance(a : String, b : String, limit : Int32) -> Int32? {
  let left = chars_of(a)
  let right = chars_of(b)
  let n = left.length()
  let m = right.length()
  if n == 0 {
    return if m <= limit { Some(m) } else { None }
  }
  if m == 0 {
    return if n <= limit { Some(n) } else { None }
  }
  if (n - m).abs() > limit {
    return None
  }
  // Strip the common prefix, then the common suffix of what is left.
  let mut prefix = 0
  while prefix < n && prefix < m && left[prefix] == right[prefix] {
    prefix = prefix + 1
  }
  let mut suffix = 0
  while suffix < n - prefix &&
        suffix < m - prefix &&
        left[n - 1 - suffix] == right[m - 1 - suffix] {
    suffix = suffix + 1
  }
  let s1 = left[prefix:n - suffix]
  let s2 = right[prefix:m - suffix]
  let ln = s1.length()
  let lm = s2.length()
  if ln == 0 {
    return if lm <= limit { Some(lm) } else { None }
  }
  if lm == 0 {
    return if ln <= limit { Some(ln) } else { None }
  }
  // `prev[j]` is the distance of `s1[0:i-1]` and `s2[0:j-1]`.
  let mut prev : Array[Int32] = Array::make(lm + 1, 0)
  let mut cur : Array[Int32] = Array::make(lm + 1, 0)
  for j = 0; j <= lm; j = j + 1 {
    prev[j] = j
  }
  for i = 1; i <= ln; i = i + 1 {
    cur[0] = i
    let mut row_min = cur[0]
    for j = 1; j <= lm; j = j + 1 {
      let cost = if s1[i - 1] == s2[j - 1] { 0 } else { 1 }
      let deletion = prev[j] + 1
      let insertion = cur[j - 1] + 1
      let substitution = prev[j - 1] + cost
      let mut best = deletion
      if insertion < best {
        best = insertion
      }
      if substitution < best {
        best = substitution
      }
      cur[j] = best
      if best < row_min {
        row_min = best
      }
    }
    if row_min > limit {
      return None
    }
    let tmp = prev
    prev = cur
    cur = tmp
  }
  let result = prev[lm]
  if result <= limit {
    Some(result)
  } else {
    None
  }
}

///|
/// Are the two names equal when ignoring ASCII case?
fn equal_ignoring_case(a : String, b : String) -> Bool {
  let left = chars_of(a)
  let right = chars_of(b)
  if left.length() != right.length() {
    return false
  }
  for i = 0; i < left.length(); i = i + 1 {
    if lower_code(left[i]) != lower_code(right[i]) {
      return false
    }
  }
  true
}

///|
/// The suggestion upstream's `Scope.didYouMean` makes for an unresolved type
/// name, if any.
///
/// `candidates` are the type names that are in scope; `specific` is the
/// hard-coded heuristic for names that are common in other languages.
pub fn did_you_mean(
  name : String,
  candidates : Array[String],
  specific : (String) -> String?,
) -> String? {
  match specific(name) {
    Some(suggestion) => Some(suggestion)
    None => {
      // Priority 2: an exact case-insensitive match.
      for candidate in candidates {
        if equal_ignoring_case(candidate, name) {
          return Some("Did you mean \{candidate}?")
        }
      }
      // Priority 3: the closest name within the edit-distance limit.
      let threshold = (name.length() + 2).max(3) / 3
      let mut best : (Int32, String)? = None
      for candidate in candidates {
        match edit_distance(name, candidate, threshold) {
          Some(d) =>
            match best {
              Some((best_d, _)) if best_d <= d => ()
              _ => best = Some((d, candidate))
            }
          None => ()
        }
      }
      match best {
        Some((_, c)) => Some("Did you mean \{c}?")
        None => None
      }
    }
  }
}

///|
/// The hard-coded type-name suggestions (upstream `didYouMeanTypeHeuristic`).
/// Most of these are names from other languages.
pub fn did_you_mean_type(name : String) -> String? {
  match name {
    "Boolean" | "boolean" => Some("Did you mean Bool?")
    "Str" | "str" => Some("Did you mean String?")
    "Integer" | "Int32" | "Int64" | "I32" | "I64" | "i32" | "i64" =>
      Some("Did you mean Int?")
    "UInt32" | "UInt64" | "UInt" | "U32" | "U64" | "u32" | "u64" =>
      Some("Effekt only supports signed integers, did you mean Int?")
    "Int8" | "UInt8" | "I8" | "U8" | "i8" | "u8" =>
      Some("Did you mean Byte (8 bits) or Char (32 bits)?")
    "Float" | "float" | "F64" | "F32" | "f64" | "f32" =>
      Some("Effekt only supports 64bit floating numbers, did you mean Double?")
    "Maybe" | "maybe" => Some("Did you mean Option?")
    "Void" | "void" => Some("Did you mean Unit?")
    _ => None
  }
}
