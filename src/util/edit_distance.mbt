// Levenshtein distance with a limit, mirroring `effekt/util/EditDistance.scala`.
//
// Used for "Did you mean ...?" suggestions: only *close* names are interesting,
// so the distance is only computed while it can still stay below `limit`.

///|
/// The lower-case ASCII code of a character, so that names can be compared
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
/// The edit distance between two already stripped strings, where swapping two
/// adjacent characters counts as one edit (upstream `levenshtein`: `Bolo` is one
/// edit away from `Bool`).
fn levenshtein(s1 : ArrayView[Char], s2 : ArrayView[Char]) -> Int32 {
  let n = s1.length()
  let m = s2.length()
  let d : Array[Int32] = Array::make((n + 1) * (m + 1), 0)
  let at = (i : Int32, j : Int32) => i * (m + 1) + j
  for i in 0..<=n {
    d[at(i, 0)] = i
  }
  for j in 0..<=m {
    d[at(0, j)] = j
  }
  for i in 1..<=n {
    for j in 1..<=m {
      let delete = d[at(i - 1, j)] + 1
      let insert = d[at(i, j - 1)] + 1
      let cost = if s1[i - 1] == s2[j - 1] { 0 } else { 1 }
      let substitute = d[at(i - 1, j - 1)] + cost
      let mut best = delete.min(insert).min(substitute)
      if i > 1 && j > 1 && s1[i - 1] == s2[j - 2] && s1[i - 2] == s2[j - 1] {
        best = best.min(d[at(i - 2, j - 2)] + 1)
      }
      d[at(i, j)] = best
    }
  }
  d[at(n, m)]
}

///|
/// The edit distance between `a` and `b`, or `None` when it exceeds `limit`.
///
/// The common prefix and suffix are stripped first (like upstream), which makes
/// the dynamic program tiny for the typos that actually occur in practice.
fn edit_distance(a : String, b : String, limit : Int32) -> Int32? {
  let left = a.to_array()
  let right = b.to_array()
  let n = left.length()
  let m = right.length()
  guard n != 0 else { return Some(m) }
  guard m != 0 else { return Some(n) }
  guard (n - m).abs() <= limit else { return None }
  // Strip the common prefix, then the common suffix of what is left.
  let mut prefix = 0
  while prefix < n && prefix < m && left[prefix] == right[prefix] {
    prefix += 1
  }
  let mut suffix = 0
  while suffix < n - prefix &&
        suffix < m - prefix &&
        left[n - 1 - suffix] == right[m - 1 - suffix] {
    suffix += 1
  }
  let s1 = left[prefix:n - suffix]
  let s2 = right[prefix:m - suffix]
  guard !s1.is_empty() else { return Some(s2.length()) }
  guard !s2.is_empty() else { return Some(s1.length()) }
  let distance = levenshtein(s1, s2)
  if distance <= limit {
    Some(distance)
  } else {
    None
  }
}

///|
/// Are the two names equal when ignoring ASCII case?
fn equal_ignoring_case(a : String, b : String) -> Bool {
  let left = a.to_array()
  let right = b.to_array()
  guard left.length() == right.length() else { return false }
  for (l, r) in left.zip(right) {
    guard lower_code(l) == lower_code(r) else { return false }
  }
  true
}

///|
/// The candidates within the edit limit of a name, grouped by how close they
/// are: equal up to case comes first (upstream treats it as distance `-1`), then
/// fewer edits, then an earlier group of candidates. Mirrors
/// `CloseMatches` in `effekt/util/EditDistance.scala`.
///
/// The Scala original is a `LazyList` so that `filter` and `closest` only do the
/// work they need; here the groups are computed eagerly, which is fine for the
/// few hundred names that are in scope at any point.
pub(all) struct CloseMatches[A] {
  /// The groups, closest first. A group holds the candidates of one
  /// `(distance, preference)` rank, in the order the scopes provided them.
  groups : Array[Array[A]]
}

///|
/// The closest candidates, or none when no candidate is within the limit.
pub fn[A] CloseMatches::closest(self : CloseMatches[A]) -> Array[A] {
  for group in self.groups {
    guard group.is_empty() else { return group }
  }
  []
}

///|
/// The same matches, keeping only the candidates that satisfy `p`. A group that
/// ends up empty is skipped by `closest`, so the next closest one wins —
/// `didYouMeanMethod` relies on that: a close name whose candidate does not
/// accept the call must not hide a slightly farther one that does.
pub fn[A] CloseMatches::filter(
  self : CloseMatches[A],
  p : (A) -> Bool,
) -> CloseMatches[A] {
  { groups: self.groups.map(group => group.filter(p)), }
}

///|
/// The candidates within the edit limit of `name` (`CloseMatches.apply`).
/// `groups` are the candidate groups, the preferred group first (for a scope
/// chain: nearest scope first).
pub fn[A] close_matches(
  name : String,
  groups : ArrayView[Array[A]],
  name_of : (A) -> String,
) -> CloseMatches[A] {
  let limit = (name.length().max(3) / 3).to_int()
  // The ranks in the order they are found; kept sorted by `(distance,
  // preference)` so that the group list is closest-first.
  let ranks : Array[(Int32, Int32)] = []
  let buckets : Array[Array[A]] = []
  for group_index, group in groups {
    for candidate in group {
      let distance = if equal_ignoring_case(name_of(candidate), name) {
        // equal up to case is closer than any edit
        Some(-1)
      } else {
        edit_distance(name, name_of(candidate), limit)
      }
      guard distance is Some(d) else { continue }
      let rank = (d, group_index.to_int())
      let mut slot = -1
      for i, existing in ranks {
        if existing == rank {
          slot = i
          break
        }
        if rank.0 < existing.0 || (rank.0 == existing.0 && rank.1 < existing.1) {
          ranks.insert(i, rank)
          buckets.insert(i, [])
          slot = i
          break
        }
      }
      if slot == -1 {
        slot = ranks.length()
        ranks.push(rank)
        buckets.push([])
      }
      // matches at the same rank are distinct by name
      let bucket = buckets[slot]
      if !bucket.any(other => name_of(other) == name_of(candidate)) {
        bucket.push(candidate)
      }
    }
  }
  { groups: buckets, }
}

///|
/// `a`, `a and b`, `a, b and c` for the conjunction `and` (upstream
/// `messages.enumerated`).
pub fn enumerated(items : ArrayView[String], conjunction : String) -> String {
  guard !items.is_empty() else { return "" }
  guard items.length() != 1 else { return items[0] }
  let init = items[:items.length() - 1].join(", ")
  "\{init} \{conjunction} \{items[items.length() - 1]}"
}

///|
/// The "Did you mean ...?" hint for a list of names, at most three of them
/// (upstream `messages.suggestion`).
pub fn suggestion(names : ArrayView[String]) -> String? {
  guard !names.is_empty() else { return None }
  Some("Did you mean \{enumerated(names[:names.length().min(3)], "or")}?")
}

///|
/// The suggestion upstream's `Scope.didYouMean` makes for an unresolved name, if
/// any: a hard-coded heuristic first, then the closest of the candidates given
/// by the scopes (nearest scope first).
///
/// `candidates` are the names that are in scope, grouped by scope; `specific` is
/// the heuristic for names that are common in other languages.
pub fn did_you_mean(
  name : String,
  candidates : ArrayView[Array[String]],
  specific : (String) -> String?,
) -> String? {
  match specific(name) {
    Some(suggestion) => Some(suggestion)
    None => suggestion(close_matches(name, candidates, name => name).closest())
  }
}

///|
/// The hard-coded type-name suggestions (upstream `didYouMeanTypeHeuristic`).
/// Most of these are names from other languages.
pub fn did_you_mean_type(name : String) -> String? {
  match name {
    "Boolean" | "boolean" => suggestion(["Bool"])
    "Str" | "str" => suggestion(["String"])
    "Integer" | "Int32" | "Int64" | "I32" | "I64" | "i32" | "i64" =>
      suggestion(["Int"])
    "UInt32" | "UInt64" | "UInt" | "U32" | "U64" | "u32" | "u64" =>
      Some("Effekt only supports signed integers, did you mean Int?")
    "Int8" | "UInt8" | "I8" | "U8" | "i8" | "u8" =>
      Some("Did you mean Byte (8 bits) or Char (32 bits)?")
    "Float" | "float" | "F64" | "F32" | "f64" | "f32" =>
      Some("Effekt only supports 64bit floating numbers, did you mean Double?")
    "Maybe" | "maybe" => suggestion(["Option"])
    "Void" | "void" => suggestion(["Unit"])
    _ => None
  }
}
