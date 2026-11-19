import Std.Data.HashMap

/-!
# Exported data as text

A native check (`Cert/Native.lean`) reads a subtree's data from one string instead of from
elaborated definitions. The string holds the exporter's Lean terms (`code/lean-export`) as entries
`@name term`; `Syn.entries` parses them into syntax trees, and `Cert/Decode.lean` decodes those
into the checkers' data types.

Neither step is trusted: a native check is sound for any data it accepts
(`Native.settled_of_check`), so a parse or decoding error can only make a check fail.

The syntax is the part of Lean's term syntax that the exporter writes: integer literals (`-n` only
where a term starts), names (`true`, `false`, `none`, references to entries such as `c0`),
constructors in dot notation with their arguments (`.split 3 lo hi`), `some a`, anonymous
constructors `⟨a, b⟩`, lists `[a, b]`, tuples `(a, b)` and parentheses.
-/

namespace Nieuwland.Cert

/-- A term as the exporter writes data. -/
inductive Syn where
  /-- An integer literal. -/
  | num (n : Int)
  /-- A name: `true`, `false`, `none`, or a reference to an entry. -/
  | name (s : String)
  /-- A constructor in dot notation with its arguments, `.c a b`. -/
  | dot (c : String) (args : Array Syn)
  /-- `some a`. -/
  | someOf (a : Syn)
  /-- An anonymous constructor `⟨a, b⟩`. -/
  | anon (xs : Array Syn)
  /-- A list `[a, b]`. -/
  | list (xs : Array Syn)
  /-- A tuple `(a, b)` of at least two components. -/
  | tuple (xs : Array Syn)
  deriving Inhabited

namespace Syn

/-! ### Bytes -/

/-- `⟨` (`last = 0xA8`) or `⟩` (`last = 0xA9`) at byte `i`: `E2 9F A8`, `E2 9F A9` in UTF-8. -/
private def angleAt (b : ByteArray) (i : Nat) (last : UInt8) : Bool :=
  i + 2 < b.size && b[i]! == 0xE2 && b[i + 1]! == 0x9F && b[i + 2]! == last

private def isSpace (c : UInt8) : Bool :=
  c == 32 || c == 10 || c == 13 || c == 9

private def isDigit (c : UInt8) : Bool :=
  48 ≤ c && c ≤ 57

private def isNameStart (c : UInt8) : Bool :=
  (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95

private def isNameChar (c : UInt8) : Bool :=
  isNameStart c || isDigit c || c == 46 || c == 39

/-- The first byte at or after `i` that is not white space. -/
private partial def skip (b : ByteArray) (i : Nat) : Nat :=
  if i < b.size && isSpace b[i]! then skip b (i + 1) else i

/-- The decimal digits from `i`, added to `acc`, and the byte after them. -/
private partial def digits (b : ByteArray) (i acc : Nat) : Nat × Nat :=
  if i < b.size && isDigit b[i]! then digits b (i + 1) (acc * 10 + (b[i]! - 48).toNat)
  else (acc, i)

/-- The name from `i` to the first byte `j` that cannot continue a name. -/
private partial def nameEnd (b : ByteArray) (j : Nat) : Nat :=
  if j < b.size && isNameChar b[j]! then nameEnd b (j + 1) else j

/-- The name between bytes `i` and `j`. -/
private def nameOf (b : ByteArray) (i j : Nat) : String :=
  String.fromUTF8! (b.extract i j)

/-- An atom starts at byte `i`: a literal, a name, a constructor or an opening bracket. -/
private def atomStart (b : ByteArray) (i : Nat) : Bool :=
  i < b.size &&
    (isDigit b[i]! || isNameStart b[i]! || b[i]! == 46 || b[i]! == 40 || b[i]! == 91 ||
      angleAt b i 0xA8)

/-! ### Terms -/

mutual

/-- A term from byte `i`, and the byte after it: a negative literal, `some a`, a constructor with
its arguments, or an atom. -/
partial def term (b : ByteArray) (i : Nat) : Option (Syn × Nat) :=
  let i := skip b i
  if i < b.size && b[i]! == 45 then
    let (n, j) := digits b (i + 1) 0
    if j == i + 1 then none else some (.num (-(n : Int)), j)
  else
    match atom b i with
    | some (.dot c #[], j) =>
      let (xs, k) := args b j #[]
      some (.dot c xs, k)
    | some (.name "some", j) =>
      match atom b (skip b j) with
      | some (a, k) => some (.someOf a, k)
      | none => none
    | r => r

/-- The atoms from byte `i` (the arguments of a constructor), added to `acc`. -/
partial def args (b : ByteArray) (i : Nat) (acc : Array Syn) : Array Syn × Nat :=
  let j := skip b i
  if atomStart b j then
    match atom b j with
    | some (a, k) => args b k (acc.push a)
    | none => (acc, j)
  else (acc, j)

/-- An atom at byte `i`: a natural literal, a name, a constructor without its arguments, or a
bracketed term or sequence. -/
partial def atom (b : ByteArray) (i : Nat) : Option (Syn × Nat) :=
  if i < b.size then
    let c := b[i]!
    if isDigit c then
      let (n, j) := digits b i 0
      some (.num n, j)
    else if isNameStart c then
      let j := nameEnd b i
      some (.name (nameOf b i j), j)
    else if c == 46 then
      let j := nameEnd b (i + 1)
      if j == i + 1 then none else some (.dot (nameOf b (i + 1) j) #[], j)
    else if c == 40 then
      match seq b (i + 1) 41 #[] with
      | some (xs, j) =>
        if xs.size == 1 then some (xs[0]!, j)
        else if xs.size ≥ 2 then some (.tuple xs, j) else none
      | none => none
    else if c == 91 then
      (seq b (i + 1) 93 #[]).map fun (xs, j) ↦ (.list xs, j)
    else if angleAt b i 0xA8 then
      (seq b (i + 3) 0 #[]).map fun (xs, j) ↦ (.anon xs, j)
    else none
  else none

/-- Terms separated by commas up to the closing byte `close` (`0`: up to `⟩`), added to `acc`,
and the byte after the closing one. -/
partial def seq (b : ByteArray) (i : Nat) (close : UInt8) (acc : Array Syn) :
    Option (Array Syn × Nat) :=
  let closes (j : Nat) : Option Nat :=
    if close == 0 then (if angleAt b j 0xA9 then some (j + 3) else none)
    else if j < b.size && b[j]! == close then some (j + 1) else none
  let i := skip b i
  match closes i with
  | some j => if acc.isEmpty then some (acc, j) else none
  | none =>
    match term b i with
    | some (t, j) =>
      let j := skip b j
      match closes j with
      | some k => some (acc.push t, k)
      | none =>
        if j < b.size && b[j]! == 44 then seq b (j + 1) close (acc.push t) else none
    | none => none

end

/-- The entries `@name term` of a text from byte `i`, added to `acc`. -/
partial def entriesFrom (b : ByteArray) (i : Nat) (acc : Array (String × Syn)) :
    Option (Array (String × Syn)) :=
  let i := skip b i
  if i ≥ b.size then some acc
  else if b[i]! == 64 then
    let j := nameEnd b (i + 1)
    match term b j with
    | some (t, k) => entriesFrom b k (acc.push (nameOf b (i + 1) j, t))
    | none => none
  else none

/-- The entries `@name term` of a text, by name. -/
def entries (text : String) : Option (Std.HashMap String Syn) :=
  (entriesFrom text.toUTF8 0 #[]).map fun es ↦ es.foldl (fun m (n, t) ↦ m.insert n t) {}

end Syn

end Nieuwland.Cert
