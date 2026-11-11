/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.FormatString
public import StrataPythonTest.Dyn.Sem.Library.FormatStringCases
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Library.FormatString
meta import StrataPythonTest.Dyn.Sem.Library.FormatStringCases

set_option autoImplicit false

/-!
# The format strings of `str.format`

`FormatStringCases.cases` holds CPython 3.12's reading of format strings: the pieces that
`_string.formatter_parser` gives, the parts that `_string.formatter_field_name_split` gives, and
the numbering of the fields that `str.format` uses. The functions must give the same.
-/

namespace StrataPython.Dyn.Sem.Library.FormatStringTest

open StrataPython.Dyn.Sem.Library.FormatString

/-- The pieces of `s`, written as the cases write CPython's; adjacent literal text is joined. -/
private def showPieces (s : String) : String :=
  let lines := (pieces s).foldl (fun (acc : Array String) p =>
    match p with
    | .literal t =>
      match acc.back? with
      | some l => if l.startsWith "L" then acc.pop.push (l ++ t) else acc.push ("L" ++ t)
      | none => acc.push ("L" ++ t)
    | .field f =>
      acc.push s!"F{f.name}|{(f.conversion.map toString).getD ""}|{f.spec}"
    | .error e => acc.push ("E" ++ e)) #[]
  "\n".intercalate lines.toList

/-- The parts of the field name `s`, written as the cases write CPython's. -/
private def showSplit (s : String) : String :=
  let (first, index, rest) := splitName s
  match index with
  | .error e => "E" ++ e
  | .ok index =>
    let head := match index with
      | some i => s!"I{i}"
      | none => "S" ++ first
    let accessors := rest.map fun
      | .ok (.attr n) => "A" ++ n
      | .ok (.index i) => s!"N{i}"
      | .ok (.key k) => "K" ++ k
      | .error e => "E" ++ e
    "\n".intercalate (head :: accessors)

/-- `s.format('a', 'b', 'c', x='X')` for a format string whose fields have no accessor, conversion
or spec: the numbering of `autoNumber`, with the lookups of `str.format`. -/
private def showNumber (s : String) : String :=
  let args := #["a", "b", "c"]
  let rec go : List Piece → AutoState → String → String
    | [], _, out => out
    | .literal t :: ps, st, out => go ps st (out ++ t)
    | .error e :: _, _, _ => "EValueError: " ++ e
    | .field f :: ps, st, out =>
      let (first, index, _) := splitName f.name
      match index with
      | .error e => "EValueError: " ++ e
      | .ok index =>
        match autoNumber st first index with
        | .error e => "EValueError: " ++ e
        | .ok (some i, st) =>
          match args[i]? with
          | some v => go ps st (out ++ v)
          | none => s!"EIndexError: Replacement index {i} out of range for positional args tuple"
        | .ok (none, st) =>
          if first == "x" then go ps st (out ++ "X") else s!"EKeyError: '{first}'"
  go (pieces s) .init ""

private def run (kind s : String) : String :=
  if kind == "pieces" then showPieces s
  else if kind == "split" then showSplit s
  else showNumber s

private def mismatches : List (String × String) :=
  FormatStringCases.cases.toList.filterMap fun (k, s, r) =>
    if run k s == r then none else some (k, s)

#guard FormatStringCases.cases.size == 1391
#guard mismatches == []

/-! ## What the cases don't show

`_string.formatter_parser` doesn't say whether a spec must be formatted first. -/

/-- Results compared by their contents, for the guards below. -/
private instance {α : Type} [BEq α] : BEq (Except String α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private def fieldOf (s : String) : Option Field :=
  match pieces s with
  | [.field f] => some f
  | _ => none

#guard (fieldOf "{0:{1}}").map (·.specNeedsExpanding) == some true
#guard (fieldOf "{0:>{1}}").map (·.specNeedsExpanding) == some true
#guard (fieldOf "{0:>5}").map (·.specNeedsExpanding) == some false
#guard (fieldOf "{0!r}").map (·.specNeedsExpanding) == some false
-- A brace inside `[]` doesn't make the spec nested.
#guard (fieldOf "{0[{]:x}").map (fun f => (f.name, f.spec, f.specNeedsExpanding)) ==
  some ("0[{]", "x", false)
-- The numbering goes on across a keyword field, and a keyword field leaves the numbering state
-- as it is.
#guard autoNumber .init "x" none == .ok (none, .init)
#guard autoNumber (.auto 2) "x" none == .ok (none, .auto 2)
#guard autoNumber .manual "x" none == .ok (none, .manual)

/-! ## Unknown conversions -/

#guard conversionError 'x' == "Unknown conversion specifier x"
#guard conversionError ' ' == "Unknown conversion specifier \\x20"
#guard conversionError '\x7f' == "Unknown conversion specifier \\x7f"
#guard conversionError 'é' == "Unknown conversion specifier \\xe9"
#guard conversionError '€' == "Unknown conversion specifier \\x20ac"
#guard conversionError '\x1f' == "Unknown conversion specifier \\x1f"
#guard conversionError '😀' == "Unknown conversion specifier \\x1f600"

end StrataPython.Dyn.Sem.Library.FormatStringTest
