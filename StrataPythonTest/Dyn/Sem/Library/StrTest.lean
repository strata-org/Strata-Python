/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Str
public import StrataPythonTest.Dyn.Sem.Library.StrMethodCases
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Library.Str
meta import StrataPythonTest.Dyn.Sem.Library.StrMethodCases

set_option autoImplicit false

/-!
# Searching, splitting and padding of `str`

`StrMethodCases.cases` holds CPython 3.12's results of these methods on random strings; the
functions must give the same.
-/

namespace StrataPython.Dyn.Sem.Library.StrTest

open StrataPython.Dyn.Sem.Library.Str

/-- A string's code points, as the cases write them. -/
private def cps (a : Chars) : String := " ".intercalate (a.toList.map fun c => toString c.toNat)

private def encStr (a : Chars) : String := "s " ++ cps a
private def encList (xs : Array Chars) : String := "l " ++ "|".intercalate (xs.toList.map cps)
private def encInt (n : Int) : String := s!"i {n}"
private def encBool (b : Bool) : String := s!"b {if b then 1 else 0}"

/-- The function's result for a case, written as the cases write CPython's; `e` for a
`ValueError` (an empty separator). -/
private def run (m : String) (s' a' : String) (b c : Option Int) : String :=
  let s := chars s'
  let a := chars a'
  let n := b.getD 0
  let ch := (a.toList.headD ' ')
  match m with
  | "find" => encInt (find s a b c)
  | "rfind" => encInt (rfind s a b c)
  | "count" => encInt (count s a b c)
  | "startswith" => encBool (startsWith s a b c)
  | "endswith" => encBool (endsWith s a b c)
  | "replace" =>
    let old := a.toList.takeWhile (· != '\x00')
    let new := (a.toList.dropWhile (· != '\x00')).drop 1
    encStr (replace s old.toArray new.toArray n)
  | "split" => if h : a.isEmpty then "e" else encList (split s a (size_pos_of_not_isEmpty h) n)
  | "rsplit" => if h : a.isEmpty then "e" else encList (rsplit s a (size_pos_of_not_isEmpty h) n)
  | "splitws" => encList (splitWhitespace s n)
  | "rsplitws" => encList (rsplitWhitespace s n)
  | "partition" =>
    if h : a.isEmpty then "e"
    else let (x, y, z) := partition s a (size_pos_of_not_isEmpty h); encList #[x, y, z]
  | "rpartition" =>
    if a.isEmpty then "e" else let (x, y, z) := rpartition s a; encList #[x, y, z]
  | "splitlines" => encList (splitlines s (n != 0))
  | "strip" => encStr (strip s none true true)
  | "lstrip" => encStr (strip s none true false)
  | "rstrip" => encStr (strip s none false true)
  | "stripchars" => encStr (strip s (some a) (n != 2) (n != 1))
  | "removeprefix" => encStr (removePrefix s a)
  | "removesuffix" => encStr (removeSuffix s a)
  | "ljust" => encStr (ljust s n ch)
  | "rjust" => encStr (rjust s n ch)
  | "center" => encStr (center s n ch)
  | "zfill" => encStr (zfill s n)
  | "expandtabs" => encStr (expandtabs s n)
  | _ => "unknown method"

/-- The cases where a function differs from CPython. -/
private def mismatches : List (String × String × String) :=
  StrMethodCases.cases.toList.filterMap fun (m, s, a, b, c, r) =>
    if run m s a b c == r then none else some (m, s, a)

#guard StrMethodCases.cases.size == 1500
#guard mismatches == []

/-! ## Long inputs

A pattern that almost matches everywhere, in a long text. (A `#guard` has no time limit, so these
pin results, not the cost.) -/

#guard find (Array.replicate 100000 'a') (Array.replicate 999 'a' |>.push 'b') none none == -1
#guard count (Array.replicate 100000 'a') #['a', 'a'] none none == 50000

end StrataPython.Dyn.Sem.Library.StrTest
