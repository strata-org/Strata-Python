/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.Dyn.Sem.Contracts.Regex
meta import StrataPythonTest.Dyn.Sem.Contracts.RegexCases
meta import Std.Data.HashMap

set_option autoImplicit false

/-!
# The matcher of `py.reSearch` against CPython 3.12

`RegexCases.lean` holds CPython 3.12's verdicts for patterns of the subset and outside it, crossed
with strings over an alphabet of ASCII and non-ASCII characters.  `regex_cases.py` generates it,
and `StrataPythonTestExtra/ContractRegexCasesTest.lean` checks it against CPython.  Every case must
give its verdict: an answer for a pattern of the subset that CPython reads, and a gap for one that
CPython rejects or warns on, that nests more than 20 groups, or that lies outside the subset.  The counts
of the verdicts are pinned, so a change of the generated cases shows here.
-/

namespace StrataPython.Dyn.Sem.Contracts.RegexTest

open StrataPython.Dyn.Sem.Contracts.Regex

meta section

/-- The matcher's verdict for `pattern` on `s`: `True`, `False`, or `gap` where `parse` gives
nothing. -/
def verdictOf (pattern s : String) : String :=
  match parse pattern with
  | none => "gap"
  | some r => if search pyClasses r s.toList.toArray then "True" else "False"

/-- Check every case, and print the counts and the cases that disagree. -/
def checkCases : IO Unit := do
  let mut counts : Std.HashMap String Nat := {}
  let mut bad : Array String := #[]
  for (p, s, v) in RegexCases.cases do
    counts := counts.insert v (counts.getD v 0 + 1)
    let got := verdictOf p s
    if got != v then bad := bad.push s!"{repr p} on {repr s}: CPython {v}, the rule {got}"
  IO.println s!"True {counts.getD "True" 0}, False {counts.getD "False" 0}, gap {counts.getD "gap" 0}"
  for b in bad.toList.take 20 do IO.println b
  IO.println s!"{bad.size} cases disagree"

/--
info: True 7735, False 6617, gap 2886
0 cases disagree
-/
#guard_msgs in #eval checkCases

-- Nested counted repeats stop as soon as a round changes nothing: without the early stop, this
-- search applies the inner repeat 10^9 times.
#guard (Regex.parse "(?:(?:a{1000}){1000}){1000}").map
  (fun r => Regex.search Regex.pyClasses r #['a']) == some false

-- A repeat of a one-character test, or of an alternation of such tests, takes one pass over the
-- string, whatever its counts: with a round per count or per position, each of these searches
-- would take seconds to minutes.
#guard (Regex.parse "^[a-z0-9-]+$").map
  (fun r => Regex.search Regex.pyClasses r (Array.replicate 20000 'a')) == some true
#guard (Regex.parse "^[a-z0-9-]{1,1000}$").map
  (fun r => Regex.search Regex.pyClasses r (Array.replicate 20000 'a')) == some false
#guard (Regex.parse "^a{1000}").map
  (fun r => Regex.search Regex.pyClasses r (Array.replicate 20000 'a')) == some true
#guard (Regex.parse "^(?:[a-z]|-)+$").map
  (fun r => Regex.search Regex.pyClasses r (Array.replicate 20000 'a')) == some true

-- The one-pass path applies to a one-character test and to an alternation of such tests, and not
-- to a longer body.
#guard ((Regex.parse "(?:[a-z]|-)").bind (Regex.charTest Regex.pyClasses)).map
  (fun f => (f 'q', f '-', f 'A')) == some (true, true, false)
#guard ((Regex.parse "(?:ab)").bind (Regex.charTest Regex.pyClasses)).isNone
#guard ((Regex.parse "(?:a|\\b)").bind (Regex.charTest Regex.pyClasses)).isNone

end

end StrataPython.Dyn.Sem.Contracts.RegexTest
