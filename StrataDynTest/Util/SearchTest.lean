/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Util.Search
meta import StrataDyn.Util.Search

set_option autoImplicit false

/-! # Substring search

`occurrences` against a naive search, on every text over two letters up to length 8 and every
pattern up to length 4: the patterns with borders (`aab`, `abab`, …) make the search fall back
along its failure function. -/

namespace Strata.Dyn.Util.SearchTest

open Strata.Dyn.Util.Search

/-- Every array over `{'a', 'b'}` of length `n`. -/
private def words : Nat → List (Array Char)
  | 0 => [#[]]
  | n + 1 => (words n).flatMap fun w => [w.push 'a', w.push 'b']

/-- The starts of the non-overlapping occurrences of `p` in `a` from `i`, by trying each start. -/
private def naive (a p : Array Char) (i : Nat) (fuel : Nat) : List Nat :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if i + p.size > a.size then []
    else if a.extract i (i + p.size) == p then i :: naive a p (i + p.size) fuel
    else naive a p (i + 1) fuel

private def mismatches : List (Array Char × Array Char) :=
  ((List.range 9).flatMap words).flatMap fun a =>
    ((List.range 4).flatMap fun n => words (n + 1)).filterMap fun p =>
      if h : 0 < p.size then
        if (occurrences a p h 0 a.size a.size).toList == naive a p 0 (a.size + 1) then none
        else some (a, p)
      else some (a, p)

#guard mismatches == []

-- The search reads only `a[lo, hi)`, and no further than the end of `a`.
#guard occurrences #['a'] #[(default : Char)] (by decide) 0 5 9 == #[]
#guard occurrences #['a', 'a', 'a', 'b'] #['a', 'a', 'b'] (by decide) 0 4 1 == #[1]
#guard occurrences #['a', 'b', 'a', 'b', 'a', 'b'] #['a', 'b', 'a', 'b'] (by decide) 0 6 9 == #[0]
#guard occurrences #['a', 'a', 'a', 'a'] #['a', 'a'] (by decide) 1 4 9 == #[1]
#guard occurrences #['a', 'a', 'a', 'a'] #['a'] (by decide) 0 4 2 == #[0, 1]

end Strata.Dyn.Util.SearchTest
