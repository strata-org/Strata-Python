/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# Substring search

The Knuth–Morris–Pratt search of a pattern in an array, in time linear in the two lengths:
`occurrences` finds the starts of the occurrences that don't overlap, from the left. It is
generic in the item type, so a front end searches its own string units (Python's code points,
JavaScript's UTF-16 code units).
-/

namespace Strata.Dyn.Util.Search

@[expose] public section

variable {α : Type} [BEq α] [Inhabited α]

/-- The longest `k' ≤ k` such that the first `k'` items of `p`, which end the text read so far,
can go on with `x`; or 0. `f` is `p`'s failure function. -/
def back (p : Array α) (f : Array Nat) (x : α) (k : Nat) : Nat :=
  if _h : k > 0 ∧ x != p.getD k default then
    -- `f[k - 1] < k`, so `min` changes nothing; it gives the termination proof its bound.
    back p f x (min (f.getD (k - 1) 0) (k - 1))
  else k
termination_by k

/-- The failure function of `p`: for each prefix `p[0, i + 1)`, the length of its longest proper
prefix that is also a suffix. -/
def failure (p : Array α) : Array Nat := go 1 0 (Array.replicate p.size 0)
where
  go (i k : Nat) (f : Array Nat) : Array Nat :=
    if _h : i < p.size then
      let x := p.getD i default
      let k := back p f x k
      let k := if x == p.getD k default then k + 1 else k
      go (i + 1) k (f.setIfInBounds i k)
    else f
  termination_by p.size - i

/-- The start of every occurrence of the non-empty `p` in `a[lo, hi)`, from the left, that does
not overlap an earlier one, up to `limit` of them. -/
def occurrences (a p : Array α) (_hp : 0 < p.size) (lo hi limit : Nat) : Array Nat :=
  go (failure p) (min hi a.size) lo 0 #[]
where
  go (f : Array Nat) (hi i k : Nat) (acc : Array Nat) : Array Nat :=
    if _h : i < hi ∧ acc.size < limit then
      let x := a.getD i default
      let k := back p f x k
      let k := if x == p.getD k default then k + 1 else k
      -- A whole match ends at `i`; the next one starts after it.
      if k == p.size then go f hi (i + 1) 0 (acc.push (i + 1 - p.size))
      else go f hi (i + 1) k acc
    else acc
  termination_by hi - i

end

end Strata.Dyn.Util.Search
