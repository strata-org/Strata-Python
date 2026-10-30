/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Hash

set_option autoImplicit false

/-!
# Properties of the hashes

* `frozensetHashExact_perm`: a frozenset's exact hash doesn't depend on the order of its members'
  hashes, as CPython's doesn't (it combines them with `^`).
* `frozensetHash_perm`: a frozenset's hash, exact or symbolic, doesn't depend on that order
  either.  A symbolic hash sorts the members' hashes, and the order on hashes is a lawful total
  order (`Std.TransOrd Hash`, `Std.LawfulEqOrd Hash`), so two orders of the members sort to the
  same list.
-/

namespace StrataPython.Dyn.Sem

/-- `frozensetMix` gives the same result for any order of the hashes: it folds them with `^`,
which is commutative and associative. -/
public theorem frozensetMix_perm {hs hs' : List Int} (p : hs.Perm hs') :
    frozensetMix hs = frozensetMix hs' := by
  unfold frozensetMix
  apply List.Perm.foldl_eq' p
  intro x _ y _ z
  rw [UInt64.xor_assoc, UInt64.xor_assoc, UInt64.xor_comm (frozensetShuffle (toUHash x))]

/-- `frozensetHashExact` gives the same hash for any order of the members' hashes, as CPython's
`frozenset_hash` does. -/
public theorem frozensetHashExact_perm {hs hs' : List Int} (p : hs.Perm hs') :
    frozensetHashExact hs = frozensetHashExact hs' := by
  simp only [frozensetHashExact, frozensetMix_perm p, p.length_eq]

/-- The order on hash sources, the lexicographic order on their codes, is transitive. -/
public instance : Std.TransOrd HashSrc :=
  inferInstanceAs (Std.TransCmp (compareOn HashSrc.code))

/-- Two hash sources compare equal only when they are equal. -/
public instance : Std.LawfulEqOrd HashSrc where
  eq_of_compare h := HashSrc.ext (Std.LawfulEqOrd.eq_of_compare (α := List Nat) h)

/-- The derived order on hashes: exact hashes by number, before symbolic hashes by source. -/
private theorem compare_hash (a b : Hash) : compare a b = match a, b with
    | .exact x, .exact y => compare x y
    | .exact _, .symbolic _ => .lt
    | .symbolic _, .exact _ => .gt
    | .symbolic x, .symbolic y => compare x y := by
  cases a <;> cases b <;> simp [compare, instOrdHash.ord]

/-- The order on hashes (exact hashes first, by number, then symbolic hashes, by source) is
transitive. -/
public instance : Std.TransOrd Hash where
  eq_swap {a b} := by
    cases a <;> cases b <;> simp only [compare_hash, Ordering.swap] <;>
      exact Std.OrientedOrd.eq_swap
  isLE_trans {a b c} := by
    cases a <;> cases b <;> cases c <;> simp only [compare_hash, Ordering.isLE] <;>
      first | exact Std.TransOrd.isLE_trans | simp

/-- Two hashes compare equal only when they are equal. -/
public instance : Std.LawfulEqOrd Hash where
  eq_of_compare {a b} h := by
    cases a <;> cases b <;> simp only [compare_hash] at h <;> first
      | (congr; exact Std.LawfulEqOrd.eq_of_compare h) | cases h

/-- Sorting two permutations of each other by the order of hashes gives the same list, since
the order is total, transitive and antisymmetric. -/
private theorem mergeSort_hash_perm {hs hs' : List Hash} (p : hs.Perm hs') :
    hs.mergeSort (fun a b => compare a b != .gt) =
      hs'.mergeSort (fun a b => compare a b != .gt) := by
  have isLE : (fun a b : Hash => compare a b != .gt) = fun a b => (compare a b).isLE := by
    funext a b; cases compare a b <;> rfl
  have total (a b : Hash) : (compare a b).isLE || (compare b a).isLE := by
    rw [Std.OrientedOrd.eq_swap (a := b)]; cases compare a b <;> rfl
  have sorted (l : List Hash) := List.pairwise_mergeSort (le := fun a b => (compare a b).isLE)
    (fun _ _ _ => Std.TransOrd.isLE_trans) total l
  rw [isLE]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => Std.LawfulEqOrd.eq_of_compare (Std.OrientedCmp.isLE_antisymm hab hba))
    (sorted hs) (sorted hs')
    ((List.mergeSort_perm _ _).trans (p.trans (List.mergeSort_perm _ _).symm))

/-- `Hash.allExact? hs` checks that every hash of `hs` is exact, and keeps their numbers. -/
private theorem allExact?_eq (hs : List Hash) : Hash.allExact? hs =
    if hs.all (· matches .exact _) then
      some (hs.filterMap fun | .exact n => some n | .symbolic _ => none)
    else none := by
  induction hs with
  | nil => rfl
  | cons h t ih => cases h <;> simp [Hash.allExact?, ih]

/-- `frozensetHash` gives the same hash for any order of the members' hashes, whether they are
all exact or not: a frozenset's hash doesn't depend on the order of its members. -/
public theorem frozensetHash_perm {hs hs' : List Hash} (p : hs.Perm hs') :
    frozensetHash hs = frozensetHash hs' := by
  simp only [frozensetHash, allExact?_eq, p.all_eq]
  by_cases hc : hs'.all (· matches .exact _) <;>
    simp [hc, frozensetHashExact_perm (p.filterMap _), mergeSort_hash_perm p]

end StrataPython.Dyn.Sem
