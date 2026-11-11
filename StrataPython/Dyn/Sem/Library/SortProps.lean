/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Sort

set_option autoImplicit false

/-!
# Properties of the fast path of `list.sort`

`fastSort` sorts positions by keys of the fast path (`FastKey`) with `List.mergeSort`, using
`FastKey.le` as the order. The order is total and transitive for all keys, so the theorems on
`List.mergeSort` apply.

* `FastKey.le_total`: of any two keys, one is at most the other.
* `FastKey.le_trans`: the order of the keys is transitive. The key lemma is that two finite
  values `m * 2 ^ e` and `n * 2 ^ f` compare the same way at every common scale at or below
  `min e f`, so three finite values can be compared at one scale.
* `fastSort_perm`: `fastSort xs` is a permutation of `xs`.
* `pairwise_fastSort`: `fastSort xs` is sorted by the keys.
* `sublist_fastSort`: `fastSort` is stable: every sublist of `xs` that is sorted by the keys is a
  sublist of `fastSort xs`.
-/

namespace StrataPython.Dyn.Sem.Library

namespace FastKey

/-- At the scale `k`, the value `m * 2 ^ e` is the integer `m * 2 ^ (e - k)`. Lowering the scale
from `j` to `k`, for `k ≤ j ≤ e`, multiplies that integer by `2 ^ (j - k)`. -/
private theorem scale_shift (m e j k : Int) (hkj : k ≤ j) (hje : j ≤ e) :
    m * 2 ^ (e - k).toNat = m * 2 ^ (e - j).toNat * 2 ^ (j - k).toNat := by
  rw [Int.mul_assoc, ← Int.pow_add]
  congr 2
  omega

/-- The finite key `fin m e` is below `fin n f` exactly when `m * 2 ^ (e - k) < n * 2 ^ (f - k)`,
at every scale `k` at or below both exponents (`lt` compares them at the scale `min e f`). -/
private theorem lt_fin_fin (m e n f k : Int) (hke : k ≤ e) (hkf : k ≤ f) :
    lt (.fin m e) (.fin n f) = true ↔ m * 2 ^ (e - k).toNat < n * 2 ^ (f - k).toNat := by
  have hpos : (0 : Int) < 2 ^ (min e f - k).toNat := Int.pow_pos (by decide)
  rw [scale_shift m e (min e f) k (Int.le_min.2 ⟨hke, hkf⟩) (Int.min_le_left e f),
    scale_shift n f (min e f) k (Int.le_min.2 ⟨hke, hkf⟩) (Int.min_le_right e f),
    Int.mul_lt_mul_right hpos, ← Int.compare_eq_lt]
  show (some _ == some Ordering.lt) = true ↔ _
  simp only [Option.some_beq_some, beq_iff_eq]

/-- The finite key `fin m e` is at most `fin n f` exactly when
`m * 2 ^ (e - k) ≤ n * 2 ^ (f - k)`, at every scale `k` at or below both exponents. -/
private theorem le_fin_fin (m e n f k : Int) (hke : k ≤ e) (hkf : k ≤ f) :
    le (.fin m e) (.fin n f) = true ↔ m * 2 ^ (e - k).toNat ≤ n * 2 ^ (f - k).toNat := by
  rw [le, Bool.not_eq_true', ← Bool.not_eq_true, lt_fin_fin n f m e k hkf hke, Int.not_lt]

/-- The key `str s` is at most `str t` exactly when `s ≤ t` as strings. -/
private theorem le_str_str (s t : String) : le (.str s) (.str t) = true ↔ s ≤ t := by
  simp only [le, lt, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, String.not_lt]

/-- The order of the keys is total: of any two keys, one is at most the other. -/
public theorem le_total (a b : FastKey) : le a b || le b a := by
  rcases a with ⟨_ | _⟩ | ⟨m, e⟩ | s <;> rcases b with ⟨_ | _⟩ | ⟨n, f⟩ | t
  case fin.fin =>
    rw [Bool.or_eq_true, le_fin_fin m e n f (min e f) (Int.min_le_left e f)
      (Int.min_le_right e f), le_fin_fin n f m e (min e f) (Int.min_le_right e f)
      (Int.min_le_left e f)]
    exact Int.le_total _ _
  case str.str =>
    rw [Bool.or_eq_true, le_str_str, le_str_str]
    exact String.le_total s t
  all_goals simp [le, lt, exact, Arith.Exact.compare]

/-- The order of the keys is transitive: if `a` is at most `b` and `b` is at most `c`, then `a`
is at most `c`. -/
public theorem le_trans (a b c : FastKey) : le a b → le b c → le a c := by
  intro hab hbc
  rcases a with ⟨_ | _⟩ | ⟨m, e⟩ | s <;> rcases b with ⟨_ | _⟩ | ⟨n, f⟩ | t <;>
    rcases c with ⟨_ | _⟩ | ⟨p, g⟩ | u
  case fin.fin.fin =>
    -- Compare the three values at the lowest of their exponents.
    have he : min e (min f g) ≤ e := Int.min_le_left _ _
    have hf : min e (min f g) ≤ f := Int.le_trans (Int.min_le_right _ _) (Int.min_le_left _ _)
    have hg : min e (min f g) ≤ g := Int.le_trans (Int.min_le_right _ _) (Int.min_le_right _ _)
    rw [le_fin_fin _ _ _ _ _ he hf] at hab
    rw [le_fin_fin _ _ _ _ _ hf hg] at hbc
    rw [le_fin_fin _ _ _ _ _ he hg]
    exact Int.le_trans hab hbc
  case str.str.str =>
    rw [le_str_str] at hab hbc ⊢
    exact String.le_trans hab hbc
  all_goals simp [le, lt, exact, Arith.Exact.compare] at hab hbc ⊢

end FastKey

/-- `fastSort xs` is a permutation of `xs`: it has the same items, each as many times. -/
public theorem fastSort_perm (xs : List (Nat × FastKey)) : (fastSort xs).Perm xs :=
  List.mergeSort_perm xs _

/-- `fastSort xs` is sorted by the keys: of any two items of `fastSort xs`, the key of the
earlier one is at most the key of the later one. -/
public theorem pairwise_fastSort (xs : List (Nat × FastKey)) :
    (fastSort xs).Pairwise fun a b => FastKey.le a.2 b.2 :=
  List.pairwise_mergeSort (le := fun a b : Nat × FastKey => FastKey.le a.2 b.2)
    (fun a b c => FastKey.le_trans a.2 b.2 c.2)
    (fun a b => FastKey.le_total a.2 b.2) xs

/-- `fastSort` is stable: if `ys` is a sublist of `xs` (its items in the order they have in
`xs`) and `ys` is sorted by the keys, then `ys` is a sublist of `fastSort xs`. In particular, two
items whose keys compare equal (each key is at most the other) keep their order. -/
public theorem sublist_fastSort {xs ys : List (Nat × FastKey)}
    (hsorted : ys.Pairwise fun a b => FastKey.le a.2 b.2) (hsub : ys.Sublist xs) :
    ys.Sublist (fastSort xs) :=
  List.sublist_mergeSort (le := fun a b : Nat × FastKey => FastKey.le a.2 b.2)
    (fun a b c => FastKey.le_trans a.2 b.2 c.2)
    (fun a b => FastKey.le_total a.2 b.2) hsorted hsub

end StrataPython.Dyn.Sem.Library
