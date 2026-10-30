/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# List facts

Facts the proofs about the scoping checker (`StrataDyn/DomProps.lean`,
`StrataDyn/DomDecide.lean`) and the termination of its diagnostics' searches
(`StrataDyn/DomDiag.lean`) need.

## Main theorems

* `length_le_of_nodup_subset`: a list with no duplicates is no longer than any list holding all
  its elements;
* `findIdx_le_of_getElem?`: `findIdx` stops at or before any element satisfying the predicate;
* `countP_lt_countP`: a weaker predicate counts strictly more elements if it holds of an element
  the stronger one fails on.

Everything here is private: a module that uses it imports it with `import all`.
-/

namespace Strata.Dyn.List

/-- A list with no duplicates, all of whose elements are in `m`, is no longer than `m`. -/
theorem length_le_of_nodup_subset {β : Type} [DecidableEq β] :
    ∀ {l m : List β}, l.Nodup → l ⊆ m → l.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, m, hn, hs => by
    have ha : a ∈ m := hs List.mem_cons_self
    have hl := length_le_of_nodup_subset (List.nodup_cons.mp hn).2 (m := m.erase a)
      fun y hy =>
        (List.mem_erase_of_ne fun h => (List.nodup_cons.mp hn).1 (by subst h; exact hy)).mpr
          (hs (List.mem_cons_of_mem _ hy))
    rw [List.length_erase_of_mem ha] at hl
    have hpos : 0 < m.length := List.length_pos_of_mem ha
    exact (Nat.le_sub_iff_add_le hpos).mp hl

/-- `findIdx` stops at or before any element that satisfies the predicate. -/
theorem findIdx_le_of_getElem? {β : Type} {p : β → Bool} {l : List β} {k : Nat} {x : β}
    (h : l[k]? = some x) (hp : p x = true) : l.findIdx p ≤ k := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact Nat.le_of_not_lt fun hlt => Bool.false_ne_true ((List.not_of_lt_findIdx hlt).symm.trans hp)

/-- If `p` implies `q` on the elements of `l`, and `a` in `l` satisfies `q` but not `p`, then `q`
holds of more elements of `l` than `p` does. -/
theorem countP_lt_countP {β : Type} {p q : β → Bool} :
    ∀ {l : List β}, (∀ x ∈ l, p x → q x) → ∀ a ∈ l, p a = false → q a = true →
      l.countP p < l.countP q
  | [], _, a, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, ha, hpa, hqa => by
    have hxs : ∀ y ∈ xs, p y → q y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hmono := List.countP_mono_left hxs
    simp only [List.countP_cons]
    rcases List.mem_cons.mp ha with rfl | hmem
    · simp [hpa, hqa]; omega
    · have ih := countP_lt_countP hxs a hmem hpa hqa
      have hx := h x List.mem_cons_self
      by_cases hpx : p x <;> by_cases hqx : q x <;> simp_all <;> omega

end Strata.Dyn.List
