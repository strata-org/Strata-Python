/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Mro

set_option autoImplicit false

/-!
# Properties of C3

* `C3.merge_sublist`: a successful merge keeps the order of every list it merges.
* `C3.mro_extends_bases`: an MRO starts with its class and keeps the order of every base's MRO, and of the
  bases themselves.
-/

namespace StrataPython.Dyn.Sem.C3

variable {α : Type} [DecidableEq α]

/-- A merge that succeeds gives the accumulated classes, then a list in which every merged list
appears in order (as a sublist).  By induction on the merge: each step appends a class `c` that
heads every list it is dropped from, so a list keeps its order. -/
public theorem merge_sublist (ls : List (List α)) (acc r : List α) (h : merge ls acc = .ok r) :
    ∃ s, r = acc.reverse ++ s ∧ ∀ l ∈ ls, l.Sublist s := by
  induction ls, acc using merge.induct generalizing r with
  | case1 ls acc hall =>
    rw [merge] at h
    simp only [hall, ↓reduceIte, Except.ok.injEq] at h
    refine ⟨[], by simp [h], fun l hl => ?_⟩
    have hempty := List.all_eq_true.mp hall l hl
    simp only [List.isEmpty_iff] at hempty
    simp [hempty]
  | case2 ls acc hall hnone =>
    rw [merge] at h
    simp only [hall, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · simp at h
    · rename_i c hc; simp [hc] at hnone
  | case3 ls acc hall c hc _ ih =>
    rw [merge] at h
    simp only [hall, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · rename_i hn; simp [hn] at hc
    · rename_i c' hc'
      rw [hc] at hc'
      injection hc' with hcc
      subst hcc
      rw [attach_map_dropHead] at ih
      obtain ⟨s, hr, hsub⟩ := ih r h
      refine ⟨c :: s, by simp [hr], fun l hl => ?_⟩
      have hd := hsub (dropHead c l) (List.mem_map_of_mem hl)
      cases l with
      | nil => exact List.nil_sublist _
      | cons x xs =>
        by_cases hx : x = c
        · subst hx
          simp only [dropHead, ↓reduceIte] at hd
          exact hd.cons_cons x
        · simp only [dropHead, hx, ↓reduceIte] at hd
          exact hd.cons c

/-- An MRO that `mro` computes starts with the class, has every base's MRO as a sublist (C3's
monotonicity), and has the bases as a sublist (the local precedence order).  Only a class with one
base, whose MRO CPython takes without a merge, needs `hself`: that each base's MRO holds the base. -/
public theorem mro_extends_bases (cls : α) (bases : List α) (mroOf : α → List α) (r : List α)
    (hself : ∀ b ∈ bases, b ∈ mroOf b) (h : mro cls bases mroOf = .ok r) :
    ∃ s, r = cls :: s ∧ (∀ b ∈ bases, (mroOf b).Sublist s) ∧ bases.Sublist s := by
  unfold mro at h
  split at h
  · rename_i b
    injection h with h
    refine ⟨mroOf b, h.symm, fun b' hb' => ?_, ?_⟩
    · simp only [List.mem_singleton] at hb'
      subst hb'
      exact List.Sublist.refl _
    · exact List.singleton_sublist.mpr (hself b (by simp))
  · split at h
    · exact absurd h (by simp)
    · split at h
      · rename_i r' hm
        injection h with h
        subst h
        obtain ⟨s, hr, hsub⟩ := merge_sublist _ [cls] r' hm
        exact ⟨s, by simpa using hr, fun b hb => hsub _ (List.mem_append_left _ (List.mem_map_of_mem hb)),
          hsub _ (by simp)⟩
      · exact absurd h (by simp)

end StrataPython.Dyn.Sem.C3
