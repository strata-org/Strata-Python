/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Translate
import Std.Data.HashSet.Lemmas
import Strata.Util.ListUtilsProps

set_option autoImplicit false

/-!
# Properties of the translator

* `freshName_not_mem`: the name `freshName` picks for a new function is not taken.  The
  candidates it tries are distinct, so they cannot all be among the names taken
  (Strata's `List.subset_nodup_length`).
* `freshName_first_free`: it is the first candidate that is not taken.

`freshName_eq_fast` is in `Translate.lean`, because `allocName` must be compiled after it to
run the fast search.
-/

namespace StrataPython.Dyn.PyTranslate

open Strata.Dyn

public section

/-- Different indices give different candidates. -/
private theorem candidate_injective (first : Name) : Function.Injective (candidate first) := by
  intro a b h
  cases a <;> cases b <;> simp only [candidate, Name.num.injEq] at h
  · rfl
  · have hsize := congrArg sizeOf h; simp at hsize; omega
  · have hsize := congrArg sizeOf h; simp at hsize; omega
  · omega

/-- The name that `freshName taken first` picks is not in `taken`: the first
`taken.size + 1` candidates are distinct, so one of them is free. -/
theorem freshName_not_mem (taken : Std.HashSet Name) (first : Name) :
    freshName taken first ∉ taken := by
  unfold freshName
  split
  · rename_i k hk
    have hfree := List.find?_some hk
    rw [Std.HashSet.mem_iff_contains]
    simpa using hfree
  · rename_i hnone
    exfalso
    rw [List.find?_eq_none] at hnone
    have hsub : ((List.range (taken.size + 1)).map (candidate first)) ⊆ taken.toList := by
      intro x hx
      simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have htaken := hnone k (List.mem_range.mpr hk)
      rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
      simpa using htaken
    have hnd : ((List.range (taken.size + 1)).map (candidate first)).Nodup :=
      List.Pairwise.map (candidate first) (fun _ _ hab h => hab (candidate_injective first h))
        List.nodup_range
    have hlen := List.subset_nodup_length hnd hsub
    simp [Std.HashSet.length_toList] at hlen
    omega

/-- `freshName taken first` is the first free candidate: the `k`-th one, where every candidate
before it is taken. -/
theorem freshName_first_free (taken : Std.HashSet Name) (first : Name) :
    ∃ k, freshName taken first = candidate first k ∧ candidate first k ∉ taken ∧
      ∀ j < k, candidate first j ∈ taken := by
  have hnotMem := freshName_not_mem taken first
  unfold freshName at hnotMem ⊢
  split
  · rename_i k hk
    rw [List.find?_range_eq_some] at hk
    obtain ⟨hfree, -, hbefore⟩ := hk
    refine ⟨k, rfl, ?_, fun j hj => ?_⟩
    · rw [Std.HashSet.mem_iff_contains]; simpa using hfree
    · rw [Std.HashSet.mem_iff_contains]; simpa using hbefore j hj
  · rename_i hnone
    exfalso
    rw [hnone] at hnotMem
    rw [List.find?_range_eq_none] at hnone
    exact hnotMem (by rw [Std.HashSet.mem_iff_contains]; simpa using hnone taken.size (by omega))

end -- public section

end StrataPython.Dyn.PyTranslate
