/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Index

set_option autoImplicit false

/-!
# Properties of indexes

Key theorem: `Groups.count_spec`, which says that `Groups.count c` is the number of distinct keys
of class `c`.
-/

namespace StrataPython.Dyn.Sem.Groups

variable {α C K : Type} [BEq C] [Hashable C] [BEq K] [LawfulBEq K] [Hashable K]
  {f : α → Option (C × K)}

/-- `count c` is the length of a list without duplicates of exactly the keys `k` that some element
of `es` has with the class `c`. -/
public theorem count_spec {es : Array α} (g : Groups α C K f es) (c : C) :
    ∃ l : List K, l.Nodup ∧ (∀ k, k ∈ l ↔ 0 < countBy f es (c, k)) ∧ g.count c = l.length := by
  refine ⟨(g.map.getD c ∅).keys, ?_, fun k => ?_, ?_⟩
  · have := (Std.HashMap.distinct_keys (m := g.map.getD c ∅))
    exact this.imp fun h => by simpa using h
  · rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_isSome_getElem?, g.wf]
    unfold nz; split <;> simp_all <;> omega
  · rw [count, Std.HashMap.length_keys]

end StrataPython.Dyn.Sem.Groups
