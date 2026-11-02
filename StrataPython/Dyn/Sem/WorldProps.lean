/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.World
public import StrataPython.Dyn.Sem.StoreProps

set_option autoImplicit false

/-!
# Properties of the world

The module table: adding a cell keeps every entry and cell (`Modules.extends_withCell`), adds
only the new cell (`Modules.cell?_withCell_eq`, `Modules.cell?_withCell_self`), and keeps two
worlds that a `pure` operation can't tell apart so (`immEq_withCell`).  `Same` is a preorder
(`Same.refl`, `Same.trans`), which makes Python's world a `WorldSpec` (`spec`).  A new object, or
a change of an object made since the start, keeps `Same` and `ImmEq` (`same_allocObj`,
`immEq_allocObj`, `same_updObj`, `immEq_updObj`).
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ]

/-- Every module table extends itself. -/
theorem Modules.Extends.refl (m : Modules σ) : m.Extends m :=
  fun _ e h => ⟨e, h, rfl, fun _ _ h => h⟩

/-- A world is the same as itself: `Same` is reflexive, as a read-only update needs. -/
theorem Same.refl (s : Start) (w : World σ) : Same s w w :=
  ⟨Nat.le_refl _, fun _ _ _ h => h, Modules.Extends.refl _, rfl, rfl⟩

/-- Extending module tables is transitive. -/
theorem Modules.Extends.trans {m₁ m₂ m₃ : Modules σ} (h₁ : m₁.Extends m₂) (h₂ : m₂.Extends m₃) :
    m₁.Extends m₃ := fun k e he =>
  let ⟨e₂, he₂, ho₂, hc₂⟩ := h₁ k e he
  let ⟨e₃, he₃, ho₃, hc₃⟩ := h₂ k e₂ he₂
  ⟨e₃, he₃, ho₃.trans ho₂, fun n r hr => hc₃ n r (hc₂ n r hr)⟩

/-- `Same` is transitive: two updates that each keep the state an operation must leave alone keep
it together. -/
theorem Same.trans {s : Start} {w₁ w₂ w₃ : World σ} (h₁ : Same s w₁ w₂) (h₂ : Same s w₂ w₃) :
    Same s w₁ w₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun id o hid ho => h₂.2.1 id o hid (h₁.2.1 id o hid ho),
    h₁.2.2.1.trans h₂.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩

/-- Python's world, for the effects. -/
def spec : Effects.WorldSpec (World σ) Start :=
  { immEq := ImmEq, same := Same, same_refl := Same.refl,
    same_trans := fun _ _ _ _ => Same.trans, inCall := HasInCall.inCall }

/-- Adding a cell keeps every entry and every cell of the table. -/
theorem Modules.extends_withCell (m : Modules σ) (module name : String) (obj : ObjId)
    (r : Ref σ Value) : m.Extends (m.withCell module name obj r) := by
  intro k e he
  unfold Modules.withCell
  split
  · rename_i e₀ h₀
    by_cases hk : module = k
    · subst hk
      rw [h₀] at he
      injection he with he
      subst he
      refine ⟨{ e₀ with cells := e₀.cells.insertIfNew name r }, ?_, rfl, fun n r' hn => ?_⟩
      · simp
      · simp only [Std.TreeMap.getElem?_insertIfNew, Std.LawfulEqCmp.compare_eq_iff_eq]
        split
        · rename_i hc
          obtain ⟨rfl, hm⟩ := hc
          exact absurd (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by simp [hn])) hm
        · exact hn
    · exact ⟨e, by simp [Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hk, he],
        rfl, fun _ _ h => h⟩
  · rename_i h₀
    by_cases hk : module = k
    · subst hk
      rw [h₀] at he
      cases he
    · exact ⟨e, by simp [Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hk, he],
        rfl, fun _ _ h => h⟩

/-- The cells of a table with a new cell are its old cells and the new one. -/
theorem Modules.cell?_withCell (m : Modules σ) (module name : String) (obj : ObjId)
    (r : Ref σ Value) (k n : String) (r' : Ref σ Value)
    (h : (m.withCell module name obj r).cell? k n = some r') : m.cell? k n = some r' ∨ r' = r := by
  unfold Modules.withCell at h
  unfold Modules.cell?
  split at h
  · rename_i e₀ h₀
    by_cases hk : module = k
    · subst hk
      simp only [Modules.cell?, Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        ite_true, Option.bind_some, Std.TreeMap.getElem?_insertIfNew] at h
      split at h
      · cases h; exact .inr rfl
      · exact .inl (by simp [h₀, h])
    · simp only [Modules.cell?, Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        hk, ite_false] at h
      exact .inl h
  · by_cases hk : module = k
    · subst hk
      simp only [Modules.cell?, Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        ite_true, Option.bind_some] at h
      split at h
      · cases h; exact .inr rfl
      · simp at h
    · simp only [Modules.cell?, Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        hk, ite_false] at h
      exact .inl h

/-- A table with a new cell for `name` of `module`, which it didn't hold, holds that cell. -/
theorem Modules.cell?_withCell_self (m : Modules σ) (module name : String) (obj : ObjId)
    (r : Ref σ Value) (h : m.cell? module name = none) :
    (m.withCell module name obj r).cell? module name = some r := by
  unfold Modules.withCell
  split
  · rename_i e h₀
    simp only [Modules.cell?, h₀, Option.bind_some] at h
    have hn : name ∉ e.cells := fun hm => by
      rw [Std.TreeMap.mem_iff_isSome_getElem?, h] at hm
      cases hm
    simp only [Modules.cell?, Std.TreeMap.getElem?_insert_self, Option.bind_some,
      Std.TreeMap.getElem?_insertIfNew, Std.compare_self, hn, not_false_eq_true, and_self,
      ite_true]
  · simp only [Modules.cell?, Std.TreeMap.getElem?_insert_self, Option.bind_some]

/-- The cells of a table with a new cell: the new one for `name` of `module` if the table held
none, and the old ones otherwise. -/
theorem Modules.cell?_withCell_eq (m : Modules σ) (module name : String) (obj : ObjId)
    (r : Ref σ Value) (k n : String) :
    (m.withCell module name obj r).cell? k n =
      if k = module ∧ n = name ∧ m.cell? module name = none then some r else m.cell? k n := by
  unfold Modules.withCell
  split
  · rename_i e h₀
    by_cases hk : k = module
    · subst hk
      simp only [Modules.cell?, Std.TreeMap.getElem?_insert_self, Option.bind_some, h₀,
        Std.TreeMap.getElem?_insertIfNew, Std.LawfulEqCmp.compare_eq_iff_eq,
        Std.TreeMap.mem_iff_isSome_getElem?, true_and]
      by_cases hn : name = n
      · subst hn; cases e.cells[name]? <;> simp
      · simp [hn, Ne.symm hn]
    · simp only [Modules.cell?, Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        Ne.symm hk, hk, ite_false, false_and]
  · rename_i h₀
    by_cases hk : k = module
    · subst hk
      simp only [Modules.cell?, Std.TreeMap.getElem?_insert_self, Option.bind_some, h₀,
        Option.bind_none, and_true, true_and, Std.TreeMap.getElem?_insert,
        Std.LawfulEqCmp.compare_eq_iff_eq]
      by_cases hn : name = n
      · subst hn; simp
      · simp [hn, Ne.symm hn]
    · simp only [Modules.cell?, Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        Ne.symm hk, hk, ite_false, false_and]

/-- The module objects of a table with a new cell: `obj` for `module` if the table had no entry
for it, and the old ones otherwise. -/
theorem Modules.obj?_withCell (m : Modules σ) (module name : String) (obj : ObjId)
    (r : Ref σ Value) (k : String) :
    ((m.withCell module name obj r).map[k]?).map (ModuleEntry.obj (σ := σ)) =
      if k = module then some (((m.map[module]?).map (ModuleEntry.obj (σ := σ))).getD obj)
      else (m.map[k]?).map (ModuleEntry.obj (σ := σ)) := by
  unfold Modules.withCell
  by_cases hk : k = module
  · subst hk
    split <;> rename_i h₀ <;> simp [h₀]
  · split <;> simp [Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hk, Ne.symm hk]

/-- A new module entry keeps every entry and every cell of the table. -/
theorem Modules.extends_addNew (m : Modules σ) (name : String) (obj : ObjId) :
    m.Extends (m.addNew name obj) := by
  intro k e he
  unfold Modules.addNew
  split
  · exact ⟨e, he, rfl, fun _ _ h => h⟩
  · rename_i h₀
    by_cases hk : name = k
    · subst hk
      simp only [Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at h₀
      rw [h₀] at he
      cases he
    · exact ⟨e, by simp [Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hk, he],
        rfl, fun _ _ h => h⟩

/-- A new module entry adds no cell. -/
theorem Modules.cell?_addNew (m : Modules σ) (name : String) (obj : ObjId) (k n : String)
    (r : Ref σ Value) (h : (m.addNew name obj).cell? k n = some r) : m.cell? k n = some r := by
  unfold Modules.addNew at h
  split at h
  · exact h
  · by_cases hk : name = k
    · subst hk
      simp [Modules.cell?] at h
    · simpa [Modules.cell?, Std.TreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hk]
        using h

/-- Adding the same cell to two module tables with the same lookups gives tables with the same
lookups. -/
theorem immEq_withCell {s : Start} {w₁ w₂ : World σ} (h : ImmEq s w₁ w₂) (module name : String)
    (obj : ObjId) (r : Ref σ Value) :
    ImmEq s { w₁ with modules := w₁.modules.withCell module name obj r }
      { w₂ with modules := w₂.modules.withCell module name obj r } := by
  obtain ⟨hs, hn, ho, hm, hc⟩ := h
  refine ⟨hs, hn, ho, fun k => ?_, fun k n => ?_⟩
  · simp only [Modules.obj?_withCell, hm]
  · simp only [Modules.cell?_withCell_eq, hc]

/-! ## How the parts of the world change -/

/-- An allocation changes no protected state. -/
theorem same_allocObj (s : Start) (o : Obj σ) (w : World σ) : Same s w (w.allocObj o) := by
  refine ⟨by simp [World.allocObj, ObjStore.size_alloc], fun id o' _ h => ?_,
    Modules.Extends.refl _, rfl, rfl⟩
  have hlt : id < w.store.size := by
    simp only [ObjStore.get?, ObjStore.size] at h ⊢
    exact (Array.getElem?_eq_some_iff.mp h).1
  simp only [World.allocObj]
  rw [ObjStore.get?_alloc_lt _ _ hlt]
  exact h

/-- Two worlds that a `pure` operation can't tell apart stay so after the same allocation. -/
theorem immEq_allocObj {s : Start} (o : Obj σ) {w₁ w₂ : World σ} (h : ImmEq s w₁ w₂) :
    ImmEq s (w₁.allocObj o) (w₂.allocObj o) := by
  obtain ⟨hs, hn, ho, hm, hc⟩ := h
  refine ⟨by simp [World.allocObj, ObjStore.size_alloc, hs], fun id hid => ?_, fun id hid => ?_,
    hm, hc⟩
  · simp only [World.allocObj, ObjStore.get?_alloc, hs, hn id hid]
  · simp only [World.allocObj, ObjStore.get?_alloc, hs]
    split
    · rfl
    · exact ho id hid

/-- An update of an object made since the start changes no protected state. -/
theorem same_updObj {s : Start} {id : ObjId} (hid : s.storeSize ≤ id) (f : Obj σ → Obj σ)
    (w : World σ) : Same s w (w.updObj id f) := by
  refine ⟨by simp [World.updObj, ObjStore.size_update], fun id' o hlt h => ?_,
    Modules.Extends.refl _, rfl, rfl⟩
  simp only [World.updObj]
  rw [ObjStore.get?_update_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt hid))]
  exact h

/-- Two worlds that a `pure` operation can't tell apart stay so after the same update of an
object made since the start. -/
theorem immEq_updObj {s : Start} {id : ObjId} (hid : s.storeSize ≤ id) (f : Obj σ → Obj σ)
    {w₁ w₂ : World σ} (h : ImmEq s w₁ w₂) : ImmEq s (w₁.updObj id f) (w₂.updObj id f) := by
  obtain ⟨hs, hn, ho, hm, hc⟩ := h
  refine ⟨by simp [World.updObj, ObjStore.size_update, hs], fun id' hid' => ?_,
    fun id' hid' => ?_, hm, hc⟩
  · simp only [World.updObj]
    by_cases he : id = id'
    · subst he; rw [ObjStore.get?_update_self, ObjStore.get?_update_self, hn id hid']
    · rw [ObjStore.get?_update_ne _ _ he, ObjStore.get?_update_ne _ _ he]; exact hn id' hid'
  · simp only [World.updObj]
    have hne : id ≠ id' := Nat.ne_of_gt (Nat.lt_of_lt_of_le hid' hid)
    rw [ObjStore.get?_update_ne _ _ hne, ObjStore.get?_update_ne _ _ hne]
    exact ho id' hid'

end

end StrataPython.Dyn.Sem
