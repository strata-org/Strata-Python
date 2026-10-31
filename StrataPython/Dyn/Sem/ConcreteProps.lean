/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Concrete

set_option autoImplicit false

/-!
# Properties of the primitives

`StoreOK`: no object of the store has a class whose values are always immediates.  It holds of
the initial world (`storeOK_w0`), and allocating an object of another class (`storeOK_alloc`;
`alloc` refuses one of these classes, `Prim.alloc_immClass`) and updating an object's payload
(`storeOK_update`) keep it.
`Prim.callClosureT_restores`: a call writes back the depth that it read before the call.
-/

namespace StrataPython.Dyn.Sem.Prim

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ]

/-- `alloc` refuses an object of a class whose values are always immediates. -/
theorem alloc_immClass (o : ObjData) (h : o.cls.isImmClass) :
    alloc (σ := σ) o = PyM.failure "an object of a class whose values are immediates" := by
  simp [alloc, h]

/-- **The call restores the depth**: on a function object, under the depth part's laws, the
call reads the world, raises the depth by one in one update, makes the call, and then, in the
update before its continuation, writes back the depth that the world had before the raise. -/
theorem callClosureT_restores {ε : Eff} {E β : Type} [PyLang σ ε] [LawfulHasPart ε.W Depth]
    (id : ObjId) (args kwargs : Value) (k ke : Value → Sem ε E β) (w : ε.W) (f : FuncObj σ)
    (hf : (((HasPart.get w : ObjStore σ).get? id).map (·.payload) : Option (ObjPayload σ)) =
      some (.func f)) :
    ∃ kw, callClosureT id args kwargs k ke = .update kw ∧ (kw w).1 = w ∧
      ∃ g, (kw w).2 = .update g ∧ ∀ w₁ : ε.W,
        (HasPart.get (g w₁).1 : Depth) =
          { (HasPart.get w₁ : Depth) with py := (HasPart.get w₁ : Depth).py + 1 } ∧
        ∃ k', (g w₁).2 =
        .vis (HasCall.callReq (funcSig (ε := ε)) f.closure (args, kwargs)) k' ∧
        ∀ o, ∃ h, k' o = .update h ∧ ∀ w₂ : ε.W,
          (HasPart.get (h w₂).1 : Depth) = HasPart.get w₁ ∧
          (h w₂).2 = contOf k ke (HasCall.callAns (funcSig (ε := ε)) f.closure (args, kwargs) o) := by
  refine ⟨_, rfl, rfl, ?_⟩
  dsimp only [Sem.bindAfter, Sem.bind]
  rw [hf]
  simp only [modifyGetThe_eq]
  exact ⟨_, rfl, fun w₁ => ⟨LawfulHasPart.get_set _ _, _, rfl,
    fun o => ⟨_, rfl, fun w₂ => ⟨LawfulHasPart.get_set _ _, rfl⟩⟩⟩⟩

end

end StrataPython.Dyn.Sem.Prim

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ]

/-- No object of the store has a class whose values are always immediates. -/
def StoreOK (st : ObjStore σ) : Prop := ∀ id o, st.get? id = some o → o.cls.isImmClass = false

/-- The initial world's store has no object of an immediate's class. -/
theorem storeOK_w0 : StoreOK (w0 (σ := σ)).store := by
  intro id o h
  simp only [w0, ObjStore.get?] at h
  match id, h with
  | 0, h => simp at h; subst h; rfl
  | 1, h => simp at h; subst h; rfl
  | n + 2, h => simp at h

/-- Allocating an object of another class keeps `StoreOK`. -/
theorem storeOK_alloc {st : ObjStore σ} (h : StoreOK st) (o : Obj σ) (ho : o.cls.isImmClass = false) :
    StoreOK (st.alloc o).1 := by
  intro id o' h'
  rw [ObjStore.get?_alloc] at h'
  split at h'
  · cases h'; exact ho
  · exact h id o' h'

/-- Updating an object without changing its class keeps `StoreOK`. -/
theorem storeOK_update {st : ObjStore σ} (h : StoreOK st) (id : ObjId) (f : Obj σ → Obj σ)
    (hf : ∀ o, (f o).cls = o.cls) : StoreOK (st.update id f) := by
  intro id' o h'
  by_cases he : id = id'
  · subst he
    rw [ObjStore.get?_update_self] at h'
    obtain ⟨o₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp h'
    rw [hf]; exact h id o₀ h₀
  · rw [ObjStore.get?_update_ne _ _ he] at h'
    exact h id' o h'

end

end StrataPython.Dyn.Sem
