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
`Prim.callClosureT_restores`, `Prim.bracketed_restores`, `Prim.withDepth_restores` and
`Prim.withPyDepth_restores`: a call and the call bracket write back the depth that they read
before they ran their body, each edge changing nothing but the depth; each depth count writes back
its own counter.  `Prim.withDepth_keeps_bracket` and
`Prim.withPyDepth_keeps_bracket`: the depth counts never move the call bracket's marker.
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
call reads the world, raises the depth by one and lowers the call bracket's marker in one update
that changes nothing else, makes the call, and then, in an update that changes nothing else
before its continuation, writes back the depth that the world had before. -/
theorem callClosureT_restores {ε : Eff} {E β : Type} [PyLang σ ε] [LawfulHasPart ε.W Depth]
    (id : ObjId) (args kwargs : Value) (k ke : Value → Sem ε E β) (w : ε.W) (f : FuncObj σ)
    (hf : (((HasPart.get w : ObjStore σ).get? id).map (·.payload) : Option (ObjPayload σ)) =
      some (.func f)) :
    ∃ kw, callClosureT id args kwargs k ke = .update kw ∧ (kw w).1 = w ∧
      ∃ g, (kw w).2 = .update g ∧ ∀ w₁ : ε.W,
        (g w₁).1 = HasPart.set w₁
          ({ (HasPart.get w₁ : Depth) with py := (HasPart.get w₁ : Depth).py + 1, bracket := 0 } : Depth) ∧
        ∃ k', (g w₁).2 =
        .vis (HasCall.callReq (funcSig (ε := ε)) f.closure (args, kwargs)) k' ∧
        ∀ o, ∃ h, k' o = .update h ∧ ∀ w₂ : ε.W,
          (h w₂).1 = HasPart.set w₂ (HasPart.get w₁ : Depth) ∧
          (h w₂).2 = contOf k ke (HasCall.callAns (funcSig (ε := ε)) f.closure (args, kwargs) o) := by
  refine ⟨_, rfl, rfl, ?_⟩
  dsimp only [Sem.bindAfter, Sem.bind]
  rw [hf]
  simp only [modifyGetThe_eq]
  exact ⟨_, rfl, fun w₁ => ⟨rfl, _, rfl, fun o => ⟨_, rfl, fun w₂ => ⟨rfl, rfl⟩⟩⟩⟩

/-- **`withDepth` restores the C recursion count**: when the count `c` of the world `w` plus `n` is
within the limit, `withDepth` reads the world, raises `c` by `n` in one update, and runs the body
with continuations that each set `c` back to `w`'s in the update before they go on. -/
theorem withDepth_restores {ε : Eff} {E β : Type} [PyLang σ ε] [LawfulHasPart ε.W Depth]
    {e : Effects.Level} {fr : Bool} {α : Type} (hnp0 : e ≠ .pure) (n : Nat) (body : PyM σ e fr α)
    (hs : Handles ε E) (s : Start) (k : α → Sem ε E β) (ke : Value → Sem ε E β) (w : ε.W)
    (hle : ¬ cDepthLimit < (HasPart.get w : Depth).c + n) :
    ∃ kw, (withDepth hnp0 n body).1 hs s k ke = .update kw ∧ (kw w).1 = w ∧
      ∃ g kb kbe, (kw w).2 = .update g ∧
        (∀ w₁ : ε.W, (HasPart.get (g w₁).1 : Depth) =
          { (HasPart.get w₁ : Depth) with c := (HasPart.get w : Depth).c + n } ∧
          (g w₁).2 = body.1 hs s kb kbe) ∧
        (∀ a, ∃ h, kb a = .update h ∧ ∀ w₂ : ε.W,
          (HasPart.get (h w₂).1 : Depth) = { (HasPart.get w₂ : Depth) with c := (HasPart.get w : Depth).c } ∧
          (h w₂).2 = k a) ∧
        (∀ x, ∃ h, kbe x = .update h ∧ ∀ w₂ : ε.W,
          (HasPart.get (h w₂).1 : Depth) = { (HasPart.get w₂ : Depth) with c := (HasPart.get w : Depth).c } ∧
          (h w₂).2 = ke x) := by
  refine ⟨_, rfl, rfl, ?_⟩
  dsimp only [Sem.bindAfter, Sem.bind]
  simp only [hle, ↓reduceIte, modifyThe_eq]
  exact ⟨_, _, _, rfl, fun w₁ => ⟨LawfulHasPart.get_set _ _, rfl⟩,
    fun a => ⟨_, rfl, fun w₂ => ⟨LawfulHasPart.get_set _ _, rfl⟩⟩,
    fun x => ⟨_, rfl, fun w₂ => ⟨LawfulHasPart.get_set _ _, rfl⟩⟩⟩

/-- **`withPyDepth` restores the Python call depth**: when the depth `py` of the world `w` plus `n`
is within the limit, `withPyDepth` reads the world, raises `py` by `n` in one update, and runs the
body with continuations that each set `py` back to `w`'s in the update before they go on. -/
theorem withPyDepth_restores {ε : Eff} {E β : Type} [PyLang σ ε] [LawfulHasPart ε.W Depth]
    {e : Effects.Level} {fr : Bool} {α : Type} (hnp0 : e ≠ .pure) (n : Nat) (body : PyM σ e fr α)
    (hs : Handles ε E) (s : Start) (k : α → Sem ε E β) (ke : Value → Sem ε E β) (w : ε.W)
    (hle : ¬ pyDepthLimit < (HasPart.get w : Depth).py + n) :
    ∃ kw, (withPyDepth hnp0 n body).1 hs s k ke = .update kw ∧ (kw w).1 = w ∧
      ∃ g kb kbe, (kw w).2 = .update g ∧
        (∀ w₁ : ε.W, (HasPart.get (g w₁).1 : Depth) =
          { (HasPart.get w₁ : Depth) with py := (HasPart.get w : Depth).py + n } ∧
          (g w₁).2 = body.1 hs s kb kbe) ∧
        (∀ a, ∃ h, kb a = .update h ∧ ∀ w₂ : ε.W,
          (HasPart.get (h w₂).1 : Depth) = { (HasPart.get w₂ : Depth) with py := (HasPart.get w : Depth).py } ∧
          (h w₂).2 = k a) ∧
        (∀ x, ∃ h, kbe x = .update h ∧ ∀ w₂ : ε.W,
          (HasPart.get (h w₂).1 : Depth) = { (HasPart.get w₂ : Depth) with py := (HasPart.get w : Depth).py } ∧
          (h w₂).2 = ke x) := by
  refine ⟨_, rfl, rfl, ?_⟩
  dsimp only [Sem.bindAfter, Sem.bind]
  simp only [hle, ↓reduceIte, modifyThe_eq]
  exact ⟨_, _, _, rfl, fun w₁ => ⟨LawfulHasPart.get_set _ _, rfl⟩,
    fun a => ⟨_, rfl, fun w₂ => ⟨LawfulHasPart.get_set _ _, rfl⟩⟩,
    fun x => ⟨_, rfl, fun w₂ => ⟨LawfulHasPart.get_set _ _, rfl⟩⟩⟩

/-- **`withDepth` keeps the call bracket's marker**: under the depth part's laws, when the C
recursion count of the world `w` plus `n` is within the limit, the update that raises the count and
the updates that lower it again leave `Depth.bracket` as it was. -/
theorem withDepth_keeps_bracket {ε : Eff} {E β : Type} [PyLang σ ε] [LawfulHasPart ε.W Depth]
    {e : Effects.Level} {fr : Bool} {α : Type} (hnp0 : e ≠ .pure) (n : Nat) (body : PyM σ e fr α)
    (hs : Handles ε E) (s : Start) (k : α → Sem ε E β) (ke : Value → Sem ε E β) (w : ε.W)
    (hle : ¬ cDepthLimit < (HasPart.get w : Depth).c + n) :
    ∃ kw, (withDepth hnp0 n body).1 hs s k ke = .update kw ∧ (kw w).1 = w ∧
      ∃ g kb kbe, (kw w).2 = .update g ∧
        (∀ w₁ : ε.W, (HasPart.get (g w₁).1 : Depth).bracket = (HasPart.get w₁ : Depth).bracket ∧
          (g w₁).2 = body.1 hs s kb kbe) ∧
        (∀ a, ∃ h, kb a = .update h ∧ ∀ w₂ : ε.W,
          (HasPart.get (h w₂).1 : Depth).bracket = (HasPart.get w₂ : Depth).bracket ∧ (h w₂).2 = k a) ∧
        (∀ x, ∃ h, kbe x = .update h ∧ ∀ w₂ : ε.W,
          (HasPart.get (h w₂).1 : Depth).bracket = (HasPart.get w₂ : Depth).bracket ∧ (h w₂).2 = ke x) := by
  obtain ⟨kw, h1, h2, g, kb, kbe, h3, hg, hk, hke⟩ := withDepth_restores hnp0 n body hs s k ke w hle
  refine ⟨kw, h1, h2, g, kb, kbe, h3, fun w₁ => ?_, fun a => ?_, fun x => ?_⟩
  · exact ⟨by rw [(hg w₁).1], (hg w₁).2⟩
  · obtain ⟨h, hh, hw⟩ := hk a; exact ⟨h, hh, fun w₂ => ⟨by rw [(hw w₂).1], (hw w₂).2⟩⟩
  · obtain ⟨h, hh, hw⟩ := hke x; exact ⟨h, hh, fun w₂ => ⟨by rw [(hw w₂).1], (hw w₂).2⟩⟩

/-- **`withPyDepth` keeps the call bracket's marker**: under the depth part's laws, when the Python
call depth of the world `w` plus `n` is within the limit, the update that raises the depth and the
updates that lower it again leave `Depth.bracket` as it was. -/
theorem withPyDepth_keeps_bracket {ε : Eff} {E β : Type} [PyLang σ ε] [LawfulHasPart ε.W Depth]
    {e : Effects.Level} {fr : Bool} {α : Type} (hnp0 : e ≠ .pure) (n : Nat) (body : PyM σ e fr α)
    (hs : Handles ε E) (s : Start) (k : α → Sem ε E β) (ke : Value → Sem ε E β) (w : ε.W)
    (hle : ¬ pyDepthLimit < (HasPart.get w : Depth).py + n) :
    ∃ kw, (withPyDepth hnp0 n body).1 hs s k ke = .update kw ∧ (kw w).1 = w ∧
      ∃ g kb kbe, (kw w).2 = .update g ∧
        (∀ w₁ : ε.W, (HasPart.get (g w₁).1 : Depth).bracket = (HasPart.get w₁ : Depth).bracket ∧
          (g w₁).2 = body.1 hs s kb kbe) ∧
        (∀ a, ∃ h, kb a = .update h ∧ ∀ w₂ : ε.W,
          (HasPart.get (h w₂).1 : Depth).bracket = (HasPart.get w₂ : Depth).bracket ∧ (h w₂).2 = k a) ∧
        (∀ x, ∃ h, kbe x = .update h ∧ ∀ w₂ : ε.W,
          (HasPart.get (h w₂).1 : Depth).bracket = (HasPart.get w₂ : Depth).bracket ∧ (h w₂).2 = ke x) := by
  obtain ⟨kw, h1, h2, g, kb, kbe, h3, hg, hk, hke⟩ := withPyDepth_restores hnp0 n body hs s k ke w hle
  refine ⟨kw, h1, h2, g, kb, kbe, h3, fun w₁ => ?_, fun a => ?_, fun x => ?_⟩
  · exact ⟨by rw [(hg w₁).1], (hg w₁).2⟩
  · obtain ⟨h, hh, hw⟩ := hk a; exact ⟨h, hh, fun w₂ => ⟨by rw [(hw w₂).1], (hw w₂).2⟩⟩
  · obtain ⟨h, hh, hw⟩ := hke x; exact ⟨h, hh, fun w₂ => ⟨by rw [(hw w₂).1], (hw w₂).2⟩⟩

/-- **The call bracket restores the depth**: under the depth part's laws, `bracketed` raises the
bracket's marker in one update that changes nothing else, runs its body (with continuations that
return its outcome) inside `HasBracket.bracket`, and then, in an update that changes nothing else
before its continuation, writes back the whole depth that the world had before. -/
theorem bracketed_restores {ε : Eff} {E β α : Type} [PyLang σ ε] [LawfulHasPart ε.W Depth]
    (msg : String) (body : PyM σ .writes true α) (hs : Handles ε E) (s : Start)
    (k : α → Sem ε E β) (ke : Value → Sem ε E β) :
    ∃ kw, (bracketed msg body).1 hs s k ke = .update kw ∧ ∀ w : ε.W,
      (kw w).1 = HasPart.set w
        ({ (HasPart.get w : Depth) with bracket := (HasPart.get w : Depth).bracket + 1 } : Depth) ∧
      ∃ c, (kw w).2 = Sem.bind (HasBracket.bracket msg
          (body.1 hs s (fun a => .ret (Except.ok a)) (fun x => .ret (Except.error x)))) c ∧
        ∀ r, ∃ h, c r = .update h ∧
        ∀ w₂ : ε.W, (h w₂).1 = HasPart.set w₂ (HasPart.get w : Depth) ∧ (h w₂).2 = contOf k ke r := by
  refine ⟨_, rfl, fun w => ?_⟩
  dsimp only [Sem.bind]
  simp only [modifyGetThe_eq]
  dsimp only [Sem.bindAfter]
  simp only [LawfulHasPart.modifyGet_eq]
  exact ⟨trivial, _, rfl, fun r => ⟨_, rfl, fun w₂ => ⟨rfl, rfl⟩⟩⟩

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
