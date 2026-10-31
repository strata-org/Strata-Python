/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.CertCaps

set_option autoImplicit false

/-!
# The lemmas of the capability specs

Key theorems: `refsOK_ref`, `refsOK_fn` and the `refsOK_*` lemmas of the literal types and of
`×`, `Except` and `Array`, each a corollary of `Typing.allValid_*`; the `Sat` lemma of each
capability's operation, `HeapSpec.newRef_sat`, `readRef_sat`, `writeRef_sat`, `modifyRef_sat`,
`CallSpec.callFn_sat`, `PartSpec.getThe_sat`, `modifyThe_sat` and `modifyGetThe_sat`; and
`PartSpec.of_noRefs`.

The definitions they are about are in `CertCaps.lean`: `Refs` and `RefsOK` (where a value holds
refs), and the specs of the heap (`HeapSpec`), of calls (`CallSpec`) and of a part of the world
(`PartSpec`).
-/

namespace Strata.Dyn.Exec

@[expose] public section

section
variable {σ : Type} [Store σ]

/-- A valid value stays valid in an extension. -/
theorem RefsOK.mono {α : Type} [Refs σ α] {S S₁ : Typing} (h : S.Extends S₁) {x : α}
    (hx : RefsOK (σ := σ) S x) : RefsOK (σ := σ) S₁ x :=
  Typing.AllValid.mono h hx

/-- A ref is valid exactly when its location holds its contents' tag. -/
@[simp] theorem refsOK_ref [Decode σ] {α : Type} [t : TagOf σ α] {S : Typing} {c : Ref σ α} :
    RefsOK (σ := σ) S c ↔ S.Valid c.loc t.tag := by
  unfold RefsOK
  exact Typing.allValid_singleton

/-- A closure is valid exactly when its captures cell is. -/
@[simp] theorem refsOK_fn {as : List Type} {r : Type} {S : Typing} {f : FnRef σ as r} :
    RefsOK (σ := σ) S f ↔ S.CapValid f.captured := by
  unfold RefsOK Refs.refs instRefsFnRef
  by_cases h : f.captured = 0
  · simp only [h, ↓reduceIte, Typing.allValid_nil, true_iff]
    exact .inl rfl
  · simp only [h, ↓reduceIte, Typing.allValid_singleton]
    exact Iff.rfl

/-- A value with no refs is valid in every typing. -/
theorem refsOK_nil {α : Type} [Refs σ α] {S : Typing} {x : α}
    (h : Refs.refs (σ := σ) x = []) : RefsOK (σ := σ) S x := by
  unfold RefsOK
  rw [h]
  exact Typing.allValid_nil S

/-- A value of `Unit` holds no ref, so it is valid in every typing. -/
@[simp] theorem refsOK_unit {S : Typing} {x : Unit} : RefsOK (σ := σ) S x := refsOK_nil rfl
/-- A value of `Bool` holds no ref, so it is valid in every typing. -/
@[simp] theorem refsOK_bool {S : Typing} {x : Bool} : RefsOK (σ := σ) S x := refsOK_nil rfl
/-- A value of `Int` holds no ref, so it is valid in every typing. -/
@[simp] theorem refsOK_int {S : Typing} {x : Int} : RefsOK (σ := σ) S x := refsOK_nil rfl
/-- A value of `Nat` holds no ref, so it is valid in every typing. -/
@[simp] theorem refsOK_nat {S : Typing} {x : Nat} : RefsOK (σ := σ) S x := refsOK_nil rfl
/-- A value of `Float` holds no ref, so it is valid in every typing. -/
@[simp] theorem refsOK_float {S : Typing} {x : Float} : RefsOK (σ := σ) S x := refsOK_nil rfl
/-- A value of `String` holds no ref, so it is valid in every typing. -/
@[simp] theorem refsOK_string {S : Typing} {x : String} : RefsOK (σ := σ) S x := refsOK_nil rfl
/-- A value of `Fin n` holds no ref, so it is valid in every typing. -/
@[simp] theorem refsOK_fin {n : Nat} {S : Typing} {x : Fin n} : RefsOK (σ := σ) S x :=
  refsOK_nil rfl

/-- A pair is valid when both its parts are. -/
@[simp] theorem refsOK_prod {α β : Type} [Refs σ α] [Refs σ β] {S : Typing} {x : α × β} :
    RefsOK (σ := σ) S x ↔ RefsOK (σ := σ) S x.1 ∧ RefsOK (σ := σ) S x.2 :=
  Typing.allValid_append

/-- An `Except` is valid when the value it holds is. -/
@[simp] theorem refsOK_ok {α β : Type} [Refs σ α] [Refs σ β] {S : Typing} {b : β} :
    RefsOK (σ := σ) S (Except.ok b : Except α β) ↔ RefsOK (σ := σ) S b := Iff.rfl

/-- An `Except` is valid when the error it holds is. -/
@[simp] theorem refsOK_error {α β : Type} [Refs σ α] [Refs σ β] {S : Typing} {a : α} :
    RefsOK (σ := σ) S (Except.error a : Except α β) ↔ RefsOK (σ := σ) S a := Iff.rfl

/-- An array is valid when each element is. -/
theorem refsOK_array {α : Type} [Refs σ α] {S : Typing} {xs : Array α} :
    RefsOK (σ := σ) S xs ↔ ∀ x ∈ xs.toList, RefsOK (σ := σ) S x :=
  Typing.allValid_flatMap

end

section
variable {ε : Eff} {E : Type} {σ : Type} [Store σ] [Decode σ] {V : Spec Typing ε E}

section
variable {h : HasHeap σ ε} {α : Type} [t : TagOf σ α] [Refs σ α] (hh : HeapSpec V h α)
  {β : Type} {S : Typing}
include hh

/-- A new cell of a valid value is a valid ref, in every grown typing. -/
theorem HeapSpec.newRef_sat {v : α} (hv : RefsOK (σ := σ) S v) {Q : Typing → Ref σ α → Prop}
    (hQ : ∀ S₁, V.Ext S S₁ → ∀ c : Ref σ α, S₁.Valid c.loc t.tag → Q S₁ c) :
    V.Sat Q S (@newRef σ _ _ ε E h α t v) :=
  Spec.sat_vis.mpr ⟨hh.new S v hv, fun S₁ he o ho => Spec.sat_ret.mpr (hQ S₁ he _ (hh.newAns S₁ v o ho))⟩

/-- Reading a valid ref gives a valid value. -/
theorem HeapSpec.readRef_sat {c : Ref σ α} (hc : S.Valid c.loc t.tag) {Q : Typing → α → Prop}
    (hQ : ∀ S₁, V.Ext S S₁ → ∀ x : α, RefsOK (σ := σ) S₁ x → Q S₁ x) :
    V.Sat Q S (@readRef σ _ _ ε E h α t c) :=
  Spec.sat_vis.mpr ⟨hh.get S c hc, fun S₁ he o ho => Spec.sat_ret.mpr (hQ S₁ he _ (hh.getAns S₁ c o ho))⟩

/-- Writing a valid value through a valid ref is allowed. -/
theorem HeapSpec.writeRef_sat {c : Ref σ α} (hc : S.Valid c.loc t.tag) {v : α}
    (hv : RefsOK (σ := σ) S v) {Q : Typing → Unit → Prop} (hQ : ∀ S₁, V.Ext S S₁ → Q S₁ ()) :
    V.Sat Q S (@writeRef σ _ _ ε E h α t c v) :=
  Spec.sat_vis.mpr ⟨hh.set S c v hc hv, fun S₁ he _ _ => Spec.sat_ret.mpr (hQ S₁ he)⟩

/-- Updating a valid ref's contents by a function that keeps values valid is allowed. -/
theorem HeapSpec.modifyRef_sat {c : Ref σ α} (hc : S.Valid c.loc t.tag) {f : α → α}
    (hf : ∀ x, RefsOK (σ := σ) S x → RefsOK (σ := σ) S (f x)) {Q : Typing → Unit → Prop}
    (hQ : ∀ S₁, V.Ext S S₁ → Q S₁ ()) : V.Sat Q S (@modifyRef σ _ _ ε E h α t c f) :=
  Spec.sat_vis.mpr ⟨hh.modify S c f hc hf, fun S₁ he _ _ => Spec.sat_ret.mpr (hQ S₁ he)⟩

end

/-- Calling a valid closure on valid arguments gives a valid result. -/
theorem CallSpec.callFn_sat {h : HasCall σ ε} {as : List Type} {r : Type} [s : SigOf σ as r]
    [Refs σ (Payload as)] [Refs σ r] (hc : CallSpec V h as r) {S : Typing} {f : FnRef σ as r}
    {a : Payload as} (hf : RefsOK (σ := σ) S f) (ha : RefsOK (σ := σ) S a)
    {Q : Typing → r → Prop} (hQ : ∀ S₁, V.Ext S S₁ → ∀ x : r, RefsOK (σ := σ) S₁ x → Q S₁ x) :
    V.Sat Q S (@callFn σ _ _ ε E h as r s f a) :=
  Spec.sat_vis.mpr ⟨hc.call S f a hf ha, fun S₁ he o ho =>
    Spec.sat_ret.mpr (hQ S₁ he _ (hc.callAns S₁ f a o ho))⟩

end

section
variable {ε : Eff} {E : Type} {σ : Type} [Store σ] {V : Spec Typing ε E}

section
variable {P : Type} [HasPart ε.W P] [Refs σ P] (hp : PartSpec (σ := σ) V P) {S : Typing}
include hp

/-- Reading a part of the world gives a valid part. -/
theorem PartSpec.getThe_sat {Q : Typing → P → Prop}
    (hQ : ∀ x : P, RefsOK (σ := σ) S x → Q S x) : V.Sat Q S (getThe P : Sem ε E P) :=
  Spec.sat_update.mpr fun w hw => ⟨hw, Spec.sat_ret.mpr (hQ _ (hp.get S w hw))⟩

/-- Updating a part of the world by a function that keeps parts valid is allowed. -/
theorem PartSpec.modifyThe_sat [LawfulHasPart ε.W P] {f : P → P}
    (hf : ∀ x : P, RefsOK (σ := σ) S x → RefsOK (σ := σ) S (f x)) {Q : Typing → Unit → Prop}
    (hQ : Q S ()) : V.Sat Q S (modifyThe P f : Sem ε E Unit) := by
  rw [modifyThe_eq]
  exact Spec.sat_update.mpr fun w hw =>
    ⟨hp.set S w _ hw (hf _ (hp.get S w hw)), Spec.sat_ret.mpr hQ⟩

/-- Updating a part of the world and returning a value is allowed when the function keeps parts
valid, and its value meets the postcondition. -/
theorem PartSpec.modifyGetThe_sat [LawfulHasPart ε.W P] {β : Type} {f : P → β × P}
    (hf : ∀ x : P, RefsOK (σ := σ) S x → RefsOK (σ := σ) S (f x).2) {Q : Typing → β → Prop}
    (hQ : ∀ x : P, RefsOK (σ := σ) S x → Q S (f x).1) :
    V.Sat Q S (modifyGetThe P f : Sem ε E β) := by
  rw [modifyGetThe_eq]
  exact Spec.sat_update.mpr fun w hw =>
    ⟨hp.set S w _ hw (hf _ (hp.get S w hw)), Spec.sat_ret.mpr (hQ _ (hp.get S w hw))⟩

end

/-- A part with no refs is valid in every world: its spec needs only that putting it back keeps
the world possible. -/
theorem PartSpec.of_noRefs {P : Type} [HasPart ε.W P] [Refs σ P]
    (hn : ∀ x : P, Refs.refs (σ := σ) x = [])
    (hs : ∀ S w (p : P), V.World S w → V.World S (HasPart.set w p)) : PartSpec (σ := σ) V P :=
  ⟨fun _ _ _ => refsOK_nil (hn _), fun S w p hw _ => hs S w p hw⟩

end

end

end Strata.Dyn.Exec
