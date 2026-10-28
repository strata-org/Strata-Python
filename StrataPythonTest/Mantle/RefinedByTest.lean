/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataPython.Mantle.Env
import StrataMantle.Env.WF
-- The builder and the checker run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.WF
meta import StrataMantle.Env.WF
meta import StrataPython.Mantle.Env
-- `decide +kernel` unfolds the environment for `boxFresh`.
import all StrataMantle.Env
import all StrataMantle.Base
import all StrataPython.Mantle.Env
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq

set_option autoImplicit false

/-!
# Refinement, by instance search

Three levels: `base`, `Py.env` refining it, and a test environment `Ext3.env` refining
`Py.env`.  Each level declares its parent with one instance, and a base reference is then
available in every level, and in code generic over any of them.
-/

namespace StrataPython.Mantle.RefinedByTest

open Strata.Mantle

/-! ## A third level -/

namespace Ext3

/-- `ext3.Box (+a)`. -/
def boxD : TypeDecl Unit :=
  { ann := (), name := .str (.str .base "ext3") "Box", params := #[⟨"a", .pos⟩] }

theorem boxFresh : boxD.name ∉ Py.env := by rw [Py.mem_env]; decide +kernel

/-- `Py.env` plus `ext3.Box`. -/
def env : Env Unit := Py.env.addType boxD boxFresh

/-- `Ext3.env` extends `Py.env`. -/
theorem hsub : Py.env ⊆ env := Env.subset_addType _ _ _

/-- `Ext3`'s declared parent is `Py`. -/
instance toPy {e : Env Unit} [h : env ⊑ e] : Py.env ⊑ e :=
  ⟨Env.Le.trans (Env.le_of_subset hsub) h.le⟩

end Ext3

/-! ## Concrete queries -/

example : base ⊑ base := inferInstance
example : base ⊑ Py.env := inferInstance
example : base ⊑ Ext3.env := inferInstance
example : Py.env ⊑ Ext3.env := inferInstance
example : Ext3.env ⊑ Ext3.env := inferInstance

/-- The same base reference, in each level. -/
example : TypeRef base 1 := Base.Ref.ref
example : TypeRef Py.env 1 := Base.Ref.ref
example : TypeRef Ext3.env 1 := Base.Ref.ref

/-! ## The generic case

Over `[Py.env ⊑ e]`, the base is reached through `Py`'s declared parent, so no second
hypothesis is needed. -/

private def cellOfInt {e : Env Unit} [Py.env ⊑ e] : TypeExpr e := Base.Ref Base.Int

example : TypeExpr Ext3.env := cellOfInt

/-- A builder generic over every refinement of `Py`: the same code emits into `Py.env` and
`Ext3.env`. -/
private def body {e : Env Unit} [Py.env ⊑ e] : BuildM e Unit Unit := do
  let x ← Build.freshVal (.str .base "x") Base.Int
  let _ ← Build.startFreshBlock #[x]
  let cell ← Build.emitApply (.str .base "cell") (Base.Ref Base.Int) Base.refNew
      #[x.id]
  let got ← Build.emitApply (.str .base "got") Base.Int Base.refGet #[cell]
  Build.finishBlock (.ret () got)

#guard (Build.build (env := Py.env) (.str .base "f") Base.Int () body).isOk
#guard (Build.build (env := Ext3.env) (.str .base "f") Base.Int () body).isOk

/-! ## A failing query: the base does not refine `Py` -/

/--
error: failed to synthesize instance of type class
  Py.env ⊑ base

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Py.env ⊑ base := inferInstance

/-! ## Coherence

A proof of `base ⊑ Ext3.env` written by hand and the one search finds give the same
reference, by proof irrelevance. -/

private theorem byHand : base ≤ Ext3.env :=
  Env.Le.trans (Py.toBase (e := Py.env)).le (Env.le_of_subset Ext3.hsub)

example : @Base.refNew Ext3.env ⟨byHand⟩ = Base.refNew := rfl

example (h₁ h₂ : base ⊑ Ext3.env) : @Base.refNew.sig _ h₁ = @Base.refNew.sig _ h₂ := rfl

/-! ## Order

Refinement reads what names resolve to, not where they are declared: the same types, added in
either order, refine each other. -/

namespace Order

private def aD : TypeDecl Unit := { ann := (), name := .str .base "A" }
private def bD : TypeDecl Unit := { ann := (), name := .str .base "B" }

private def ab : Env Unit :=
  (Env.empty.addType aD (by simp)).addType bD (by simp [aD, bD])
private def ba : Env Unit :=
  (Env.empty.addType bD (by simp)).addType aD (by simp [aD, bD])

/-- `ab` and `ba` name every type alike. -/
private theorem typeOf?_ab_ba (n : Name) : ab.typeOf? n = ba.typeOf? n := by
  simp only [ab, ba, Env.typeOf?_addType, Env.typeOf?_empty]
  by_cases ha : aD.name = n <;> by_cases hb : bD.name = n
  · exact absurd (ha.trans hb.symm) (by decide)
  all_goals simp [ha, hb]

/-- An environment of two types declares no datatype. -/
private theorem dataOf?_two {d₁ d₂ : TypeDecl Unit} {f₁ : d₁.name ∉ (Env.empty : Env Unit)}
    {g₁ : d₁.paramNames.Nodup}
    {f₂ : d₂.name ∉ Env.empty.addType d₁ f₁ g₁} {g₂ : d₂.paramNames.Nodup} {n : Name} :
    ((Env.empty.addType d₁ f₁ g₁).addType d₂ f₂ g₂).dataOf? n = none := by
  simp [Env.dataOf?_addType]

/-- An environment of two types declares no instruction. -/
private theorem not_declaresInsn_two {d₁ d₂ : TypeDecl Unit} {f₁ : d₁.name ∉ (Env.empty : Env Unit)}
    {g₁ : d₁.paramNames.Nodup}
    {f₂ : d₂.name ∉ Env.empty.addType d₁ f₁ g₁} {g₂ : d₂.paramNames.Nodup} {n : Name}
    {σ : InsnSig ((Env.empty.addType d₁ f₁ g₁).addType d₂ f₂ g₂)} {k : InsnKind} :
    ¬ ((Env.empty.addType d₁ f₁ g₁).addType d₂ f₂ g₂).DeclaresInsn n σ k := fun h => by
  obtain ⟨_, h₁, -⟩ := Env.declaresInsn_addType h
  obtain ⟨_, h₂, -⟩ := Env.declaresInsn_addType h₁
  exact Env.not_declaresInsn_empty h₂

example : ab ≤ ba := show Env.LeBy _ ab ba from
  { type := fun hd => ⟨_, (typeOf?_ab_ba _).symm.trans hd, rfl, rfl⟩
    data := fun hd => by simp [ab, dataOf?_two] at hd
    insn := fun hd => (not_declaresInsn_two hd).elim }
example : ba ≤ ab := show Env.LeBy _ ba ab from
  { type := fun hd => ⟨_, (typeOf?_ab_ba _).trans hd, rfl, rfl⟩
    data := fun hd => by simp [ba, dataOf?_two] at hd
    insn := fun hd => (not_declaresInsn_two hd).elim }

end Order

/-! ## `⊒`

`s ⊒ t` is `t ⊑ s` written larger first.  It is input syntax only: a goal stated with it
prints with `⊑`. -/

example : Ext3.env ⊒ base := inferInstance

example {e : Env _root_.Unit} [e ⊒ Py.env] : TypeExpr e := Base.Ref Base.Int

/-- info: Py.env ⊑ Ext3.env : Prop -/
#guard_msgs in
#check (Ext3.env ⊒ Py.env)

/-! ## `Lean.Order`'s `⊑`

Its notation is scoped too.  With both open, the overload is resolved by type. -/

section
open Lean.Order
example : base ⊑ Py.env := inferInstance
end

end StrataPython.Mantle.RefinedByTest
