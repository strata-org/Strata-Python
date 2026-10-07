/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataPython.Mantle.Env
import StrataMantle.Env.WF
-- `decide +kernel` unfolds the checker, the environment and core's array operations.
import all StrataMantle.WF
import all StrataMantle.Env
import all StrataMantle.Base
import all StrataMantle.Build
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
instance toPy {e : Env Unit} [h : env ⊑ e] : Py.env ⊑ e := ⟨Env.Prefix.trans hsub h.subset⟩

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

private def cellOfInt {e : Env Unit} [Py.env ⊑ e] : TypeExpr e 0 := Base.Ref.ty Base.Int.ty

example : TypeExpr Ext3.env 0 := cellOfInt

/-- A builder generic over every refinement of `Py`: the same code emits into `Py.env` and
`Ext3.env`. -/
private def body {e : Env Unit} [Py.env ⊑ e] : BuildM e Unit Unit := do
  let x ← Build.freshVal "x" Base.Int.ty
  let _ ← Build.startFreshBlock #[x]
  let cell ← Build.emitApply "cell" (Base.Ref.ty Base.Int.ty) Base.refNew #v[Base.Int.ty] #[x.id]
  let got ← Build.emitApply "got" Base.Int.ty Base.refGet #v[Base.Int.ty] #[cell]
  Build.finishBlock (.ret () got)

private def fPy : Except Build.Errors (Func Py.env Unit) :=
  Build.build (.str .base "f") Base.Int.ty () body
private def fExt3 : Except Build.Errors (Func Ext3.env Unit) :=
  Build.build (.str .base "f") Base.Int.ty () body

example : Build.Holds (Func.WF #[]) fPy := by decide +kernel
example : Build.Holds (Func.WF #[]) fExt3 := by decide +kernel

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

private theorem byHand : base ⊆ Ext3.env :=
  Env.Prefix.trans (Py.toBase (e := Py.env)).subset Ext3.hsub

example : @Base.refNew Ext3.env ⟨byHand⟩ = Base.refNew := rfl

example (h₁ h₂ : base ⊑ Ext3.env) : @Base.refNew.sig _ h₁ = @Base.refNew.sig _ h₂ := rfl

/-! ## `⊒`

`s ⊒ t` is `t ⊑ s` written larger first.  It is input syntax only: a goal stated with it
prints with `⊑`. -/

example : Ext3.env ⊒ base := inferInstance

example {e : Env _root_.Unit} [e ⊒ Py.env] : TypeExpr e 0 := Base.Ref.ty Base.Int.ty

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
