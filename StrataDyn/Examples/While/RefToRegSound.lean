/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Examples.While.Cert
public import StrataDyn.RefToRegSound.RefToReg

set_option autoImplicit false

/-!
# Promoting the cells of While programs improves on them under every oracle

`refToReg_sound_while` is `refToReg_sound_cell` at While's table, whose certificate is
`WhileCert.certified`: the target's run improves on the source's up to a bad cell.  Like
`refToReg_sound_cell`, it holds for any target that `PromotionOK` relates to the source; that
`refToReg`'s output is one is not yet proved.  It observes the result and the world, not the
choices made or the final heap.
-/

namespace Strata.Dyn.WhileCert

open Strata.Dyn.Exec Strata.Dyn.RefToRegSound

@[expose] public section

/-- **A target that promotes the cells of a While program improves on it under every oracle,
up to a bad cell.**  If the module `m` links and validates against `WhileSem.model` with function
`f` at index `i`, and `PromotionOK` relates the linked source to a well-formed linked target
`lm₁`, then a start of `f` in `m`, on arguments that hold no ref, has a start at index `i` in
`lm₁`, and for every observation of the world and every oracle the target's run improves on the
source's under the same oracle: the same, or the source faults with a bad cell after what the
target shows. -/
theorem refToReg_sound_while {α : Type} {m : Module While.env α} {f : Name}
    {lm : LModule WhileSem.model.at} {hw : WF lm} {i : Nat}
    (hp : prepare WhileSem.model m f = .ok ⟨lm, hw, i⟩) {lm₁ : LModule WhileSem.model.at}
    (hw₁ : WF lm₁) (hcert : PromotionOK lm lm₁)
    (args : List (Dyn WhileSem.model.at.interp)) (hargs : ∀ d ∈ args, acct d.1 d.2 = [])
    {B : Ty} {c : Core WhileSem.model.at} {h : CoreOK lm B c}
    (hs : startCore hw i args .initial = .ok ⟨B, c, h⟩) :
    ∃ B₁ c₁ h₁, startCore hw₁ i args .initial = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : WhileRules.World → O),
        Exec.OracleRefines hw hw₁ obs Wrong ⟨⟨c, .exec, 0, ()⟩, h⟩ ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩ :=
  refToReg_sound_cell WhileSem.model accounts certified hp hw₁ hcert rfl args hargs hs

end

end Strata.Dyn.WhileCert
