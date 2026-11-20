/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Link

set_option autoImplicit false

/-!
# Properties of linking

## Main theorems

* `linkSite_target_exit`: linking resolves a target to the body's exit exactly when the target
  names `Label.exit`, and to a block of the body otherwise.  So the machine leaves a body only
  along a successor that names `Label.exit` (`Exec.step_ret`), which is the IR's notion of
  leaving a body (`Body.leaves_iff`), given that linking makes an instruction's sites from its
  successors, in order, which is not proved yet (`link_wf`).
-/

namespace Strata.Dyn.Exec

public section

variable {M : Model}

/-- Linking resolves the target `k` to the body's exit exactly when `k` names `Label.exit`. -/
theorem linkSite_target_exit {labels : LabelMap Nat} {k : Target.Raw} {ctx : LinkCtx}
    {st st' : LinkState M} {site : LSite}
    (h : linkSite (M := M) labels k ctx st = .ok (site, st')) :
    site.target = .exit ↔ k.label = Label.exit := by
  unfold linkSite at h
  by_cases hk : k.label = Label.exit
  · simp only [hk, ↓reduceIte] at h
    cases h
    exact ⟨fun _ => hk, fun _ => rfl⟩
  · simp only [hk, ↓reduceIte] at h
    cases hf : labels.find? k.label with
    | some i =>
      simp only [hf] at h
      cases h
      simp [hk]
    | none =>
      simp only [hf] at h
      cases h

end

end Strata.Dyn.Exec
