/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Base

set_option autoImplicit false

/-!
# The contracts' base instructions stop with a gap

`old_eq` and `cellLoc_eq`: the rules of `base.old` and `base.cellLoc` stop with a gap, on every
input.  So these instructions stop visibly, never with a failure, which a verifier would read as a
path that can't happen.
-/

namespace Strata.Dyn

namespace Exec.BaseRules

public section

variable {ε : Eff} {E : Type}

/-- `base.old body err` stops with the gap that says the state at the call is not kept at run time,
for every region and target. -/
theorem old_eq {e a : Type} (body : Region ε [] (Except e a)) (err : Target E [e]) :
    old body err = semanticGap "base.old: the state at the call is not kept at run time" := rfl

/-- `base.cellLoc cell` stops with the gap that says frames have no meaning at run time, for every
cell. -/
theorem cellLoc_eq {σ : Type} [Store σ] {a : Type} (cell : Ref σ a) :
    cellLoc (ε := ε) (E := E) cell =
      semanticGap "base.cellLoc: frames have no meaning at run time" :=
  rfl

end

end Exec.BaseRules

end Strata.Dyn
