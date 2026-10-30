/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.FinallyEntered
import all StrataPython.Dyn.FinallyEntered

set_option autoImplicit false

/-!
# Each `finally` body pushes the completion it was entered with, decided

## Main theorems

* `PyCanonical.checkFinallyEntered_iff`: `checkFinallyEntered` decides `FinallyEntered`.
-/

namespace StrataPython.Dyn.PyCanonical

open Strata.Dyn

variable {α : Type}

/-- `finEnteredB` decides `FinEntered`: whether the block holds `py.pushPending` only as its first
instruction, and, if it starts a `finally` body, pushes its own first parameter, a
`py.Completion`. -/
theorem finEnteredB_iff (b : Block Py.env α) : finEnteredB b = true ↔ FinEntered b := by
  simp only [finEnteredB, FinEntered, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Option.any_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  refine and_congr Iff.rfl ⟨fun h hf => ?_, fun h => ?_⟩
  · rcases h with hn | ⟨p, hp, ht, ha⟩
    · exact absurd hf hn
    · exact ⟨p, hp, ht, ha⟩
  · by_cases hf : IsFin b
    · obtain ⟨p, hp, ht, ha⟩ := h hf
      exact .inr ⟨p, hp, ht, ha⟩
    · exact .inl hf

/-- `checkFinallyEntered` holds exactly when every block of the function holds `py.pushPending`
only as its first instruction, and every block that starts a `finally` body pushes its own first
parameter, a `py.Completion`. -/
public theorem checkFinallyEntered_iff (fn : Func Py.env α) :
    checkFinallyEntered fn = true ↔ FinallyEntered fn := by
  simp only [checkFinallyEntered, FinallyEntered, List.all_eq_true, finEnteredB_iff]

end StrataPython.Dyn.PyCanonical
