/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Sum

set_option autoImplicit false

/-!
# Properties of the numeric core of `sum`

Key theorems: `step_next_rank` and `afterAdd_rank`, which say that the phases come in their order
(int, then float, then generic) and that the loop never goes back to an earlier one; and
`step_int_next`, which says what the int phase takes and that its total is the exact sum, within
a C `long`. `rank` numbers the phases.
-/

namespace StrataPython.Dyn.Sem.Library.Sum

@[expose] public section

/-- The position of a phase in the order of the phases: int, then float, then generic. -/
def rank {α : Type} : State α → Nat
  | .int _ => 0
  | .float _ _ => 1
  | .generic _ => 2

/-- A step that takes the item stays in the same phase. -/
theorem step_next_rank {α : Type} {s s' : State α} {i : Item} (h : step s i = .next s') :
    rank s' = rank s := by
  unfold step at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h
  · cases h
  · cases h

/-- After an add that gave `r`, the loop goes on in a later phase, or stays in the generic phase
with `r` as its total. -/
theorem afterAdd_rank {α : Type} (s : State α) (r : α) (bits : Option UInt64) :
    rank s < rank (afterAdd s r bits) ∨ afterAdd s r bits = .generic r := by
  cases s <;> cases bits <;> simp [afterAdd, rank]

/-- In the int phase, a step takes only an item whose type is `int` or `bool`, and only when the
item and the new total fit in a C `long`; the new total is the old total plus the item's value. -/
theorem step_int_next {α : Type} {t : Int} {i : Item} {s : State α}
    (h : step (.int t) i = .next s) :
    ∃ b, i = .int b true ∧ s = .int (t + b) ∧ fitsLong b ∧ fitsLong (t + b) := by
  unfold step at h
  split at h
  · split at h
    · rename_i hf
      cases h
      simp only [Bool.and_eq_true] at hf
      simp_all
    · cases h
  all_goals simp_all

end

end StrataPython.Dyn.Sem.Library.Sum
