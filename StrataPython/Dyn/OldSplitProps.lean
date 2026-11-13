/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPython.Dyn.OldSplit

set_option autoImplicit false

/-!
# Unfolding the old-part rule

Equations of `OldSplit.hasOld`, `readsOnlyOld`, `unOld` and `splitOld` without `attach`, for
proofs about an instance. Use them with `rw`, once per step: given to `simp`, the definitions'
own equations unfold without end.

Key theorems: `OldSplit.hasOld_eq`, `OldSplit.readsOnlyOld_eq`, `OldSplit.unOld_eq`,
`OldSplit.splitOld_eq`.
-/

namespace StrataPython.Dyn.OldSplit

public section

variable {α : Type} [SizeOf α] [OldSyntax α]
open OldSyntax

/-- `e` holds an `OLD` when it is one, or when one of its children holds one. -/
theorem hasOld_eq (e : α) : hasOld e = ((oldArg? e).isSome || (children e).any hasOld) := by
  rw [hasOld]; simp

/-- `e` reads no state outside its `OLD`s when it is an `OLD`, or when it doesn't read state
itself and none of its children does. -/
theorem readsOnlyOld_eq (e : α) : readsOnlyOld e =
    (if (oldArg? e).isSome then true else !readsState e && (children e).all readsOnlyOld) := by
  rw [readsOnlyOld]; simp

/-- Removing the `OLD`s of `OLD(a)` removes those of `a`; of any other node, those of its
children. -/
theorem unOld_eq (e : α) : unOld e =
    match oldArg? e with
    | some a => unOld a
    | none => mapChildren e fun c _ => unOld c := by
  rw [unOld]; split <;> simp_all

/-- `splitOld` makes a wrappable old part one `OLD`; otherwise it rebuilds an `OLD(a)` as
`OLD(unOld a)` and splits any other node's children. -/
theorem splitOld_eq (e : α) : splitOld e =
    if wrappable e && hasOld e && readsOnlyOld e then mkOld (unOld e) else
    match oldArg? e with
    | some a => mkOld (unOld a)
    | none => mapChildren e fun c _ => splitOld c := by
  rw [splitOld]; split <;> (try split) <;> simp_all

end -- public section

end StrataPython.Dyn.OldSplit
