/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Clause
public import StrataPython.Dyn.OldSplitProps

set_option autoImplicit false

/-! # Properties of checked clauses

Key result:
- `CExpr.splitOld_oldContents_no_result`: when no `OLD` of a clause mentions `result`, no old part
  that `CExpr.splitOld` makes mentions it either. So `base.old` never reads the call's result,
  which does not exist in the state at the call (§12.4, *`OLD(e)`*).

Definitions a reader needs: `CExpr.splitOld`, `CExpr.oldsWithoutResult`, `CExpr.oldContents`
(`Clause.lean`).
-/

namespace StrataPython.Dyn.PySpec

public section

/-- Removing the `old` markers changes nothing about whether `e` mentions `result`. -/
private theorem CExpr.mentionsResult_unOld (e : CExpr) : e.unOld.mentionsResult = e.mentionsResult := by
  unfold CExpr.unOld
  induction e <;> rw [OldSplit.unOld_eq] <;>
    simp_all [OldSyntax.oldArg?, OldSyntax.mapChildren, CExpr.mapOldChildren, CExpr.mentionsResult]

/-- An expression that reads only the state at the call, and none of whose `OLD`s mentions
`result`, does not mention `result`: `result` is not state at the call. -/
private theorem CExpr.mentionsResult_of_readsOnlyOld (e : CExpr) (h₁ : e.readsOnlyOld = true)
    (h₂ : e.oldsWithoutResult = true) : e.mentionsResult = false := by
  unfold CExpr.readsOnlyOld at h₁
  induction e <;> rw [OldSplit.readsOnlyOld_eq] at h₁ <;>
    simp_all [OldSyntax.oldArg?, OldSyntax.readsState, OldSyntax.children, CExpr.oldChildren,
      CExpr.oldsWithoutResult, CExpr.mentionsResult]

/-- No old part that `splitOld` makes mentions `result`, when no `OLD` of the clause does. By
induction on the clause: a part that `splitOld` moves into `base.old` reads only the state at
the call, which has no result. -/
theorem CExpr.splitOld_oldContents_no_result (e : CExpr) (h : e.oldsWithoutResult = true) :
    ∀ p ∈ e.splitOld.oldContents, p.mentionsResult = false := by
  unfold CExpr.splitOld
  induction e with
  | old a _ =>
    intro p hp
    rw [OldSplit.splitOld_eq] at hp
    split at hp
    · simp only [OldSyntax.mkOld, CExpr.oldContents, List.mem_singleton] at hp
      subst hp
      have := CExpr.mentionsResult_unOld (CExpr.old a)
      simp_all [CExpr.unOld, CExpr.oldsWithoutResult, CExpr.mentionsResult]
    · have := CExpr.mentionsResult_unOld a
      simp_all [OldSyntax.oldArg?, OldSyntax.mkOld, CExpr.oldContents, CExpr.oldsWithoutResult,
        CExpr.unOld]
  | _ =>
    intro p hp
    rw [OldSplit.splitOld_eq] at hp
    split at hp
    · simp only [OldSyntax.mkOld, CExpr.oldContents, List.mem_singleton] at hp
      subst hp
      rw [show OldSplit.unOld _ = CExpr.unOld _ from rfl, CExpr.mentionsResult_unOld]
      apply CExpr.mentionsResult_of_readsOnlyOld <;> simp_all [CExpr.readsOnlyOld]
    · simp_all [OldSyntax.oldArg?, OldSyntax.mapChildren, CExpr.mapOldChildren, CExpr.oldContents,
        CExpr.oldsWithoutResult]
      all_goals first
        | (rcases hp with hp | hp <;> solve_by_elim)
        | solve_by_elim

end -- public section

end StrataPython.Dyn.PySpec
