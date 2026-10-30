/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Clause

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
  induction e <;> simp_all [CExpr.unOld, CExpr.mentionsResult]

/-- An expression that reads only the state at the call, and none of whose `OLD`s mentions
`result`, does not mention `result`: `result` is not state at the call. -/
private theorem CExpr.mentionsResult_of_readsOnlyOld (e : CExpr) (h₁ : e.readsOnlyOld = true)
    (h₂ : e.oldsWithoutResult = true) : e.mentionsResult = false := by
  induction e <;> simp_all [CExpr.readsOnlyOld, CExpr.oldsWithoutResult, CExpr.mentionsResult]

/-- No old part that `splitOld` makes mentions `result`, when no `OLD` of the clause does. By
induction on the clause: a part that `splitOld` moves into `base.old` reads only the state at
the call, which has no result. -/
theorem CExpr.splitOld_oldContents_no_result (e : CExpr) (h : e.oldsWithoutResult = true) :
    ∀ p ∈ e.splitOld.oldContents, p.mentionsResult = false := by
  induction e with
  | old a _ =>
    intro p hp
    unfold CExpr.splitOld at hp
    split at hp <;> simp_all [CExpr.oldContents, CExpr.oldsWithoutResult, CExpr.mentionsResult_unOld,
      CExpr.mentionsResult]
  | _ =>
    intro p hp
    unfold CExpr.splitOld at hp
    split at hp
    · simp only [CExpr.oldContents, List.mem_singleton] at hp
      subst hp
      rw [CExpr.mentionsResult_unOld]
      apply CExpr.mentionsResult_of_readsOnlyOld <;> simp_all
    · simp_all [CExpr.oldContents, CExpr.oldsWithoutResult]
      all_goals first
        | (rcases hp with hp | hp <;> solve_by_elim)
        | solve_by_elim

end -- public section

end StrataPython.Dyn.PySpec
