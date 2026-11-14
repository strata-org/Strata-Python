/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Shrink
public import StrataDynTest.Exec.ShrinkProps
meta import StrataDynTest.Exec.Shrink

set_option autoImplicit false

/-!
# The shrink loop on lists of numbers

A program is a list of numbers; its candidates drop one element each, in order.  A candidate is
kept when it still holds both 3 and 7, so a smallest failing program is `[3, 7]` or `[7, 3]`.
-/

namespace Strata.Dyn.Exec.ShrinkTest

open Strata.Dyn.Exec.Shrink

/-- The lists that drop one element of `xs`, the first element first. -/
private meta def dropOne {m : Type → Type} [Monad m] (xs : List Nat) : m (List (List Nat)) :=
  pure ((List.range xs.length).map xs.eraseIdx)

/-- Keeps the lists that hold 3 and 7. -/
private meta def holds37 (cs : List (List Nat)) : Id (List Bool) :=
  cs.map fun c => c.contains 3 && c.contains 7

private meta def start : List Nat := [1, 3, 5, 7, 9, 3]

-- The loop reaches a smallest failing list: `[1, 3, 5, 7, 9, 3]`, `[3, 5, 7, 9, 3]`,
-- `[5, 7, 9, 3]`, `[7, 9, 3]`, `[7, 3]`.
#guard (Id.run (shrink dropOne holds37 8 500 start)).best == [7, 3]
-- It takes one step per dropped element: 6 elements down to 2.
#guard (Id.run (shrink dropOne holds37 8 500 start)).steps == 4
-- When the budget isn't reached, the batch size doesn't change the result, only the number of
-- candidates judged.
#guard (List.range 8).all fun b =>
  (Id.run (shrink dropOne holds37 (b + 1) 500 start)).best == [7, 3]
#guard (Id.run (shrink dropOne holds37 1 500 start)).calls == 7
#guard (Id.run (shrink dropOne holds37 8 500 start)).calls == 20
-- When it is reached, the batch size changes the result: a batch of 8 spends the budget of 3 in
-- its first batch.
#guard Id.run (shrink dropOne holds37 1 3 start) == ⟨[7, 9, 3], 3, 3⟩
#guard Id.run (shrink dropOne holds37 8 3 start) == ⟨[3, 5, 7, 9, 3], 3, 1⟩
-- A batch of 0 judges one candidate at a time.
#guard Id.run (shrink dropOne holds37 0 500 start) == Id.run (shrink dropOne holds37 1 500 start)

-- The first kept candidate in the proposer's order wins: either 3 of `[3, 7, 3]` can go, and the
-- proposer's order says which.
#guard (Id.run (shrink dropOne holds37 8 500 [3, 7, 3])).best == [7, 3]
#guard (Id.run (shrink (fun xs => pure ((List.range xs.length).map xs.eraseIdx).reverse) holds37 8 500 [3, 7, 3])).best == [3, 7]
#guard firstKept [[1], [2], [3]] [false, true, true] == some [2]
#guard firstKept [[1], [2]] [false] == none
#guard firstKept ([] : List (List Nat)) [true] == none

-- The loop stops at the bound of candidates judged (above, a budget of 3); with a budget of 1:
-- `[3, 5, 7, 9, 3]` is the first kept candidate, found by the first call.
#guard (Id.run (shrink dropOne holds37 1 1 start)) == ⟨[3, 5, 7, 9, 3], 1, 1⟩
-- A budget of 0 judges nothing, and keeps the start.
#guard Id.run (shrink dropOne holds37 8 0 start) == ⟨start, 0, 0⟩
-- A start none of whose candidates is kept is its own result, after judging them all once.
#guard Id.run (shrink dropOne holds37 8 500 [3, 7]) == ⟨[3, 7], 2, 0⟩
-- A start with no candidates: nothing is judged.
#guard Id.run (shrink dropOne holds37 8 500 []) == ⟨[], 0, 0⟩

-- The judge sees the batches in order, each of at most `batch` candidates.
private meta def batches (b : Nat) : List (List (List Nat)) :=
  ((shrink (m := StateM (List (List (List Nat)))) dropOne
    (fun cs => do modify (· ++ [cs]); pure (holds37 cs).run) b 500 [1, 2, 3, 7]).run []).2
#guard batches 2 == [[[2, 3, 7], [1, 3, 7]], [[3, 7], [2, 7]], [[7], [3]]]
-- A batch that keeps nothing is followed by the next batch of the same step.
#guard batches 1 == [[[2, 3, 7]], [[3, 7]], [[7]], [[3]]]

-- The theorems of `ShrinkProps.lean` apply to a shrink outside it.
example : (Id.run (shrink (pure ∘ fun xs : List Nat => (List.range xs.length).map xs.eraseIdx)
    (pure ∘ fun cs => cs.map fun c => c.contains 3 && c.contains 7) 8 3 [1, 3, 5, 7, 9, 3])).calls ≤ 3 :=
  shrink_calls_le_id _ _ 8 3 _
example : let r := Id.run (shrink (pure ∘ fun xs : List Nat => (List.range xs.length).map xs.eraseIdx)
    (fun cs => pure (cs.map fun c => c.contains 3 && c.contains 7)) 8 500 [1, 3, 5, 7, 9, 3])
    r.best = [1, 3, 5, 7, 9, 3] ∨ (r.best.contains 3 && r.best.contains 7) = true :=
  shrink_best_id _ _ 8 500 _

-- The general theorems hold in any lawful monad, e.g. a judge with state, whatever it answers.
example (propose : List Nat → StateM Nat (List (List Nat)))
    (judge : List (List Nat) → StateM Nat (List Bool)) :
    Strata.Dyn.Util.Sort.SatisfiesM (fun r : Result (List Nat) => r.calls ≤ 500)
      (shrink propose judge 8 500 [1, 2, 3]) :=
  shrink_calls_le propose judge 8 500 _

end Strata.Dyn.Exec.ShrinkTest
