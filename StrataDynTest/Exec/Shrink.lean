/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# Shrinking a failing program

A front end's fuzzer finds a program on which its semantics and the source language's
implementation disagree.  Such a program is large, so it is shrunk to a small one that fails the
same way, for the owner of the bug.  This file holds the shrink loop, which knows nothing of the
programs: a *proposer* gives the smaller candidates of a program, in a fixed order, and a *judge*
says of a batch of candidates which ones still fail the same way.

The loop is greedy.  Each step judges the candidates of the current program in batches, in the
proposer's order, and moves to the first kept candidate in that order; it stops when no candidate
is kept, or when `budget` candidates have been judged in all.  So when the budget isn't reached,
the result depends only on the proposer and the judge, not on the size of a batch or on how a
batch is run.

`shrink` is the loop, with its `Result`. `ShrinkProps.lean` proves, in any lawful monad, that it
judges at most `budget` candidates, and that it ends with its start or with a candidate that the
judge kept; Lean has no `LawfulMonad` instance for `IO`, so this doesn't cover a judge in `IO`. The
loop is a test tool, so it lives in this test library; it stays language-neutral, for any front
end's fuzzer.
-/

namespace Strata.Dyn.Exec.Shrink

/-- The end of a shrink: the last program kept (the original if none was), the number of
candidates judged, and the number of steps taken (each step keeps one candidate). -/
public structure Result (α : Type) where
  best : α
  calls : Nat
  steps : Nat
  deriving Repr, DecidableEq

/-- The first candidate of `cs` that the verdicts `vs` keep (`true`), in the order of `cs`; a
candidate without a verdict isn't kept. -/
@[expose] public def firstKept {α : Type} : List α → List Bool → Option α
  | c :: cs, v :: vs => if v then some c else firstKept cs vs
  | _, _ => none

/-- One step's search: the candidates `cs` are judged in batches of `batch` (at least one),
judging at most `budget` candidates, until a batch keeps one.  It gives the first kept candidate
and the number of candidates judged.  `fuel` bounds the batches; `cs.length` is enough, because
each batch judges at least one candidate. -/
@[expose] public def search {m : Type → Type} [Monad m] {α : Type} (judge : List α → m (List Bool))
    (batch : Nat) : (fuel budget : Nat) → List α → m (Option α × Nat)
  | 0, _, _ => pure (none, 0)
  | fuel + 1, budget, cs =>
    if budget = 0 || cs.isEmpty then pure (none, 0) else do
      let now := cs.take (min (max batch 1) budget)
      let vs ← judge now
      match firstKept now vs with
      | some c => pure (some c, now.length)
      | none =>
        let (r, n) ← search judge batch fuel (budget - now.length) (cs.drop now.length)
        pure (r, now.length + n)

/-- The steps of `shrink` from the program `x`, with `calls` candidates judged and `steps` steps
taken so far; `fuel` bounds the steps (`budget` is enough, because each step judges at least one
candidate). -/
@[expose] public def loop {m : Type → Type} [Monad m] {α : Type} (propose : α → m (List α))
    (judge : List α → m (List Bool)) (batch budget : Nat) :
    (fuel : Nat) → α → (calls steps : Nat) → m (Result α)
  | 0, x, calls, steps => pure ⟨x, calls, steps⟩
  | fuel + 1, x, calls, steps => do
    let cs ← propose x
    let (r, n) ← search judge batch cs.length (budget - calls) cs
    match r with
    | some y => loop propose judge batch budget fuel y (calls + n) (steps + 1)
    | none => pure ⟨x, calls + n, steps⟩

/-- Shrink `x`: move to the first candidate of `propose` that `judge` keeps, judging batches of
`batch` candidates, until no candidate is kept or `budget` candidates have been judged. -/
@[expose] public def shrink {m : Type → Type} [Monad m] {α : Type} (propose : α → m (List α))
    (judge : List α → m (List Bool)) (batch budget : Nat) (x : α) : m (Result α) :=
  loop propose judge batch budget budget x 0 0

end Strata.Dyn.Exec.Shrink
