/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Shrink
public import StrataDyn.Util.SortProps

set_option autoImplicit false

/-!
# Properties of the shrink loop

The key theorems hold in any lawful monad, e.g. a judge with state:
* `shrink_calls_le`: every result of `shrink` has judged at most `budget` candidates, whatever the
  proposer and the judge do;
* `shrink_best`: if the judge keeps only candidates that satisfy a predicate `keep` (`KeepsOnly`),
  every result of `shrink` ends with its start or with a candidate that satisfies `keep`.

`SatisfiesM p x` (from `StrataDyn/Util/SortProps.lean`) says that every result of the monadic
program `x` satisfies `p`. `shrink_calls_le_id` and `shrink_best_id` state the same in the identity
monad, without `SatisfiesM`.

`IO` has no `LawfulMonad` instance, so neither theorem applies to a judge that runs programs in
`IO`; `shrink_best` would also need `KeepsOnly` of such a judge, which no judge that runs programs
can promise. Such a caller checks the result at run time, e.g. by running the kept candidate
again.
-/

namespace Strata.Dyn.Exec.Shrink

open Strata.Dyn.Util.Sort (SatisfiesM)

/-- The first candidate that the verdicts keep is at an index whose verdict is `true`. -/
private theorem firstKept_spec {α : Type} :
    ∀ (cs : List α) (vs : List Bool) (c : α), firstKept cs vs = some c →
      ∃ i : Nat, cs[i]? = some c ∧ vs[i]? = some true := by
  intro cs
  induction cs with
  | nil => intro vs c h; simp [firstKept] at h
  | cons x xs ih =>
    intro vs c h
    cases vs with
    | nil => simp [firstKept] at h
    | cons v vs =>
      simp only [firstKept] at h
      split at h
      · rename_i hv; cases h; exact ⟨0, by simp, by simp [hv]⟩
      · obtain ⟨i, hc, hvi⟩ := ih vs c h
        exact ⟨i + 1, by simpa using hc, by simpa using hvi⟩


/-- Every result of one step's search has judged at most `budget` candidates, whatever the judge
answers. -/
private theorem search_calls_le {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (judge : List α → m (List Bool)) (batch : Nat) :
    ∀ (fuel budget : Nat) (cs : List α),
      SatisfiesM (fun r : Option α × Nat => r.2 ≤ budget) (search judge batch fuel budget cs) := by
  intro fuel
  induction fuel with
  | zero => intro budget cs; exact SatisfiesM.pure' (Nat.zero_le _)
  | succ fuel ih =>
    intro budget cs
    simp only [search]
    split
    · exact SatisfiesM.pure' (Nat.zero_le _)
    · have hlen : (cs.take (min (max batch 1) budget)).length ≤ budget := by
        simp [List.length_take]; omega
      refine SatisfiesM.bind' SatisfiesM.triv fun vs _ => ?_
      split
      · exact SatisfiesM.pure' hlen
      · refine SatisfiesM.bind'
          (ih (budget - (cs.take (min (max batch 1) budget)).length)
            (cs.drop (cs.take (min (max batch 1) budget)).length)) fun r hr => ?_
        obtain ⟨r, n⟩ := r
        exact SatisfiesM.pure' (by simp only at hr ⊢; omega)


/-- The judge's verdicts `vs` on the candidates `cs` keep only candidates that satisfy `keep`: a
candidate whose verdict is `true` satisfies `keep`. -/
@[expose] public def KeepsOnly {α : Type} (keep : α → Prop) (cs : List α) (vs : List Bool) : Prop :=
  ∀ (i : Nat) (c : α), cs[i]? = some c → vs[i]? = some true → keep c

/-- If the judge keeps only candidates that satisfy `keep`, then the candidate that one step's
search finds, if any, satisfies `keep`. -/
private theorem search_kept {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (judge : List α → m (List Bool)) (keep : α → Prop) (batch : Nat)
    (hjudge : ∀ cs, SatisfiesM (KeepsOnly keep cs) (judge cs)) :
    ∀ (fuel budget : Nat) (cs : List α),
      SatisfiesM (fun r : Option α × Nat => ∀ c, r.1 = some c → keep c)
        (search judge batch fuel budget cs) := by
  intro fuel
  induction fuel with
  | zero => intro budget cs; exact SatisfiesM.pure' (by simp)
  | succ fuel ih =>
    intro budget cs
    simp only [search]
    split
    · exact SatisfiesM.pure' (by simp)
    · refine SatisfiesM.bind' (hjudge _) fun vs hvs => ?_
      split
      · rename_i c hc
        refine SatisfiesM.pure' ?_
        intro c' hc'
        cases hc'
        obtain ⟨i, hi, hvi⟩ := firstKept_spec _ _ _ hc
        exact hvs i c hi hvi
      · refine SatisfiesM.bind' (ih _ _) fun r hr => ?_
        obtain ⟨r, n⟩ := r
        exact SatisfiesM.pure' hr

/-- The steps of the loop that start with at most `budget` candidates judged end with at most
`budget` judged: each step's search stays within what is left. -/
private theorem loop_calls_le {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (propose : α → m (List α)) (judge : List α → m (List Bool))
    (batch budget : Nat) :
    ∀ (fuel : Nat) (x : α) (calls steps : Nat), calls ≤ budget →
      SatisfiesM (fun r : Result α => r.calls ≤ budget)
        (loop propose judge batch budget fuel x calls steps) := by
  intro fuel
  induction fuel with
  | zero => intro x calls steps h; exact SatisfiesM.pure' h
  | succ fuel ih =>
    intro x calls steps h
    simp only [loop]
    refine SatisfiesM.bind' SatisfiesM.triv fun cs _ => ?_
    refine SatisfiesM.bind' (search_calls_le judge batch _ (budget - calls) cs)
      fun r hr => ?_
    obtain ⟨r, n⟩ := r
    simp only at hr
    split
    · exact ih _ _ _ (by omega)
    · exact SatisfiesM.pure' (by simp only; omega)

/-- If the judge keeps only candidates that satisfy `keep`, then the steps of the loop end with
their start or with a program that satisfies `keep`. -/
private theorem loop_best {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (propose : α → m (List α)) (judge : List α → m (List Bool))
    (keep : α → Prop) (batch budget : Nat)
    (hjudge : ∀ cs, SatisfiesM (KeepsOnly keep cs) (judge cs)) :
    ∀ (fuel : Nat) (x : α) (calls steps : Nat),
      SatisfiesM (fun r : Result α => r.best = x ∨ keep r.best)
        (loop propose judge batch budget fuel x calls steps) := by
  intro fuel
  induction fuel with
  | zero => intro x calls steps; exact SatisfiesM.pure' (Or.inl rfl)
  | succ fuel ih =>
    intro x calls steps
    simp only [loop]
    refine SatisfiesM.bind' SatisfiesM.triv fun cs _ => ?_
    refine SatisfiesM.bind' (search_kept judge keep batch hjudge _ _ cs)
      fun r hr => ?_
    obtain ⟨r, n⟩ := r
    split
    · rename_i y hry
      have hy : keep y := hr y hry
      refine SatisfiesM.imp (ih y _ _) fun r h => ?_
      rcases h with h | h
      · exact Or.inr (h ▸ hy)
      · exact Or.inr h
    · exact SatisfiesM.pure' (Or.inl rfl)

/-- In any lawful monad, every result of `shrink` has judged at most `budget` candidates, whatever
the proposer and the judge do. -/
public theorem shrink_calls_le {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (propose : α → m (List α)) (judge : List α → m (List Bool))
    (batch budget : Nat) (x : α) :
    SatisfiesM (fun r : Result α => r.calls ≤ budget) (shrink propose judge batch budget x) :=
  loop_calls_le propose judge batch budget budget x 0 0 (Nat.zero_le _)

/-- In any lawful monad, if the judge keeps only candidates that satisfy `keep` (`KeepsOnly`), then
every result of `shrink` ends with its start `x` or with a program that satisfies `keep`: a shrink
never ends on a program that the judge didn't keep. -/
public theorem shrink_best {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (propose : α → m (List α)) (judge : List α → m (List Bool))
    (keep : α → Prop) (batch budget : Nat)
    (hjudge : ∀ cs, SatisfiesM (KeepsOnly keep cs) (judge cs))
    (x : α) :
    SatisfiesM (fun r : Result α => r.best = x ∨ keep r.best)
      (shrink propose judge batch budget x) :=
  loop_best propose judge keep batch budget hjudge budget x 0 0

/-- With a pure judge, `shrink` judges at most `budget` candidates. -/
public theorem shrink_calls_le_id {α : Type} (propose : α → List α) (judge : List α → List Bool)
    (batch budget : Nat) (x : α) :
    (Id.run (shrink (pure ∘ propose) (pure ∘ judge) batch budget x)).calls ≤ budget := by
  obtain ⟨y, hy⟩ := shrink_calls_le (m := Id) (pure ∘ propose) (pure ∘ judge) batch budget x
  rw [← hy]
  exact y.2

/-- With a judge `cs.map keep`, `shrink` ends with its start `x` or with a program that `keep`
keeps. -/
public theorem shrink_best_id {α : Type} (propose : α → List α) (keep : α → Bool)
    (batch budget : Nat) (x : α) :
    let r := Id.run (shrink (pure ∘ propose) (fun cs => pure (cs.map keep)) batch budget x)
    r.best = x ∨ keep r.best = true := by
  have hjudge : ∀ cs : List α, SatisfiesM (m := Id) (KeepsOnly (keep · = true) cs)
      (pure (cs.map keep)) := fun cs => SatisfiesM.pure' fun i c hc hv => by
    rw [List.getElem?_map, hc] at hv
    simpa using hv
  obtain ⟨y, hy⟩ := shrink_best (m := Id) (pure ∘ propose) (fun cs => pure (cs.map keep))
    (keep · = true) batch budget hjudge x
  simp only
  rw [← hy]
  exact y.2

end Strata.Dyn.Exec.Shrink
