/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Util.Trace.Backward

set_option autoImplicit false

/-!
# Dropping an unused choice

The source is `tmp := choose; x := choose; return x` and the target drops the first, unused,
choice: `x := choose; return x`.  Both are oracle machines that read the oracle at `drawn`.

* Compared under one oracle for both, with choices observed through `drawn`, the drop is not an
  improvement, so no forward simulation under one oracle exists (`a_not_improves`, `a_no_sim`).
  It fails even when choices are not observed, since the target's `x` reads the answer that the
  source spent on `tmp` (`a_not_improves_x`).
* Over runs of the relations, without observing choices, it is a trace refinement
  (`b_refines`), by a backward simulation with a measure (`dropB`), or one whose matches take one
  or more steps on both sides (`dropJ`).
* With oracles, it is "for every target oracle, some source oracle" (`a₁_refines`), from
  `b_refines` and `Oracle.refines_iff`.
* Trace refinement under one oracle is strictly stronger than trace refinement over runs: a
  source that goes wrong on one answer is refined over runs by any target (`w_any_refines`), but
  under one oracle only by a target that agrees on the other answers (`w_oracle_fails`,
  `w_oracle_ok`).
-/

namespace Strata.Dyn.ChoiceTest

open Strata.Dyn.Trace

/-- A state: the program counter, the variables `x` and `tmp`, and the choices made. -/
structure St where
  pc : Nat
  x : Nat
  tmp : Nat
  drawn : Nat

/-- The source, `tmp := choose; x := choose; return x`, under the oracle `o`. -/
def src (o : Nat → Nat) : St → Config St Nat
  | ⟨0, x, _, d⟩ => .running ⟨1, x, o d, d + 1⟩
  | ⟨1, _, t, d⟩ => .running ⟨2, o d, t, d + 1⟩
  | ⟨_, x, _, _⟩ => .ended x

/-- The target, `x := choose; return x`, under the oracle `o`. -/
def tgt (o : Nat → Nat) : St → Config St Nat
  | ⟨0, _, t, d⟩ => .running ⟨2, o d, t, d + 1⟩
  | ⟨_, x, _, _⟩ => .ended x

/-- The start. -/
def s₀ : St := ⟨0, 0, 0, 0⟩

/-- No result is wrong. -/
def noWrong : Nat → Prop := fun _ => False

/-- What the current library observes: `x`, and the choices made. -/
def obsD (s : St) : Nat × Nat := (s.x, s.drawn)

/-! ## One oracle for both, choices observed -/

/-- Under the oracle that always answers `0`, the drop is not an improvement: the source makes
two choices and the target one. -/
theorem a_not_improves :
    ¬ Improves noWrong ((Run.ofFun (tgt fun _ => 0) s₀).beh obsD id)
      ((Run.ofFun (src fun _ => 0) s₀).beh obsD id) := by
  rw [Run.beh_ended _ (n := 2) (f := 0) rfl, Run.beh_ended _ (n := 3) (f := 0) rfl]
  rintro (h | ⟨_, _, _, hw, _⟩)
  · exact nomatch h
  · exact hw

/-- **The drop has no forward simulation under one oracle**: for the oracle that always answers
`0`, there is none from related starts. -/
theorem a_no_sim :
    ¬ ∀ o, ∃ sim : Sim (src o) (tgt o) obsD obsD id id noWrong, sim.rel s₀ s₀ := by
  intro h
  obtain ⟨sim, hr⟩ := h fun _ => 0
  exact a_not_improves (sim.improves hr _)

/-- Even observing `x` alone, one oracle for both fails: under the oracle `id`, the source returns
`1` and the target `0`. -/
theorem a_not_improves_x :
    ¬ Improves noWrong ((Run.ofFun (tgt id) s₀).beh St.x id)
      ((Run.ofFun (src id) s₀).beh St.x id) := by
  rw [Run.beh_ended _ (n := 2) (f := 0) rfl, Run.beh_ended _ (n := 3) (f := 1) rfl]
  rintro (h | ⟨_, _, _, hw, _⟩)
  · exact nomatch h
  · exact hw

/-! ## Runs of the relations, choices not observed -/

/-- The source is not about to choose `x`, and agrees with the target on where it is and `x`. -/
def rel (s t : St) : Prop := s.pc = t.pc ∧ s.x = t.x ∧ s.pc ≠ 1

/-- **The drop, as a backward simulation with a measure.** The target's step from the start is
matched by the source's two: the unused choice, which changes nothing observed, then the choice
of `x` with the answer the target got.  No target step goes unmatched, so the measure is `0`. -/
def dropB : BSimStep (Oracle.Rel src) (Oracle.Rel tgt) St.x St.x id id noWrong where
  rel := rel
  measure _ := 0
  obs_eq h := h.2.1
  next := by
    rintro ⟨sp, sx, stmp, sd⟩ ⟨tp, tx, ttmp, td⟩ t₁ ⟨hp, hx, h₁⟩ ⟨o, ho⟩
    change sp = tp at hp
    change sx = tx at hx
    change sp ≠ 1 at h₁
    subst hp hx
    left
    match sp, ho, h₁ with
    | 0, ho, _ =>
      cases ho
      exact ⟨_, .cons ⟨fun _ => 0, rfl⟩ rfl
        (.last ⟨fun _ => o td, rfl⟩ ⟨rfl, rfl, (by decide : (2 : Nat) ≠ 1)⟩)⟩
    | 1, _, h₁ => exact absurd rfl h₁
    | _ + 2, ho, _ => exact nomatch ho
  final := by
    rintro ⟨sp, sx, stmp, sd⟩ ⟨tp, tx, ttmp, td⟩ g ⟨hp, hx, h₁⟩ ⟨o, ho⟩
    change sp = tp at hp
    change sx = tx at hx
    change sp ≠ 1 at h₁
    subst hp hx
    match sp, ho, h₁ with
    | 0, ho, _ => exact nomatch ho
    | 1, _, h₁ => exact absurd rfl h₁
    | _ + 2, ho, _ =>
      cases ho
      exact ⟨_, .last ⟨fun _ => 0, rfl⟩ (.inr rfl)⟩

/-- **The drop, as a backward simulation whose matches take steps on both sides.** -/
def dropJ : BSim (Oracle.Rel src) (Oracle.Rel tgt) St.x St.x id id noWrong where
  rel := rel
  obs_eq h := h.2.1
  «match» := by
    rintro ⟨sp, sx, stmp, sd⟩ ⟨tp, tx, ttmp, td⟩ ⟨hp, hx, h₁⟩ r
    change sp = tp at hp
    change sx = tx at hx
    change sp ≠ 1 at h₁
    subst hp hx
    obtain ⟨o, ho⟩ := r.next r.start
    refine ⟨0, ?_⟩
    rcases sp with _ | _ | sp
    · exact ⟨_, .single r.start, .cons ⟨fun _ => 0, rfl⟩ rfl
        (.last ⟨fun _ => o td, rfl⟩ ⟨_, ho.symm, rfl, rfl, (by decide : (2 : Nat) ≠ 1)⟩)⟩
    · exact absurd rfl h₁
    · exact ⟨_, .single r.start, .last ⟨fun _ => 0, rfl⟩ (.inr ⟨_, ho.symm, rfl⟩)⟩

/-- **Dropping the unused choice is a trace refinement**: every run of the target improves on some
run of the source. -/
theorem b_refines : Refines (Oracle.Rel src) (Oracle.Rel tgt) St.x St.x id id noWrong s₀ s₀ :=
  dropB.toBSim.refines ⟨rfl, rfl, by decide⟩

/-- Dropping the unused choice is a trace refinement, proved by the backward simulation whose
matches take steps on both sides (`dropJ`). -/
theorem b_refines_J : Refines (Oracle.Rel src) (Oracle.Rel tgt) St.x St.x id id noWrong s₀ s₀ :=
  dropJ.refines ⟨rfl, rfl, by decide⟩

/-! ## Oracles: for every target oracle, some source oracle -/

/-- The source reads the oracle only at `drawn`. -/
theorem src_local : Oracle.Local src St.drawn := by
  rintro o o₁ ⟨pc, x, t, d⟩ h
  change o d = o₁ d at h
  match pc with
  | 0 => show Config.running _ = Config.running _; rw [h]
  | 1 => show Config.running _ = Config.running _; rw [h]
  | _ + 2 => rfl

/-- The source's choices are counted. -/
theorem src_advance : Oracle.Advance src St.drawn := by
  rintro o ⟨pc, x, t, d⟩ s₁ h
  match pc, h with
  | 0, h => cases h; exact ⟨Nat.le_succ d, fun h => absurd h (Nat.succ_ne_self d)⟩
  | 1, h => cases h; exact ⟨Nat.le_succ d, fun h => absurd h (Nat.succ_ne_self d)⟩
  | _ + 2, h => exact nomatch h

/-- The target reads the oracle only at `drawn`. -/
theorem tgt_local : Oracle.Local tgt St.drawn := by
  rintro o o₁ ⟨pc, x, t, d⟩ h
  change o d = o₁ d at h
  match pc with
  | 0 => show Config.running _ = Config.running _; rw [h]
  | _ + 1 => rfl

/-- The target's choices are counted. -/
theorem tgt_advance : Oracle.Advance tgt St.drawn := by
  rintro o ⟨pc, x, t, d⟩ s₁ h
  match pc, h with
  | 0, h => cases h; exact ⟨Nat.le_succ d, fun h => absurd h (Nat.succ_ne_self d)⟩
  | _ + 1, h => exact nomatch h

/-- **For every target oracle, some source oracle** whose trace the target's improves on. -/
theorem a₁_refines : ∀ oₜ, ∃ oₛ,
    Improves noWrong ((Oracle.run tgt oₜ s₀).beh St.x id) ((Oracle.run src oₛ s₀).beh St.x id) :=
  (Oracle.refines_iff src_local src_advance tgt_local tgt_advance s₀ s₀).mp b_refines

/-! ## Long runs without a run that never ends

`choose n`, then count down from `n`: every run ends, yet for every `N` some run is still going
after `N` steps.  A choice over `Nat` branches infinitely, so König's lemma does not apply, and
divergence over a relation has to be one infinite run, not runs of every length. -/

/-- Choose `n`, then count down to `0`, then end. -/
inductive KStep : Option Nat → Config (Option Nat) Unit → Prop where
  | pick (n : Nat) : KStep none (.running (some n))
  | down (n : Nat) : KStep (some (n + 1)) (.running (some n))
  | stop : KStep (some 0) (.ended ())

/-- The run that chooses `N`. -/
def kDet (N : Nat) : Option Nat → Config (Option Nat) Unit
  | none => .running (some N)
  | some (n + 1) => .running (some n)
  | some 0 => .ended ()

/-- The run that chooses `N` counts down. -/
theorem kDet_trace (N : Nat) : ∀ j, j ≤ N → trace (kDet N) (some N) j = .running (some (N - j))
  | 0, _ => rfl
  | j + 1, hj => by
    rw [trace_succ, kDet_trace N j (Nat.le_of_succ_le hj)]
    show kDet N (some (N - j)) = _
    rw [show N - j = (N - (j + 1)) + 1 by omega]
    rfl

/-- **Runs of every length.** For every `N`, some run is still going after `N` steps. -/
theorem k_long (N : Nat) : ∃ r : Run KStep none, ∃ s, r.cfg N = .running s := by
  let r : Run KStep none := Run.ofDet (kDet N) id (fun _ => True)
    (fun _ c _ _ => by cases c <;> trivial)
    (fun q _ => by
      match q with
      | none => exact .pick N
      | some (n + 1) => exact .down n
      | some 0 => exact .stop) none trivial
  refine ⟨r, ?_⟩
  cases N with
  | zero => exact ⟨none, rfl⟩
  | succ N =>
    refine ⟨some 1, ?_⟩
    show (trace (kDet (N + 1)) none (N + 1)).mapS id = _
    rw [trace_succ_running (f := kDet (N + 1)) (s := none) rfl N,
      kDet_trace (N + 1) N (Nat.le_succ N),
      show N + 1 - N = 1 by omega]
    rfl

/-- A run that is counting down keeps counting. -/
theorem k_count {r : Run KStep none} {n : Nat} (h₁ : r.cfg 1 = .running (some n)) :
    ∀ j, j ≤ n → r.cfg (1 + j) = .running (some (n - j))
  | 0, _ => h₁
  | j + 1, hj => by
    have ih := k_count h₁ j (Nat.le_of_succ_le hj)
    have hs := r.next ih
    rw [show n - j = (n - (j + 1)) + 1 by omega] at hs
    generalize hc : r.cfg (1 + j + 1) = c at hs
    cases hs
    rfl

/-- **No run diverges.** -/
theorem k_not_diverges : ¬ Diverges KStep none := by
  rintro ⟨r, hr⟩
  have h₀ := r.next r.start
  cases hc : r.cfg (0 + 1) with
  | ended f => rw [hc] at h₀; exact nomatch h₀
  | running s =>
    rw [hc] at h₀
    cases h₀ with
    | pick n =>
      have h₁ := k_count hc n (Nat.le_refl n)
      rw [Nat.sub_self] at h₁
      have hs := r.next h₁
      obtain ⟨s₁, hs₁⟩ := hr (1 + n + 1)
      rw [hs₁] at hs
      cases hs

/-! ## Trace refinement under one oracle against trace refinement over runs

The source makes one choice, goes wrong (result `1`) on the answer `7` and returns `0` on any
other.  One target returns `42`, the other `0`. -/

/-- The source: one choice, wrong on `7`, `0` otherwise. -/
def wSrc (o : Nat → Nat) : Nat → Config Nat Nat
  | 0 => if o 0 = 7 then .ended 1 else .ended 0
  | _ => .ended 0

/-- A target that returns `42`. -/
def wTgt (_ : Nat → Nat) : Nat → Config Nat Nat
  | _ => .ended 42

/-- A target that returns `0`. -/
def wTgt₀ (_ : Nat → Nat) : Nat → Config Nat Nat
  | _ => .ended 0

/-- The wrong result. -/
def wWrong (r : Nat) : Prop := r = 1

/-- **Over runs, any target refines the source**, since the source's run on `7` goes wrong at
once. -/
theorem w_any_refines :
    Refines (Oracle.Rel wSrc) (Oracle.Rel wTgt) (fun _ => ()) (fun _ => ()) id id wWrong 0 0 := by
  intro rₜ
  refine ⟨Oracle.run wSrc (fun _ => 7) 0, .inr ⟨[()], 1, ?_, rfl, ?_⟩⟩
  · exact Run.beh_ended _ (n := 1) rfl
  · exact (rₜ.beh_extends_iff).mpr ⟨0, List.prefix_refl _⟩

/-- **Under one oracle, the target that returns `42` does not refine the source**: under an
oracle that answers `0`, the source returns `0`. -/
theorem w_oracle_fails :
    ¬ Oracle.Refines wSrc wTgt (fun _ => ()) (fun _ => ()) id id wWrong 0 0 := by
  intro h
  have h₀ := h (fun _ => 0)
  rw [Run.beh_ended (Oracle.run wTgt (fun _ => 0) 0) (n := 1) (f := 42) rfl,
    Run.beh_ended (Oracle.run wSrc (fun _ => 0) 0) (n := 1) (f := 0) rfl] at h₀
  rcases h₀ with h | ⟨_, _, h, hw, _⟩
  · cases h
  · cases h; exact Nat.zero_ne_one hw

/-- **Under one oracle, the target that returns `0` refines the source**: the source going wrong
on `7` excuses the target only under oracles that answer `7`. -/
theorem w_oracle_ok :
    Oracle.Refines wSrc wTgt₀ (fun _ => ()) (fun _ => ()) id id wWrong 0 0 := by
  intro o
  by_cases h₇ : o 0 = 7
  · have he : (Oracle.run wSrc o 0).cfg 1 = .ended 1 := by
      show trace (wSrc o) 0 1 = _
      simp [trace, wSrc, h₇]
    refine .inr ⟨[()], 1, ?_, rfl, ?_⟩
    · rw [Run.beh_ended (obs := fun _ => ()) (res := id) _ he,
        Run.obsUpTo_ended (Oracle.run wSrc o 0) (n := 0) he]
      rfl
    · exact ((Oracle.run wTgt₀ o 0).beh_extends_iff).mpr ⟨0, List.prefix_refl _⟩
  · have he : (Oracle.run wSrc o 0).cfg 1 = .ended 0 := by
      show trace (wSrc o) 0 1 = _
      simp [trace, wSrc, h₇]
    left
    rw [Run.beh_ended (Oracle.run wTgt₀ o 0) (n := 1) (f := 0) rfl, Run.beh_ended _ (n := 1) he,
      Run.obsUpTo_ended (Oracle.run wTgt₀ o 0) (n := 0) (f := 0) rfl,
      Run.obsUpTo_ended _ (n := 0) he]
    rfl

/-- Trace refinement under one oracle gives trace refinement over runs, here for the target
that returns `0`. -/
theorem w_ok_refines :
    Refines (Oracle.Rel wSrc) (Oracle.Rel wTgt₀) (fun _ => ()) (fun _ => ()) id id wWrong 0 0 :=
  Oracle.Refines.refines (idxₜ := fun _ => 0) (fun _ _ _ _ => rfl)
    (fun _ _ _ h => by simp [wTgt₀] at h) w_oracle_ok

end Strata.Dyn.ChoiceTest
