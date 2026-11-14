/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToRegSound.Promote
public import StrataDyn.Exec.Run

set_option autoImplicit false

/-!
# A certified promotion improves on the source under every oracle

`promote_sim` is the step diagram (`step_good`) as a simulation of the machine under one
oracle (`Exec.simOfDiagram`), whose only wrong results are bad cells (`Wrong`);
`promote_refines_cell` turns it, for every oracle, into trace refinement under one oracle
(`Exec.oracleRefines_of_sim_obsCfg`).
`promote_sound_cell` is the theorem: for linked modules that `ModOK` certifies, with rules whose
trees respect the heap's typing, every start of function `i` of the source on arguments that hold
no promoted cell, from a snapshot whose values are valid, has a start of the same function of the
target, and for every observation of the world and every oracle, the target's run improves on the
source's run under the same oracle (`Exec.OracleRefines`): the same, or the source faults with a
bad cell after what the target shows.  A promotion keeps every choice, so the oracle is shared,
and a source run that faults frees only the target run that made the same choices.  Trace
refinement over runs (`Exec.Refines`) follows by `OracleRefines.refines`.  `promote_sound` is a
weaker corollary, which excuses every wrong result of the source (`Result.Wrong`).  The
simulation observes the world and the number of choices made (`obsCfg`); the theorems observe the
world only (`obsW`).
-/

namespace Strata.Dyn.RefToRegSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel} (A : Accounts M) (X : CertEnv M) {B B₁ : Ty} (hwf : WF X.m)
  (hwf₁ : WF X.m₁) (hok : ModOK X) (hR : ∀ i, X.R i → A.InsnOK i)
  (hRT : ∀ t, X.RT t → A.TermOK t) (oracle : Nat → Nat) {O : Type} [DecidableEq O]
  (obs : M.W → O)

include hok hR hRT in
/-- The step diagram, as a simulation of the machine's traces that keeps the observation of the
world and the choices, whose only wrong results are bad cells. -/
def promote_sim :
    Trace.Sim (stepAt hwf oracle (B := B)) (stepAt hwf₁ oracle (B := B₁)) (obsCfg obs) (obsCfg obs)
      Final.result Final.result Wrong :=
  simOfDiagram hwf hwf₁ oracle (Rel A X) measure Wrong obs (fun hr => ⟨hr.1, hr.2.1⟩)
    (step_good hwf hwf₁ hok hR hRT oracle)

include hok hR hRT in
/-- **Corresponding states refine under every oracle**: the target's run from a state
corresponding to a source state improves on the source's run under the same oracle, where the
only wrong results are bad cells. -/
theorem promote_refines_cell {s s₁ : State M} {h : StateOK X.m B s}
    {h₁ : StateOK X.m₁ B₁ s₁} (hr : Rel A X s s₁) :
    Exec.OracleRefines hwf hwf₁ obs Wrong ⟨s, h⟩ ⟨s₁, h₁⟩ :=
  oracleRefines_of_sim_obsCfg obs fun oracle =>
    ⟨promote_sim A X hwf hwf₁ hok hR hRT oracle obs, _, .refl _, hr⟩

/-- A bad cell is a wrong result. -/
theorem wrong_of_badCell {r : Result M.interp} : Wrong r → Result.Wrong r
  | ⟨_, h⟩ => h ▸ trivial

/-- A snapshot whose values are all valid, in the typing of its own heap. -/
def SnapOK (snap : Snapshot M) : Prop :=
  HeapInv A [] snap.heap ∧ (typOff snap.heap []).AllValid (A.world snap.world)

variable {A} in
omit [DecidableEq O] in
/-- The engine's start, an empty heap and the initial world, is a snapshot whose values are valid
when the initial world holds no ref. -/
theorem SnapOK.initial (hw : A.world M.w0 = []) : SnapOK A (.initial : Snapshot M) :=
  ⟨⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩, by
    show (typOff (.initial : Snapshot M).heap []).AllValid (A.world M.w0)
    rw [hw]
    exact Typing.allValid_nil _⟩

include hok hR hRT in
/-- **A certified promotion improves on the source under every oracle, up to a bad cell.**  If
`ModOK` certifies the linked module `X.m₁` against `X.m`, and every rule of the source respects
the heap's typing (`hR`, `hRT`), then a start of function `i` of `X.m` on arguments `args`, valid
in the typing of the snapshot `snap`'s heap, from a snapshot whose values are valid, has a start
of function `i` of `X.m₁`, and for every observation `obs` of the world and every oracle, the
target's run improves on the source's run under the same oracle, where the only wrong results are
bad cells. -/
theorem promote_sound_cell (i : Nat) (args : List (Dyn M.interp)) (snap : Snapshot M)
    (hsnap : SnapOK A snap) (hargs : ∀ d ∈ args, A.DynOK (typOff snap.heap []) d)
    {c : Core M} {h : CoreOK X.m B c} (hs : startCore hwf i args snap = .ok ⟨B, c, h⟩) :
    ∃ B₁ c₁ h₁, startCore hwf₁ i args snap = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.W → O),
        Exec.OracleRefines hwf hwf₁ obs Wrong ⟨⟨c, .exec, 0, ()⟩, h⟩ ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩ := by
  obtain ⟨fn, b, hf, hb, ha, rfl, rfl⟩ := startCore_ok hs
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hf
  obtain ⟨hi₁, E, hB, hst, -, -, -⟩ := hok.funcs i hi
  obtain ⟨h0, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨h0₁, -⟩ := hB 0 h0
  have hf₁ : X.m₁.funcs[i]? = some (X.m₁.funcs[i]'hi₁) := Array.getElem?_eq_getElem hi₁
  have hb₁ : (X.m₁.funcs[i]'hi₁).blocks[0]? = some ((X.m₁.funcs[i]'hi₁).blocks[0]'h0₁) :=
    Array.getElem?_eq_getElem h0₁
  have ha₁ : args.map (·.1) = ((X.m₁.funcs[i]'hi₁).blocks[0]'h0₁).paramTys := by
    rw [ha]
    have := hst.1
    rw [paramsOf_eq h0, paramsOf_eq h0₁] at this
    exact this.symm
  refine ⟨_, _, _, startCore_eq_ok hwf₁ hf₁ hb₁ ha₁ snap,
    fun obs => promote_refines_cell A X hwf hwf₁ hok hR hRT obs ?_⟩
  have hl : ∀ (bb : LBlock M), args.map (·.1) = bb.paramTys →
      args.length + ([] : List Ty).length = bb.params.length := by
    intro bb hbb
    have := congrArg List.length hbb
    simp only [List.length_map, LBlock.paramTys] at this
    simpa using this
  obtain ⟨hF, hnp⟩ := start_frameOK (P := []) (heap := snap.heap) hB hst
    (Array.getElem?_eq_getElem h0) hb₁ (ds := args) .nil
    (fun d hd => hargs d (by simpa [Args.toList] using hd)) (hl _ ha) (hl _ ha₁)
    (fresh_fits _) (fresh_fits _) (WF.fits_of_getElem? hwf hf (Array.getElem?_eq_getElem h0))
    (WF.fits_of_getElem? hwf₁ hf₁ hb₁)
  exact ⟨rfl, rfl, [], [_], [], ⟨rfl, fun _ _ => rfl, fun _ h => (nomatch h), rfl⟩, hsnap.1,
    hsnap.2, .exec hF, .nil, ⟨fun l hl => (hnp l hl).elim, trivial⟩⟩

include hok hR hRT in
/-- **A certified promotion improves on the source under every oracle.**  If `ModOK` certifies
the linked module `X.m₁` against `X.m`, and every rule of the source respects the heap's typing
(`hR`, `hRT`), then a start of function `i` of `X.m` on arguments `args`, valid in the typing of
the snapshot `snap`'s heap, from a snapshot whose values are valid, has a start of function `i`
of `X.m₁`, and for every observation `obs` of the world and every oracle, the target's run
improves on the source's run under the same oracle. -/
theorem promote_sound (i : Nat) (args : List (Dyn M.interp)) (snap : Snapshot M)
    (hsnap : SnapOK A snap) (hargs : ∀ d ∈ args, A.DynOK (typOff snap.heap []) d)
    {c : Core M} {h : CoreOK X.m B c} (hs : startCore hwf i args snap = .ok ⟨B, c, h⟩) :
    ∃ B₁ c₁ h₁, startCore hwf₁ i args snap = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.W → O),
        Exec.OracleRefines hwf hwf₁ obs Result.Wrong ⟨⟨c, .exec, 0, ()⟩, h⟩
          ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩ :=
  let ⟨B₁, c₁, h₁, hs₁, himp⟩ :=
    promote_sound_cell A X hwf hwf₁ hok hR hRT i args snap hsnap hargs hs
  ⟨B₁, c₁, h₁, hs₁, fun obs => (himp obs).mono fun _ => wrong_of_badCell⟩

end

end Strata.Dyn.RefToRegSound
