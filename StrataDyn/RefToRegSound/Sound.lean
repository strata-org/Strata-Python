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

`promote_sim` packs the step diagram (`step_good`) as a simulation of the machine under one
oracle (`Trace.Sim`), whose only wrong results are bad cells (`Wrong`); `promote_refines_cell`
turns it, for every oracle, into trace refinement under one oracle
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
      Final.result Final.result Wrong where
  rel s s₁ := Rel A X s.1 s₁.1
  measure s := measure s.1
  obs_eq hr := by
    obtain ⟨hd, hw, -⟩ := hr
    simp only [obsCfg, hd, hw]
  next {s t s₁} hr hs := by
    have hg := step_good hwf hwf₁ hok hR hRT oracle s.2 t.2 hr
    simp only [stepAt] at hs
    revert hg
    cases he : Exec.step hwf oracle s.1 s.2 with
    | final r hp w d => rw [he] at hs; exact nomatch hs
    | next e s₂ h₂ =>
      rw [he] at hs
      cases hs
      intro hg
      rcases hg with ⟨e₁, t₁, h₃, he₁, hr₁⟩ | ⟨hlt, hr₁⟩
      · refine Or.inl ⟨0, t, ⟨t₁, h₃⟩, .refl _, ?_, hr₁⟩
        simp only [stepAt, he₁, StepR.config]
      · exact Or.inr ⟨hlt, hr₁⟩
  final {s t f} hr hs := by
    have hg := step_good hwf hwf₁ hok hR hRT oracle s.2 t.2 hr
    simp only [stepAt] at hs
    revert hg
    cases he : Exec.step hwf oracle s.1 s.2 with
    | next e s₂ h₂ => rw [he] at hs; exact nomatch hs
    | final r₀ hp w d =>
      rw [he] at hs
      cases hs
      intro hg
      rcases hg with hw | ⟨hp₁, he₁⟩
      · exact Or.inl hw
      · refine Or.inr ⟨0, t, ⟨r₀, ⟨hp₁, w⟩, d⟩, .refl _, ?_, rfl⟩
        simp only [stepAt, he₁, StepR.config]

include hok hR hRT in
/-- **Corresponding states refine under every oracle**: the target's run from a state
corresponding to a source state improves on the source's run under the same oracle, where the
only wrong results are bad cells. -/
theorem promote_refines_cell {s s₁ : State M} {h : StateOK X.m B s}
    {h₁ : StateOK X.m₁ B₁ s₁} (hr : Rel A X s s₁) :
    Exec.OracleRefines hwf hwf₁ obs Wrong ⟨s, h⟩ ⟨s₁, h₁⟩ :=
  oracleRefines_of_sim_obsCfg obs fun oracle =>
    ⟨promote_sim A X hwf hwf₁ hok hR hRT oracle obs, hr⟩

/-- A bad cell is a wrong result. -/
theorem wrong_of_badCell {r : Result M.interp} : Wrong r → Result.Wrong r
  | ⟨_, h⟩ => h ▸ trivial

omit [DecidableEq O] in
/-- What a successful start is: the function and its entry block, and arguments that fit it. -/
private theorem startCore_ok {m : LModule M} {hwf : WF m} {i : Nat} {args : List (Dyn M.interp)}
    {snap : Snapshot M} {B : Ty} {c : Core M} {h : CoreOK m B c}
    (hs : startCore hwf i args snap = .ok ⟨B, c, h⟩) :
    ∃ fn b, ∃ (hf : m.funcs[i]? = some fn) (hb : fn.blocks[0]? = some b),
      args.map (·.1) = b.paramTys ∧
      B = fn.ret ∧ c = { top := Frame.entry fn b (freshStore M fn.slots) args .nil (fresh_fits fn)
                                  (hwf.fits_of_getElem? hf hb),
                         conts := [], heap := snap.heap, world := snap.world } := by
  unfold startCore at hs
  cases he : entry? m i args with
  | error e => rw [he] at hs; exact nomatch hs
  | ok p =>
    obtain ⟨⟨fn, b⟩, hf, hb, ha⟩ := p
    rw [he] at hs
    simp only [Except.map, Except.ok.injEq] at hs
    obtain ⟨rfl, hc⟩ := Sigma.mk.inj hs
    obtain rfl := congrArg Subtype.val (eq_of_heq hc).symm
    exact ⟨fn, b, hf, hb, ha, rfl, rfl⟩

omit [DecidableEq O] in
/-- Function `i`, with an entry block that the arguments fit, starts. -/
private theorem entry?_ok {m : LModule M} {i : Nat} {fn : LBody M} {b : LBlock M}
    {args : List (Dyn M.interp)} (hf : m.funcs[i]? = some fn) (hb : fn.blocks[0]? = some b)
    (ha : args.map (·.1) = b.paramTys) : ∃ p, entry? m i args = .ok p ∧ p.1 = (fn, b) := by
  unfold entry?
  rw [hf]
  dsimp only
  split
  · rename_i he₂; rw [hb] at he₂; exact nomatch he₂
  · rename_i b₁ he₂
    rw [hb] at he₂
    cases he₂
    rw [dite_eq_left_of_eq_true (eq_true ha)]
    exact ⟨_, rfl, rfl⟩

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
  obtain ⟨⟨⟨fn₂, b₂⟩, hf₂, hb₂, ha₂⟩, he₁, hp₁⟩ := entry?_ok (m := X.m₁) hf₁ hb₁ ha₁
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp₁
  have hs₁ : startCore hwf₁ i args snap = .ok ⟨_, _, start_ok hwf₁ hf₁ hb₁ ha₁ snap⟩ := by
    unfold startCore
    rw [he₁]
    rfl
  refine ⟨_, _, _, hs₁, fun obs => promote_refines_cell A X hwf hwf₁ hok hR hRT obs ?_⟩
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
    hsnap.2, ⟨_, rfl, hF⟩, trivial, ⟨fun l hl => (hnp l hl).elim, trivial⟩⟩

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
