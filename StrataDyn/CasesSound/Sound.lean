/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.CasesSound.Sim
public import StrataDyn.Exec.Run

set_option autoImplicit false

/-!
# A certified case lowering keeps the behaviour under every oracle

`cases_sim` is the step diagram (`step_match`) as a simulation of the machine under one oracle
(`Exec.simOfDiagram`) with no wrong result: a source step is matched by a target step and then
silent ones, so the simulation needs no measure.  `cases_refines` turns it, for every oracle, into
trace refinement under one oracle with no wrong result, which is equality of behaviours.

`lowering_sound` is the theorem: for validated linked modules that `LoweringOK` relates, every
start of function `i` of the source, on any arguments and from any snapshot, has a start of the
same function of the target on them, and for every observation of the world and every oracle the
target's run behaves as the source's run under the same oracle: the same outputs, the same
result or fault, or both diverge.  `lowering_sound_runs` is the form over all runs: every run of
the target behaves as some run of the source, and every run of the source as some run of the
target.  Neither bounds the steps: the target takes more, so a run on a fixed fuel is not
compared.

The theorems need no certified model and no condition on the arguments or the snapshot: the heap
and the world are the same on both sides, and the rules run on the same operands.  They hold for
any target that `LoweringOK` relates to the source, and do not mention the pass.  That the
output of `cases`, linked, is such a target, with the accessors' laws for the model's
instructions, is not proved here.
-/

namespace Strata.Dyn.CasesSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel} {bound : Nat → Nat} {m m₁ : LModule M} {B B₁ : Ty} (hwf : WF m)
  (hwf₁ : WF m₁) (hok : CasesOK bound m m₁) (oracle : Nat → Nat) {O : Type} [DecidableEq O]
  (obs : M.W → O)

include hok in
/-- The step diagram, as a simulation of the machine's traces that keeps the observation of the
world and the choices, with no wrong result. -/
def cases_sim :
    Trace.Sim (stepAt hwf oracle (B := B)) (stepAt hwf₁ oracle (B := B₁)) (obsCfg obs) (obsCfg obs)
      Final.result Final.result (fun _ => False) :=
  simOfDiagram hwf hwf₁ oracle (Match bound) (fun _ => 0) (fun _ => False) obs
    (fun hm => ⟨hm.1, hm.2.1.world⟩) (step_match hwf hwf₁ hok oracle)

include hok in
/-- **Corresponding states behave alike under every oracle**: the target's run from a state that
corresponds to a source state improves on the source's run under the same oracle, with no wrong
result. -/
theorem cases_refines {s : State M} {h : StateOK m B s} {c₁ : Cfg m₁ B₁}
    (hr : Match bound s c₁.1) :
    Exec.OracleRefines hwf hwf₁ obs (fun _ => False) ⟨s, h⟩ c₁ :=
  oracleRefines_of_sim_obsCfg obs fun oracle =>
    ⟨cases_sim hwf hwf₁ hok oracle obs, c₁, .refl _, hr⟩

omit [DecidableEq O] in
/-- **A certified case lowering keeps the behaviour under every oracle.**  If `LoweringOK`
relates the validated linked module `m₁` to `m`, then a start of function `i` of `m` on
arguments `args` from the snapshot `snap` has a start of function `i` of `m₁`, and for every
observation `obs` of the world and every oracle, the target's run behaves as the source's run
under the same oracle. -/
theorem lowering_sound (hcert : LoweringOK m m₁) (i : Nat) (args : List (Dyn M.interp))
    (snap : Snapshot M) {c : Core M} {h : CoreOK m B c}
    (hs : startCore hwf i args snap = .ok ⟨B, c, h⟩) :
    ∃ B₁ c₁ h₁, startCore hwf₁ i args snap = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.W → O) (oracle : Nat → Nat),
        behW hwf₁ obs (oracleRun hwf₁ oracle ⟨c₁, .exec, 0, ()⟩ h₁) =
          behW hwf obs (oracleRun hwf oracle ⟨c, .exec, 0, ()⟩ h) := by
  obtain ⟨bound, hok⟩ := hcert
  obtain ⟨fn, b, hf, hb, ha, rfl, rfl⟩ := startCore_ok hs
  obtain ⟨g₁, β, hg₁, hsl, hB⟩ := hok.funcs i fn hf
  obtain ⟨b₁, hb₁, hps, -⟩ := hB.2 0 b hb
  rw [hB.1] at hb₁
  have ha₁ : args.map (·.1) = b₁.paramTys := by
    rw [ha]
    unfold LBlock.paramTys
    rw [hps]
  refine ⟨_, _, _, startCore_eq_ok hwf₁ hg₁ hb₁ ha₁ snap, fun obs oracle => ?_⟩
  have hm : Match bound
      ⟨⟨Frame.entry fn b (freshStore M fn.slots) args .nil (fresh_fits fn)
          (hwf.fits_of_getElem? hf hb), [], snap.heap, snap.world⟩, .exec, 0, ()⟩
      ⟨⟨Frame.entry g₁ b₁ (freshStore M g₁.slots) args .nil (fresh_fits g₁)
          (hwf₁.fits_of_getElem? hg₁ hb₁), [], snap.heap, snap.world⟩, .exec, 0, ()⟩ := by
    exact Match.of ⟨rfl, rfl, .nil⟩ (.exec (entry_rel hB hb hb₁ (envRel_freshStore hsl)
      Array.size_replicate args .nil (fresh_fits fn) (hwf.fits_of_getElem? hf hb) (fresh_fits g₁)
      (hwf₁.fits_of_getElem? hg₁ hb₁)))
  exact (cases_refines hwf hwf₁ hok obs
    (c₁ := ⟨⟨_, .exec, 0, ()⟩, start_ok hwf₁ hg₁ hb₁ ha₁ snap⟩) hm oracle).eq fun _ _ _ hw => hw

omit [DecidableEq O] in
/-- **A certified case lowering keeps the behaviours of runs.**  If `LoweringOK` relates the
validated linked module `m₁` to `m`, then a start of function `i` of `m` on arguments `args`
from the snapshot `snap` has a start of function `i` of `m₁`, and for every observation of the
world, every run of the target behaves as some run of the source, and every run of the source as
some run of the target. -/
theorem lowering_sound_runs (hcert : LoweringOK m m₁) (i : Nat) (args : List (Dyn M.interp))
    (snap : Snapshot M) {c : Core M} {h : CoreOK m B c}
    (hs : startCore hwf i args snap = .ok ⟨B, c, h⟩) :
    ∃ B₁ c₁ h₁, startCore hwf₁ i args snap = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.W → O),
        (∀ r₁ : RunFrom hwf₁ ⟨c₁, .exec, 0, ()⟩ h₁, ∃ r : RunFrom hwf ⟨c, .exec, 0, ()⟩ h,
          behW hwf₁ obs r₁ = behW hwf obs r) ∧
        ∀ r : RunFrom hwf ⟨c, .exec, 0, ()⟩ h, ∃ r₁ : RunFrom hwf₁ ⟨c₁, .exec, 0, ()⟩ h₁,
          behW hwf₁ obs r₁ = behW hwf obs r :=
  let ⟨B₁, c₁, h₁, hs₁, heq⟩ := lowering_sound hwf hwf₁ hcert i args snap hs
  ⟨B₁, c₁, h₁, hs₁, fun obs =>
    behW_runs_of_oracle (c := ⟨⟨c, .exec, 0, ()⟩, h⟩) (c₁ := ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩) (heq obs)⟩

end

end Strata.Dyn.CasesSound
