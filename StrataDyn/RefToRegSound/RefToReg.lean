/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToRegSound.Sound
public import StrataDyn.Exec.CertLink
public import StrataDyn.Exec.Safety

set_option autoImplicit false

/-!
# A target that promotes its source's cells improves on it under every oracle

`refToReg_sound_cell` states, for a model whose rules are certified (`Model.Certified`), that a
linked source and a linked target run alike when the target promotes the source's cells, that
is, when `PromotionOK` relates them: for every start of a function on arguments that hold no ref,
every observation of the world and every oracle, the target's run improves on the source's run
under the same oracle, up to a bad cell.  The two runs show the same, or the source faults with a
bad cell after showing what the target also shows.  This is trace refinement under one oracle
(`Exec.OracleRefines`) whose only excused result is a bad cell.  Promotion keeps every choice, so
the oracle is shared; trace refinement over runs follows (`OracleRefines.refines`).
`refToReg_sound` is a weaker corollary: it excuses every wrong result of the source
(`Result.Wrong`), a failed rule or a bad call as well as a bad cell.

A certified run faults with no bad cell unless a rule stops with one itself
(`Exec.never_badCell_startCore`), so when no rule of the linked source does, `refToReg_sound_eq`
gives equal behaviours under every oracle, and `refToReg_sound_runs` the same behaviours of runs
both ways.

These theorems observe the world only, not the number of choices made.  The simulation underneath
(`promote_sim`) also keeps that number, but `Exec.OracleRefines` and `behW` do not observe it, so
a target that makes an extra, unused choice after all of the source's would satisfy them too.
Choices are internal to the machine, and no observer of the program sees how many were made.

The theorems hold for any target that `PromotionOK` relates to the source, and do not mention the
pass.  That `refToReg`'s output, linked, is such a target is the static half of the proof, which
relates the pass's plan, through linking, to the linked code; it is not yet proved.  The rules'
half, that every rule reaches only the cells it is given, comes from the model's certificate
through linking (`link_rulesOK`).
-/

namespace Strata.Dyn.RefToRegSound

open Strata.Dyn.Exec

@[expose] public section

variable (M : Model) (A : Accounts M.at) (hc : M.Certified A) {env : Env Unit} [base ≼ env]
  {α : Type} {m : Module env α} {f : Name} {lm : LModule M.at} {hw : WF lm} {i : Nat}
  (hp : prepare M m f = .ok ⟨lm, hw, i⟩) {lm₁ : LModule M.at} (hw₁ : WF lm₁)
  (hcert : PromotionOK lm lm₁) (hN : lm.Avoids Fault.IsBadCell) (hw0 : A.world M.at.w0 = [])
  (args : List (Dyn M.at.interp)) (hargs : ∀ d ∈ args, A.acct d.1 d.2 = []) {B : Ty}
  {c : Core M.at} {h : CoreOK lm B c} (hs : startCore hw i args .initial = .ok ⟨B, c, h⟩)
include hc hp hcert hw0 hargs hs

/-- **A target that promotes the source's cells improves on it under every oracle, up to a bad
cell**, for a certified model.  If the module `m` links and validates against the model `M` with
function `f` at index `i`, and `PromotionOK` relates the linked source to a well-formed linked
target `lm₁`, then a start of `f` in `m`, on arguments that hold no ref, from the initial
snapshot, whose world holds no ref, has a start at index `i` in `lm₁`, and for every observation
of the world and every oracle the target's run improves on the source's under the same oracle:
the same, or the source faults with a bad cell after what the target shows.  The target need not
come from `refToReg`. -/
theorem refToReg_sound_cell :
    ∃ B₁ c₁ h₁, startCore hw₁ i args .initial = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.at.W → O),
        Exec.OracleRefines hw hw₁ obs Wrong ⟨⟨c, .exec, 0, ()⟩, h⟩ ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩ := by
  obtain ⟨ER, hok⟩ := hcert
  have hr := link_rulesOK hc (link_of_prepare hp)
  exact promote_sound_cell A _ hw hw₁ (hok.withRules A.InsnOK A.TermOK hr.1 hr.2)
    (fun _ h => h) (fun _ h => h) i args .initial (SnapOK.initial hw0)
    (fun d hd => Accounts.dynOK_of_nil (hargs d hd)) hs

/-- **A target that promotes the source's cells improves on it under every oracle**, for a
certified model: `refToReg_sound_cell`, with every wrong result of the source excused, not only
a bad cell.  If the module `m` links and validates against the model `M` with function `f` at
index `i`, and `PromotionOK` relates the linked source to a well-formed linked target `lm₁`,
then a start of `f` in `m`, on arguments that hold no ref, from the initial snapshot, whose world
holds no ref, has a start at index `i` in `lm₁`, and for every observation of the world and
every oracle the target's run improves on the source's under the same oracle: the same, or the
source goes wrong after what the target shows.  The target need not come from `refToReg`: that
the pass's output satisfies `PromotionOK` after linking is not yet proved. -/
theorem refToReg_sound :
    ∃ B₁ c₁ h₁, startCore hw₁ i args .initial = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.at.W → O),
        Exec.OracleRefines hw hw₁ obs Result.Wrong ⟨⟨c, .exec, 0, ()⟩, h⟩
          ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩ :=
  let ⟨B₁, c₁, h₁, hs₁, himp⟩ := refToReg_sound_cell M A hc hp hw₁ hcert hw0 args hargs hs
  ⟨B₁, c₁, h₁, hs₁, fun obs => (himp obs).mono fun _ => wrong_of_badCell⟩

include hN in
/-- **A target that promotes the source's cells keeps its behaviour under every oracle exactly**,
for a certified model, when no rule of the source stops with a bad cell itself. If the module `m`
links and validates against the model `M` with function `f` at index `i`, `PromotionOK` relates the
linked source to a well-formed linked target `lm₁`, and no instruction or terminator of the linked
source stops with `Fault.badCell` itself, then a start of `f` in `m`, on arguments that hold no ref,
from the initial snapshot, whose world holds no ref, has a start at index `i` in `lm₁`, and for
every observation of the world and every oracle, the target's run behaves as the source's run under
the same oracle: no run of the source from that start faults with a bad cell
(`never_badCell_startCore`). -/
theorem refToReg_sound_eq :
    ∃ B₁ c₁ h₁, startCore hw₁ i args .initial = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.at.W → O) (oracle : Nat → Nat),
        behW hw₁ obs (oracleRun hw₁ oracle ⟨c₁, .exec, 0, ()⟩ h₁) =
          behW hw obs (oracleRun hw oracle ⟨c, .exec, 0, ()⟩ h) :=
  let ⟨B₁, c₁, h₁, hs₁, himp⟩ := refToReg_sound_cell M A hc hp hw₁ hcert hw0 args hargs hs
  ⟨B₁, c₁, h₁, hs₁, fun obs oracle =>
    (himp obs oracle).eq fun t x hb ⟨l, hx⟩ => by
      obtain ⟨n, fin, he, -, rfl⟩ := (oracleRun hw oracle ⟨c, .exec, 0, ()⟩ h).beh_eq_term_iff.mp hb
      have hsafe := never_badCell_startCore (link_rulesOK hc (link_of_prepare hp)) hN hs
        (Snapshot.ok_initial hw0) hargs (oracleRun hw oracle ⟨c, .exec, 0, ()⟩ h) n
      rw [he] at hsafe
      exact hsafe l hx⟩

include hN in
/-- **A target that promotes the source's cells keeps the behaviours of runs**, for a certified
model, when no rule of the source stops with a bad cell itself. If the module `m` links and
validates against the model `M` with function `f` at index `i`, `PromotionOK` relates the linked
source to a well-formed linked target `lm₁`, and no instruction or terminator of the linked source
stops with `Fault.badCell` itself, then a start of `f` in `m`, on arguments that hold no ref, from
the initial snapshot, whose world holds no ref, has a start at index `i` in `lm₁`, and for every
observation of the world, every run of the target behaves as some run of the source, and every run
of the source as some run of the target. -/
theorem refToReg_sound_runs :
    ∃ B₁ c₁ h₁, startCore hw₁ i args .initial = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.at.W → O),
        (∀ r₁ : RunFrom hw₁ ⟨c₁, .exec, 0, ()⟩ h₁, ∃ r : RunFrom hw ⟨c, .exec, 0, ()⟩ h,
          behW hw₁ obs r₁ = behW hw obs r) ∧
        ∀ r : RunFrom hw ⟨c, .exec, 0, ()⟩ h, ∃ r₁ : RunFrom hw₁ ⟨c₁, .exec, 0, ()⟩ h₁,
          behW hw₁ obs r₁ = behW hw obs r :=
  let ⟨B₁, c₁, h₁, hs₁, heq⟩ := refToReg_sound_eq M A hc hp hw₁ hcert hN hw0 args hargs hs
  ⟨B₁, c₁, h₁, hs₁, fun obs =>
    behW_runs_of_oracle (c := ⟨⟨c, .exec, 0, ()⟩, h⟩) (c₁ := ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩) (heq obs)⟩

end

end Strata.Dyn.RefToRegSound
