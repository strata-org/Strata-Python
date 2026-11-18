/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.DemoteSound.Cert
public import StrataDyn.RefToRegSound.RefToReg

set_option autoImplicit false

/-!
# A certified demotion runs as its padded original

`demote_sound_eq` gives equality of world-observed behaviours under every oracle;
`demote_sound_runs` gives the same behaviours over all runs, in both directions. The demoted
module is the source of a certified promotion, and its padded original is the target, so both
results reuse ref-to-reg's soundness without another simulation. Padding is computed from the
original and the supplied function-entry prefixes (`DemotionOK`): padding reads only earlier
padding results, and writes only added slots; regions are unchanged. The theorems never mention
the pass.

The proofs use only the promotion half of `DemotionOK`. Its freshness half does not make the
theorems hold: it restricts what may be called a padding, for the comparison with the unpadded
original, which is not proved here. The theorems go from a start of the demoted module to a
start of the padded original, as ref-to-reg's go from its source; the converse is not stated.

The hypotheses are ref-to-reg's: a certified model; the demoted module linked and validated by
`prepare`; a validated padded original; a start from the initial snapshot, with no refs in the
arguments or initial world; and no rule of the demoted module that stops with a bad cell itself
(`LModule.Avoids`). These are hypotheses, not obligations discharged for the pass here.

The observation is of the world, not of step counts or choices. No fixed-fuel comparison is
claimed. Neither that `demote`'s linked output satisfies `DemotionOK`, nor that the padded
original runs as the original, is proved here. A padding that the certificate accepts cannot
fault: it is constants, total functions and allocations. What separates the padded original
from the original is that an allocation renumbers the cells made after it. `demote`'s
defaults are literals and constructors; in the execution table generated for the environment,
they link to constants and total functions.
-/

namespace Strata.Dyn.DemoteSound

open Strata.Dyn.Exec

@[expose] public section

variable (M : Model) (A : Accounts M.at) (hc : M.Certified A) {env : Env Unit} [base ≼ env]
  {α : Type} {m : Module env α} {f : Name} {demoted : LModule M.at} {hw : WF demoted} {i : Nat}
  (hp : prepare M m f = .ok ⟨demoted, hw, i⟩) {original : LModule M.at}
  {padding : Padding M.at} (hw₁ : WF (padding.apply original))
  (hcert : DemotionOK original demoted padding) (hN : demoted.Avoids Fault.IsBadCell)
  (hw0 : A.world M.at.w0 = []) (args : List (Dyn M.at.interp))
  (hargs : ∀ d ∈ args, A.acct d.1 d.2 = []) {B : Ty} {c : Core M.at}
  {h : CoreOK demoted B c} (hs : startCore hw i args .initial = .ok ⟨B, c, h⟩)
include hc hp hcert hN hw0 hargs hs

/-- **A certified demotion runs as its padded original under every oracle.** From a start of the
linked demoted module under ref-to-reg's safety hypotheses, there is a start of the same function
of the computed padded original whose world-observed behaviour agrees under every oracle.
This does not compare with the unpadded original or certify the output of the pass. -/
theorem demote_sound_eq :
    ∃ B₁ c₁ h₁, startCore hw₁ i args .initial = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.at.W → O) (oracle : Nat → Nat),
        behW hw₁ obs (oracleRun hw₁ oracle ⟨c₁, .exec, 0, ()⟩ h₁) =
          behW hw obs (oracleRun hw oracle ⟨c, .exec, 0, ()⟩ h) :=
  RefToRegSound.refToReg_sound_eq M A hc hp hw₁ hcert.2 hN hw0 args hargs hs

/-- **A certified demotion and its padded original have the same behaviours of runs.** Every
run from the corresponding starts behaves as some run of the other module, in both directions,
for every observation of the world. The hypotheses and scope are those of `demote_sound_eq`;
there is no bound on steps or comparison of runs on fixed fuel. -/
theorem demote_sound_runs :
    ∃ B₁ c₁ h₁, startCore hw₁ i args .initial = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.at.W → O),
        (∀ r₁ : RunFrom hw₁ ⟨c₁, .exec, 0, ()⟩ h₁, ∃ r : RunFrom hw ⟨c, .exec, 0, ()⟩ h,
          behW hw₁ obs r₁ = behW hw obs r) ∧
        ∀ r : RunFrom hw ⟨c, .exec, 0, ()⟩ h, ∃ r₁ : RunFrom hw₁ ⟨c₁, .exec, 0, ()⟩ h₁,
          behW hw₁ obs r₁ = behW hw obs r :=
  RefToRegSound.refToReg_sound_runs M A hc hp hw₁ hcert.2 hN hw0 args hargs hs

end

end Strata.Dyn.DemoteSound
