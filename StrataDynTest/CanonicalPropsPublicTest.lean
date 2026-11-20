/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataDyn.CanonicalProps
import StrataDyn.Exec.MachineProps
import StrataDyn.Exec.LinkProps

/-! # The theorems that later stages cite

`docs/Dyn.md` and `StrataDyn/Canonical.lean` tell a stage that checks loop invariants or places
contract obligations to cite `Body.Preheader.root_ne`, `.transfer_head_latch`, `.atLoop_of_path_head` and
`.transfer_head_of_not_isHead`, which rest on `Body.dom_of_atLoop`, `.transfer_head` and
`.atLoop_of_path`.  For how a run leaves a body, `docs/Dyn.md` names `Exec.step_ret` and
`Exec.linkSite_target_exit`, and the headers of `StrataDyn/Exec/MachineProps.lean` and
`LinkProps.lean` also name `Body.leaves_iff`.  This file imports their modules without
`import all`, as such a stage does, and states each theorem again, so that it fails if one of them
becomes private or its statement changes. -/

namespace Strata.Dyn.CanonicalPropsPublicTest

open Strata.Dyn Strata.Dyn.Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)}

example {h : Label} {w : Point} (hw : AtLoop bs h w) : Dom bs ⟨h, 0⟩ w :=
  dom_of_atLoop hw

example {h : Label} {pre : Block env α} (hp : Preheader bs h pre) : root bs ≠ ⟨h, 0⟩ :=
  hp.root_ne

example {h : Label} {pre : Block env α} (hp : Preheader bs h pre) {u : Point}
    (ht : Transfer bs u h) : u = endOf pre ∨ IsBackEdge bs u h :=
  hp.transfer_head ht

example {h : Label} {pre l : Block env α} (hp : Preheader bs h pre) (hl : Latch bs h l)
    {u : Point} (ht : Transfer bs u h) : u = endOf pre ∨ u = endOf l :=
  hp.transfer_head_latch hl ht

example {h : Label} {pre : Block env α} (hp : Preheader bs h pre) (hh : ¬ IsHead bs h)
    {u : Point} (ht : Transfer bs u h) : u = endOf pre :=
  hp.transfer_head_of_not_isHead hh ht

example {h : Label} {pre : Block env α} (hp : Preheader bs h pre) {x y : Point}
    (hxy : PathAvoid bs (endOf pre) x y) (hy : AtLoop bs h y) : AtLoop bs h x :=
  hp.atLoop_of_path hxy hy

example {h : Label} {pre : Block env α} (hp : Preheader bs h pre) (hh : IsHead bs h) {x : Point}
    (hx : PathAvoid bs (endOf pre) x ⟨h, 0⟩) : AtLoop bs h x :=
  hp.atLoop_of_path_head hh hx

example {u : Point} :
    Leaves bs u ↔ ∃ b ∈ bs, b.label = u.label ∧
      ((∃ i, b.instrs[u.count]? = some i ∧ ∃ s ∈ i.succs, s.label = Label.exit) ∨
        (u.count = b.instrs.size ∧ ∃ s ∈ b.term.succs, s.label = Label.exit)) :=
  leaves_iff

example {M : Exec.RunModel} {m : Exec.LModule M} {B : Exec.Ty} (hwf : Exec.WF m)
    (oracle : Nat → Nat) {s : Exec.State M} {h : Exec.StateOK m B s} {ev : Exec.Event}
    {s' : Exec.State M}
    {h' : Exec.StateOK m B s'} {v : Exec.Dyn M.interp}
    (hs : Exec.step hwf oracle s h = .next ev s' h')
    (hm : s'.mode = .ret v) : ∃ f ss, Exec.StepSites s f ss ∧ Exec.LeftByExit f ss v :=
  Exec.step_ret hwf oracle hs hm

example {M : Exec.Model} {labels : LabelMap Nat} {k : Target.Raw} {ctx : Exec.LinkCtx}
    {st st' : Exec.LinkState M} {site : Exec.LSite}
    (h : Exec.linkSite (M := M) labels k ctx st = .ok (site, st')) :
    site.target = .exit ↔ k.label = Label.exit :=
  Exec.linkSite_target_exit h

end Strata.Dyn.CanonicalPropsPublicTest
