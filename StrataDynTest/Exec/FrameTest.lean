/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Frame
public import StrataDyn.Examples.While.Cert
import StrataDyn.Env.WF
-- `#guard` runs the checks and the engine as compiled code.
meta import StrataDyn.Exec.Frame
meta import StrataDyn.Examples.While.Cert
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The frame theorem, on a function that writes through its argument

`bump(r, v)` writes `v` into the cell `r` names and returns `v`, at While's run model, linked by
hand.  Started on a ref to cell `0` from a heap with a second cell `1`:

* cell `1` is not reachable from the arguments and the world, so the frame theorem says that
  every configuration of the run, ended or not, leaves it unchanged (`bump_keeps_unreached`);
* cell `0` is reachable (`cell0_reached`), so the theorem says nothing of it, and the run does
  change it (`#guard` below): the hypothesis matters.

The axioms of the main theorems are pinned.
-/

namespace Strata.Dyn.ExecTest.FrameTest

open Strata.Dyn.Exec

@[expose] public section

/-- While's run model. -/
abbrev M : RunModel := WhileSem.model.at

/-- While's accounts. -/
abbrev A : Accounts M := WhileCert.accounts

/-- A return of `v`. -/
def retOf (v : Nat) : LTerm M := .case [] [[]] (Exit.here .nil) [] [⟨.exit, [v]⟩]

/-- `bump(r, v)`, with `r v u` at slots `0`–`2`:
```
entry(r, v): u = refSet r v; ret v
``` -/
def bump : LBody M where
  name := .base
  ret := M.int
  slots := 3
  params := [Ty.ref M.int, M.int]
  blocks := #[⟨Label.exit, [(0, Ty.ref M.int), (1, M.int)], [], [.refSet 2 M.int 0 1], retOf 1⟩]

/-- `bump`'s code pointer, as a value. -/
def bumpPtr : Dyn M.interp := ⟨Ty.fn [Ty.ref M.int, M.int] M.int, M.fnAt _ _ 0⟩

/-- `bump`'s code pointer holds no ref: it captures nothing. -/
theorem bumpPtr_acct : A.acct _ bumpPtr.2 = [] := by
  show A.acct _ (M.fnAt _ _ 0) = []
  rw [A.fn, M.fnOf_fnAt]
  rfl

/-- The module of `bump`. -/
def lm : LModule M := ⟨#[bump], #[]⟩

/-- The arguments: a ref to cell `0` and the integer `5`. -/
def args : List (Dyn M.interp) := [⟨Ty.ref M.int, M.cellAt M.int 0⟩, ⟨M.int, M.ofInt 5⟩]

/-- `bump`'s rules are certified: a machine write and a return. -/
theorem rulesOK : lm.RulesOK A := by
  refine ⟨fun g hg b hb => ?_, fun g hg => absurd hg (by simp [lm])⟩
  simp only [lm, List.mem_toArray, List.mem_singleton] at hg
  subst hg
  simp only [bump, List.mem_toArray, List.mem_singleton] at hb
  subst hb
  exact ⟨fun i hi => by simp only [List.mem_singleton] at hi; subst hi; trivial,
    fun _ => trivial⟩

/-- An integer holds no ref. -/
theorem acct_int (x : M.interp M.int) : A.acct M.int x = [] := rfl

/-- The refs of the arguments and the world: cell `0`, at the integers' tag. -/
theorem roots_eq (w : M.W) : startRoots A args w = [.cell 0 M.int] := by
  simp only [startRoots, args, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [A.ref, M.locOf_cellAt, acct_int]
  rfl

/-- From cell `0`, whose contents are an integer, only cell `0` is reached. -/
private theorem reached_eq {heap : Heap M} {x : M.interp M.int}
    (h0 : heap.cells[0]? = some ⟨M.int, x⟩) {p : Loc}
    (h : Reachable A heap [.cell 0 M.int] p) : p = .cell 0 M.int := by
  induction h with
  | root hp => exact List.mem_singleton.mp hp
  | cell _ hd hp ih =>
    cases ih
    rw [h0] at hd
    cases hd
    exact absurd hp (by rw [acct_int]; exact List.not_mem_nil)
  | caps _ _ _ _ ih => exact nomatch ih

/-- From cell `0`, whose contents are an integer, every ref reached names a cell of its tag. -/
theorem wellTagged_cell0 {heap : Heap M} {x : M.interp M.int}
    (h0 : heap.cells[0]? = some ⟨M.int, x⟩) : WellTagged A heap [.cell 0 M.int] := by
  refine ⟨fun l t h => ?_, fun k h => nomatch reached_eq h0 h⟩
  cases reached_eq h0 h
  obtain ⟨hl, he⟩ := Array.getElem?_eq_some_iff.mp h0
  exact ⟨hl, by rw [he]⟩

/-- From cell `0`, whose contents are an integer, cell `1` is not reached. -/
theorem cell1_unreached {heap : Heap M} {x : M.interp M.int}
    (h0 : heap.cells[0]? = some ⟨M.int, x⟩) : ¬ ReachesCell A heap [.cell 0 M.int] 1 :=
  fun ⟨_, ht⟩ => nomatch reached_eq h0 ht

/-- **A cell the arguments do not reach is kept.**  Run from any heap whose cell `0` holds an
integer and that has a cell `1`, every run of `bump` on a ref to cell `0` leaves cell `1` as it
was, at every configuration and at its end. -/
theorem bump_keeps_unreached (hwf : WF lm) {snap : Snapshot M} {x : M.interp M.int}
    (h0 : snap.heap.cells[0]? = some ⟨M.int, x⟩) (h1 : 1 < snap.heap.cells.size) {B : Ty}
    {c : Core M} {hc : CoreOK lm B c} (hst : startCore hwf 0 args snap = .ok ⟨B, c, hc⟩)
    (r : RunFrom hwf ⟨c, .exec, 0, ()⟩ hc) (n : Nat) :
    (r.cfg n).Sat (fun c => Kept (· = 1) snap.heap c.1.core.heap)
      (fun f => Kept (· = 1) snap.heap f.snapshot.heap) := by
  refine frame_startCore (P := (· = 1)) rulesOK hst ?_ (fun l (hl : l = 1) => hl ▸ h1)
    (fun l (hl : l = 1) => ?_) r n
  · rw [roots_eq]
    exact wellTagged_cell0 h0
  · rw [hl, roots_eq]
    exact cell1_unreached h0

/-- **The twin: cell `0` is reachable**, so the frame theorem does not apply to it. -/
theorem cell0_reached (heap : Heap M) (w : M.W) : ReachesCell A heap (startRoots A args w) 0 :=
  ⟨M.int, .root (by rw [roots_eq]; exact List.mem_singleton_self _)⟩

/-- The heap of two integer cells, `1` and `2`. -/
def heap₀ : Heap M := { cells := #[⟨M.int, M.ofInt 1⟩, ⟨M.int, M.ofInt 2⟩] }

/-- The integer at location `l` of the heap where `bump`'s run from `heap₀` ends. -/
def cellAfter (l : Nat) : Option Int :=
  match hw : checkModule lm with
  | .error _ => none
  | .ok () =>
    match startCore (m := lm) hw 0 args ⟨heap₀, M.w0⟩ with
    | .error _ => none
    | .ok ⟨_, c, hc⟩ =>
      match runFused hw (fun _ => 0) 20 ⟨c, .exec, 0, ()⟩ hc with
      | .done _ sn _ _ => (sn.heap.cells[l]?).bind fun d => WhileSem.model.read? (.ok d) Int
      | .timeout .. => none

-- The reachable cell is overwritten with `5`; the unreachable one keeps `2`.
#guard cellAfter 0 == some 5
#guard cellAfter 1 == some 2

/--
info: 'Strata.Dyn.Exec.frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms frame

/--
info: 'Strata.Dyn.Exec.frame_startCore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms frame_startCore

/--
info: 'Strata.Dyn.Exec.step_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms step_inv

/--
info: 'Strata.Dyn.ExecTest.FrameTest.bump_keeps_unreached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bump_keeps_unreached

end

end Strata.Dyn.ExecTest.FrameTest
