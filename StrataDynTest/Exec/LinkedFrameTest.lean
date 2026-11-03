/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.CertLink
public import StrataDyn.Examples.While.Elab
public import StrataDyn.Examples.While.Lower
public import StrataDynTest.Exec.FrameTest
import StrataDyn.Env.WF
-- `#guard` runs the lowering, the linker, the checks and the engine as compiled code.
meta import StrataDyn.Exec.CertLink
meta import StrataDyn.Examples.While.Lower
meta import StrataDynTest.Exec.FrameTest
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The frame theorem, on a function that `link` makes from While's table

`store(c, v)`, a While function, writes `v` into the cell `c` and returns what `c` holds.  It
lowers to `while.cellSet` and `while.cellGet`, and `link` makes them instructions that run the
rules' trees, which write and read the cell (`#guard` below).  The linked module's rules are
certified, by `link_rulesOK` from `WhileCert.certified`, so the frame theorem applies.  Started
on a ref to cell `0` from a heap with a second cell `1`, which the arguments do not reach, every
run of `store` leaves cell `1` as it was, at every configuration and at its end
(`store_keeps_unreached`).  The run does change cell `0` and keeps cell `1` (`#guard` below).

The axioms of the main theorem are pinned.
-/

namespace Strata.Dyn.ExecTest.LinkedFrameTest

open Strata.Dyn.Exec
open Strata.Dyn.ExecTest.FrameTest (M A args heap₀ roots_eq wellTagged_cell0 cell1_unreached)

@[expose] public section

/-- `store(c, v)`: write `v` into the cell `c`, then return what `c` holds. -/
def prog : While.Ast.Program := #while
  fun store(c : Cell, v : Int) : Int {
    *c := v;
    return *c;
  }
#end

/-- `lm` is what `link` makes, against While's table, of the module that `prog` lowers to. -/
def Linked (lm : LModule M) : Prop :=
  ∃ m, While.lower prog = .ok m ∧ link WhileSem.model m = .ok lm

/-- **A cell the arguments do not reach is kept, by a module that `link` makes.**  Run from any
heap whose cell `0` holds an integer and that has a cell `1`, every run of the linked `store` on
a ref to cell `0` leaves cell `1` as it was, at every configuration and at its end.  The proof
does not look at `store`'s code: `link_rulesOK` certifies the rules of every linked module. -/
theorem store_keeps_unreached {lm : LModule M} (hl : Linked lm) (hwf : WF lm) {snap : Snapshot M}
    {x : M.interp M.int} (h0 : snap.heap.cells[0]? = some ⟨M.int, x⟩)
    (h1 : 1 < snap.heap.cells.size) {B : Ty} {c : Core M} {hc : CoreOK lm B c}
    (hst : startCore hwf 0 args snap = .ok ⟨B, c, hc⟩) (r : RunFrom hwf ⟨c, .exec, 0, ()⟩ hc)
    (n : Nat) :
    (r.cfg n).Sat (fun c => Kept (· = 1) snap.heap c.1.core.heap)
      (fun f => Kept (· = 1) snap.heap f.snapshot.heap) := by
  obtain ⟨_, -, hl⟩ := hl
  refine frame_startCore (P := (· = 1)) (link_rulesOK WhileCert.certified hl) hst ?_
    (fun l (hl : l = 1) => hl ▸ h1) (fun l (hl : l = 1) => ?_) r n
  · rw [roots_eq]
    exact wellTagged_cell0 h0
  · rw [hl, roots_eq]
    exact cell1_unreached h0

/-- The linked module of `prog`, if it lowers and links. -/
def linked : Option (LModule M) := do
  let m ← (While.lower prog).toOption
  (link WhileSem.model m).toOption

/-- The operations whose rules the linked `store` runs, in order: those of its instructions and
terminators that run a rule's tree. -/
def rules : Option (List String) :=
  linked.bind fun lm => lm.funcs[0]?.map fun g =>
    g.blocks.toList.flatMap fun b =>
      b.insns.filterMap (fun | .sem op .. => some (nameStr op) | _ => none) ++
        match b.term with
        | .sem op .. => [nameStr op]
        | .case .. => []

-- `store` writes and reads its cell through While's rules, and returns through a base rule.
#guard rules == some ["while.cellSet", "while.cellGet", "base.jump"]

/-- What the linked `store`'s run on a ref to cell `0` and `5`, from `heap₀`, returned, and the
integers at locations `0` and `1` of the heap where it ended. -/
def outcome : Option (Int × Int × Int) :=
  match linked with
  | none => none
  | some lm =>
    match hw : checkModule lm with
    | .error _ => none
    | .ok () =>
      match startCore (m := lm) hw 0 args ⟨heap₀, M.w0⟩ with
      | .error _ => none
      | .ok ⟨_, c, hc⟩ =>
        match runFused hw (fun _ => 0) 50 ⟨c, .exec, 0, ()⟩ hc with
        | .done (.ok d) sn _ _ => do
          let int (l : Nat) := (sn.heap.cells[l]?).bind fun d => WhileSem.model.read? (.ok d) Int
          return (← WhileSem.model.read? (.ok d) Int, ← int 0, ← int 1)
        | _ => none

-- The reachable cell is overwritten with `5`, which `store` returns; the unreachable one keeps
-- `2`.
#guard outcome == some (5, 5, 2)

/--
info: 'Strata.Dyn.ExecTest.LinkedFrameTest.store_keeps_unreached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms store_keeps_unreached

end

end Strata.Dyn.ExecTest.LinkedFrameTest
