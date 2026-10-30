/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Safety
public import StrataDynTest.Exec.FrameTest
public import StrataDynTest.Exec.Programs
import StrataDyn.Env.WF
-- `#guard` runs the checks and the engine as compiled code.
meta import StrataDyn.Exec.Safety
meta import StrataDynTest.Exec.FrameTest
meta import StrataDynTest.Exec.Programs
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Heap safety

`main(v)`, at While's run model, linked by hand, makes a cell holding `v`, calls `bump` on it
(`FrameTest`), which writes `v` into it, and reads it back.  Its rules are certified, and none
stops with a bad cell itself, so from the engine's start, on an integer, no configuration of any run
faults with `Fault.badCell` (`main_never_badCell`), and neither does a run of it from where
another run ended (`main_never_badCell_after`).  Beside it:

* `Ex`'s `retyped(x)` reads, at `Bool`, a cell holding `x`, through the ref that `ex.retype`
  returns; that rule has no certificate (`CertTest.retype_not_certified`), and the run faults
  with a bad cell (`#guard` below);
* `bump` started from the engine's start on a ref to cell `0`, an argument that holds a ref into
  the empty heap, faults with a bad cell: the start's hypothesis matters.

The axioms of the main theorems are pinned.
-/

namespace Strata.Dyn.ExecTest.SafetyTest

open Strata.Dyn.Exec
open Strata.Dyn.ExecTest.FrameTest (M A retOf bump bumpPtr bumpPtr_acct acct_int)

@[expose] public section

/-- `main(v)`, with `v r f x y` at slots `0`–`4`:
```
entry(v): r = refNew v; f = const bump; x = callCode f(r, v); y = refGet r; ret y
``` -/
def main : LBody M where
  name := .num .base 1
  ret := M.int
  slots := 5
  params := [M.int]
  blocks := #[⟨Label.exit, [(0, M.int)], [],
    [.refNew 1 M.int 0, .const 2 bumpPtr, .callCode 3 [Ty.ref M.int, M.int] M.int 2 [1, 0],
      .refGet 4 M.int 1], retOf 4⟩]

/-- The module of `bump` and `main`. -/
def lm : LModule M := ⟨#[bump, main], #[]⟩

/-- The module's rules are certified: a constant that holds no ref, the machine's cell
instructions, a machine call and returns. -/
theorem rulesOK : lm.RulesOK A := by
  refine ⟨fun g ⟨hg⟩ b ⟨hb⟩ => ?_, fun g ⟨hg⟩ => nomatch hg⟩
  rcases hg with _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩
  · rcases hb with _ | ⟨_, ⟨⟩⟩
    exact ⟨fun i hi => by rcases hi with _ | ⟨_, ⟨⟩⟩; trivial, fun _ => trivial⟩
  · rcases hb with _ | ⟨_, ⟨⟩⟩
    refine ⟨fun i hi => ?_, fun _ => trivial⟩
    rcases hi with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩⟩⟩
    · trivial
    · exact bumpPtr_acct
    · trivial
    · trivial

/-- No rule of the module stops with a bad cell itself: it has machine instructions and `case`
terminators only, which run no tree. -/
theorem avoids : lm.Avoids Fault.IsBadCell := by
  refine ⟨fun g ⟨hg⟩ b ⟨hb⟩ => ?_, fun g ⟨hg⟩ => nomatch hg⟩
  rcases hg with _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩
  · rcases hb with _ | ⟨_, ⟨⟩⟩
    exact ⟨fun i hi => by rcases hi with _ | ⟨_, ⟨⟩⟩; trivial, trivial⟩
  · rcases hb with _ | ⟨_, ⟨⟩⟩
    refine ⟨fun i hi => ?_, trivial⟩
    rcases hi with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩⟩⟩ <;> trivial

/-- The argument: the integer `5`. -/
def args : List (Dyn M.interp) := [⟨M.int, M.ofInt 5⟩]

/-- The argument holds no ref. -/
theorem args_nil : ∀ d ∈ args, A.acct d.1 d.2 = []
  | _, .head _ => acct_int _

/-- **A certified run never faults on a cell.**  From the engine's start, `main` on `5` faults
with `Fault.badCell` at no configuration of any run. -/
theorem main_never_badCell (hwf : WF lm) {B : Ty} {c : Core M} {hc : CoreOK lm B c}
    (hst : startCore hwf 1 args .initial = .ok ⟨B, c, hc⟩) (r : RunFrom hwf ⟨c, .exec, 0, ()⟩ hc)
    (n : Nat) :
    (r.cfg n).Sat
      (fun c => ∀ l, c.1.mode ≠ .done (.fault (.badCell l)))
      (fun f => ∀ l, f.result ≠ .fault (.badCell l)) :=
  never_badCell_startCore rulesOK avoids hst (Snapshot.ok_initial rfl) args_nil r n

/-- **Nor does a run from where another ended.**  If a run of `lm` from a state where
the run invariant holds ends at `f`, then `main` on `5`, started from `f`'s snapshot, faults
with `Fault.badCell` at no configuration of any run. -/
theorem main_never_badCell_after (hwf : WF lm) {B₀ : Ty} {s : State M} {h : StateOK lm B₀ s}
    {T : Typing} (hs : A.Inv (fun _ => False) s.core.heap T s) (r₀ : RunFrom hwf s h) {k : Nat}
    {f : Final M} (he : r₀.cfg k = .ended f) {B : Ty} {c : Core M}
    {hc : CoreOK lm B c} (hst : startCore hwf 1 args f.snapshot = .ok ⟨B, c, hc⟩)
    (r : RunFrom hwf ⟨c, .exec, 0, ()⟩ hc) (n : Nat) :
    (r.cfg n).Sat
      (fun c => ∀ l, c.1.mode ≠ .done (.fault (.badCell l)))
      (fun f => ∀ l, f.result ≠ .fault (.badCell l)) :=
  never_badCell_startCore rulesOK avoids hst (ended_ok rulesOK (fun _ h => h.elim) hs r₀ he)
    args_nil r n

/-- How a run of function `i` of `lm` on `as` from the engine's start ended: its fault, or its
integer. -/
def outcome (i : Nat) (as : List (Dyn M.interp)) : Option (Fault ⊕ Int) :=
  match hw : checkModule lm with
  | .error _ => none
  | .ok () =>
    match startCore (m := lm) hw i as .initial with
    | .error _ => none
    | .ok ⟨_, c, hc⟩ =>
      match runFused hw (fun _ => 0) 50 ⟨c, .exec, 0, ()⟩ hc with
      | .done (.ok d) _ _ _ => (WhileSem.model.read? (.ok d) Int).map .inr
      | .done (.fault f) _ _ _ => some (.inl f)
      | .timeout .. => none

-- The certified run returns the value `bump` wrote.
#guard outcome 1 args == some (.inr 5)

-- The twin on its start: `bump` on a ref to cell `0` of the empty heap faults at its write.
#guard outcome 0 FrameTest.args == some (.inl (.badCell 0))

/--
info: 'Strata.Dyn.Exec.never_badCell' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms never_badCell

/--
info: 'Strata.Dyn.Exec.never_badCell_startCore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms never_badCell_startCore

/--
info: 'Strata.Dyn.Exec.access_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms access_ok

/--
info: 'Strata.Dyn.Exec.ended_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ended_ok

/--
info: 'Strata.Dyn.Exec.frame_startCore_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms frame_startCore_ok

/--
info: 'Strata.Dyn.ExecTest.SafetyTest.main_never_badCell' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms main_never_badCell

end

end Strata.Dyn.ExecTest.SafetyTest
