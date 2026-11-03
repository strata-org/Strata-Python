/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Call
public import StrataDynTest.Exec.FrameTest
import StrataDyn.Env.WF
-- `#guard` runs the checks and the engine as compiled code.
meta import StrataDyn.Exec.Call
meta import StrataDynTest.Exec.FrameTest
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The frame theorem for a call

`caller(r, s)` calls `bump(r, 5)` by `base.callCode`, at While's run model, linked by hand;
`bump` writes `5` into the cell `r` names (`FrameTest`).  The caller holds a second ref, `s`,
which it does not pass.  Its `callCode` makes the pending call of `bump`'s entry frame on a ref
to cell `0` and `5` (`caller_calls`, from `step_callCode`).  At that call, with `s` naming cell
`1`:

* cell `1` is reachable from the caller's frame but not from the call's arguments and the world,
  so the frame theorem for a call says that every run of the call keeps it until `bump` returns,
  and when the caller resumes (`call_keeps_unpassed`);
* cell `0` is passed (`passed_reached`), so the theorem says nothing of it, and the run does
  change it (`#guard` below), while cell `1` keeps its value.

The axioms of the main theorems are pinned.
-/

namespace Strata.Dyn.ExecTest.CallTest

open Strata.Dyn.Exec
open Strata.Dyn.ExecTest.FrameTest (M A retOf bump bumpPtr bumpPtr_acct args acct_int roots_eq
  wellTagged_cell0 cell1_unreached)

@[expose] public section

/-- `caller(r, s)`, with `r s f v x` at slots `0`–`4`:
```
entry(r, s): f = const bump; v = const 5; x = callCode f(r, v); ret x
``` -/
def caller : LBody M where
  name := .num .base 1
  ret := M.int
  slots := 5
  params := [Ty.ref M.int, Ty.ref M.int]
  blocks := #[⟨Label.exit, [(0, Ty.ref M.int), (1, Ty.ref M.int)], [],
    [.const 2 bumpPtr, .const 3 ⟨M.int, M.ofInt 5⟩,
      .callCode 4 [Ty.ref M.int, M.int] M.int 2 [0, 3]], retOf 4⟩]

/-- The module of `bump` and `caller`. -/
def lm : LModule M := ⟨#[bump, caller], #[]⟩

/-- `bump` is function `0`. -/
theorem bump_lt : 0 < lm.funcs.size := by decide

/-- The module's rules are certified: constants that hold no ref, a machine write, a machine
call and returns. -/
theorem rulesOK : lm.RulesOK A := by
  refine ⟨fun g hg b hb => ?_, fun g hg => absurd hg (by simp [lm])⟩
  simp only [lm, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp only [bump, List.mem_toArray, List.mem_singleton] at hb
    subst hb
    exact ⟨fun i hi => by simp only [List.mem_singleton] at hi; subst hi; trivial,
      fun _ => trivial⟩
  · simp only [caller, List.mem_toArray, List.mem_singleton] at hb
    subst hb
    refine ⟨fun i hi => ?_, fun _ => trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact bumpPtr_acct
    · exact acct_int _
    · trivial

/-- The call's roots: cell `0`, at the integers' tag. -/
theorem call_roots (w : M.W) : startRoots A (args ++ Args.toList .nil) w = [.cell 0 M.int] := by
  rw [show args ++ Args.toList (Args.nil (I := M.interp)) = args from List.append_nil _]
  exact roots_eq w

/-- **A cell the caller does not pass is kept by the call.**  At any pending call of `bump` on a ref
to cell `0`, in a run of `lm` whose heap holds an integer at cell `0` and has a cell `1`, every run
of the call keeps cell `1` along each of its runs of `bump` (`CallKeeps`): as it was at the call,
at every configuration until `bump` returns, at the end if the run ends there, and when the
caller resumes, with the frames that waited below the call. -/
theorem call_keeps_unpassed (hwf : WF lm) {c : Core M} {w : Wait M} {drawn : Nat} {B : Ty}
    (h : StateOK lm B ⟨c, .call (callFrame hwf 0 bump_lt args .nil) w, drawn, ()⟩)
    {x : M.interp M.int} (h0 : c.heap.cells[0]? = some ⟨M.int, x⟩) (h1 : 1 < c.heap.cells.size)
    (r : RunFrom hwf ⟨c, .call (callFrame hwf 0 bump_lt args .nil) w, drawn, ()⟩ h)
    (r₀ : RunFrom hwf _ (bodyStart_ok h.1 _ _ _)) (hr₀ : CalleeRun r r₀) :
    CallKeeps (· = 1) r r₀ := by
  refine frame_callFrame (P := (· = 1)) rulesOK h ?_ (fun l (hl : l = 1) => hl ▸ h1)
    (fun l (hl : l = 1) => ?_) r r₀ hr₀
  · rw [call_roots]
    exact wellTagged_cell0 h0
  · rw [hl, call_roots]
    exact cell1_unreached h0

/-- Entry frames of equal functions on equal values are equal. -/
private theorem callFrame_congr {hwf : WF lm} {i i₁ : Nat} {hi : i < lm.funcs.size}
    {hi₁ : i₁ < lm.funcs.size} {ds : List (Dyn M.interp)} (he : i = i₁) :
    callFrame hwf i hi ds .nil = callFrame hwf i₁ hi₁ ds .nil := by
  subst he
  rfl

/-- Steps to equal states are equal. -/
private theorem next_congr {B : Ty} {e : Event} {s s₁ : State M} (h : StateOK lm B s)
    (h₁ : StateOK lm B s₁) (hs : s = s₁) : StepR.next e s h = .next e s₁ h₁ := by
  subst hs
  rfl

/-- The value of a slot, from its lookup. -/
private theorem getD_of {env : Array (Dyn M.interp)} {v : Nat} {d : Dyn M.interp}
    (h : env[v]? = some d) (hb : Bound env v) : getD env v hb = d :=
  Option.some.inj ((Array.getElem?_eq_getElem hb).symm.trans h)

/-- A value's payload, cast to its tag. -/
private theorem cast_snd {d : Dyn M.interp} {t : Ty} {x : M.interp t} (he : d = ⟨t, x⟩)
    (p : M.interp d.1 = M.interp t) : cast p d.2 = x := by
  subst he
  rfl

/-- The value of a slot at its tag, from its lookup. -/
private theorem getT_of {env : Array (Dyn M.interp)} {v : Nat} {t : Ty} {x : M.interp t}
    (h : env[v]? = some ⟨t, x⟩) (hh : HasTy env v t) : getT env v t hh = x := by
  unfold getT
  exact cast_snd (getD_of h hh.1) _

/-- **The caller's call.**  At `caller`'s `callCode`, with `r` naming cell `0`, `v` holding `5`
and `f` holding `bump`'s pointer, the step is the pending call of `bump`'s entry frame on a ref
to cell `0` and `5`, the caller waiting to bind the result to `x`. -/
theorem caller_calls (hwf : WF lm) {c : Core M} {B : Ty} (h : CoreOK lm B c)
    (hc : c.top.code = [.callCode 4 [Ty.ref M.int, M.int] M.int 2 [0, 3]])
    (h0 : c.top.env[0]? = some ⟨Ty.ref M.int, M.cellAt M.int 0⟩)
    (h2 : c.top.env[2]? = some bumpPtr) (h3 : c.top.env[3]? = some ⟨M.int, M.ofInt 5⟩)
    (oracle : Nat → Nat) (drawn : Nat) :
    ∃ h₁, step hwf oracle ⟨c, .exec, drawn, ()⟩ h = .next (.instr c.top.pos)
      ⟨c, .call (callFrame hwf 0 bump_lt args .nil)
        (.call { c.top with code := [], pc := c.top.pc + 1 } 4 M.int), drawn, ()⟩ h₁ := by
  have hf : M.fnOf (getT c.top.env 2 _ (h.ready hc).1) = ⟨⟨0, 0, trivial⟩⟩ := by
    rw [getT_of h2, M.fnOf_fnAt]
  have hok : lm.CallOK c.heap (M.fnOf (getT c.top.env 2 _ (h.ready hc).1)).idx
      (M.fnOf (getT c.top.env 2 _ (h.ready hc).1)).captured [Ty.ref M.int, M.int] M.int [] := by
    rw [hf]
    exact ⟨bump_lt, rfl, rfl, rfl⟩
  obtain ⟨h₁, hs⟩ := step_callCode hwf oracle h hc hok drawn
  have ha : appendCaps [] (lookupAll c.top.env [0, 3] (h.ready hc).2) = args := by
    simp only [appendCaps, lookupAll, getD_of h0, getD_of h3, args]
  have hi : (M.fnOf (getT c.top.env 2 _ (h.ready hc).1)).idx = 0 := congrArg (·.idx) hf
  have hS : callFrame hwf _ hok.1 (appendCaps [] (lookupAll c.top.env [0, 3] (h.ready hc).2)) .nil =
      callFrame hwf 0 bump_lt args .nil := by
    rw [← ha]
    exact callFrame_congr hi
  refine ⟨hS ▸ h₁, hs.trans ?_⟩
  exact next_congr _ _ (by rw [hS])

/-- **The twin: the passed cell is reachable** from the call's arguments, so the frame theorem
for a call does not apply to it. -/
theorem passed_reached (heap : Heap M) (w : M.W) :
    ReachesCell A heap (startRoots A (args ++ Args.toList .nil) w) 0 :=
  ⟨M.int, .root (by rw [call_roots]; exact List.mem_singleton_self _)⟩

/-- The caller's arguments: refs to cells `0` and `1`. -/
def callerArgs : List (Dyn M.interp) :=
  [⟨Ty.ref M.int, M.cellAt M.int 0⟩, ⟨Ty.ref M.int, M.cellAt M.int 1⟩]

/-- The heap of two integer cells, `1` and `2`. -/
def heap₀ : Heap M := { cells := #[⟨M.int, M.ofInt 1⟩, ⟨M.int, M.ofInt 2⟩] }

/-- The integer at location `l` of the heap where `caller`'s run from `heap₀` ends. -/
def cellAfter (l : Nat) : Option Int :=
  match hw : checkModule lm with
  | .error _ => none
  | .ok () =>
    match startCore (m := lm) hw 1 callerArgs ⟨heap₀, M.w0⟩ with
    | .error _ => none
    | .ok ⟨_, c, hc⟩ =>
      match runFused hw (fun _ => 0) 40 ⟨c, .exec, 0, ()⟩ hc with
      | .done _ sn _ _ => (sn.heap.cells[l]?).bind fun d => WhileSem.model.read? (.ok d) Int
      | .timeout .. => none

-- The passed cell is overwritten with `5`; the caller's other cell keeps `2`.
#guard cellAfter 0 == some 5
#guard cellAfter 1 == some 2

/--
info: 'Strata.Dyn.Exec.trace_atop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms trace_atop

/--
info: 'Strata.Dyn.Exec.trace_call' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms trace_call

/--
info: 'Strata.Dyn.Exec.frame_call' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms frame_call

/--
info: 'Strata.Dyn.Exec.run_call' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms run_call

/--
info: 'Strata.Dyn.Exec.frame_call_of_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms frame_call_of_inv

/--
info: 'Strata.Dyn.ExecTest.CallTest.call_keeps_unpassed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms call_keeps_unpassed

end

end Strata.Dyn.ExecTest.CallTest
