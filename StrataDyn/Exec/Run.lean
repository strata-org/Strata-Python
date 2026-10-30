/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Fused
-- Running a module needs the environment representation at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Running a module

* `start`: the state that runs a function of a linked, validated module on arguments,
  from a `Snapshot` of a heap and a world: by default `Snapshot.initial`, or where an earlier
  run ended, `o.snapshot`.
* `runModule`: link, validate, start and run on `runFused`.
  An argument is a Lean value at its tag, `M.arg x`, and `M.read? r α`, or `o.read? α` on an
  outcome, reads a result as an `α`.  Both find `α`'s tag as a rule does, as a `TagOf σ α`, at
  the model's decoding.
* `runPreparedFrom`: run a function of a prepared module from where an earlier run of that
  module ended, if it returned a value: from its snapshot, with its oracle's next answers.
* `debugRun`: a debugger's loop over `runHooked`, which resumes each time its hook stops the
  run.
* `tapeOracle`: the oracle that answers from a recorded list of choices.
-/

namespace Strata.Dyn.Exec

@[expose] public section

section
variable {M : RunModel} {m : LModule M}

/-- Starting function `i` on arguments of its entry block's parameter tags, with nothing
waiting, satisfies the run invariant, from any snapshot: the machine checks every access of a
cell when it happens. -/
theorem start_ok (hwf : WF m) {i : Nat} {fn : LBody M} {b : LBlock M}
    {args : List (Dyn M.interp)} (hf : m.funcs[i]? = some fn) (hb : fn.blocks[0]? = some b)
    (ha : args.map (·.1) = b.paramTys) (snap : Snapshot M := .initial) :
    CoreOK m fn.ret { top := Frame.entry fn b (freshStore M fn.slots) args .nil
                                (fresh_fits fn) (hwf.fits_of_getElem? hf hb),
                       conts := [], heap := snap.heap, world := snap.world } := by
  obtain ⟨hi, hfe⟩ := Array.getElem?_eq_some_iff.mp hf
  have hm : fn ∈ m.funcs := hfe ▸ Array.getElem_mem hi
  obtain ⟨⟨b₀, hb₀, hsc, -⟩, hblocks⟩ := hwf.func hm
  obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
  obtain ⟨hj, hbe⟩ := Array.getElem?_eq_some_iff.mp hb
  refine ⟨⟨Or.inl hm, entryCtx b₀, ?_, ?_⟩, rfl⟩
  · unfold entryCtx
    rw [hsc]
    exact Agree.bindSite _ _ .nil _ Agree.nil (by rw [List.append_nil]; exact ha)
  · exact hblocks b₀ (hbe ▸ Array.getElem_mem hj)

variable (m) in
/-- Function `i` of `m`, with its entry block, if `args` fit the block. -/
def entry? (i : Nat) (args : List (Dyn M.interp)) :
    Except Fault { p : LBody M × LBlock M // m.funcs[i]? = some p.1 ∧ p.1.blocks[0]? = some p.2 ∧
      args.map (·.1) = p.2.paramTys } :=
  match m.funcs[i]? with
  | none => .error (.invalid s!"no function #{i}")
  | some fn => match (generalizing := false) hb : fn.blocks[0]? with
    | none => .error (.invalid s!"{nameStr fn.name} has no blocks")
    | some b =>
      if ha : args.map (·.1) = b.paramTys then .ok ⟨(fn, b), rfl, hb, ha⟩
      else .error (.invalid s!"{nameStr fn.name} takes other arguments")

/-- The frames and data that run function `i` on `args`, which must fit its entry block, from
the heap and the world of `snap`, and its return code.  By default the heap starts empty, so a
cell among the arguments faults at its first access, and the world is the initial one.  One
`Snapshot` holds both, so no run starts from one run's heap and another run's world. -/
def startCore (hwf : WF m) (i : Nat) (args : List (Dyn M.interp))
    (snap : Snapshot M := .initial) : Except Fault ((B : Ty) × { c : Core M // CoreOK m B c }) :=
  (entry? m i args).map fun ⟨(fn, b), hf, hb, ha⟩ =>
    ⟨fn.ret, ⟨{ top := Frame.entry fn b (freshStore M fn.slots) args .nil (fresh_fits fn)
                  (hwf.fits_of_getElem? hf hb),
                conts := [], heap := snap.heap, world := snap.world },
              start_ok hwf hf hb ha snap⟩⟩

/-- **A successful start** runs the entry frame of function `i` on `args`, with nothing waiting,
on the heap and the world of `snap`. -/
theorem startCore_entry {hwf : WF m} {i : Nat} {args : List (Dyn M.interp)} {snap : Snapshot M}
    {B : Ty} {c : Core M} {hc : CoreOK m B c} (hst : startCore hwf i args snap = .ok ⟨B, c, hc⟩) :
    ∃ (fn : LBody M) (b : LBlock M) (hf : m.funcs[i]? = some fn) (hb : fn.blocks[0]? = some b),
      c = { top := Frame.entry fn b (freshStore M fn.slots) args .nil (fresh_fits fn)
              (hwf.fits_of_getElem? hf hb),
            conts := [], heap := snap.heap, world := snap.world } := by
  unfold startCore at hst
  cases he : entry? m i args with
  | error e =>
    rw [he] at hst
    exact nomatch hst
  | ok p =>
    rw [he] at hst
    obtain ⟨⟨fn, b⟩, hf, hb, ha⟩ := p
    cases hst
    exact ⟨fn, b, hf, hb, rfl⟩

/-- A state running function `i` on `args`, which must fit its entry block, from the
heap and the world of `snap`, and its return code. -/
def start (hwf : WF m) (i : Nat) (args : List (Dyn M.interp)) (snap : Snapshot M := .initial) :
    Except Fault ((B : Ty) × { s : State M // StateOK m B s }) :=
  (startCore hwf i args snap).map fun ⟨B, c, h⟩ => ⟨B, ⟨c, .exec, 0, ()⟩, h⟩

end

/-- The oracle that answers the choices in `tape`, in order, then `0`. -/
def tapeOracle (tape : List Nat) : Nat → Nat := fun i => tape.getD i 0

/-- How a run at a run model ended: its result, the snapshot of its heap and world, from which
another run can start, the fused steps taken, and the choices made. -/
structure Ran (M : RunModel) where
  result : Result M.interp
  snapshot : Snapshot M
  steps : Nat
  drawn : Nat

/-- How a run of a module against the model `M` ended. -/
abbrev Outcome (M : Model) : Type := Ran M.at

/-- The value `r` returned, if its tag is the tag of `α` in `M`, and `none` if it has another
tag or the run faulted. -/
def Model.read? (M : Model) {σ : Type} [Store σ] (r : Result (M.interp σ)) (α : Type)
    [t : @TagOf σ _ (M.decode σ) α] : Option α :=
  match r with
  | .ok d => if h : d.1 = t.tag then some (cast ((congrArg _ h).trans (Model.tag_ok t)) d.2)
    else none
  | .fault _ => none

/-- The value the run returned, if it is an `α`. -/
abbrev Outcome.read? {M : Model} (o : Outcome M) (α : Type)
    [@TagOf Run _ (M.decode Run) α] : Option α :=
  M.read? o.result α

/-- A run that faulted with `f` before its first step. -/
def Outcome.failed (M : Model) (f : Fault) : Outcome M := ⟨.fault f, .initial, 0, 0⟩

/-- The index of the function named `f`. -/
def LModule.funcIndex {M : RunModel} (m : LModule M) (f : Name) : Option Nat :=
  m.funcs.toList.findIdx? (fun g => decide (g.name = f))

/-- How a run of `fuel` steps ended, as an outcome. -/
def RunEnd.outcome {M : RunModel} {m : LModule M} {B : Ty} (fuel : Nat) : RunEnd m B → Ran M
  | .done r sn d left => ⟨r, sn, fuel - left, d⟩
  | .timeout s _ => ⟨.fault .outOfFuel, ⟨s.core.heap, s.core.world⟩, fuel, s.drawn⟩

/-- The module's function `f`, linked and validated. -/
def prepare (M : Model) {env : Env Unit} [base ≼ env] {α : Type} (prog : Module env α)
    (f : Name) : Except Fault ((lm : LModule M.at) ×' WF lm ×' Nat) :=
  match link M prog with
  | .error e => .error e
  | .ok lm => match hw : checkModule lm with
    | .error msg => .error (.invalid msg)
    | .ok () => match lm.funcIndex f with
      | none => .error (.noFunction f)
      | some i => .ok ⟨lm, hw, i⟩

/-- A prepared module is a linked one. -/
theorem link_of_prepare {M : Model} {env : Env Unit} [base ≼ env] {α : Type} {m : Module env α}
    {f : Name} {lm : LModule M.at} {hw : WF lm} {i : Nat}
    (hp : prepare M m f = .ok ⟨lm, hw, i⟩) : link M m = .ok lm := by
  unfold prepare at hp
  split at hp
  · exact nomatch hp
  · rename_i lm₀ hl
    split at hp
    · exact nomatch hp
    · split at hp
      · exact nomatch hp
      · cases hp
        exact hl

/-- Run function `i` of the validated module `lm` on `args` for at most `fuel` fused steps,
with the oracle `oracle`, from the snapshot `snap`.  Pass `Snapshot.initial`, or a snapshot that
a run of `lm` returned, unchanged: a world made by hand may hold a ref or a closure that names
another cell or function. -/
def runPrepared {M : RunModel} {lm : LModule M} (hw : WF lm) (i : Nat)
    (args : Array (Dyn M.interp)) (fuel : Nat) (oracle : Nat → Nat)
    (snap : Snapshot M := .initial) : Ran M :=
  match startCore hw i args.toList snap with
  | .error e => ⟨.fault e, snap, 0, 0⟩
  | .ok ⟨_, c, h⟩ => (runFused hw oracle fuel ⟨c, .exec, 0, ()⟩ h).outcome fuel

/-- Run function `f` of `prog` on `args` for at most `fuel` fused steps, with the oracle
`oracle`: link, validate, then run.  The arguments are values at every token, so none
holds a ref or a closure.  A fault before the first step takes no steps. -/
def runModule (M : Model) {env : Env Unit} [base ≼ env] {α : Type} (prog : Module env α)
    (f : Name) (args : Array M.Arg) (fuel : Nat) (oracle : Nat → Nat := fun _ => 0) :
    Outcome M :=
  match prepare M prog f with
  | .error e => .failed M e
  | .ok ⟨_, hw, i⟩ => runPrepared hw i (args.map (· Run)) fuel oracle

/-- Run function `i` of the validated module `lm` from where the run `prev` of the same module
ended, if `prev` returned a value: from its snapshot.  So the run finds the cells that `prev` made
and kept in its world, and its new cells come after them.  The run takes the oracle's answers from
`prev.drawn` on.  The result's `drawn` is `prev.drawn` plus the number of choices of the new run,
and its `steps` are only the new run's.  The arguments are values at every token, so none holds a
ref or a closure.  If `prev` ended with any fault, a lack of fuel or a blocked path included,
nothing runs, and the result is `.error prev`.  Pass the oracle that `prev` ran with, so that the
run takes the answers that `prev` didn't use.  Pass `prev` as a run of `lm` returned it: a snapshot
from another module's run, or one changed between the runs, may hold a ref or a closure that names
another cell or function of the same type, and the run then reads or calls that one. -/
def runPreparedFrom {M : Model} {lm : LModule M.at} (hw : WF lm) (i : Nat) (prev : Outcome M)
    (args : Array M.Arg) (fuel : Nat) (oracle : Nat → Nat := fun _ => 0) :
    Except (Outcome M) (Outcome M) :=
  match prev.result with
  | .fault _ => .error prev
  | .ok _ =>
    let o := runPrepared hw i (args.map (· Run)) fuel (fun k => oracle (prev.drawn + k)) prev.snapshot
    .ok { o with drawn := prev.drawn + o.drawn }

/-- After a run `prev` that ended with a fault, `runPreparedFrom` runs nothing and gives `prev`
back, as an error. -/
theorem runPreparedFrom_of_fault {M : Model} {lm : LModule M.at} (hw : WF lm) (i : Nat)
    {prev : Outcome M} {f : Fault} (h : prev.result = .fault f) (args : Array M.Arg)
    (fuel : Nat) (oracle : Nat → Nat) :
    runPreparedFrom hw i prev args fuel oracle = .error prev := by
  simp [runPreparedFrom, h]

/-- What a debugging run saw: where its hook stopped it, in order, the outcome, or `none` if
the fuel ran out, and the hook's final state. -/
structure DebugRun (M : Model) (ρ : Type) where
  stops : Array Pos
  result : Option (Result (M.interp Run))
  st : ρ

/-- A debugger's loop: run function `f` of `prog` with `hook`, and each time the hook stops the
run, note where and resume, at most `maxStops` times.  A hook that never modifies resumes as
the uninterrupted run would go on (`runHooked_resume`). -/
def debugRun (M : Model) {env : Env Unit} [base ≼ env] {α : Type} (prog : Module env α)
    (f : Name) (args : Array M.Arg) (fuel : Nat) {ρ : Type}
    (hook : {m : LModule M.at} → {B : Ty} → Hook m B ρ) (st : ρ)
    (oracle : Nat → Nat := fun _ => 0) (maxStops : Nat := 100) :
    Except Fault (DebugRun M ρ) := do
  let lm ← link M prog
  match hw : checkModule lm with
  | .error msg => .error (.invalid msg)
  | .ok () =>
    let some i := lm.funcIndex f | .error (.noFunction f)
    let ⟨_, s, h⟩ ← start hw i (args.map (· Run)).toList
    let (stops, result, st) := go hw maxStops fuel st s h #[]
    return ⟨stops, result, st⟩
where
  go {m : LModule M.at} (hw : WF m) {B : Ty} : Nat → Nat → ρ → (s : State M.at) →
      StateOK m B s → Array Pos → Array Pos × Option (Result (M.interp Run)) × ρ
    | stops + 1, fuel, st, s, h, seen => match runHooked hw oracle hook fuel st s h with
      | (.done r _ _ _, st₁) => (seen, some r, st₁)
      | (.timeout .., st₁) => (seen, none, st₁)
      | (.stopped s₁ h₁ left, st₁) => go hw stops left st₁ s₁ h₁ (seen.push s₁.core.top.pos)
    | 0, _, st, _, _, seen => (seen, none, st)

end

end Strata.Dyn.Exec
