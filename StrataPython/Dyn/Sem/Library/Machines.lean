/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Iterators
public import StrataPython.Dyn.Sem.Library.Collections

set_option autoImplicit false

/-!
# The step machines of the built-in library

The frames of the library's step machines (`LoopState`), their first steps (`machineStart`) and
their resume entry (`machineResume`): `any`, `all`, `sum`, `max` and `min` (`Iterables`), and the
container constructors (`Collections`). `Assembly` joins `LoopState` into `py.call`'s loop
state.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

/-- The frames of the library's step machines. -/
inductive LoopState (V : Type) where
  /-- `any(…)` (`stopAt = true`) or `all(…)` (`stopAt = false`) over the iterator `it`: the walk
  ends at the first item whose truth is `stopAt`. -/
  | anyAll (stopAt : Bool) (it : V)
  /-- `sum(…)` over the iterator `it`, in the phase `s`. -/
  | sum (it : V) (s : Sum.State V)
  /-- `max(…)` (`isMax`) or `min(…)` over the iterator `it`, with the key function `key` and the
  default `dflt`; `best` is the best item so far with its key. `pending` is the item whose key
  call suspended; the frames of that call follow this frame. -/
  | minMax (isMax : Bool) (it : V) (key dflt : Option V) (best : Option (V × V))
      (pending : Option V)
  /-- A container constructor's loop (`Collections`). -/
  | collect (s : CollectState V)

section
variable {m : Type → Type 1} {V : Type}

section
variable {S : Type} [HasLoopPart S (LoopState V)]

/-- The call's step from a machine's step: the result, or the machine's frame `frame st`. -/
def toCallStep [PyPure m V] {T : Type} (frame : T → LoopState V) : LoopStep T V → m (CallStep S V)
  | .done v => pure (.done v)
  | .more st => pure (.suspend [HasLoopPart.inj (frame st)])

/-- One activation of a machine that makes no call that may suspend (`any`, `all`, `sum` and the
container constructors), from its frame. -/
def stepNoCalls [PyWrites m V] [PyNew m V] : LoopState V → m (CallStep S V)
  | .anyAll stopAt it => do
    match ← anyAllStep stopAt it with
    | .done r => pure (.done (PyPure.imm (m := m) (.bool r)))
    | .more it => pure (.suspend [HasLoopPart.inj (LoopState.anyAll stopAt it)])
  | .sum it s => do toCallStep (.sum it) (← sumStep it s)
  | .collect st => do toCallStep .collect (← collectStep st)
  | .minMax .. => PyPure.modelInvariant "a frame of max or min reached the machines without calls"

section
variable [PyWrites m V] [PyNew m V] [PyMachines m V S] [HasLoopPart S (Proto.OpsLoopState V)]

/-- A call of the key function `k` on the item `x` that a step machine may suspend. -/
def callKeyResumable (k x : V) : m (CallStep S V) := do
  callResumable dispatchDepth k (PyPure.imm (m := m) (.tuple #[x])) (← PyPure.allocDict) []

/-- One activation of `max` or `min` from the best item `best`: the result once the iterator
ends, or the frames to go on from. -/
def minMaxFrames (isMax : Bool) (it : V) (key dflt : Option V) (best : Option (V × V)) :
    m (CallStep S V) := do
  let frame (best : Option (V × V)) (pending : Option V) : S :=
    HasLoopPart.inj (LoopState.minMax isMax it key dflt best pending)
  match ← minMaxStep callKeyResumable isMax it key best with
  | .done best => return .done (← minMaxResult isMax dflt best)
  | .more best => return .suspend [frame best none]
  | .suspended best x fs => return .suspend (frame best (some x) :: fs)

/-- **The first step of the machine of the built-in `f`**, called with `args` and `kwargs`; `none`
when `f` is not one of the library's machines. -/
def machineStart (f args kwargs : V) : m (Option (CallStep S V)) := do
  match ← PyPure.immView f with
  | some (.builtin .any) => some <$> stepNoCalls (.anyAll true (← anyAllIter "any" args kwargs))
  | some (.builtin .all) => some <$> stepNoCalls (.anyAll false (← anyAllIter "all" args kwargs))
  | some (.builtin .sum) =>
    let (it, s) ← sumInit args kwargs
    some <$> stepNoCalls (.sum it s)
  | some (.builtin .max) => some <$> minMaxStart true
  | some (.builtin .min) => some <$> minMaxStart false
  | _ =>
    match ← collectCallee f args with
    | some (t, name, xs) => some <$> (toCallStep .collect (← collectFirst t name xs kwargs))
    | none => pure none
where
  minMaxStart (isMax : Bool) : m (CallStep S V) := do
    let (it, key, dflt) ← minMaxInit isMax args kwargs
    minMaxFrames isMax it key dflt none

/-- **The resume entry of the frames of this file**: the machine of the frame `fr` goes on. A frame
of `max` or `min` whose key call suspended first resumes that call, from the frames after it, and
offers its item. A frame list that doesn't fit its phase can't happen: it stops with a model
invariant.
-/
def machineResume (fr : LoopState V) (rest : List S) : m (CallStep S V) := do
  match fr, rest with
  | .minMax isMax it key dflt best (some x), s :: rest' =>
    if key.isNone then PyPure.modelInvariant "a frame of max or min with a pending item and no key"
    match ← PyMachines.resume s rest' with
    | .suspend fs => return .suspend (HasLoopPart.inj fr :: fs)
    | .done val => minMaxFrames isMax it key dflt (← minMaxOffer isMax best x val)
  | .minMax isMax it key dflt best none, [] => minMaxFrames isMax it key dflt best
  | .minMax .., _ => PyPure.modelInvariant "a frame list that doesn't fit the call"
  | fr, [] => stepNoCalls fr
  | _, _ :: _ => PyPure.modelInvariant "a frame list that doesn't fit the call"

end

end

end

end

end StrataPython.Dyn.Sem.Library
