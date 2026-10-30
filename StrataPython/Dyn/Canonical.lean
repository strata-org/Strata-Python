/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Canonicalize
public import StrataPython.Dyn.Env
public import StrataPython.Dyn.Shape
public import StrataDyn.LoopRecordAttr
public import StrataPython.Dyn.FinallyEnteredProps
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Python's canonical form

What the Python translator asks of `Canonicalize.run` (`docs/PythonToDyn.md` §6.4):
`py.Completion` as the completion type, the loop records of each function's `py.loops`
attribute, and the preamble (F1).  `PyCanonical.runModule` is the entry point for every stage
after the translator: `pydyn canonical`, `DynReadTest`, and the stages that place
contracts.  `PyCanonical.checkModule` checks the same form without the pass, after a later pass
that should keep it.

It also checks one part of P6 of the canonical form: the first block of each `finally` body
pushes the completion it was entered with (`StrataPython/Dyn/FinallyEntered.lean`).
-/

namespace StrataPython.Dyn.PyCanonical

open Strata.Dyn

public section

/-- `py.Completion`, by its constructors' names: `return` and `raise` are forwarded out of every
loop. -/
def shape : CompletionShape Py.env :=
  { ty := Py.Completion, data := Py.Completion.name,
    normal := Py.Completion.completionNormal.name, brk := Py.Completion.completionBreak.name,
    cont := Py.Completion.completionContinue.name,
    forwarded := [Py.Completion.completionReturn.name, Py.Completion.completionRaise.name] }

/-- The loop records of the `py.loops` attribute of `i`, or `none` if some entry does not read as
one. -/
def records? (i : Info) : Option (List LoopRecord) :=
  LoopRecord.ofAttrs? (Shape.key "loops") i.attrs

/-- What the Python translator asks of `Canonicalize.run`.  `runModule` first checks that every
function's `py.loops` attribute reads, so the records it passes on are the whole attribute. -/
def spec : CanonicalSpec Py.env Info :=
  { shape := some shape, records := fun i => (records? i).getD [], preamble := true }

/-- A module in Python's canonical form: canonical, with what `spec` asks, and with the first
block of every `finally` body pushing the completion it was entered with (`FinallyEntered`). -/
structure CanonicalModule where
  canonical : Canonicalize.CanonicalModule Py.env Info spec
  finallyEntered : ∀ f ∈ canonical.module.raw.funcs, FinallyEntered f

/-- Why the function does not hold `FinallyEntered`: its first block that does not. -/
def finallyWhy {α : Type} (fn : Func Py.env α) : String :=
  match fn.allBlocks.find? (!finEnteredB ·) with
  | some b =>
    let l := ToDDM.nameText b.label.name
    if !(b.instrs.toList.drop 1).all (fun i => insnName? i != some Py.pushPending.name) then
      s!"{l} runs py.pushPending after its first instruction"
    else
      s!"{l} starts a finally body, but does not push its first parameter, the pending completion"
  | none => "every block passes the check"

/-- `step m spec`, once every function's `py.loops` attribute of `m` reads as loop records, then
the check of `FinallyEntered` on each function of its result.  A front end's record that does not
read is reported, since a loop with no back edge would otherwise pass without its record. -/
def withRecords
    (step : Module Py.env Info → (spec : CanonicalSpec Py.env Info) →
      Except (Array Canonicalize.Failure) (Canonicalize.CanonicalModule Py.env Info spec))
    (m : Module Py.env Info) : Except (Array Canonicalize.Failure) CanonicalModule :=
  let unread := m.raw.funcs.filter fun f => (records? f.info).isNone
  if !unread.isEmpty then
    .error (unread.map fun f => .notAsSpecified f.name "its py.loops attribute does not read as \
      loop records")
  else match step m spec with
    | .error fs => .error fs
    | .ok cm =>
      if h : ∀ f ∈ cm.module.raw.funcs, checkFinallyEntered f = true then
        .ok ⟨cm, fun f hf => (checkFinallyEntered_iff f).mp (h f hf)⟩
      else
        .error (cm.module.raw.funcs.filter (checkFinallyEntered · = false) |>.map fun f =>
          .notAsSpecified f.name (finallyWhy f))

/-- `m` in Python's canonical form: `Canonicalize.runModule` with `spec`, once every function's
`py.loops` attribute reads as loop records, then the check of `FinallyEntered`. -/
def runModule (m : Module Py.env Info) : Except (Array Canonicalize.Failure) CanonicalModule :=
  withRecords (fun m spec => Canonicalize.runModule m spec) m

/-- `m` itself, checked for Python's canonical form without the pass: `Canonicalize.checkModule`
with `spec`, once every function's `py.loops` attribute reads as loop records, then the check of
`FinallyEntered`. -/
def checkModule (m : Module Py.env Info) : Except (Array Canonicalize.Failure) CanonicalModule :=
  withRecords (fun m spec => Canonicalize.checkModule m spec) m

end

end StrataPython.Dyn.PyCanonical
