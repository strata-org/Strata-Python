/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Canonicalize
public import StrataPython.Dyn.Env
public import StrataPython.Dyn.Shape
public import StrataDyn.LoopRecordAttr
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

/-- `step m spec`, once every function's `py.loops` attribute of `m` reads as loop records.  A
front end's record that does not read is reported, since a loop with no back edge would otherwise
pass without its record. -/
def withRecords
    (step : Module Py.env Info → (spec : CanonicalSpec Py.env Info) →
      Except (Array Canonicalize.Failure) (Canonicalize.CanonicalModule Py.env Info spec))
    (m : Module Py.env Info) :
    Except (Array Canonicalize.Failure) (Canonicalize.CanonicalModule Py.env Info spec) :=
  let unread := m.raw.funcs.filter fun f => (records? f.info).isNone
  if !unread.isEmpty then
    .error (unread.map fun f => .notAsSpecified f.name "its py.loops attribute does not read as \
      loop records")
  else step m spec

/-- `m` in Python's canonical form: `Canonicalize.runModule` with `spec`, once every function's
`py.loops` attribute reads as loop records. -/
def runModule (m : Module Py.env Info) :
    Except (Array Canonicalize.Failure) (Canonicalize.CanonicalModule Py.env Info spec) :=
  withRecords (fun m spec => Canonicalize.runModule m spec) m

/-- `m` itself, checked for Python's canonical form without the pass: `Canonicalize.checkModule`
with `spec`, once every function's `py.loops` attribute reads as loop records. -/
def checkModule (m : Module Py.env Info) :
    Except (Array Canonicalize.Failure) (Canonicalize.CanonicalModule Py.env Info spec) :=
  withRecords (fun m spec => Canonicalize.checkModule m spec) m

end

end StrataPython.Dyn.PyCanonical
