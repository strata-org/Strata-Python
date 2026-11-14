/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.Table
import StrataDyn.DDMRead
import StrataDyn.Exec.Run
import StrataPythonTest.Dyn.Sem.HasattrSamples
meta import StrataPython.Dyn.Sem.Table
meta import StrataDyn.DDMRead
meta import StrataDyn.Exec.Run
meta import StrataPythonTest.Dyn.Sem.HasattrSamples

set_option autoImplicit false

/-!
# The `hasattr` test

For each sample of `HasattrSamples.lean` (a value of each kind, and every name of `dir(x)` and
`dir(type(x))` with CPython 3.12's `hasattr(x, name)`), the rules run `x.name` with `py.attr`: it
must give a value of the class that CPython's has where CPython has the attribute, and raise
`AttributeError` where CPython doesn't, or stop with a gap.  The test pins how many names agree and how many gap, and that none
disagrees.
-/

namespace StrataPython.Dyn.Sem.HasattrTest

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn.Sem

/-- The run of `body`, after the sample's instructions `ir`, as the function `main` that returns
`%v.0` or the exception it raises: the result, `none` for a gap, and an error for a fault. -/
def runSample (ir body : String) : IO (Except String (Option (Option Value × Exec.Ran PySem.model.at))) := do
  let pre := "\n".intercalate ((ir.splitOn "\n").map ("      " ++ ·))
  let text := s!"module m \{
  func @m.main() -> py.Value \{
    entry.0():
{pre}
{body}
      ret(%v.0)
    err.0(%e.0 : py.Value):
      ret(%e.0)
  }
}"
  match ← Module.read Py.env text "t.dyn" with
  | .error e => return .error s!"read: {e}"
  | .ok m => return Id.run <| ExceptT.run (m := Id) do
    let o := runModule PySem.model m (.str (.str .base "m") "main") #[] 1000
    match o.result with
    | .fault (.gap _) => return none
    | .fault f => throw s!"fault: {repr f}"
    | .ok _ => return some (o.read? Value, o)

/-- What `x.name` gives in the rules: `some (some t)` for a value of the class named `t` (its
`__class__.__name__`), `some none` for an `AttributeError`, `none` for a gap, and an error for
anything else. -/
def attrOutcome (ir name : String) : IO (Except String (Option (Option String))) := do
  let get := s!"      %v.0 : py.Value = py.attr(%x.0, {repr name}) ^err.0()"
  match ← runSample ir get with
  | .error e => return .error e
  | .ok none => return .ok none
  | .ok (some (r, o)) =>
    match r with
    | some (.obj id) => match o.snapshot.world.store.get? id with
      | some { cls := .builtin .AttributeError, payload := .exc _, .. } => return .ok (some none)
      | some { cls, payload := .exc _, .. } => return .error s!"an exception of class {repr cls}"
      | _ => pure ()
    | some _ => pure ()
    | none => return .error "a result that is not a value"
    -- The value's class name, read with the attribute protocol of the rules.
    let name := get.replace "%v.0" "%got.0" ++ "\n      %c.0 : py.Value = py.attr(%got.0, \"__class__\") ^err.0()\n      %v.0 : py.Value = py.attr(%c.0, \"__name__\") ^err.0()"
    match ← runSample ir name with
    | .error e => return .error e
    | .ok none => return .ok none
    | .ok (some (some (.str t), _)) => return .ok (some (some t.s))
    | .ok (some _) => return .error "a class name that is not a str"

/-- The number of names that agree with CPython and that gap, and the names that disagree. -/
def summary : IO (Nat × Nat × Array String) := do
  let mut agree := 0
  let mut gaps := 0
  let mut bad : Array String := #[]
  for (label, ir, names) in HasattrSamples.samples do
    for (name, has) in names do
      match ← attrOutcome ir name with
      | .ok (some r) => if r == has then agree := agree + 1 else bad := bad.push s!"{label}.{name}: {r} where CPython has {has}"
      | .ok none => gaps := gaps + 1
      | .error e => bad := bad.push s!"{label}.{name}: {e}"
  return (agree, gaps, bad)

/-- info: (741, 58, #[]) -/
#guard_msgs in
#eval summary
