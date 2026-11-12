/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.Table
import StrataDyn.DDMRead
import StrataDyn.Exec.Run
import StrataPython.Dyn.Sem.Run
meta import StrataPython.Dyn.Sem.Table
meta import StrataDyn.DDMRead
meta import StrataDyn.Exec.Run
meta import StrataPython.Dyn.Sem.Run

set_option autoImplicit false

/-!
# The location operations, in a run

A module in the IR's text that makes a location stops with that operation's gap when `PySem` runs
it.  `LocationsProps.lean` and `StrataDyn/Exec/BaseProps.lean` prove the same of each rule, on
every input.  `base.old` has no run here: only an `ensures` clause or a loop invariant may
apply it, and no run evaluates either; the theorem `old_eq` covers it.
-/

namespace StrataPython.Dyn.Sem.LocationsTest

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn.Sem

/-- Run `@m.main`, whose body is `body`, and print its fault, or that it ended. -/
def run (body : String) : IO Unit := do
  let text := s!"module m \{
  func @m.main() -> py.Value \{
    entry.0():
      %x.0 : py.Value = py.noneLit
{body}
      ret(%x.0)
  }
}"
  match ← Module.read Py.env text "t.dyn" with
  | .error e => IO.println s!"read: {e}"
  | .ok m =>
    match (runModule PySem.model m (.str (.str .base "m") "main") #[] 1000).result with
    | .ok _ => IO.println "ended"
    | .fault f => IO.println s!"fault: {repr f}"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.attrLoc: frames have no meaning at run time" -/
#guard_msgs in
#eval run "      %l.0 : base.Loc = py.attrLoc(%x.0, \"a\")"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.itemLoc: frames have no meaning at run time" -/
#guard_msgs in
#eval run "      %l.0 : base.Loc = py.itemLoc(%x.0, \"k\")"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.objLoc: frames have no meaning at run time" -/
#guard_msgs in
#eval run "      %l.0 : base.Loc = py.objLoc(%x.0)"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.reachLoc: frames have no meaning at run time" -/
#guard_msgs in
#eval run "      %l.0 : base.Loc = py.reachLoc(%x.0)"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.instanceState: frames have no meaning at run time" -/
#guard_msgs in
#eval run "      %l.0 : base.Loc = py.instanceState"
-- The base's location of a cell stops the same way.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "base.cellLoc: frames have no meaning at run time" -/
#guard_msgs in
#eval run "      %c.0 : base.Ref(py.Value) = base.refNew[py.Value](%x.0)
      %l.0 : base.Loc = base.cellLoc[py.Value](%c.0)"

end StrataPython.Dyn.Sem.LocationsTest
