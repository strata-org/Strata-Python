/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Examples.While.Env
public import StrataDyn.RefToReg
public import StrataDyn.DDMRead
public import StrataDyn.DDM
import StrataDyn.Env.WF
meta import StrataDyn.Examples.While.Env
meta import StrataDyn.RefToReg
meta import StrataDyn.DDMRead
meta import StrataDyn.DDM
meta import StrataDyn.Env.WF

/-!
The guide's ref-to-reg listing, compiled against the package: `mean` in the cell style, read
against While's environment, promoted, and printed.  `checks/run.sh` elaborates this file, and
`scripts/export-data.py --check` checks that both texts are the guide's, `data/mean-cells.dyn`
and `data/mean-cells.promoted.dyn`.
-/

namespace Strata.Dyn.Guide

/-- `mean` in the cell style, written by hand. -/
def cells : String := "
module main {
  func @mean(%n.0 : base.Int, %d.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int, %d.0 : base.Int):
      %s.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %i.0 : base.Ref(base.Int) = base.refNew[base.Int](1)
      jump ^head.0()
    head.0():
      %t.0 : base.Int = base.refGet[base.Int](%i.0)
      %t.1 : base.Bool = while.le(%t.0, %n.0)
      branch(%t.1) ^body.0() ^exit.0()
    body.0():
      %t.2 : base.Int = base.refGet[base.Int](%s.0)
      %t.3 : base.Int = base.refGet[base.Int](%i.0)
      %t.4 : base.Int = while.add(%t.2, %t.3)
      %u.0 : base.Unit = base.refSet[base.Int](%s.0, %t.4)
      %t.5 : base.Int = base.refGet[base.Int](%i.0)
      %t.6 : base.Int = while.add(%t.5, 1)
      %u.1 : base.Unit = base.refSet[base.Int](%i.0, %t.6)
      jump ^head.0()
    exit.0():
      %t.7 : base.Int = base.refGet[base.Int](%s.0)
      %t.8 : base.Int = while.div(%t.7, %d.0) ^catch.0()
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.8)
      ret(%ok.0)
    catch.0(%e.0 : base.Int):
      %t.9 : base.Int = while.sub(0, %e.0)
      %ok.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.9)
      ret(%ok.1)
  }
}
"

/-- Read `text`, promote its cells, and print the result, or the errors. -/
def promote (text : String) : IO Unit := do
  match ← Module.read While.env text "mean-cells.dyn" with
  | .error e => IO.println e
  | .ok m => match refToReg m with
    | .ok m₁ => IO.print (toString m₁)
    | .error es => for (f, e) in es do IO.println s!"{repr f}: {e}"

/--
info: module main {
  func @mean(%n.0 : base.Int, %d.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int, %d.0 : base.Int):
      %s.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %i.0 : base.Ref(base.Int) = base.refNew[base.Int](1)
      jump ^head.0(0, 1)
    head.0(%c.4 : base.Int, %c.5 : base.Int):
      %t.1 : base.Bool = while.le(%c.5, %n.0)
      branch(%t.1) ^body.0() ^exit.0()
    body.0():
      %t.4 : base.Int = while.add(%c.4, %c.5)
      %t.6 : base.Int = while.add(%c.5, 1)
      jump ^head.0(%t.4, %t.6)
    exit.0():
      %t.8 : base.Int = while.div(%c.4, %d.0) ^catch.0()
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.8)
      ret(%ok.0)
    catch.0(%e.0 : base.Int):
      %t.9 : base.Int = while.sub(0, %e.0)
      %ok.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.9)
      ret(%ok.1)
  }
}
-/
#guard_msgs in #eval promote cells

end Strata.Dyn.Guide
