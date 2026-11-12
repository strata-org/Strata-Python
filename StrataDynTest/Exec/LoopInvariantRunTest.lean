/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Base
public import StrataDyn.Exec.Run
import StrataDyn.DDMRead
import StrataDyn.Env.WF
import StrataDyn.DSL
-- `#eval` runs the reader and the machine as compiled code.
meta import StrataDyn.Exec.Base
meta import StrataDyn.Exec.Run
meta import StrataDyn.DDMRead
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# A run skips a loop invariant, rules or not

A run skips a loop invariant without running its region, so the operations in the region need no
rule.  Here `inv.ge` has no rule: a contract may apply it, but a run can't.  A function whose
loop invariant applies `inv.ge` still runs, and one whose code applies it doesn't.
-/

namespace Strata.Dyn.ExecTest.LoopInvariantRunTest

open Strata.Dyn.Exec

/-- A comparison with no rule. -/
public environment Inv extends Base where
  namespace inv
  open base
  /-- `lhs ≥ rhs`. -/
  pure insn ge (lhs rhs : Int) : Bool
  end inv

/-- info: InvSem: no rule for inv.ge -/
#guard_msgs in
#dyn_sem_table InvSem for Inv

/-- Read `text`, run its `@m.main`, and print the result as an `Int`, or the fault, or the
reader's diagnostics. -/
private def runMain (text : String) : IO Unit := do
  match ← Module.read Inv.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    let o := runModule InvSem.model m (.str (.str .base "m") "main") #[] 1000
    match o.result with
    | .fault (.invalid msg) => IO.println s!"invalid: {msg}"
    | .fault f => IO.println (repr f)
    | _ => IO.println (repr (o.read? Int))

/-- A loop that runs once, whose invariant applies `inv.ge`.  Control enters the head twice, and
`@m.main` returns `7`. -/
private def withInvariant : String := "module m {
  func @m.main() -> base.Int {
    entry.0():
      %c.0 : base.Ref(base.Bool) = base.refNew[base.Bool](true)
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = inv.ge(%i.0, 0)
          ret(%ok.0)
      }
      %b.0 : base.Bool = base.refGet[base.Bool](%c.0)
      branch(%b.0) ^body.0() ^done.0()
    body.0():
      %u.0 : base.Unit = base.refSet[base.Bool](%c.0, false)
      jump ^head.0(7)
    done.0():
      ret(%i.0)
  }
}
"

/-- info: some 7 -/
#guard_msgs in
#eval runMain withInvariant

/-- The same function, where the code itself applies `inv.ge`: linking reports the missing rule. -/
private def inCode : String := "module m {
  func @m.main() -> base.Int {
    entry.0():
      %ok.0 : base.Bool = inv.ge(1, 0)
      branch(%ok.0) ^yes.0() ^no.0()
    yes.0():
      ret(1)
    no.0():
      ret(0)
  }
}
"

/-- info: Strata.Dyn.Exec.Fault.missingRules #[Strata.Dyn.Name.str (Strata.Dyn.Name.str (Strata.Dyn.Name.base) "inv") "ge"] -/
#guard_msgs in
#eval runMain inCode

end Strata.Dyn.ExecTest.LoopInvariantRunTest
