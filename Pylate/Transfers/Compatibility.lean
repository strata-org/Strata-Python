/-
Loss-aware adapters between the legacy expression/statement results and the
flow domains.

`Fset` is list-backed, so conversions copy exception classes in list order.
Do not use `RaisedFlow.classes` here: its repeated front insertion reverses
the order of `RaisedFlow.cases`.
-/
import Pylate.Transfers.Flow

namespace Pylate.RuleDriven.Compatibility

open Pylate
open Pylate.RuleDriven

private def raisedOfLegacy (fallback : AState) (state : Option AState)
    (classes : Fset String) : RaisedFlow :=
  if classes.isEmpty then {}
  else
    let raisedState := state.getD fallback
    {
      cases := classes.map fun cls =>
        -- Expanded from the joined `Exc` view, which carries no raise site.
        { cls, value := AbsVal.bot, state := raisedState, origin := {} }
    }

/-- Lift all five legacy statement completions. `fallback` is consulted only
    when a malformed legacy value has nonempty `excs` but no `excSt`; valid
    `AMulti` values retain their shared exception raise-point state exactly. -/
def completionOfAMulti (fallback : AState) (result : AMulti) : Completion :=
  {
    normal := result.normal
    returned := result.retSt.map fun state => (result.retVal, state)
    broke := result.brk
    continued := result.cont
    raised := raisedOfLegacy fallback result.excSt result.excs
  }

/-- Lower all five statement completions. Distinct per-class raise-point
    states are joined into `AMulti.excSt`; exception values cannot be retained
    by the legacy representation. -/
def aMultiOfCompletion (flow : Completion) : AMulti :=
  let (retVal, retSt) := match flow.returned with
    | some (value, state) => (value, some state)
    | none => (AbsVal.bot, none)
  {
    normal := flow.normal
    brk := flow.broke
    cont := flow.continued
    retSt
    retVal
    excSt := flow.raised.state?
    excs := flow.raised.cases.map (·.cls)
  }

end Pylate.RuleDriven.Compatibility
