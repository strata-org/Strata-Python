/-
Dispatch adapter from compiled rules to the plan executor.
-/
import Pylate.RuleLang.Compile

namespace Pylate.RuleDriven

open Pylate

/-- Report a rule's outcomes from the flow it returned, rather than relying on
    each rule to remember. An internal signal is consumed by its own transfer
    and is not an outcome of the site. -/
private def reportFlow (p : Pos) (kind desc tag : String)
    (flow : Flow) : M Unit := do
  for raised in flow.raised.cases do
    if raised.from? != .internal then
      resCaseAt p kind desc tag s!"!{raised.cls}"

partial def invokeCompiled (rules : CompiledRules) (fallback : Services)
    (p : Pos) (operation : Operation) (receiver : Option AbsVal)
    (arguments : List AbsVal) (keywords : List (String × AbsVal))
    (state : AState) : M Flow := do
  let services : Services :=
    { fallback with invoke := invokeCompiled rules fallback }
  let input : CallInput := ⟨arguments, keywords⟩
  match operation with
  | .function name =>
    match rules.find? (.function name) with
    | some rule => do
      let flow ← executeRule services p rule AbsVal.bot input state
      reportFlow p "call" s!"{name}(..)" "func" flow
      pure flow
    | none => fallback.invoke p operation receiver arguments keywords state
  | .method name =>
    match receiver with
    | none => fallback.invoke p operation receiver arguments keywords state
    | some value =>
      let mut result : Flow := {}
      for tag in value.tags do
        let restricted := value.restrictTags [tag]
        match rules.find? (.method tag name) with
        | some rule =>
          let flow ← executeRule services p rule restricted input state
          reportFlow p "call" s!".{name}(..)" tag.render flow
          result := result.join flow
        | none =>
          result := result.join
            (← fallback.invoke p operation (some restricted)
              arguments keywords state)
      pure result
  | _ => fallback.invoke p operation receiver arguments keywords state

def CompiledRules.services (rules : CompiledRules)
    (fallback : Services := Services.opaque) : Services :=
  { fallback with invoke := invokeCompiled rules fallback }

end Pylate.RuleDriven
