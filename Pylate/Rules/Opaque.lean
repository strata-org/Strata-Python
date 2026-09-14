/-
Closed Transfer for admitted builtin methods whose detailed protocol is
not yet modeled. The imprecision is explicit in rule metadata and in the
obligation log; reachable heap cells are widened to their contracts.
-/
import Pylate.Rules.KnownMethods

namespace Pylate.RuleDriven.Opaque

open Pylate

def execute (p : Pos) (method : OpaqueBuiltinMethod) (receiver : AbsVal)
    (arguments : List AbsVal) (state : AState) : M Flow := do
  match ← KnownMethods.execute p method receiver arguments state with
  | some flow => pure flow
  | none =>
    oblige p "external-havoc"
      s!"builtin {method.receiver.render}.{method.name} is real but not modeled: result widened, receiver havocked"
    let outputState ← havocReachable p (receiver :: arguments) state
    -- External code may add to or empty any collection it can reach.
    let outputState := (reachableLocs outputState
      ((receiver :: arguments).foldl
        (fun roots value => Fset.union value.locs roots) [])).foldl
      (fun current location =>
        if location.cls.tracksEmptiness then
          current.emptinessSet location .top
        else current) outputState
    let mut flow := Flow.ofNormal anyV outputState
    -- `generator.throw(exc)` re-raises exactly what it was given.
    if method == .genThrow then
      let injected := arguments.headD AbsVal.bot
      let classes := injected.tags.foldl (fun names tag =>
        match tag with
        | .tobj className => Fset.insert className names
        | _ => names) injected.classes
      for cls in classes do
        resCase p "call" s!".{method.name}(..)" method.receiver.render s!"!{cls}"
        flow := flow.join
          (← executeRaise p { kind := .user, classes := [cls] } {} outputState)
    for cls in method.documentedExceptions do
      resCase p "call" s!".{method.name}(..)" method.receiver.render s!"!{cls}"
      flow := flow.join
        (← executeRaise p (RaiseSpec.machine cls) {} outputState)
    pure flow

end Pylate.RuleDriven.Opaque
