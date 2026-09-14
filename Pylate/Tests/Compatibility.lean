import Pylate.Transfers.Compatibility

namespace Pylate.Tests.Compatibility

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.Compatibility

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def containsTag (value : AbsVal) (tag : Tag) : Bool :=
  decide (tag ∈ value.tags)

def markedState (name : String) (tag : Tag) : AState :=
  ({} : AState).envSet name (V [tag])

def expectStateTag (state : Option AState) (name : String) (tag : Tag)
    (message : String) : IO Unit :=
  match state with
  | none => throw (IO.userError s!"{message}: missing state")
  | some state =>
    ensure (containsTag (state.envGet name) tag) message

def legacyClasses : Fset String :=
  Fset.insert "RuntimeError"
    (Fset.insert "ValueError" (Fset.insert "LookupError" []))

/-- One transfer result carries a state per raised class, so two classes raised at
    one point keep their own states. The joined `Exc` view is still available, and
    still joins. -/
def testPerClassRaisePointsStayDistinct : IO Unit := do
  let first := markedState "raisePoint" .tint
  let second := markedState "raisePoint" .tstr
  let flow : Flow := {
    raised := {
      cases := [
        { cls := "FirstError", value := V [.tobj "FirstError"], state := first, origin := {} },
        { cls := "SecondError", value := V [.tobj "SecondError"], state := second, origin := {} }
      ]
    }
  }
  ensure flow.normal.isNone "a raised-only flow has no normal completion"
  let some firstCase := flow.raised.cases.find? (·.cls == "FirstError")
    | throw (IO.userError "lost the first raised class")
  let some secondCase := flow.raised.cases.find? (·.cls == "SecondError")
    | throw (IO.userError "lost the second raised class")
  ensure (containsTag (firstCase.state.envGet "raisePoint") .tint &&
      !containsTag (firstCase.state.envGet "raisePoint") .tstr)
    "the first raise point absorbed the second"
  ensure (containsTag (secondCase.state.envGet "raisePoint") .tstr &&
      !containsTag (secondCase.state.envGet "raisePoint") .tint)
    "the second raise point absorbed the first"
  ensure (flow.exc.tags == ["FirstError", "SecondError"])
    "the joined view changed raised-case order"
  match flow.exc.st with
  | none => throw (IO.userError "the joined view dropped exceptional states")
  | some state =>
    let value := state.envGet "raisePoint"
    ensure (containsTag value .tint && containsTag value .tstr)
      "the joined view is supposed to join the per-class states"

def testAMultiAllFiveCompletions : IO Unit := do
  let normalState := markedState "normal" .tint
  let returnState := markedState "return" .tstr
  let breakState := markedState "break" .tbool
  let continueState := markedState "continue" .tfloat
  let exceptionState := markedState "raise" .tnone
  let legacy : AMulti := {
    normal := some normalState
    brk := some breakState
    cont := some continueState
    retSt := some returnState
    retVal := V [.ttuple]
    excSt := some exceptionState
    excs := legacyClasses
  }
  let completion := completionOfAMulti
    (markedState "unusedFallback" .tcomplex) legacy
  expectStateTag completion.normal "normal" .tint
    "AMulti-to-Completion lost normal"
  expectStateTag completion.broke "break" .tbool
    "AMulti-to-Completion lost break"
  expectStateTag completion.continued "continue" .tfloat
    "AMulti-to-Completion lost continue"
  match completion.returned with
  | none => throw (IO.userError "AMulti-to-Completion lost return")
  | some (value, state) =>
    ensure (containsTag value .ttuple)
      "AMulti-to-Completion lost the return value"
    ensure (containsTag (state.envGet "return") .tstr)
      "AMulti-to-Completion lost the return state"
  ensure (completion.raised.cases.map (·.cls) == legacyClasses)
    "AMulti-to-Completion reversed legacy Fset insertion order"
  for raised in completion.raised.cases do
    ensure (containsTag (raised.state.envGet "raise") .tnone)
      "AMulti-to-Completion lost the shared exception state"

  let roundTrip := aMultiOfCompletion completion
  ensure (roundTrip.excs == legacyClasses)
    "Completion-to-AMulti reversed legacy Fset insertion order"
  expectStateTag roundTrip.normal "normal" .tint
    "AMulti round trip lost normal"
  expectStateTag roundTrip.brk "break" .tbool
    "AMulti round trip lost break"
  expectStateTag roundTrip.cont "continue" .tfloat
    "AMulti round trip lost continue"
  expectStateTag roundTrip.retSt "return" .tstr
    "AMulti round trip lost return"
  ensure (containsTag roundTrip.retVal .ttuple)
    "AMulti round trip lost the return value"
  expectStateTag roundTrip.excSt "raise" .tnone
    "AMulti round trip lost raise"

def testAMultiNormalAbsence : IO Unit := do
  let completion := completionOfAMulti
    (markedState "fallback" .tbool) ({} : AMulti)
  ensure completion.normal.isNone
    "empty AMulti acquired a normal completion"
  let legacy := aMultiOfCompletion ({} : Completion)
  ensure legacy.normal.isNone
    "empty Completion acquired a normal legacy completion"

def testCompletionExceptionalStateCollapse : IO Unit := do
  let completion : Completion := {
    raised := {
      cases := [
        {
          cls := "AlphaError"
          value := V [.tobj "AlphaError"]
          origin := {}
          state := markedState "raisePoint" .tint
        },
        {
          cls := "BetaError"
          value := V [.tobj "BetaError"]
          origin := {}
          state := markedState "raisePoint" .tstr
        }
      ]
    }
  }
  let legacy := aMultiOfCompletion completion
  ensure (legacy.excs == ["AlphaError", "BetaError"])
    "Completion-to-AMulti changed raised-case order"
  match legacy.excSt with
  | none => throw (IO.userError "Completion-to-AMulti lost raise states")
  | some state =>
    let value := state.envGet "raisePoint"
    ensure (containsTag value .tint && containsTag value .tstr)
      "Completion-to-AMulti did not join per-class raise states"

  let recovered := completionOfAMulti
    (markedState "unusedFallback" .tbool) legacy
  for raised in recovered.raised.cases do
    let value := raised.state.envGet "raisePoint"
    ensure (containsTag value .tint && containsTag value .tstr)
      "AMulti recovery did not retain its joined exception state"
    ensure raised.value.isBot
      "AMulti recovery invented an exception value"

def testMalformedAMultiUsesExplicitFallback : IO Unit := do
  let fallback := markedState "fallback" .tcomplex
  let malformed : AMulti := {
    excs := ["BrokenLegacyError"]
  }
  let completion := completionOfAMulti fallback malformed
  match completion.raised.cases with
  | [raised] =>
    ensure (containsTag (raised.state.envGet "fallback") .tcomplex)
      "missing AMulti.excSt did not use the explicit fallback"
  | _ => throw (IO.userError "malformed AMulti exception class was lost")

def runAll : IO Unit := do
  testPerClassRaisePointsStayDistinct
  testAMultiAllFiveCompletions
  testAMultiNormalAbsence
  testCompletionExceptionalStateCollapse
  testMalformedAMultiUsesExplicitFallback
  IO.println "RuleCompatibility tests passed"

end Pylate.Tests.Compatibility
