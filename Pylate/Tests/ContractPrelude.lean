/-
The compiled contract prelude of a builtin rule: a failing argument contract
must suppress the rule body, including its mutation, and a mixed argument must
retain both outcomes from the same input state.
-/
import Pylate.Rules.Builtins
import Pylate.Transfers.Iteration

namespace Pylate.Tests.ContractPrelude

open Pylate
open Pylate.RuleDriven

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def position : Pos := ⟨9401, 3, 0⟩

def hasTag (value : AbsVal) (tag : Tag) : Bool :=
  tag ∈ value.tags

def hasRaised (flow : Flow) (cls : String) : Bool :=
  flow.raised.cases.any (·.cls == cls)

def raisedCase (flow : Flow) (cls : String) : IO RaisedCase :=
  match flow.raised.cases.find? (·.cls == cls) with
  | some result => pure result
  | none => throw (IO.userError s!"expected {cls}")

def contractServices : Contracts.Services :=
  {
    classInfo := fun _ => pure none
    resolveMethod := fun _ _ => pure none
    invokeUser := fun _ _ _ _ _ state => pure (Flow.ofNormal anyV state)
    unknownProtocol := fun _ _ _ state => pure (Flow.ofNormal anyV state)
    truthValue := fun _ _ state => pure (Flow.ofNormal (V [.tbool]) state)
    consumeElements := fun _ value _ state =>
      pure (Flow.ofNormal value state)
    invokeCallable := fun _ _ _ state => pure (Flow.ofNormal anyV state)
    consumeMappingPairs := fun _ _ state => pure (Flow.ofNormal anyV state)
    recursiveAnnotation := fun _ _ value state =>
      pure (Flow.ofNormal value state)
  }

/-- The builtin rule set with the contract executor installed, as the analyzer
    installs it. -/
def services : Services :=
  compiledBuiltinRules.services
    { Services.opaque with
      applyContracts := Contracts.applyContracts contractServices }

def runMethod (name : String) (receiver : AbsVal) (arguments : List AbsVal)
    (state : AState) : Flow × Actx :=
  (services.invoke position (.method name) (some receiver) arguments []
    state).run { policy := Policy.audit }

def listWith (site : NodeId) (element : AbsVal) : AbsVal × AState :=
  let location : Loc := ⟨site, .list, true⟩
  let (_, allocated) := allocate {} site .list []
  (V [.tlist] [location], allocated.heapSet location .elem element)

def testFailingIndexBlocksMutation : IO Unit := do
  let (receiver, state) := listWith 10 (V [.tint])
  let location : Loc := ⟨10, .list, true⟩
  let (flow, _) := runMethod "insert" receiver [V [.tstr], V [.tfloat]] state
  ensure flow.normal.isNone
    "a definitely invalid index retained a normal insert"
  let failure <- raisedCase flow "TypeError"
  let elements := failure.state.heapGet location .elem
  ensure (!(hasTag elements .tfloat))
    "insert mutated the receiver on its index-conversion failure"
  ensure (hasTag elements .tint)
    "insert lost the pre-call element summary"

def testValidIndexStillMutates : IO Unit := do
  let (receiver, state) := listWith 11 (V [.tint])
  let location : Loc := ⟨11, .list, true⟩
  let (flow, _) := runMethod "insert" receiver [V [.tint], V [.tfloat]] state
  let some (value, output) := flow.normal
    | throw (IO.userError "a valid index lost the normal insert")
  ensure (hasTag value .tnone) "insert did not return None"
  ensure (hasTag (output.heapGet location .elem) .tfloat)
    "insert did not record the inserted element"
  ensure (!(hasRaised flow "TypeError"))
    "a definitely valid index invented a TypeError"
  ensure (output.emptinessGet location == .nonempty)
    "insert did not establish NonEmpty"

def testMixedIndexKeepsBothOutcomes : IO Unit := do
  let (receiver, state) := listWith 12 (V [.tint])
  let location : Loc := ⟨12, .list, true⟩
  let (flow, _) :=
    runMethod "insert" receiver [V [.tint, .tstr], V [.tfloat]] state
  let some (_, output) := flow.normal
    | throw (IO.userError "a mixed index lost its valid arm")
  ensure (hasTag (output.heapGet location .elem) .tfloat)
    "the valid arm of a mixed index did not mutate"
  let failure <- raisedCase flow "TypeError"
  ensure (!(hasTag (failure.state.heapGet location .elem) .tfloat))
    "the invalid arm of a mixed index observed the mutation"

def testStringContract : IO Unit := do
  let (invalid, _) := runMethod "replace" (V [.tstr]) [V [.tint], V [.tstr]] {}
  ensure invalid.normal.isNone
    "a non-string replace operand retained a normal result"
  ensure (hasRaised invalid "TypeError")
    "a non-string replace operand did not raise TypeError"
  let (valid, _) := runMethod "replace" (V [.tstr]) [V [.tstr], V [.tstr]] {}
  ensure valid.normal.isSome "valid replace lost its normal result"
  ensure (!(hasRaised valid "TypeError"))
    "valid replace invented a TypeError"

def testOptionalStringContract : IO Unit := do
  let (none', _) := runMethod "strip" (V [.tstr]) [V [.tnone]] {}
  ensure (none'.normal.isSome && !(hasRaised none' "TypeError"))
    "strip(None) must be accepted"
  let (bad, _) := runMethod "strip" (V [.tstr]) [V [.tint]] {}
  ensure (bad.normal.isNone && hasRaised bad "TypeError")
    "strip(int) must raise only TypeError"

def runAll : IO Unit := do
  testFailingIndexBlocksMutation
  testValidIndexStillMutates
  testMixedIndexKeepsBothOutcomes
  testStringContract
  testOptionalStringContract
  IO.println "RuleContractPrelude tests passed"

end Pylate.Tests.ContractPrelude
