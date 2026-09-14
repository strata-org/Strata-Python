import Pylate.Rules.Builtins
import Pylate.Transfers.Iteration

namespace Pylate.Tests.Plan

open Pylate
open Pylate.RuleDriven

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def containsTag (value : AbsVal) (tag : Tag) : Bool :=
  decide (tag ∈ value.tags)

def testPos : Pos := ⟨9001, 1, 0⟩

/-- The plan executor as the analyzer installs it, contract executor included:
    a rule that declares contracts must not be exercised without one. -/
def planFallback : Services :=
  { Services.opaque with
    applyContracts := Contracts.applyContracts {
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
    } }

def runMethod (name : String) (receiver : AbsVal)
    (input : CallInput) (state : AState) : Flow × Actx :=
  let services := compiledFoundationRules.services planFallback
  (services.invoke testPos (.method name) (some receiver)
    input.positional input.keywords state).run { policy := Policy.audit }

def runFunction (name : String) (input : CallInput)
    (state : AState := {}) : Flow × Actx :=
  let services := compiledBuiltinRules.services planFallback
  (services.invoke testPos (.function name) none
    input.positional input.keywords state).run { policy := Policy.audit }

def normalState (flow : Flow) : IO (AbsVal × AState) :=
  match flow.normal with
  | some normal => pure normal
  | none => throw (IO.userError "expected normal completion")

def raisedCase (flow : Flow) (cls : String) : IO RaisedCase :=
  match flow.raised.cases.find? (·.cls == cls) with
  | some raised => pure raised
  | none => throw (IO.userError s!"expected {cls}")

def testAppend : IO Unit := do
  let location : Loc := ⟨10, .list, true⟩
  let receiver := V [.tlist] [location]
  let state := ({} : AState).heapSet location .elem (V [.tint])
  let (flow, _) := runMethod "append" receiver
    ⟨[V [.tstr]], []⟩ state
  let (value, output) <- normalState flow
  ensure (containsTag value .tnone) "append did not return None"
  let elements := output.heapGet location .elem
  ensure (containsTag elements .tint && containsTag elements .tstr)
    "append lost the old or new element type"
  ensure (output.emptinessGet location == .nonempty)
    "append did not establish NonEmpty"
  ensure flow.raised.cases.isEmpty "append unexpectedly raised"

def testClear : IO Unit := do
  let location : Loc := ⟨17, .list, true⟩
  let receiver := V [.tlist] [location]
  let state := ({} : AState).heapSet location .elem (V [.tint])
  let (flow, _) := runMethod "clear" receiver {} state
  let (value, output) <- normalState flow
  ensure (containsTag value .tnone) "clear did not return None"
  ensure (output.heapGet location .elem).isBot
    "clear did not empty a sole recent receiver"
  ensure (output.emptinessGet location == .empty)
    "clear did not establish Empty"
  ensure flow.raised.cases.isEmpty "clear unexpectedly raised"

def testCopy : IO Unit := do
  let source : Loc := ⟨18, .list, true⟩
  let receiver := V [.tlist] [source]
  let state := ({} : AState).heapSet source .elem (V [.tstr])
  let (flow, _) := runMethod "copy" receiver {} state
  let (value, output) <- normalState flow
  let copied : Loc := ⟨testPos.id, .list, true⟩
  ensure (containsTag value .tlist && value.locs == [copied])
    "copy did not return the fresh list"
  ensure (containsTag (output.heapGet copied .elem) .tstr)
    "copy lost the source element type"
  ensure (containsTag (output.heapGet source .elem) .tstr)
    "copy mutated the source list"
  ensure flow.raised.cases.isEmpty "copy unexpectedly raised"

def testSignatureFailurePrecedesMutation : IO Unit := do
  let location : Loc := ⟨11, .list, true⟩
  let receiver := V [.tlist] [location]
  let state := ({} : AState).heapSet location .elem (V [.tint])
  let (flow, _) := runMethod "append" receiver {} state
  ensure flow.normal.isNone "missing append argument had a normal path"
  let raised <- raisedCase flow "TypeError"
  let elements := raised.state.heapGet location .elem
  ensure (containsTag elements .tint && !containsTag elements .tstr)
    "signature failure observed a mutation"

def testHashabilityFailurePrecedesMutation : IO Unit := do
  let setLocation : Loc := ⟨12, .set, true⟩
  let listLocation : Loc := ⟨13, .list, true⟩
  let receiver := V [.tset] [setLocation]
  let argument := V [.tlist] [listLocation]
  let state := (({} : AState).heapSet setLocation .elem (V [.tint]))
    |>.heapSet listLocation .elem (V [.tstr])
  let (flow, _) := runMethod "add" receiver ⟨[argument], []⟩ state
  ensure flow.normal.isNone "unhashable set element had a normal path"
  let raised <- raisedCase flow "TypeError"
  let elements := raised.state.heapGet setLocation .elem
  ensure (containsTag elements .tint && !containsTag elements .tlist)
    "hashability failure observed the set mutation"

def testSameInputAlternatives : IO Unit := do
  let location : Loc := ⟨14, .list, true⟩
  let receiver := V [.tlist] [location]
  let state := ({} : AState).heapSet location .elem (V [.tbool])
  let overwrite (value : ValueExpr) : Plan :=
    .mutate (.clear (.read .receiver) .list (.fixed .elem))
      (.mutate (.grow (.read .receiver) .list (.fixed .elem) value)
        (.normal .none))
  let plan := Plan.alternatives [overwrite .int, overwrite .str]
  let (planned, _) := (executePlan Services.opaque testPos plan
    { receiver } state).run { policy := Policy.audit }
  let flow := planned.flow
  let (_, output) <- normalState flow
  let elements := output.heapGet location .elem
  ensure (containsTag elements .tint && containsTag elements .tstr)
    "alternatives were not joined"
  ensure (!containsTag elements .tbool)
    "an alternative did not start from the common input"

def testProtocolThreadsPostHookState : IO Unit := do
  let location : Loc := ⟨15, .list, true⟩
  let receiver := V [.tlist] [location]
  let state := ({} : AState).heapSet location .elem (V [.tint])
  let grow (value : ValueExpr) (result : ValueExpr) : Plan :=
    .mutate (.grow (.read .receiver) .list (.fixed .elem) value) (.normal result)
  let plan := Plan.protocolChain
    [grow .bool .notImplemented, grow .str .int]
    (.raise (RaiseSpec.machine "TypeError"))
  let (planned, _) := (executePlan Services.opaque testPos plan
    { receiver } state).run { policy := Policy.audit }
  let flow := planned.flow
  let (value, output) <- normalState flow
  ensure (containsTag value .tint) "protocol chain lost the successful result"
  let elements := output.heapGet location .elem
  ensure (containsTag elements .tbool && containsTag elements .tstr)
    "NotImplemented did not continue from the post-hook state"
  ensure flow.raised.cases.isEmpty "protocol fallback ran after success"

def testPostMutationRaise : IO Unit := do
  let location : Loc := ⟨16, .list, true⟩
  let receiver := V [.tlist] [location]
  let state := ({} : AState).heapSet location .elem (V [.tint])
  let plan := Plan.mutate
    (.grow (.read .receiver) .list (.fixed .elem) .str)
    (.raise { kind := .user, classes := ["ValueError"] })
  let (planned, _) := (executePlan Services.opaque testPos plan
    { receiver } state).run { policy := Policy.audit }
  let flow := planned.flow
  ensure flow.normal.isNone "raising plan retained a normal path"
  let raised <- raisedCase flow "ValueError"
  ensure (containsTag (raised.state.heapGet location .elem) .tstr)
    "post-mutation raise captured the pre-mutation state"

def testEmptySetConstructor : IO Unit := do
  let (flow, _) := runFunction "set" {}
  let (value, output) <- normalState flow
  let location : Loc := ⟨testPos.id, .set, true⟩
  ensure (containsTag value .tset && value.locs == [location])
    "set() did not return a fresh set"
  ensure (output.heapGet location .elem).isBot
    "set() did not retain an empty element summary"
  ensure flow.raised.cases.isEmpty "set() unexpectedly raised"

def testBuiltinFunctionInventory : IO Unit := do
  for name in builtinFuncs do
    ensure
      ((compiledBuiltinRules.find? (.function name)).isSome)
      s!"builtin function '{name}' has no compiled rule"

def testBuiltinMethodInventory : IO Unit := do
  let tags : List Tag :=
    [.tlist, .tdict, .tset, .tstr, .ttuple, .trange, .tgen]
  for tag in tags do
    for name in knownMethods tag do
      ensure
        ((compiledBuiltinRules.find? (.method tag name)).isSome)
        s!"builtin method '{tag.render}.{name}' has no compiled rule"

def testStaticValidation : IO Unit := do
  let invalid : RuleSet :=
    { rules := [{
        key := .function "bad"
        callable := {
          signature := {}
          body := .normal (.read (.local 0))
        }
      }] }
  match compileRules invalid with
  | .error errors =>
    ensure (!errors.isEmpty) "invalid plan produced an empty diagnostic"
  | .ok _ => throw (IO.userError "out-of-scope local passed validation")

def runAll : IO Unit := do
  testAppend
  testClear
  testCopy
  testSignatureFailurePrecedesMutation
  testHashabilityFailurePrecedesMutation
  testSameInputAlternatives
  testProtocolThreadsPostHookState
  testPostMutationRaise
  testEmptySetConstructor
  testBuiltinFunctionInventory
  testBuiltinMethodInventory
  testStaticValidation
  IO.println "RulePlan tests passed"

end Pylate.Tests.Plan
