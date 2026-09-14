import Pylate.Rules.KnownMethods
import Pylate.Rules.Builtins

namespace Pylate.Tests.KnownMethods

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.KnownMethods

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def position : Pos := ⟨9951, 1, 0⟩

def run (method : OpaqueBuiltinMethod) (receiver : AbsVal)
    (arguments : List AbsVal) (state : AState) :
    Option Flow × Actx :=
  (execute position method receiver arguments state).run
    { policy := Policy.audit }

def normal (flow : Flow) : IO (AbsVal × AState) :=
  match flow.normal with
  | some result => pure result
  | none => throw (IO.userError "expected normal completion")

def hasRaised (flow : Flow) (cls : String) : Bool :=
  flow.raised.cases.any (·.cls == cls)

def hasTag (value : AbsVal) (tag : Tag) : Bool :=
  decide (tag ∈ value.tags)

def testSetUpdates : IO Unit := do
  let location : Loc := ⟨10, .set, true⟩
  let receiver := V [.tset] [location]
  let state := (({} : AState).heapSet location .elem (V [.tint]))
    |> (strongEmptinessUpdate · location .nonempty)
  let (result, _) :=
    run .setDifferenceUpdate receiver [receiver] state
  let some flow := result
    | throw (IO.userError "difference_update remained opaque")
  let (value, output) <- normal flow
  ensure (Tag.tnone ∈ value.tags)
    "difference_update did not return None"
  ensure (output.heapGet location .elem).isBot
    "self difference_update did not clear the receiver"
  ensure flow.raised.cases.isEmpty
    "self difference_update unexpectedly raised"

  let (failed, _) :=
    run .setIntersectionUpdate receiver [V [.tint]] state
  let some failedFlow := failed
    | throw (IO.userError "intersection_update remained opaque")
  ensure failedFlow.normal.isNone
    "non-iterable intersection_update retained normal completion"
  ensure (hasRaised failedFlow "TypeError")
    "non-iterable intersection_update omitted TypeError"
  let raised := failedFlow.raised.cases.find? (·.cls == "TypeError")
  ensure ((raised.map (fun failure =>
      hasTag (failure.state.heapGet location .elem) .tint)).getD false)
    "precondition failure observed a receiver mutation"

def testPartition : IO Unit := do
  let receiver := strLitV "left,right"
  let (result, _) :=
    run .strPartition receiver [strLitV ","] {}
  let some flow := result
    | throw (IO.userError "partition remained opaque")
  let (value, output) <- normal flow
  let tupleLocation : Loc := ⟨position.id, .tuple, true⟩
  ensure (Tag.ttuple ∈ value.tags && value.locs == [tupleLocation])
    "partition did not return a fresh tuple"
  for index in [0, 1, 2] do
    ensure (Tag.tstr ∈
        (output.heapGet tupleLocation (.tupleSlot index)).tags)
      s!"partition tuple slot {index} is not str"

  let (emptyResult, _) :=
    run .strPartition receiver [strLitV ""] {}
  let some emptyFlow := emptyResult
    | throw (IO.userError "empty-separator partition remained opaque")
  ensure (emptyFlow.normal.isNone && hasRaised emptyFlow "ValueError")
    "empty partition separator did not raise only ValueError"

  let (badResult, _) :=
    run .strPartition receiver [V [.tint]] {}
  let some badFlow := badResult
    | throw (IO.userError "invalid partition remained opaque")
  ensure (badFlow.normal.isNone && hasRaised badFlow "TypeError")
    "non-string partition separator did not raise only TypeError"

def testPopitem : IO Unit := do
  let location : Loc := ⟨20, .dict, true⟩
  let receiver := V [.tdict] [location]
  let emptyState : AState := {}
  let (emptyResult, _) :=
    run .dictPopitem receiver [] emptyState
  let some emptyFlow := emptyResult
    | throw (IO.userError "empty popitem remained opaque")
  ensure (emptyFlow.normal.isNone && hasRaised emptyFlow "KeyError")
    "empty popitem did not raise only KeyError"

  let nonemptyState :=
    ((({} : AState).heapSet location .dictKeys (V [.tstr]))
      |>.heapSet location .dictValues (V [.tint]))
      |> (strongEmptinessUpdate · location .nonempty)
  let (fullResult, _) :=
    run .dictPopitem receiver [] nonemptyState
  let some fullFlow := fullResult
    | throw (IO.userError "nonempty popitem remained opaque")
  let (value, output) <- normal fullFlow
  let tupleLocation : Loc := ⟨position.id, .tuple, true⟩
  ensure (Tag.ttuple ∈ value.tags && value.locs == [tupleLocation])
    "popitem did not return a fresh pair"
  ensure (Tag.tstr ∈ (output.heapGet tupleLocation (.tupleSlot 0)).tags)
    "popitem lost the key type"
  ensure (Tag.tint ∈ (output.heapGet tupleLocation (.tupleSlot 1)).tags)
    "popitem lost the value type"

  let typedLocation : Loc := ⟨21, .td "Row", true⟩
  let typedReceiver := V [.tdict] [typedLocation]
  let typedState :=
    ((({} : AState).heapSet typedLocation (.literalKey "name") (V [.tstr]))
      |>.heapSet typedLocation (.literalKey "note")
        (V [.tstr, .tmissing]))
      |>.heapSet typedLocation .dictKeys (V [.tstr])
  let rowInfo : ClassInfo := {
    name := "Row"
    bases := ["dict"]
    mro := ["Row"]
    fullMro := ["Row", "dict", "object"]
    layout := []
    ownLayout := []
    ownMethods := []
    isExc := false
    isDataclass := false
    fields := [
      { name := "name", required := true },
      { name := "note", required := false }
    ]
    isTypedDict := true
    total := false
  }
  let classes : ClassTable := [("Row", rowInfo)]
  let (typedResult, typedContext) :=
    (execute position .dictPopitem typedReceiver [] typedState).run
      { policy := Policy.audit, classes }
  let some typedFlow := typedResult
    | throw (IO.userError "TypedDict popitem remained opaque")
  ensure typedFlow.normal.isSome
    "TypedDict popitem lost its optional-field alternative"
  ensure (typedContext.obligations.any (·.kind == "shape-break"))
    "TypedDict popitem omitted its required-field proof obligation"
  let (_, typedOutput) <- normal typedFlow
  ensure (Tag.tmissing ∈
      (typedOutput.heapGet typedLocation (.literalKey "note")).tags)
    "TypedDict popitem did not remove an optional field"
  ensure (Tag.tstr ∈
      (typedOutput.heapGet typedLocation (.literalKey "name")).tags)
    "TypedDict popitem mutated a required field"

def testMaketrans : IO Unit := do
  let receiver := strLitV ""
  let sourceLocation : Loc := ⟨30, .dict, true⟩
  let source := V [.tdict] [sourceLocation]
  let mappingState :=
    (({} : AState).heapSet sourceLocation .dictKeys (strLitV "a"))
      |>.heapSet sourceLocation .dictValues (V [.tstr])
  let (mappingResult, _) :=
    run .strMaketrans receiver [source] mappingState
  let some mappingFlow := mappingResult
    | throw (IO.userError "mapping maketrans remained opaque")
  let (mappingValue, mappingOutput) <- normal mappingFlow
  let mappingLocation : Loc := ⟨position.id, .dict, true⟩
  ensure (Tag.tdict ∈ mappingValue.tags &&
      mappingValue.locs == [mappingLocation])
    "mapping maketrans did not return a fresh dict"
  ensure (Tag.tint ∈ (mappingOutput.heapGet mappingLocation .dictKeys).tags)
    "mapping maketrans did not normalize string keys to int"
  ensure (Tag.tstr ∈ (mappingOutput.heapGet mappingLocation .dictValues).tags)
    "mapping maketrans lost source values"

  let badKeyState :=
    (({} : AState).heapSet sourceLocation .dictKeys (strLitV "ab"))
      |>.heapSet sourceLocation .dictValues (V [.tint])
  let (badKeyResult, _) :=
    run .strMaketrans receiver [source] badKeyState
  let some badKeyFlow := badKeyResult
    | throw (IO.userError "bad-key maketrans remained opaque")
  ensure (badKeyFlow.normal.isNone && hasRaised badKeyFlow "ValueError")
    "wrong-length mapping key did not raise only ValueError"

  let (badSourceResult, _) :=
    run .strMaketrans receiver [V [.tlist]] {}
  let some badSourceFlow := badSourceResult
    | throw (IO.userError "bad-source maketrans remained opaque")
  ensure (badSourceFlow.normal.isNone && hasRaised badSourceFlow "TypeError")
    "non-dict one-argument maketrans did not raise only TypeError"

  let (result, _) :=
    run .strMaketrans receiver [strLitV "ab", strLitV "AB"] {}
  let some flow := result
    | throw (IO.userError "maketrans remained opaque")
  let (value, output) <- normal flow
  let location : Loc := ⟨position.id, .dict, true⟩
  ensure (Tag.tdict ∈ value.tags && value.locs == [location])
    "maketrans did not return a fresh dict"
  ensure (Tag.tint ∈ (output.heapGet location .dictKeys).tags)
    "maketrans key summary is not int"
  ensure (Tag.tint ∈ (output.heapGet location .dictValues).tags)
    "maketrans value summary omitted int"

  let (lengthResult, _) :=
    run .strMaketrans receiver [strLitV "a", strLitV "AB"] {}
  let some lengthFlow := lengthResult
    | throw (IO.userError "unequal-length maketrans remained opaque")
  ensure (lengthFlow.normal.isNone && hasRaised lengthFlow "ValueError")
    "unequal-length maketrans did not raise only ValueError"

  let (typeResult, _) :=
    run .strMaketrans receiver [V [.tint], strLitV "AB"] {}
  let some typeFlow := typeResult
    | throw (IO.userError "invalid maketrans remained opaque")
  ensure (typeFlow.normal.isNone && hasRaised typeFlow "TypeError")
    "non-string maketrans did not raise only TypeError"

def testOpaqueMetadata : IO Unit := do
  let opaqueCount := compiledBuiltinRules.entries.countP (·.2.isOpaque)
  -- RULE_REVIEW_CATALOG.md 10 and 12: an opaque row is not a completed rule,
  -- and none may remain in a verdict-producing configuration.
  ensure (opaqueCount == 0)
    s!"expected no opaque rows, found {opaqueCount}"
  for (name, expectedOpaque) in [
      ("maketrans", false),
      ("partition", false),
      ("rpartition", false),
      ("popitem", false)
    ] do
    let rule := compiledBuiltinRules.find?
      (.method (if name == "popitem" then .tdict else .tstr) name)
    ensure (rule.map (·.isOpaque) == some expectedOpaque)
      s!"unexpected opacity metadata for {name}"

def runAll : IO Unit := do
  testSetUpdates
  testPartition
  testPopitem
  testMaketrans
  testOpaqueMetadata
  IO.println "RuleKnownMethods tests passed"

end Pylate.Tests.KnownMethods
