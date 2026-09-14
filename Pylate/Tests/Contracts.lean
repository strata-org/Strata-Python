import Pylate.RuleLang.Contracts

namespace Pylate.Tests.Contracts

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.Contracts

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def position : Pos := ⟨9801, 8, 1⟩

def function (name : String) : FuncDef :=
  { p := position, name, params := [], body := [] }

def objectValue (site : NodeId) (className : String) : AbsVal :=
  V [.tobj className] [⟨site, .obj className, true⟩]

def hasTag (value : AbsVal) (tag : Tag) : Bool :=
  tag ∈ value.tags

def hasRaised (flow : Flow) (cls : String) : Bool :=
  flow.raised.cases.any (·.cls == cls)

def raised (flow : Flow) (cls : String) : IO RaisedCase :=
  match flow.raised.cases.find? (·.cls == cls) with
  | some result => pure result
  | none => throw (IO.userError s!"expected {cls}")

def normal (flow : Flow) : IO Normal :=
  match flow.normal with
  | some result => pure result
  | none => throw (IO.userError "expected normal completion")

def marker (name : String) (state : AState) : AState :=
  state.envSet name (V [.tbool])

def classInfo (className : String) : M (Option ClassInfo) :=
  if className == "FrozenPair" then
    pure (some {
      name := className
      bases := []
      mro := [className]
      fullMro := [className, "object"]
      layout := ["first", "second"]
      ownLayout := ["first", "second"]
      ownMethods := []
      isExc := false
      isDataclass := true
      isTypedDict := false
      fields := [
        { name := "first" },
        { name := "second" }
      ]
      total := true
    })
  else
    pure none

def resolveMethod (className methodName : String) :
    M (Option (String × FuncDef)) :=
  let supported :=
    match className, methodName with
    | "IndexGood", "__index__"
    | "IndexAfter", "__index__"
    | "IndexBad", "__index__"
    | "IndexRaise", "__index__"
    | "IterableGood", "__iter__"
    | "IterableBad", "__iter__"
    | "SequenceOnly", "__getitem__"
    | "HashFirst", "__hash__"
    | "HashSecond", "__hash__"
    | "HashBad", "__hash__"
    | "HashRaise", "__hash__"
    | "Callable", "__call__"
    | "MappingObject", "keys"
    | "Iterator", "__next__" => true
    | _, _ => false
  if supported then
    pure (some (className, function methodName))
  else
    pure none

def invokeUser (_ : Pos) (qualifiedName : String) (_ : FuncDef)
    (_ : List AbsVal) (_ : List (String × AbsVal))
    (state : AState) : M Flow := do
  match qualifiedName with
  | "IndexGood.__index__" =>
    pure (Flow.ofNormal (V [.tint]) (marker "index_good" state))
  | "IndexAfter.__index__" =>
    let sawFirst := hasTag (state.envGet "index_good") .tbool
    let post := if sawFirst then marker "index_after_good" state
      else marker "index_out_of_order" state
    pure (Flow.ofNormal (V [.tint]) post)
  | "IndexBad.__index__" =>
    pure (Flow.ofNormal (V [.tstr]) (marker "index_bad" state))
  | "IndexRaise.__index__" =>
    pure {
      raised := {
        cases := [{
          cls := "ValueError"
          value := AbsVal.bot
          origin := {}
          state := marker "index_raise" state
        }]
      }
    }
  | "IterableGood.__iter__" =>
    let post := marker "iter_good" state
    let (iterator, allocated) := allocate post 700 .gen []
    let location : Loc := ⟨700, .gen, true⟩
    pure (Flow.ofNormal iterator
      (allocated.heapSet location .elem (V [.tstr])))
  | "IterableBad.__iter__" =>
    let post := marker "iter_bad" state
    let (notIterator, allocated) := allocate post 701 .list []
    pure (Flow.ofNormal notIterator allocated)
  | "SequenceOnly.__getitem__" =>
    pure (Flow.ofNormal (V [.tstr]) (marker "getitem_called" state))
  | "HashFirst.__hash__" =>
    pure (Flow.ofNormal (V [.tint]) (marker "hash_first" state))
  | "HashSecond.__hash__" =>
    let sawFirst := hasTag (state.envGet "hash_first") .tbool
    let post := if sawFirst then marker "hash_second_after_first" state
      else marker "hash_second_without_first" state
    pure (Flow.ofNormal (V [.tint]) post)
  | "HashBad.__hash__" =>
    pure (Flow.ofNormal (V [.tstr]) (marker "hash_bad" state))
  | "HashRaise.__hash__" =>
    pure {
      raised := {
        cases := [{
          cls := "ValueError"
          value := AbsVal.bot
          origin := {}
          state := marker "hash_raise" state
        }]
      }
    }
  | "Callable.__call__" =>
    pure (Flow.ofNormal (V [.tnone])
      (marker "callable_was_invoked" state))
  | _ => pure {}

def unknownProtocol (_ : Pos) (_ : UnknownProtocol) (_ : AbsVal)
    (state : AState) : M Flow :=
  pure {
    normal := some (anyV, marker "unknown_hook_normal" state)
    raised := {
      cases := [{
        cls := "RuntimeError"
        value := AbsVal.bot
        origin := {}
        state := marker "unknown_hook_raise" state
      }]
    }
  }

def sourceHasClass (source : AbsVal) (className : String) : Bool :=
  Tag.tobj className ∈ source.tags

def dictEdge (source : AbsVal) (edge : CellSelector)
    (state : AState) : AbsVal :=
  source.locs.foldl (fun result location =>
    if location.cls.tag == .tdict then
      result.join (state.heapGet location edge)
    else result) AbsVal.bot

def writeMappingTarget (target : MappingTarget) (key value : AbsVal)
    (state : AState) : AState :=
  target.value.locs.foldl (fun current location =>
    if location.cls.tag == .tdict then
      let current :=
        (current.heapJoin location .dictKeys key).heapJoin location .dictValues value
      let current := key.strLits.foldl (fun output literal =>
        output.heapJoin location (.literalKey literal) value) current
      strongEmptinessUpdate current location .nonempty
    else current) state

def mappingTargetValues (target : MappingTarget)
    (state : AState) : AbsVal :=
  target.value.locs.foldl (fun result location =>
    if location.cls.tag == .tdict then
      result.join (state.heapGet location .dictValues)
    else result) AbsVal.bot

def orderedMarker (required next outOfOrder : String)
    (state : AState) : AState :=
  if hasTag (state.envGet required) .tbool then
    marker next state
  else
    marker outOfOrder state

def consumeOnePair (label : String) (target : MappingTarget)
    (key value : AbsVal) (state : AState) : AState :=
  let iterated := marker s!"{label}_iter" state
  let unpacked := orderedMarker s!"{label}_iter"
    s!"{label}_unpack_after_iter" s!"{label}_unpack_out_of_order"
    iterated
  let hashed := orderedMarker s!"{label}_unpack_after_iter"
    s!"{label}_hash_after_unpack" s!"{label}_hash_out_of_order"
    unpacked
  let compared := orderedMarker s!"{label}_hash_after_unpack"
    s!"{label}_equality_after_hash" s!"{label}_equality_out_of_order"
    hashed
  let written := writeMappingTarget target key value compared
  marker s!"{label}_stored" written

def consumptionRaise (cls : String) (state : AState) : Flow :=
  {
    raised := {
      cases := [{
        cls
        value := AbsVal.bot
        state
        origin := {}
      }]
    }
  }

def consumeMappingPairs (_ : Pos) (request : MappingRequest)
    (state : AState) : M Flow := do
  match request.route with
  | .mapping =>
    let keysState := marker "mapping_keys" state
    let lookupState := orderedMarker "mapping_keys"
      "mapping_getitem_after_keys" "mapping_getitem_out_of_order"
      keysState
    let hashState := orderedMarker "mapping_getitem_after_keys"
      "mapping_hash_after_getitem" "mapping_hash_out_of_order"
      lookupState
    let equalityState := orderedMarker "mapping_hash_after_getitem"
      "mapping_equality_after_hash" "mapping_equality_out_of_order"
      hashState
    let sourceKeys := dictEdge request.source .dictKeys state
    let sourceValues := dictEdge request.source .dictValues state
    let key := if sourceKeys.isBot then strLitV "mapped" else sourceKeys
    let value := if sourceValues.isBot then V [.tint] else sourceValues
    let output :=
      writeMappingTarget request.target key value equalityState
    pure (Flow.ofNormal request.target.value
      (marker "mapping_stored" output))
  | .iterablePairs =>
    if sourceHasClass request.source "PairSource" then
      let output := consumeOnePair "pair" request.target
        (strLitV "pair-key") (V [.tstr]) state
      pure (Flow.ofNormal request.target.value output)
    else if sourceHasClass request.source "WrongPair" then
      let iterated := marker "wrong_pair_iter" state
      let arity := orderedMarker "wrong_pair_iter"
        "wrong_pair_arity_after_iter" "wrong_pair_arity_out_of_order"
        iterated
      pure (consumptionRaise "ValueError" arity)
    else if sourceHasClass request.source "PartialPairs" then
      let first := consumeOnePair "first_pair" request.target
        (strLitV "first") (V [.tint]) state
      let second := if hasTag
          (mappingTargetValues request.target first) .tint then
        marker "second_pair_after_first_store" first
      else
        marker "second_pair_before_first_store" first
      pure (consumptionRaise "ValueError"
        (marker "second_pair_bad_arity" second))
    else if sourceHasClass request.source "HashFailurePairs" then
      let first := consumeOnePair "first_hash_pair" request.target
        (strLitV "first-hash") (V [.tbool]) state
      let second := if hasTag
          (mappingTargetValues request.target first) .tbool then
        marker "second_hash_after_first_store" first
      else
        marker "second_hash_before_first_store" first
      pure (consumptionRaise "TypeError"
        (marker "second_hash_failed" second))
    else
      pure (consumptionRaise "TypeError"
        (marker "pairs_not_iterable" state))
  | .unknown =>
    let normalState := consumeOnePair "unknown_pair" request.target
      (strLitV "unknown") anyV state
    let failed := marker "unknown_pairs_failed" state
    pure {
      normal := some (request.target.value, normalState)
      raised := (consumptionRaise "TypeError" failed).raised.join
        (consumptionRaise "ValueError" failed).raised
    }

def recursiveAnnotation (_ : Pos) (_ : Ann) (value : AbsVal)
    (state : AState) : M Flow :=
  pure (Flow.ofNormal (value.restrictTags [.tint])
    (marker "annotation_service" state))

def services : Pylate.RuleDriven.Contracts.Services where
  classInfo := classInfo
  resolveMethod := resolveMethod
  invokeUser := invokeUser
  unknownProtocol := unknownProtocol
  truthValue := fun _ _ state => pure (Flow.ofNormal (V [.tbool]) state)
  consumeElements := fun _ value _ state => pure (Flow.ofNormal value state)
  invokeCallable := fun _ _ _ state => pure (Flow.ofNormal anyV state)
  consumeMappingPairs := consumeMappingPairs
  recursiveAnnotation := recursiveAnnotation

def run (contract : ArgContract) (value : AbsVal)
    (state : AState := {}) : Flow × Actx :=
  (execute services position contract value state).run
    { policy := .audit }

def testRuntimeTagsAndOptional : IO Unit := do
  let (runtime, _) :=
    run (.runtimeTags [.tint]) (V [.tbool, .tint, .tstr])
  let (accepted, _) <- normal runtime
  ensure (hasTag accepted .tbool && hasTag accepted .tint &&
      !hasTag accepted .tstr)
    "RuntimeTags lost bool <: int or retained the invalid string arm"
  ensure (hasRaised runtime "TypeError")
    "mixed RuntimeTags did not retain its invalid arm"

  let (numericTower, _) :=
    run (.runtimeTags [.tfloat]) (V [.tbool, .tint, .tfloat])
  let (numericValue, _) <- normal numericTower
  ensure (hasTag numericValue .tbool && hasTag numericValue .tint &&
      hasTag numericValue .tfloat && !hasRaised numericTower "TypeError")
    "RuntimeTags did not close the numeric tower below float"

  let (optional, _) :=
    run (.optional .string) (V [.tnone, .tstr, .tint])
  let (optionalValue, _) <- normal optional
  ensure (hasTag optionalValue .tnone && hasTag optionalValue .tstr &&
      !hasTag optionalValue .tint)
    "Optional(String) did not refine its normal union"
  ensure (hasRaised optional "TypeError")
    "Optional(String) dropped the invalid integer arm"

def testSupportsIndex : IO Unit := do
  let (mixed, _) := run .supportsIndex (V [.tbool, .tstr])
  let (converted, _) <- normal mixed
  ensure (converted.tags == [.tint])
    "SupportsIndex did not canonicalize bool to int"
  ensure (hasRaised mixed "TypeError")
    "SupportsIndex did not split a mixed builtin union"

  let (good, _) := run .supportsIndex (objectValue 10 "IndexGood")
  let (goodValue, goodState) <- normal good
  ensure (goodValue.tags == [.tint] &&
      hasTag (goodState.envGet "index_good") .tbool)
    "valid __index__ did not preserve its effect and conversion"

  let (bad, _) := run .supportsIndex (objectValue 11 "IndexBad")
  ensure bad.normal.isNone
    "invalid __index__ result retained a normal path"
  let badRaise <- raised bad "TypeError"
  ensure (hasTag (badRaise.state.envGet "index_bad") .tbool)
    "invalid __index__ result raised from the pre-hook state"

  let (failed, _) := run .supportsIndex
    (objectValue 12 "IndexRaise")
  ensure failed.normal.isNone
    "raising __index__ retained a normal path"
  let hookRaise <- raised failed "ValueError"
  ensure (hasTag (hookRaise.state.envGet "index_raise") .tbool)
    "__index__ exception lost its exact hook state"

def testIterable : IO Unit := do
  let listLocation : Loc := ⟨20, .list, true⟩
  let listValue := V [.tlist] [listLocation]
  let input := listValue.join (V [.tint])
  let inputState := ({} : AState).heapSet listLocation .elem (V [.tstr])
  let (mixed, _) := run .iterable input inputState
  let (iterator, iteratorState) <- normal mixed
  let iteratorLocation : Loc := ⟨position.id, .gen, true⟩
  ensure (hasTag iterator .tgen &&
      hasTag (iteratorState.heapGet iteratorLocation .elem) .tstr)
    "builtin Iterable did not expose an iterator element summary"
  ensure (hasRaised mixed "TypeError")
    "Iterable did not split its invalid integer arm"

  let (good, _) := run .iterable
    (objectValue 21 "IterableGood")
  let (goodIterator, goodState) <- normal good
  ensure (hasTag goodIterator .tgen &&
      hasTag (goodState.envGet "iter_good") .tbool)
    "user __iter__ lost its iterator or post-hook state"

  let (bad, _) := run .iterable
    (objectValue 22 "IterableBad")
  ensure bad.normal.isNone
    "__iter__ returning a list retained a normal path"
  let badRaise <- raised bad "TypeError"
  ensure (hasTag (badRaise.state.envGet "iter_bad") .tbool)
    "invalid iterator result raised from the pre-hook state"

  let (sequence, _) := run .iterable
    (objectValue 23 "SequenceOnly")
  let (sequenceIterator, sequenceState) <- normal sequence
  ensure (hasTag sequenceIterator .tgen)
    "__getitem__ fallback did not create a sequence iterator"
  ensure (!hasTag (sequenceState.envGet "getitem_called") .tbool)
    "constructing a sequence iterator eagerly called __getitem__"

def tupleValue (site : NodeId) (slots : List AbsVal) :
    AbsVal × AState :=
  let location : Loc := ⟨site, .tuple, true⟩
  let tuple := V [.ttuple] [location]
  let state := slots.zipIdx.foldl
    (fun current (slot, index) =>
      current.heapSet location (.tupleSlot index) slot) ({} : AState)
  let elements := slots.foldl AbsVal.join AbsVal.bot
  let state := state.heapSet location .elem elements
  let state := if slots.isEmpty then state
    else strongEmptinessUpdate state location .nonempty
  (tuple, state)

def testHashable : IO Unit := do
  let listLocation : Loc := ⟨30, .list, true⟩
  let mixed := (V [.tint]).join (V [.tlist] [listLocation])
  let (mixedFlow, _) := run .hashable mixed
  let (mixedValue, _) <- normal mixedFlow
  ensure (mixedValue.tags == [.tint] &&
      hasRaised mixedFlow "TypeError")
    "Hashable did not split hashable and unhashable builtin arms"

  let (orderedTuple, orderedState) := tupleValue 31 [
    objectValue 32 "HashFirst",
    objectValue 33 "HashSecond"
  ]
  let (ordered, _) := run .hashable orderedTuple orderedState
  let (_, hashState) <- normal ordered
  ensure (hasTag (hashState.envGet "hash_first") .tbool &&
      hasTag (hashState.envGet "hash_second_after_first") .tbool &&
      !hasTag (hashState.envGet "hash_second_without_first") .tbool)
    "tuple hash hooks did not run left-to-right"

  let (stoppedTuple, stoppedState) := tupleValue 34 [
    objectValue 35 "HashRaise",
    objectValue 36 "HashSecond"
  ]
  let (stopped, _) := run .hashable stoppedTuple stoppedState
  ensure stopped.normal.isNone
    "tuple hashing continued normally after a guaranteed hook raise"
  let stoppedRaise <- raised stopped "ValueError"
  ensure (hasTag (stoppedRaise.state.envGet "hash_raise") .tbool &&
      !hasTag (stoppedRaise.state.envGet "hash_second_after_first") .tbool &&
      !hasTag (stoppedRaise.state.envGet "hash_second_without_first") .tbool)
    "tuple hashing ran a later hook after an earlier exception"

  let (bad, _) := run .hashable (objectValue 37 "HashBad")
  ensure bad.normal.isNone
    "invalid __hash__ return retained a normal path"
  let badRaise <- raised bad "TypeError"
  ensure (hasTag (badRaise.state.envGet "hash_bad") .tbool)
    "invalid __hash__ result raised from the pre-hook state"

  let summaryLocation : Loc := ⟨38, .tuple, false⟩
  let summaryTuple := V [.ttuple] [summaryLocation]
  let maybeEmptyState := ({} : AState).heapSet summaryLocation .elem (V [.tlist] [listLocation])
  let (maybeEmpty, _) :=
    run .hashable summaryTuple maybeEmptyState
  ensure (maybeEmpty.normal.isSome &&
      hasRaised maybeEmpty "TypeError")
    "maybe-empty tuple lost its empty success or nonempty hash failure"
  let definitelyNonemptyState :=
    strongEmptinessUpdate maybeEmptyState summaryLocation .nonempty
  let (definitelyNonempty, _) :=
    run .hashable summaryTuple definitelyNonemptyState
  ensure (definitelyNonempty.normal.isNone &&
      hasRaised definitelyNonempty "TypeError")
    "definitely nonempty tuple invented an empty hash-success path"

  let dataclassLocation : Loc := ⟨39, .obj "FrozenPair", true⟩
  let dataclassValue := objectValue 39 "FrozenPair"
  let dataclassState := (({} : AState).heapSet dataclassLocation (.field "first") (objectValue 391 "HashFirst")).heapSet dataclassLocation (.field "second") (objectValue 392 "HashSecond")
  let (dataclassHash, _) :=
    run .hashable dataclassValue dataclassState
  let (_, dataclassPost) <- normal dataclassHash
  ensure (hasTag (dataclassPost.envGet "hash_first") .tbool &&
      hasTag (dataclassPost.envGet "hash_second_after_first") .tbool)
    "generated dataclass hash did not hash fields in declaration order"

  let badDataclassState := (dataclassState.heapSet dataclassLocation (.field "first") (V [.tlist] [listLocation])).heapSet dataclassLocation (.field "second") (objectValue 393 "HashSecond")
  let (badDataclass, _) :=
    run .hashable dataclassValue badDataclassState
  ensure (badDataclass.normal.isNone &&
      hasRaised badDataclass "TypeError")
    "generated dataclass hash ignored an unhashable field"
  let dataclassRaise <- raised badDataclass "TypeError"
  ensure (!hasTag
      (dataclassRaise.state.envGet "hash_second_without_first") .tbool)
    "generated dataclass hash continued after an unhashable field"

def testStringContracts : IO Unit := do
  let (direct, _) :=
    run .stringOrTupleOfStrings (V [.tstr, .tint])
  let (directValue, _) <- normal direct
  ensure (directValue.tags == [.tstr] && hasRaised direct "TypeError")
    "StringOrTupleOfStrings did not split a direct mixed union"

  let mixedSlot := (V [.tstr]).join (V [.tint])
  let (tuple, tupleState) := tupleValue 40 [
    mixedSlot,
    V [.tstr]
  ]
  let (tupleFlow, _) :=
    run .stringOrTupleOfStrings tuple tupleState
  let (tupleResult, _) <- normal tupleFlow
  ensure (hasTag tupleResult .ttuple &&
      hasRaised tupleFlow "TypeError")
    "tuple-of-strings did not preserve valid and invalid slot arms"

  let (invalidTuple, invalidState) := tupleValue 41 [
    V [.tstr],
    V [.tint]
  ]
  let (invalid, _) :=
    run .stringOrTupleOfStrings invalidTuple invalidState
  ensure (invalid.normal.isSome && hasRaised invalid "TypeError")
    "ordered tuple checking lost an earlier-match or later-TypeError path"

  let (firstInvalidTuple, firstInvalidState) := tupleValue 42 [
    V [.tint],
    V [.tstr]
  ]
  let (firstInvalid, _) :=
    run .stringOrTupleOfStrings firstInvalidTuple firstInvalidState
  ensure (firstInvalid.normal.isNone &&
      hasRaised firstInvalid "TypeError")
    "tuple checking inspected a later string after a definitely invalid prefix"

  let summaryLocation : Loc := ⟨43, .tuple, false⟩
  let summaryTuple := V [.ttuple] [summaryLocation]
  let maybeEmptyState := ({} : AState).heapSet summaryLocation .elem (V [.tint])
  let (maybeEmpty, _) :=
    run .stringOrTupleOfStrings summaryTuple maybeEmptyState
  ensure (maybeEmpty.normal.isSome &&
      hasRaised maybeEmpty "TypeError")
    "maybe-empty string tuple lost its empty or invalid-element path"

def testCallableOrNone : IO Unit := do
  let functionValue :=
    V [.tfunc] (funcs := ["callback"])
  let mixed := ((V [.tnone]).join functionValue).join (V [.tint])
  let (mixedFlow, _) := run .callableOrNone mixed
  let (accepted, _) <- normal mixedFlow
  ensure (hasTag accepted .tnone && hasTag accepted .tfunc &&
      !hasTag accepted .tint && hasRaised mixedFlow "TypeError")
    "CallableOrNone did not split callable, None, and invalid arms"

  let (callableObject, _) :=
    run .callableOrNone (objectValue 44 "Callable")
  let (objectResult, objectState) <- normal callableObject
  ensure (hasTag objectResult (.tobj "Callable") &&
      !hasTag (objectState.envGet "callable_was_invoked") .tbool)
    "CallableOrNone invoked __call__ while checking callability"

  let classValue :=
    V [.ttype] (classes := ["Callable"])
  let (classFlow, _) := run .callableOrNone classValue
  let (classResult, _) <- normal classFlow
  ensure (hasTag classResult .ttype && classFlow.raised.cases.isEmpty)
    "CallableOrNone rejected a class object"

  let (notCallable, _) :=
    run .callableOrNone (objectValue 45 "NotCallable")
  ensure (notCallable.normal.isNone &&
      hasRaised notCallable "TypeError")
    "CallableOrNone accepted an object without __call__"

def freshMappingLocation : Loc :=
  ⟨position.id, .dict, true⟩

def testMappingOrIterablePairs : IO Unit := do
  let sourceLocation : Loc := ⟨60, .dict, true⟩
  let source := V [.tdict] [sourceLocation]
  let sourceState := (({} : AState).heapSet sourceLocation .dictKeys (strLitV "source-key")).heapSet sourceLocation .dictValues (V [.tfloat])
  let (mappingFlow, _) :=
    run .mappingOrIterablePairs source sourceState
  let (mappingResult, mappingState) <- normal mappingFlow
  ensure (mappingResult.locs == [freshMappingLocation] &&
      hasTag (mappingState.heapGet freshMappingLocation .dictKeys) .tstr &&
      hasTag (mappingState.heapGet freshMappingLocation .dictValues) .tfloat)
    "mapping consumption lost its normalized destination entries"
  ensure (hasTag (mappingState.envGet "mapping_keys") .tbool &&
      hasTag
        (mappingState.envGet "mapping_getitem_after_keys") .tbool &&
      hasTag
        (mappingState.envGet "mapping_hash_after_getitem") .tbool &&
      hasTag
        (mappingState.envGet "mapping_equality_after_hash") .tbool &&
      hasTag (mappingState.envGet "mapping_stored") .tbool)
    "mapping protocol phases did not execute in order"
  ensure mappingFlow.raised.cases.isEmpty
    "successful mapping consumption unexpectedly raised"

  let (pairsFlow, _) :=
    run .mappingOrIterablePairs (objectValue 61 "PairSource")
  let (_, pairsState) <- normal pairsFlow
  ensure (hasTag
      (pairsState.heapGet freshMappingLocation .dictKeys) .tstr &&
      hasTag
        (pairsState.heapGet freshMappingLocation .dictValues) .tstr)
    "iterable-pair consumption lost its key/value entry"
  ensure (hasTag (pairsState.envGet "pair_iter") .tbool &&
      hasTag (pairsState.envGet "pair_unpack_after_iter") .tbool &&
      hasTag (pairsState.envGet "pair_hash_after_unpack") .tbool &&
      hasTag (pairsState.envGet "pair_equality_after_hash") .tbool &&
      hasTag (pairsState.envGet "pair_stored") .tbool &&
      !hasTag (pairsState.envGet "pair_hash_out_of_order") .tbool)
    "iterable-pair hash/equality/write effects were reordered"

  let (wrongArity, _) :=
    run .mappingOrIterablePairs (objectValue 62 "WrongPair")
  ensure wrongArity.normal.isNone
    "wrong pair arity retained normal completion"
  let arityRaise <- raised wrongArity "ValueError"
  ensure (hasTag
      (arityRaise.state.envGet "wrong_pair_arity_after_iter") .tbool &&
      !hasTag
        (arityRaise.state.envGet "wrong_pair_arity_out_of_order") .tbool &&
      (arityRaise.state.heapGet freshMappingLocation .dictValues).isBot)
    "wrong pair arity ran hashing/writes or lost its iteration state"

  let mixedSource :=
    (objectValue 63 "MappingObject").join
      (objectValue 64 "WrongPair")
  let (mixedFlow, _) :=
    run .mappingOrIterablePairs mixedSource
  let (_, mixedNormalState) <- normal mixedFlow
  ensure (hasTag (mixedNormalState.envGet "mapping_stored") .tbool &&
      hasRaised mixedFlow "ValueError")
    "mixed mapping/pairs union lost a normal or failure arm"
  let mixedRaise <- raised mixedFlow "ValueError"
  ensure (!hasTag (mixedRaise.state.envGet "mapping_keys") .tbool &&
      (mixedRaise.state.heapGet freshMappingLocation .dictValues).isBot)
    "mixed-union failure inherited effects from the mapping arm"

  let (partialFlow, _) :=
    run .mappingOrIterablePairs (objectValue 65 "PartialPairs")
  ensure partialFlow.normal.isNone
    "later pair failure retained normal completion"
  let partialRaise <- raised partialFlow "ValueError"
  ensure (hasTag
      (partialRaise.state.heapGet freshMappingLocation .dictValues) .tint &&
      hasTag
        (partialRaise.state.envGet "first_pair_hash_after_unpack") .tbool &&
      hasTag
        (partialRaise.state.envGet "first_pair_equality_after_hash") .tbool &&
      hasTag (partialRaise.state.envGet "first_pair_stored") .tbool &&
      hasTag
        (partialRaise.state.envGet "second_pair_after_first_store") .tbool &&
      hasTag
        (partialRaise.state.envGet "second_pair_bad_arity") .tbool)
    "later pair failure lost earlier hash/equality/write effects"

  let (hashFailureFlow, _) :=
    run .mappingOrIterablePairs
      (objectValue 66 "HashFailurePairs")
  let hashRaise <- raised hashFailureFlow "TypeError"
  ensure (hashFailureFlow.normal.isNone &&
      hasTag
        (hashRaise.state.heapGet freshMappingLocation .dictValues) .tbool &&
      hasTag
        (hashRaise.state.envGet "first_hash_pair_stored") .tbool &&
      hasTag
        (hashRaise.state.envGet "second_hash_after_first_store") .tbool &&
      hasTag (hashRaise.state.envGet "second_hash_failed") .tbool)
    "hash failure lost the previously inserted pair or failing hash effect"

  let updateLocation : Loc := ⟨67, .dict, true⟩
  let updateTarget := V [.tdict] [updateLocation]
  let updateState := (({} : AState).heapSet updateLocation .dictKeys (strLitV "existing")).heapSet updateLocation .dictValues (V [.tstr])
  let (updateFlow, _) :=
    (executeMappingOrIterablePairsInto services position
      (objectValue 68 "PartialPairs") updateTarget updateState).run
        { policy := .audit }
  let updateRaise <- raised updateFlow "ValueError"
  let updateValues := updateRaise.state.heapGet updateLocation .dictValues
  ensure (hasTag updateValues .tstr && hasTag updateValues .tint)
    "existing-target consumption lost old or partially inserted values"

def testUnknownAndRecursiveBoundaries : IO Unit := do
  let (unknown, context) := run .supportsIndex anyV
  let (_, unknownState) <- normal unknown
  ensure (hasTag (unknownState.envGet "unknown_hook_normal") .tbool)
    "unknown protocol normal effects were discarded"
  let unknownRaise <- raised unknown "RuntimeError"
  ensure (hasTag (unknownRaise.state.envGet "unknown_hook_raise") .tbool)
    "unknown protocol exception state was discarded"
  ensure (hasRaised unknown "TypeError" &&
      context.obligations.any (·.kind == "dispatch-any"))
    "unknown protocol did not retain TypeError and its obligation"

  let annotation := Ann.generic "list" [.atom "int"]
  let (checked, _) :=
    run (.recursiveAnnotation annotation) (V [.tint, .tstr])
  let (checkedValue, checkedState) <- normal checked
  ensure (checkedValue.tags == [.tint] &&
      hasTag (checkedState.envGet "annotation_service") .tbool)
    "RecursiveAnnotation did not use its explicit service boundary"
  ensure (!hasRaised checked "TypeError")
    "RecursiveAnnotation fabricated a Python runtime TypeError"

def testOrderedArgumentPrelude : IO Unit := do
  let arguments : List ContractArgument := [
    {
      name := "start"
      contract := .supportsIndex
      value := objectValue 50 "IndexGood"
    },
    {
      name := "stop"
      contract := .supportsIndex
      value := objectValue 51 "IndexAfter"
    }
  ]
  let (ordered, _) :=
    (executeArguments services position arguments {}).run
      { policy := .audit }
  match ordered.normal with
  | none => throw (IO.userError "ordered contract prelude lost normal flow")
  | some (values, state) =>
    ensure (values.length == 2 &&
        values.all (fun entry => entry.2.tags == [.tint]))
      "ordered contract prelude lost converted argument values"
    ensure (hasTag (state.envGet "index_good") .tbool &&
        hasTag (state.envGet "index_after_good") .tbool &&
        !hasTag (state.envGet "index_out_of_order") .tbool)
      "argument contracts did not execute in declaration order"

  let stoppedArguments : List ContractArgument := [
    {
      name := "bad"
      contract := .supportsIndex
      value := objectValue 52 "IndexBad"
    },
    {
      name := "unreachable"
      contract := .supportsIndex
      value := objectValue 53 "IndexAfter"
    }
  ]
  let (stopped, _) :=
    (executeArguments services position stoppedArguments {}).run
      { policy := .audit }
  ensure stopped.normal.isNone
    "guaranteed contract failure entered the operation body"
  let typeError := stopped.raised.cases.find? (·.cls == "TypeError")
  match typeError with
  | none => throw (IO.userError "contract prelude lost TypeError")
  | some failure =>
    ensure (hasTag (failure.state.envGet "index_bad") .tbool &&
        !hasTag (failure.state.envGet "index_after_good") .tbool &&
        !hasTag (failure.state.envGet "index_out_of_order") .tbool)
      "later argument contract ran after guaranteed failure"

def testCanonicalUsesAndResiduals : IO Unit := do
  ensure (literalElement.label == "Hashable" &&
      sequenceIndex.label == "SupportsIndex" &&
      typedDictKey.label == "Hashable" &&
      unpackSource.label == "Iterable" &&
      callback.label == "CallableOrNone" &&
      mappingSource.label == "MappingOrIterablePairs")
    "canonical construct contracts changed"
  let (_, context) := run .hashable (V [.tint, .tlist])
  match context.residuals.find? (·.1 == position.id) with
  | none => throw (IO.userError "contract execution emitted no residual")
  | some (_, residual) =>
    -- An accepted argument is not a dispatch alternative of the call, so
    -- only the failing partition is recorded.
    ensure (residual.kind == "contract" &&
        residual.cases.isEmpty &&
        residual.errors.any (·.contains "list"))
      "contract residual omitted its exceptional row"

/-- A violated parameter annotation aborts under *every* preset.

`contract` is deliberately absent from `policyCategories`, so this relies on
`Policy.aborts`'s fail-closed branch. That is the intended design and not an
accident, which is exactly why it is pinned here: adding `"contract"` to
`policyCategories` would silently let `audit` model it, and a modelled contract
raise is a `TypeError` edge for something CPython never raises. The call site
also discards the `Exc` that `mraise` returns, which is only sound while this
holds. -/
def testContractAbortsUnderEveryPreset : IO Unit := do
  for policy in [Policy.strict, Policy.eafp, Policy.audit] do
    ensure (policy.aborts "contract")
      s!"contract raises must abort under the {policy.preset} preset"
  -- And it must not be reachable by a preset override either, which is what
  -- keeping it out of `policyCategories` buys: `override` maps over the
  -- declared categories only.
  ensure ((Policy.audit.override "contract" RMode.model).aborts "contract")
    "a preset override must not be able to model a contract raise"

def runAll : IO Unit := do
  testContractAbortsUnderEveryPreset
  testRuntimeTagsAndOptional
  testSupportsIndex
  testIterable
  testHashable
  testStringContracts
  testCallableOrNone
  testMappingOrIterablePairs
  testUnknownAndRecursiveBoundaries
  testOrderedArgumentPrelude
  testCanonicalUsesAndResiduals
  IO.println "RuleContracts tests passed"

end Pylate.Tests.Contracts
