import Pylate.Transfers.StructuralExpressions

namespace Pylate.Tests.StructuralExpressions

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.StructuralExpressions

abbrev StructuralServices :=
  Pylate.RuleDriven.StructuralExpressions.Services

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def position (id : Nat) : Pos := ⟨NodeId.root.child id, id, 0⟩

def hasTag (value : AbsVal) (tag : Tag) : Bool :=
  tag ∈ value.tags

def lacksTag (value : AbsVal) (tag : Tag) : Bool :=
  !(hasTag value tag)

def raisedCase? (flow : Flow) (cls : String) : Option RaisedCase :=
  flow.raised.cases.find? (·.cls == cls)

def requireNormal (flow : Flow) (label : String) : IO Normal :=
  match flow.normal with
  | some normal => pure normal
  | none => throw (IO.userError s!"{label}: expected normal completion")

def requireRaised (flow : Flow) (cls : String) : IO RaisedCase :=
  match raisedCase? flow cls with
  | some raised => pure raised
  | none => throw (IO.userError s!"expected raised {cls}")

def leafEval (expression : Expr) (state : AState) : M Flow := do
  match expression with
  | .const _ constant => pure (evalConstant constant state)
  | .name p name => evalName p name state
  | _ => pure {}

def leafServices : StructuralServices where
  evalExpr := leafEval
  refine := fun _ state => pure (some state, some state)
  invokeUser := fun _ _ _ _ _ _ => pure {}

def auditContext : Actx := { policy := .audit }

def testConstantsAndNames : IO Unit := do
  let stringFlow := evalConstant (.cstr "field") {}
  let (stringValue, _) <- requireNormal stringFlow "string constant"
  ensure (hasTag stringValue .tstr &&
      stringValue.strLits == ["field"] && !stringValue.strOpen)
    "string constant lost its literal refinement"

  let localContext : Actx :=
    { policy := .audit, localScopes := [["local"]] }
  let (missingLocal, _) :=
    (evalName (position 1) "local" {}).run localContext
  ensure missingLocal.normal.isNone
    "definitely unbound local retained a normal continuation"
  let localRaised <- requireRaised missingLocal "UnboundLocalError"
  ensure (hasTag (localRaised.state.envGet "local") .tunbound)
    "local unbound exception lost its raise-point state"

  let maybeState := ({} : AState).envSet "local"
    (V [.tint, .tunbound])
  let (maybeLocal, _) :=
    (evalName (position 2) "local" maybeState).run localContext
  let (normalValue, normalState) <-
    requireNormal maybeLocal "maybe-unbound local"
  ensure (hasTag normalValue .tint && lacksTag normalValue .tunbound)
    "normal unbound-name branch was not narrowed"
  ensure (lacksTag (normalState.envGet "local") .tunbound)
    "normal state retained the unbound alternative"
  let maybeRaised <- requireRaised maybeLocal "UnboundLocalError"
  ensure (hasTag (maybeRaised.state.envGet "local") .tunbound)
    "exception state was narrowed along with the normal state"

  let (missingGlobal, _) :=
    (evalName (position 3) "missing_global" {}).run auditContext
  ensure (raisedCase? missingGlobal "NameError").isSome
    "missing global did not raise NameError"

def orderedEval (expression : Expr) (state : AState) : M Flow := do
  match expression with
  | .name _ "first" =>
    pure (Flow.ofNormal (V [.tint])
      (state.envSet "first_seen" (V [.tbool])))
  | .name _ "second" =>
    let normalState := state.envSet "second_normal" (V [.tbool])
    let raisedState := state.envSet "second_raised" (V [.tbool])
    pure {
      normal := some (V [.tstr], normalState)
      raised := {
        cases := [{
          cls := "ValueError"
          value := AbsVal.bot
          state := raisedState
          origin := {}
        }]
      }
    }
  | .name _ "third" =>
    pure (Flow.ofNormal (V [.tbool])
      (state.envSet "third_seen" (V [.tbool])))
  | .name _ "stop" =>
    pure {
      raised := {
        cases := [{
          cls := "RuntimeError"
          value := AbsVal.bot
          state := state.envSet "stopped" (V [.tbool])
          origin := {}
        }]
      }
    }
  | .name _ "after" =>
    pure (Flow.ofNormal (V [.tfloat])
      (state.envSet "after_seen" (V [.tbool])))
  | _ => leafEval expression state

def orderedServices : StructuralServices :=
  { leafServices with evalExpr := orderedEval }

def testSourceOrderedLists : IO Unit := do
  let expressions : List Expr := [
    .name (position 10) "first",
    .name (position 11) "second",
    .name (position 12) "third"
  ]
  let (result, _) :=
    (evalExpressions orderedServices expressions {}).run auditContext
  ensure (result.values.length == 3)
    "source-ordered list lost a normal value"
  match result.normal with
  | none => throw (IO.userError "source-ordered list lost normal flow")
  | some state =>
    ensure (hasTag (state.envGet "first_seen") .tbool &&
        hasTag (state.envGet "second_normal") .tbool &&
        hasTag (state.envGet "third_seen") .tbool)
      "expression states were not threaded left-to-right"
  let raised := result.raised.cases.find? (·.cls == "ValueError")
  match raised with
  | none => throw (IO.userError "earlier expression exception was lost")
  | some raised =>
    ensure (hasTag (raised.state.envGet "first_seen") .tbool &&
        hasTag (raised.state.envGet "second_raised") .tbool &&
        hasTag (raised.state.envGet "third_seen") .tunbound)
      "exception did not retain its exact pre-third-expression state"

  let stoppedExpressions : List Expr := [
    .name (position 13) "stop",
    .name (position 14) "after"
  ]
  let (stopped, _) :=
    (evalExpressions orderedServices stoppedExpressions {}).run auditContext
  ensure stopped.normal.isNone
    "guaranteed expression failure retained normal flow"
  match stopped.raised.cases.find? (·.cls == "RuntimeError") with
  | none => throw (IO.userError "guaranteed failure was lost")
  | some raised =>
    ensure (hasTag (raised.state.envGet "after_seen") .tunbound)
      "a later expression ran after guaranteed failure"

def boolEval (expression : Expr) (state : AState) : M Flow := do
  match expression with
  | .name _ "left" =>
    pure (Flow.ofNormal (V [.tnone, .tint])
      (state.envSet "left_seen" (V [.tbool])))
  | .name _ "right" =>
    pure (Flow.ofNormal (V [.tstr])
      (state.envSet "right_seen" (V [.tbool])))
  | .name _ "must_not_run" =>
    pure {
      raised := {
        cases := [{
          cls := "RuntimeError"
          value := AbsVal.bot
          state
          origin := {}
        }]
      }
    }
  | _ => leafEval expression state

def boolServices : StructuralServices :=
  { leafServices with evalExpr := boolEval }

def testBoolValueSemantics : IO Unit := do
  let falseAnd : List Expr := [
    .const (position 20) .cnone,
    .name (position 21) "must_not_run"
  ]
  let (andFlow, _) :=
    (evalBoolOp boolServices true falseAnd {}).run auditContext
  let (andValue, andState) <- requireNormal andFlow "and expression"
  ensure (hasTag andValue .tnone && lacksTag andValue .tbool)
    "`and` did not return its statically falsy operand"
  ensure (hasTag (andState.envGet "right_seen") .tunbound &&
      (raisedCase? andFlow "RuntimeError").isNone)
    "`and` evaluated its suffix after a statically falsy operand"

  let falseOr : List Expr := [
    .const (position 22) .cnone,
    .name (position 23) "right"
  ]
  let (orFlow, _) :=
    (evalBoolOp boolServices false falseOr {}).run auditContext
  let (orValue, orState) <- requireNormal orFlow "or expression"
  ensure (hasTag orValue .tstr && lacksTag orValue .tbool &&
      hasTag (orState.envGet "right_seen") .tbool)
    "`or` did not return and evaluate its suffix after a falsy operand"

  let trueOr : List Expr := [
    .const (position 24) (.cstr "selected"),
    .name (position 25) "must_not_run"
  ]
  let (shorted, _) :=
    (evalBoolOp boolServices false trueOr {}).run auditContext
  let (selected, _) <- requireNormal shorted "truthy or expression"
  ensure (selected.strLits == ["selected"] &&
      (raisedCase? shorted "RuntimeError").isNone)
    "`or` evaluated its suffix after a statically truthy operand"

  let unknownOperands : List Expr := [
    .name (position 26) "left",
    .name (position 27) "right"
  ]
  let (unknown, _) :=
    (evalBoolOp boolServices true unknownOperands {}).run auditContext
  let (unknownValue, _) <- requireNormal unknown "abstract and expression"
  ensure (hasTag unknownValue .tnone && hasTag unknownValue .tint &&
      hasTag unknownValue .tstr && lacksTag unknownValue .tbool)
    "abstract `and` stopped returning operand values"

  let (unknownOr, _) :=
    (evalBoolOp boolServices false unknownOperands {}).run auditContext
  let (unknownOrValue, _) <-
    requireNormal unknownOr "abstract or expression"
  ensure (lacksTag unknownOrValue .tnone &&
      hasTag unknownOrValue .tint && hasTag unknownOrValue .tstr)
    s!"abstract `or` retained None on its selected truthy branch: \
      {repr unknownOrValue.tags}"

def stateWith (name : String) (value : AbsVal)
    (state : AState) : Option AState :=
  if value.isBot then none else some (state.envSet name value)

def oracleRefine (expression : Expr) (state : AState) :
    M (Option AState × Option AState) := do
  match expression with
  | .name _ "x" =>
    let value := state.envGet "x"
    pure (
      stateWith "x" (value.withoutTags [.tnone]) state,
      stateWith "x" value state)
  | .cmp _ .isOp (.name _ "x") (.const _ .cnone) =>
    let value := state.envGet "x"
    pure (
      stateWith "x" (value.restrictTags [.tnone]) state,
      stateWith "x" (value.withoutTags [.tnone]) state)
  | .call _ (.name _ "isinstance")
      [(.name _ "x"), (.name _ "int")] _ =>
    let value := state.envGet "x"
    pure (
      stateWith "x" (value.restrictTags [.tint]) state,
      stateWith "x" (value.withoutTags [.tint]) state)
  | _ => pure (some state, some state)

def probeFlow (result : AbsVal) (cls : String)
    (state : AState) : Flow :=
  {
    normal := some (result, state)
    raised := {
      cases := [{
        cls
        value := AbsVal.bot
        state
        origin := {}
      }]
    }
  }

def refinementEval (expression : Expr) (state : AState) : M Flow := do
  match expression with
  | .name _ "x" =>
    pure (Flow.ofNormal (state.envGet "x") state)
  | .name _ "rhs_probe" =>
    pure (probeFlow (V [.tstr]) "AndProbe" state)
  | .name _ "none_yes" =>
    pure (probeFlow (V [.tint]) "NoneTrueProbe" state)
  | .name _ "none_no" =>
    pure (probeFlow (V [.tstr]) "NoneFalseProbe" state)
  | .name _ "isinstance_yes" =>
    pure (probeFlow (V [.tbool]) "IsinstanceTrueProbe" state)
  | .name _ "isinstance_no" =>
    pure (probeFlow (V [.tfloat]) "IsinstanceFalseProbe" state)
  | .cmp .. | .call .. =>
    pure (Flow.ofNormal (V [.tbool]) state)
  | _ => leafEval expression state

def refinementServices : StructuralServices :=
  { leafServices with
    evalExpr := refinementEval
    refine := oracleRefine }

def testPostTruthRefinement : IO Unit := do
  let maybeNone := ({} : AState).envSet "x" (V [.tnone, .tint])
  let andOperands : List Expr := [
    .name (position 28) "x",
    .name (position 29) "rhs_probe"
  ]
  let (andFlow, _) :=
    (evalBoolOp refinementServices true andOperands maybeNone).run
      auditContext
  let andProbe <- requireRaised andFlow "AndProbe"
  let andX := andProbe.state.envGet "x"
  ensure (hasTag andX .tint && lacksTag andX .tnone)
    "`x and rhs` did not pass the name-refined truthy state to rhs"

  let noneCondition := Expr.cmp (position 291) .isOp
    (.name (position 292) "x")
    (.const (position 293) .cnone)
  let (noneFlow, _) :=
    (evalConditional refinementServices noneCondition
      (.name (position 294) "none_yes")
      (.name (position 295) "none_no") maybeNone).run auditContext
  let noneTrue <- requireRaised noneFlow "NoneTrueProbe"
  let noneFalse <- requireRaised noneFlow "NoneFalseProbe"
  ensure (hasTag (noneTrue.state.envGet "x") .tnone &&
      lacksTag (noneTrue.state.envGet "x") .tint)
    "true arm of `x is None` did not receive the None-only state"
  ensure (hasTag (noneFalse.state.envGet "x") .tint &&
      lacksTag (noneFalse.state.envGet "x") .tnone)
    "false arm of `x is None` did not exclude None"

  let mixed := ({} : AState).envSet "x" (V [.tint, .tstr])
  let isinstanceCondition := Expr.call (position 296)
    (.name (position 297) "isinstance")
    [(.name (position 298) "x"), (.name (position 299) "int")] []
  let (isinstanceFlow, _) :=
    (evalConditional refinementServices isinstanceCondition
      (.name (position 300) "isinstance_yes")
      (.name (position 301) "isinstance_no") mixed).run auditContext
  let isinstanceTrue <-
    requireRaised isinstanceFlow "IsinstanceTrueProbe"
  let isinstanceFalse <-
    requireRaised isinstanceFlow "IsinstanceFalseProbe"
  ensure (hasTag (isinstanceTrue.state.envGet "x") .tint &&
      lacksTag (isinstanceTrue.state.envGet "x") .tstr)
    "true isinstance arm did not receive the retained type"
  ensure (hasTag (isinstanceFalse.state.envGet "x") .tstr &&
      lacksTag (isinstanceFalse.state.envGet "x") .tint)
    "false isinstance arm did not receive the excluded type"

def literalServices : StructuralServices := leafServices

def testLiteralAllocations : IO Unit := do
  let listPosition := position 30
  let oldLocation : Loc := ⟨listPosition.id, .list, true⟩
  let oldValue := V [.tlist] [oldLocation]
  let initial := (({} : AState).envSet "old" oldValue).heapSet oldLocation .elem (V [.tbool])
  let listElements : List Expr := [
    .const (position 31) (.cint 1),
    .const (position 32) (.cstr "x")
  ]
  let (listFlow, _) :=
    (evalListLiteral literalServices listPosition listElements initial).run
      auditContext
  let (listValue, listState) <- requireNormal listFlow "list literal"
  let newLocation : Loc := ⟨listPosition.id, .list, true⟩
  let summaryLocation : Loc := ⟨listPosition.id, .list, false⟩
  ensure (newLocation ∈ listValue.locs &&
      summaryLocation ∈ (listState.envGet "old").locs)
    "list allocation did not perform the recency fold"
  let listElementsValue := listState.heapGet newLocation .elem
  ensure (hasTag listElementsValue .tint &&
      hasTag listElementsValue .tstr)
    "list allocation lost element tags"
  ensure (listState.emptinessGet newLocation == .nonempty)
    "nonempty list allocation lost its emptiness fact"

  let tuplePosition := position 33
  let tupleElements : List Expr := [
    .const (position 34) (.cint 1),
    .const (position 35) (.cstr "x")
  ]
  let (tupleFlow, _) :=
    (evalTupleLiteral literalServices tuplePosition tupleElements {}).run
      auditContext
  let (_, tupleState) <- requireNormal tupleFlow "tuple literal"
  let tupleLocation : Loc := ⟨tuplePosition.id, .tuple, true⟩
  ensure (hasTag (tupleState.heapGet tupleLocation (.tupleSlot 0)) .tint &&
      hasTag (tupleState.heapGet tupleLocation (.tupleSlot 1)) .tstr)
    "tuple allocation did not retain positional cells"

  let setPosition := position 36
  let (setFlow, _) :=
    (evalSetLiteral literalServices setPosition
      [.const (position 37) (.cint 1)] {}).run auditContext
  let (_, setState) <- requireNormal setFlow "set literal"
  ensure (hasTag
      (setState.heapGet ⟨setPosition.id, .set, true⟩ .elem) .tint)
    "set allocation lost its element edge"

  let dictPosition := position 38
  let dictItems : List (Expr × Expr) := [
    (.const (position 39) (.cstr "field"),
      .const (position 40) (.cint 1)),
    (.const (position 41) (.cstr "other"),
      .const (position 42) (.cbool true))
  ]
  let (dictFlow, _) :=
    (evalDictLiteral literalServices dictPosition dictItems {}).run
      auditContext
  let (_, dictState) <- requireNormal dictFlow "dict literal"
  let dictLocation : Loc := ⟨dictPosition.id, .dict, true⟩
  ensure (hasTag (dictState.heapGet dictLocation .dictKeys) .tstr &&
      hasTag (dictState.heapGet dictLocation .dictValues) .tint &&
      hasTag (dictState.heapGet dictLocation .dictValues) .tbool &&
      hasTag (dictState.heapGet dictLocation (.literalKey "field")) .tint)
    "dict allocation lost key, value, or literal-field edges"

  let failingServices : StructuralServices :=
    { literalServices with
      evalExpr := fun _ state =>
        pure {
          raised := {
            cases := [{
              cls := "KeyError"
              value := AbsVal.bot
              state := state.envSet "failed_element" (V [.tbool])
              origin := {}
            }]
          }
        } }
  let failedPosition := position 43
  let (failed, _) :=
    (evalListLiteral failingServices failedPosition
      [.name (position 44) "failure"] {}).run auditContext
  ensure failed.normal.isNone
    "failed literal element still allocated a normal result"
  let failedRaised <- requireRaised failed "KeyError"
  ensure (hasTag (failedRaised.state.envGet "failed_element") .tbool)
    "literal child exception lost its exact state"

def branchEval (expression : Expr) (state : AState) : M Flow := do
  match expression with
  | .name _ "condition" =>
    pure (Flow.ofNormal (V [.tbool])
      (state.envSet "condition_seen" (V [.tbool])))
  | .name _ "yes" =>
    pure (Flow.ofNormal (V [.tint])
      (state.envSet "yes_seen" (V [.tbool])))
  | .name _ "no" =>
    pure {
      normal := some (V [.tstr],
        state.envSet "no_seen" (V [.tbool]))
      raised := {
        cases := [{
          cls := "ValueError"
          value := AbsVal.bot
          state := state.envSet "no_raised" (V [.tbool])
          origin := {}
        }]
      }
    }
  | _ => leafEval expression state

def branchServices : StructuralServices :=
  { leafServices with evalExpr := branchEval }

def testConditionalAndFString : IO Unit := do
  let (conditional, _) :=
    (evalConditional branchServices
      (.name (position 50) "condition")
      (.name (position 51) "yes")
      (.name (position 52) "no") {}).run auditContext
  let (value, _) <- requireNormal conditional "conditional expression"
  ensure (hasTag value .tint && hasTag value .tstr)
    "conditional expression did not join selected branch values"
  let raised <- requireRaised conditional "ValueError"
  ensure (hasTag (raised.state.envGet "no_raised") .tbool &&
      hasTag (raised.state.envGet "yes_seen") .tunbound)
    "conditional branch exception leaked facts from the other branch"

  let parts : List Expr := [
    .name (position 53) "first",
    .name (position 54) "second"
  ]
  let (formatted, _) :=
    (evalFString orderedServices parts {}).run auditContext
  let (formattedValue, formattedState) <-
    requireNormal formatted "f-string"
  ensure (hasTag formattedValue .tstr &&
      hasTag (formattedState.envGet "second_normal") .tbool)
    "f-string did not evaluate parts in order and return str"
  let formattedRaised <- requireRaised formatted "ValueError"
  ensure (hasTag (formattedRaised.state.envGet "third_seen") .tunbound)
    "f-string exception state was changed by a later part"

def testYieldForms : IO Unit := do
  let yieldContext : Actx := { policy := .audit, yields := [[]] }
  let (yielded, yieldOutput) :=
    (evalYield literalServices
      (some (.const (position 60) (.cint 1))) {}).run yieldContext
  let (yieldResult, _) <- requireNormal yielded "yield"
  ensure (hasTag yieldResult .tnone)
    "yield expression did not model the accepted no-send result"
  match yieldOutput.yields with
  | values :: _ =>
    ensure (values.any (fun value => hasTag value .tint))
      "yielded value was not recorded"
  | [] => throw (IO.userError "yield stack disappeared")

  let sourceLocation : Loc := ⟨61, .list, true⟩
  let sourceValue := V [.tlist] [sourceLocation]
  let sourceState := (({} : AState).envSet "source" sourceValue).heapSet sourceLocation .elem (V [.tstr])
  let sourceContext : Actx :=
    { policy := .audit, localScopes := [["source"]], yields := [[]] }
  let (delegated, delegatedOutput) :=
    (evalYieldFrom literalServices
      (.name (position 62) "source") sourceState).run sourceContext
  let (delegatedResult, _) <- requireNormal delegated "yield from"
  ensure (hasTag delegatedResult .tnone)
    "yield-from did not model the accepted no-send result"
  match delegatedOutput.yields with
  | values :: _ =>
    ensure (values.any (fun value => hasTag value .tstr))
      "yield-from did not record the source element abstraction"
  | [] => throw (IO.userError "yield-from stack disappeared")

def targetEval (receiver : AbsVal) (expression : Expr)
    (state : AState) : M Flow := do
  match expression with
  | .name _ "receiver" =>
    pure (Flow.ofNormal receiver
      (state.envSet "receiver_seen" (V [.tbool])))
  | .name _ "index" =>
    pure (Flow.ofNormal (V [.tint])
      (state.envSet "index_seen" (V [.tbool])))
  | .name _ "bad_receiver" =>
    pure (Flow.ofNormal (V [.tint])
      (state.envSet "bad_receiver_seen" (V [.tbool])))
  | _ => leafEval expression state

def targetServices (receiver : AbsVal) : StructuralServices :=
  { leafServices with evalExpr := targetEval receiver }

def testTargetBinding : IO Unit := do
  let (nameFlow, _) :=
    (bindTarget leafServices (.tname (position 70) "bound")
      (V [.tstr]) {}).run auditContext
  let (_, nameState) <- requireNormal nameFlow "name target"
  ensure (hasTag (nameState.envGet "bound") .tstr)
    "name target did not update the environment"

  let listLocation : Loc := ⟨71, .list, true⟩
  let receiver := V [.tlist] [listLocation]
  let initial := ({} : AState).heapSet listLocation .elem (V [.tint])
  let subscriptTarget := Target.tsub (position 72)
    (.name (position 73) "receiver")
    (.name (position 74) "index")
  let (stored, _) :=
    (bindTarget (targetServices receiver) subscriptTarget
      (V [.tstr]) initial).run auditContext
  let (_, storedState) <- requireNormal stored "subscript target"
  let storedElements := storedState.heapGet listLocation .elem
  ensure (hasTag storedElements .tint && hasTag storedElements .tstr)
    "subscript target did not weakly add the stored value"
  let indexRaised <- requireRaised stored "IndexError"
  ensure (hasTag (indexRaised.state.envGet "receiver_seen") .tbool &&
      hasTag (indexRaised.state.envGet "index_seen") .tbool &&
      lacksTag (indexRaised.state.heapGet listLocation .elem) .tstr)
    "subscript exception state was not captured before the heap write"

  let tupleSource : Loc := ⟨75, .tuple, true⟩
  let tupleValue := V [.ttuple] [tupleSource]
  let tupleState := ({} : AState).heapSet tupleSource .elem (V [.tint])
  let tupleTarget := Target.ttuple (position 76) [
    .tname (position 77) "first_target",
    .tsub (position 78)
      (.name (position 79) "bad_receiver")
      (.name (position 80) "index")
  ]
  let (tupleBound, _) :=
    (bindTarget (targetServices receiver) tupleTarget tupleValue
      tupleState).run auditContext
  ensure tupleBound.normal.isNone
    "failing later tuple target retained normal flow"
  let typeRaised <- requireRaised tupleBound "TypeError"
  ensure (hasTag (typeRaised.state.envGet "first_target") .tint)
    "tuple targets were not bound left-to-right before later failure"

  let (attributeBound, _) :=
    (bindTarget (targetServices anyV)
      (.tattr (position 81) (.name (position 82) "receiver") "field")
      (V [.tint]) {}).run auditContext
  ensure (attributeBound.normal.isSome &&
      (raisedCase? attributeBound "AttributeError").isSome)
    "attribute target did not route through RuleObjects"

def testOwnershipBoundary : IO Unit := do
  let plannedList := Expr.listlit (position 89)
    [.const (position 890) (.cint 1)]
  match compile? plannedList with
  | some (.sequenceLiteral .list planPosition [_]) =>
    ensure (planPosition.id == 89)
      "closed list plan lost its allocation site"
  | _ => throw (IO.userError "list literal did not compile to closed plan data")
  let (plannedResult, _) :=
    (evaluate? leafServices plannedList {}).run auditContext
  match plannedResult with
  | some flow =>
    ensure flow.normal.isSome
      "generic structural-plan executor lost list normal flow"
  | none => throw (IO.userError "compiled structural plan was not executed")

  let comprehension := Expr.comp (position 90) .clist
    (.const (position 91) (.cint 1)) none "x"
    (.name (position 92) "items") []
  let (unsupported, _) :=
    (evaluate? leafServices comprehension {}).run auditContext
  ensure unsupported.isNone
    "comprehension was accidentally claimed by the structural module"
  let operation := Expr.binop (position 93) .add
    (.const (position 94) (.cint 1))
    (.const (position 95) (.cint 2))
  let (operationResult, _) :=
    (evaluate? leafServices operation {}).run auditContext
  ensure operationResult.isNone
    "operation-level expression was accidentally claimed"

def runAll : IO Unit := do
  testConstantsAndNames
  testSourceOrderedLists
  testBoolValueSemantics
  testPostTruthRefinement
  testLiteralAllocations
  testConditionalAndFString
  testYieldForms
  testTargetBinding
  testOwnershipBoundary
  IO.println "RuleStructuralExpressions tests passed"

end Pylate.Tests.StructuralExpressions
