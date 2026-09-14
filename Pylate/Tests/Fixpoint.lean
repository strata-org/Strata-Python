import Pylate.Transfers.Fixpoint

namespace Pylate.Tests.Fixpoint

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.Fixpoint

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def containsTag (value : AbsVal) (tag : Tag) : Bool :=
  decide (tag ∈ value.tags)

def position (id : Nat) (line : Nat := 1) : Pos :=
  ⟨NodeId.root.child id, line, 0⟩

def markerExpr (id : Nat) : Expr :=
  .name (position id) s!"e{id}"

def markerBody (id : Nat) : List Stmt :=
  [.pass (position id)]

def oneRaised (cls : String) (state : AState)
    (value : AbsVal := AbsVal.bot) : RaisedFlow :=
  { cases := [{ cls, value, state, origin := {} }] }

def normalAndRaised (value : AbsVal) (normalState : AState)
    (cls : String) (raisedState : AState) : Flow :=
  {
    normal := some (value, normalState)
    raised := oneRaised cls raisedState
  }

def context : Actx := { policy := .audit }

def identityRefine (_ : Expr) (truth : TruthFlow) : M BranchFlow :=
  pure {
    truthy := truth.truthy.map (·.2)
    falsy := truth.falsy.map (·.2)
  }

def defaultServices : Fixpoint.Services where
  evalExpr := fun _ state =>
    pure (Flow.ofNormal (V [.tbool]) state)
  iterate := fun _ value state =>
    pure (Flow.ofNormal value state)
  truth := fun _ value state =>
    pure {
      truthy := some (value, state)
      falsy := some (value, state)
    }
  refine := identityRefine
  bindTarget := fun target value state =>
    match target with
    | .tname _ name =>
      pure (Flow.ofNormal value (state.envSet name value))
    | _ => pure (Flow.ofNormal value state)
  executeBody := fun _ state =>
    pure (.ofNormal state)
  requireHashable := fun _ value state =>
    pure (Flow.ofNormal value state)
  generatorExceptions := fun _ => pure []

def findRaised (raised : RaisedFlow) (cls : String) : IO RaisedCase :=
  match raised.cases.find? (·.cls == cls) with
  | some found => pure found
  | none => throw (IO.userError s!"expected raised {cls}")

def requireNormal (flow : Flow) : IO Normal :=
  match flow.normal with
  | some normal => pure normal
  | none => throw (IO.userError "expected normal expression completion")

def requireNormalCompletion (flow : Completion) : IO AState :=
  match flow.normal with
  | some state => pure state
  | none => throw (IO.userError "expected normal statement completion")

def chainState (depth : Nat) : AState := Id.run do
  let mut state := ({} : AState).envSet "x0" (V [.tstr])
  for i in [1:depth + 1] do
    state := state.envSet s!"x{i}" (V [.tnone])
  return state

def advanceChain (depth : Nat) (input : AState) : AState := Id.run do
  let mut output := input
  for i in [1:depth + 1] do
    output := output.envSet s!"x{i}" (input.envGet s!"x{i - 1}")
  return output

def testWhileBeyondOldFuel : IO Unit := do
  let depth := 45
  let services : Fixpoint.Services := {
    defaultServices with
    executeBody := fun body state =>
      match body.head? with
      | some statement =>
        if statement.pos.id == 100 then
          pure (.ofNormal (advanceChain depth state))
        else
          pure (.ofNormal (state.envSet "elseRan" (V [.tbool])))
      | none => pure (.ofNormal state)
  }
  let spec : WhileSpec := {
    position := position 90 700
    condition := markerExpr 91
    body := markerBody 100
    elseBody := markerBody 101
  }
  let (result, finalContext) :=
    (whileFixpoint services spec (chainState depth)).run context
  let normal <- requireNormalCompletion result
  ensure (containsTag (normal.envGet s!"x{depth}") .tstr)
    "while fixpoint stopped before a 45-edge propagation stabilized"
  ensure (containsTag (normal.envGet "elseRan") .tbool)
    "while exhaustion did not execute else"
  match (lineStates finalContext)[700]? with
  | none => throw (IO.userError "while loop header snapshot was not recorded")
  | some snapshot =>
    ensure (containsTag (snapshot.envGet s!"x{depth}") .tstr)
      "loop snapshot did not join the stabilized invariant"

def testWhileRoutingAndExceptionStates : IO Unit := do
  let services : Fixpoint.Services := {
    defaultServices with
    evalExpr := fun _ state =>
      let post := state.envSet "evalEffect" (V [.tint])
      pure (normalAndRaised (V [.tbool]) post "EvalError" post)
    truth := fun _ value state =>
      let post := state.envSet "truthEffect" (V [.tstr])
      pure {
        truthy := some (value, post)
        falsy := some (value, post)
        raised := oneRaised "TruthError" post
      }
    refine := fun _ truth =>
      let trueState := truth.truthy.map fun (_, state) =>
        state.envSet "refineTrue" (V [.tbool])
      let falseState := truth.falsy.map fun (_, state) =>
        state.envSet "refineFalse" (V [.tbool])
      let raisedState := (trueState.getD ({} : AState)).envSet
        "refineRaised" (V [.tfloat])
      pure {
        truthy := trueState
        falsy := falseState
        raised := oneRaised "RefineError" raisedState
      }
    executeBody := fun body state =>
      match body.head? with
      | some statement =>
        if statement.pos.id == 120 then
          pure {
            normal := some (state.envSet "normalBack" (V [.tint]))
            returned := some
              (V [.tfloat], state.envSet "returnPath" (V [.tbool]))
            broke := some (state.envSet "breakPath" (V [.tstr]))
            continued := some
              (state.envSet "continueBack" (V [.tcomplex]))
            raised := oneRaised "BodyError"
              (state.envSet "bodyRaised" (V [.tnone]))
          }
        else
          pure (.ofNormal (state.envSet "elsePath" (V [.tbool])))
      | none => pure (.ofNormal state)
  }
  let spec : WhileSpec := {
    position := position 119 710
    condition := markerExpr 118
    body := markerBody 120
    elseBody := markerBody 121
  }
  let (result, _) := (whileFixpoint services spec {}).run context
  ensure result.broke.isNone "loop-local break escaped the while"
  ensure result.continued.isNone "loop-local continue escaped the while"
  let normal <- requireNormalCompletion result
  ensure (containsTag (normal.envGet "breakPath") .tstr)
    "break did not become a normal loop exit"
  ensure (containsTag (normal.envGet "breakPath") .tunbound)
    "while else was incorrectly run on the break path"
  ensure (containsTag (normal.envGet "elsePath") .tbool)
    "while false-condition exhaustion did not run else"
  ensure (containsTag (normal.envGet "elsePath") .tunbound)
    "break path was lost when exhaustion joined"
  ensure (containsTag (normal.envGet "normalBack") .tint &&
      containsTag (normal.envGet "continueBack") .tcomplex)
    "while invariant did not join normal and continue backedges"
  match result.returned with
  | none => throw (IO.userError "return from while body was lost")
  | some (value, state) =>
    ensure (containsTag value .tfloat) "while changed returned value"
    ensure (containsTag (state.envGet "elsePath") .tunbound)
      "return from while body incorrectly ran else"
  for cls in ["EvalError", "TruthError", "RefineError", "BodyError"] do
    let _ <- findRaised result.raised cls
  let truthError <- findRaised result.raised "TruthError"
  ensure (containsTag (truthError.state.envGet "truthEffect") .tstr)
    "truth exception lost its post-protocol state"
  let refineError <- findRaised result.raised "RefineError"
  ensure (containsTag (refineError.state.envGet "refineRaised") .tfloat)
    "refinement exception lost its exact state"
  let bodyError <- findRaised result.raised "BodyError"
  ensure (containsTag (bodyError.state.envGet "bodyRaised") .tnone)
    "body exception lost its exact state"

def iterableValue (site : NodeId) (cls : LocCls) (element : AbsVal)
    (nonempty : Bool := true) : AbsVal × AState :=
  let location : Loc := ⟨site, cls, true⟩
  let state := ({} : AState).heapSet location .elem element
  let state := if nonempty
    then strongEmptinessUpdate state location .nonempty
    else state
  (V [cls.tag] [location], state)

def testForBindingFailureBlocksBodyAndElse : IO Unit := do
  let (source, sourceState) := iterableValue 200 .list (V [.tint])
  let services : Fixpoint.Services := {
    defaultServices with
    evalExpr := fun _ _ => pure (Flow.ofNormal source sourceState)
    bindTarget := fun _ _ state =>
      pure {
        raised := oneRaised "BindError"
          (state.envSet "bindFailed" (V [.tbool]))
      }
    executeBody := fun _ state => do
      markCalled "body-should-not-run"
      pure (.ofNormal state)
  }
  let spec : ForSpec := {
    position := position 201 720
    target := .tname (position 202) "item"
    iterable := markerExpr 203
    body := markerBody 204
    elseBody := markerBody 205
  }
  let (result, finalContext) :=
    (forFixpoint services spec {}).run context
  ensure result.normal.isNone
    "guaranteed binding failure on a nonempty iterable invented exhaustion"
  ensure finalContext.called.isEmpty
    "for body or else ran after guaranteed target-binding failure"
  let raised <- findRaised result.raised "BindError"
  ensure (containsTag (raised.state.envGet "bindFailed") .tbool)
    "target-binding exception lost its exact state"

def testIterationProtocolFailure : IO Unit := do
  let services : Fixpoint.Services := {
    defaultServices with
    evalExpr := fun _ state =>
      pure (Flow.ofNormal (V [.tint])
        (state.envSet "iterableEvaluated" (V [.tbool])))
    iterate := fun _ _ state =>
      pure {
        raised := oneRaised "TypeError"
          (state.envSet "iterFailed" (V [.tstr]))
      }
    executeBody := fun _ state => do
      markCalled "unreachable-loop-code"
      pure (.ofNormal state)
  }
  let spec : ForSpec := {
    position := position 206 725
    target := .tname (position 207) "item"
    iterable := markerExpr 208
    body := markerBody 209
    elseBody := markerBody 210
  }
  let (result, finalContext) :=
    (forFixpoint services spec {}).run context
  ensure result.normal.isNone
    "failed iter protocol invented a loop exhaustion"
  ensure finalContext.called.isEmpty
    "body or else ran after iter protocol failure"
  let raised <- findRaised result.raised "TypeError"
  ensure (containsTag (raised.state.envGet "iterableEvaluated") .tbool &&
      containsTag (raised.state.envGet "iterFailed") .tstr)
    "iter protocol exception lost source-order effects"

def testForBackedgesBreakElseAndGeneratorErrors : IO Unit := do
  let (source, sourceState) := iterableValue 210 .gen (V [.tint])
  let sourceState := sourceState.envSet "sourceReady" (V [.tbool])
  let services : Fixpoint.Services := {
    defaultServices with
    evalExpr := fun _ _ => pure (Flow.ofNormal source sourceState)
    bindTarget := fun target value state =>
      let name := match target with
        | .tname _ name => name
        | _ => "item"
      let post := (state.envSet name value).envSet "sawWitness"
        (if value.witness then V [.tbool] else V [.tnone])
      pure {
        normal := some (value, post)
        raised := oneRaised "BindError"
          (state.envSet "bindFailed" (V [.tstr]))
      }
    executeBody := fun body state =>
      match body.head? with
      | some statement =>
        if statement.pos.id == 214 then
          let genLocation : Loc := ⟨210, .gen, true⟩
          let sawExhausted :=
            if state.emptinessGet genLocation != .nonempty
            then V [.tbool] else V [.tnone]
          pure {
            normal := some ((state.envSet "normalBack" (V [.tint])).envSet
              "sawExhausted" sawExhausted)
            continued := some
              (state.envSet "continueBack" (V [.tstr]))
            broke := some (state.envSet "breakPath" (V [.tfloat]))
          }
        else
          pure (.ofNormal (state.envSet "elsePath" (V [.tbool])))
      | none => pure (.ofNormal state)
    generatorExceptions := fun _ =>
      pure ["StopIteration", "ValueError"]
  }
  let spec : ForSpec := {
    position := position 211 730
    target := .tname (position 212) "item"
    iterable := markerExpr 213
    body := markerBody 214
    elseBody := markerBody 215
  }
  let (result, _) := (forFixpoint services spec {}).run context
  let normal <- requireNormalCompletion result
  ensure (containsTag (normal.envGet "sawWitness") .tbool)
    "for target did not receive a multiplicity witness"
  ensure (containsTag (normal.envGet "sawExhausted") .tbool)
    "generator nonempty marker was not cleared before iteration"
  ensure (containsTag (normal.envGet "breakPath") .tfloat)
    "for break path was not retained as a normal exit"
  ensure (containsTag (normal.envGet "breakPath") .tunbound)
    "for else was incorrectly run on the break path"
  ensure (containsTag (normal.envGet "elsePath") .tbool)
    "for exhaustion did not run else"
  ensure (containsTag (normal.envGet "normalBack") .tint &&
      containsTag (normal.envGet "continueBack") .tstr)
    "for invariant did not join normal and continue backedges"
  let runtime <- findRaised result.raised "RuntimeError"
  ensure (containsTag (runtime.state.envGet "normalBack") .tint)
    "generator summary did not use the stabilized post-body state"
  let _ <- findRaised result.raised "ValueError"
  ensure (result.raised.cases.find? (·.cls == "StopIteration")).isNone
    "escaping generator StopIteration was not wrapped as RuntimeError"

structure CompHarness where
  services : Fixpoint.Services
  sourceState : AState
  source : AbsVal

def compHarness (keyTag : Tag) (bodyRaise : Option String := none)
    (generatorErrors : Fset String := []) : CompHarness :=
  let (source, sourceState) := iterableValue 300 .list (V [.tint])
  let sourceState := sourceState.envSet "item" (V [.tstr])
  let services : Fixpoint.Services := {
    defaultServices with
    evalExpr := fun expression state =>
      if expression.pos.id == 301 then
        pure (Flow.ofNormal source sourceState)
      else if expression.pos.id == 302 then
        let post := state.envSet "keyEvaluated" (V [.tint])
        let normal := some (V [keyTag], post)
        pure {
          normal
          raised := match bodyRaise with
            | some cls => oneRaised cls
                (post.envSet "keyRaised" (V [.tbool]))
            | none => {}
        }
      else if expression.pos.id == 303 then
        pure (Flow.ofNormal (V [.tbool])
          (state.envSet "valueEvaluated" (V [.tstr])))
      else
        pure (Flow.ofNormal (V [.tbool]) state)
    refine := fun _ truth =>
      pure {
        truthy := truth.truthy.map fun (_, state) =>
          state.envSet "filterTrue" (V [.tbool])
        falsy := truth.falsy.map fun (_, state) =>
          state.envSet "filterFalse" (V [.tbool])
      }
    requireHashable := fun _ value state =>
      let afterValue := containsTag (state.envGet "valueEvaluated") .tstr
      let post := state.envSet "hashRan" (V [.tbool])
      let post := if afterValue
        then post.envSet "hashAfterValue" (V [.tbool])
        else post
      pure (Flow.ofNormal value post)
    generatorExceptions := fun _ => pure generatorErrors
  }
  { services, sourceState, source }

def compSpec (kind : CompKind) (site : Nat) (withFilter : Bool := false) :
    ComprehensionSpec := {
  position := position site (800 + site)
  form := match kind with
    | .clist => .list (markerExpr 302)
    | .cset => .set (markerExpr 302)
    | .cdict => .dict (markerExpr 302) (markerExpr 303)
    | .cgen => .generator (markerExpr 302)
  target := "item"
  iterable := markerExpr 301
  filters := if withFilter then [markerExpr 304] else []
}

def resultLocation (site : Nat) (kind : CompKind) : Loc :=
  let cls := match kind with
    | .clist => LocCls.list
    | .cset => LocCls.set
    | .cdict => LocCls.dict
    | .cgen => LocCls.gen
  ⟨NodeId.root.child site, cls, true⟩

def testAllComprehensionKinds : IO Unit := do
  for (kind, expectedTag) in [
      (CompKind.clist, Tag.tlist),
      (.cset, .tset),
      (.cdict, .tdict),
      (.cgen, .tgen)] do
    let harness := compHarness .tint
    let site := match kind with
      | .clist => 310
      | .cset => 311
      | .cdict => 312
      | .cgen => 313
    let (flow, _) :=
      (comprehension harness.services (compSpec kind site true) {}).run
        context
    let (value, state) <- requireNormal flow
    ensure (containsTag value expectedTag)
      s!"{repr kind} comprehension returned the wrong runtime tag"
    ensure (containsTag (state.envGet "item") .tstr &&
        !containsTag (state.envGet "item") .tint)
      s!"{repr kind} comprehension leaked its target binding"
    ensure (containsTag (state.envGet "filterFalse") .tbool)
      s!"{repr kind} comprehension lost the skipped-filter path"
    let location := resultLocation site kind
    match kind with
    | .clist | .cset | .cgen =>
      ensure (containsTag (state.heapGet location .elem) .tint)
        s!"{repr kind} comprehension did not summarize elements"
    | .cdict =>
      ensure (containsTag (state.heapGet location .dictKeys) .tint)
        "dict comprehension did not summarize keys"
      ensure (containsTag (state.heapGet location .dictValues) .tbool)
        "dict comprehension did not summarize values"
      ensure (containsTag (state.envGet "hashAfterValue") .tbool)
        "dict comprehension hashed before evaluating its value"

def testComprehensionRecencyAndBeyondOldFuel : IO Unit := do
  let depth := 25
  let (source, sourceState0) := iterableValue 320 .list (V [.tint])
  let sourceState := (chainState depth).join sourceState0
  let elementSite := 321
  let services : Fixpoint.Services := {
    defaultServices with
    evalExpr := fun expression state =>
      if expression.pos.id == 322 then
        pure (Flow.ofNormal source sourceState)
      else
        let shifted := advanceChain depth state
        let (value, allocated) := allocate shifted elementSite .list []
        let location : Loc := ⟨elementSite, .list, true⟩
        pure (Flow.ofNormal value
          (allocated.heapSet location .elem (V [.tstr])))
  }
  let spec : ComprehensionSpec := {
    position := position 323 840
    form := .list (markerExpr 324)
    target := "item"
    iterable := markerExpr 322
  }
  let (flow, finalContext) :=
    (comprehension services spec {}).run context
  let (_, state) <- requireNormal flow
  ensure (containsTag (state.envGet s!"x{depth}") .tstr)
    "comprehension fixpoint stopped before a 25-edge propagation stabilized"
  let resultLoc : Loc := ⟨323, .list, true⟩
  let elements := state.heapGet resultLoc .elem
  ensure (decide (⟨elementSite, .list, true⟩ ∈ elements.locs))
    "comprehension lost the current allocation-site object"
  ensure (decide (⟨elementSite, .list, false⟩ ∈ elements.locs))
    "comprehension did not fold earlier allocations into the summary object"
  match (lineStates finalContext)[840]? with
  | none =>
    throw (IO.userError "comprehension fixpoint snapshot was not recorded")
  | some snapshot =>
    ensure (containsTag (snapshot.envGet s!"x{depth}") .tstr)
      "comprehension snapshot did not contain the stabilized invariant"

def testGeneratorComprehensionDefersBodyErrors : IO Unit := do
  let harness := compHarness .tint (some "BodyError")
    ["StopIteration", "ValueError"]
  let spec := compSpec .cgen 330
  let (flow, finalContext) :=
    (comprehension harness.services spec {}).run context
  let (value, _) <- requireNormal flow
  ensure (containsTag value .tgen)
    "generator comprehension did not return a generator"
  ensure flow.raised.cases.isEmpty
    "generator body exception escaped eagerly at construction"
  let classes := (finalContext.genExc.find? (·.1 == 330)).map (·.2)
    |>.getD []
  ensure (classes.contains "BodyError")
    "generator comprehension did not record body exceptions"
  ensure (classes.contains "RuntimeError" &&
      !classes.contains "StopIteration")
    "generator comprehension did not apply PEP 479 to its summary"
  ensure (classes.contains "ValueError")
    "generator comprehension lost source-generator exceptions"
  ensure (finalContext.obligations.any
      (fun obligation => obligation.node == 330 &&
        obligation.kind == "special-method"))
    "eager generator-comprehension assumption was not exposed"

def testOrdinaryComprehensionPropagatesBodyErrors : IO Unit := do
  let harness := compHarness .tint (some "BodyError")
    ["GeneratorError"]
  let (flow, _) :=
    (comprehension harness.services (compSpec .clist 331) {}).run context
  let _ <- requireNormal flow
  let _ <- findRaised flow.raised "BodyError"
  let generatorError <- findRaised flow.raised "GeneratorError"
  ensure (containsTag (generatorError.state.envGet "keyEvaluated") .tint)
    "source-generator error did not use the stabilized comprehension state"

def testGuaranteedComprehensionFailureHasNoNormalResult : IO Unit := do
  let (source, sourceState) := iterableValue 340 .list (V [.tint])
  let services : Fixpoint.Services := {
    defaultServices with
    evalExpr := fun expression _ =>
      if expression.pos.id == 341 then
        pure (Flow.ofNormal source sourceState)
      else
        pure { raised := oneRaised "ElementError" sourceState }
  }
  let spec : ComprehensionSpec := {
    position := position 342 850
    form := .list (markerExpr 343)
    target := "item"
    iterable := markerExpr 341
  }
  let (flow, _) := (comprehension services spec {}).run context
  ensure flow.normal.isNone
    "guaranteed element failure on a nonempty source invented a result"
  let _ <- findRaised flow.raised "ElementError"

def runAll : IO Unit := do
  testWhileBeyondOldFuel
  testWhileRoutingAndExceptionStates
  testForBindingFailureBlocksBodyAndElse
  testIterationProtocolFailure
  testForBackedgesBreakElseAndGeneratorErrors
  testAllComprehensionKinds
  testComprehensionRecencyAndBeyondOldFuel
  testGeneratorComprehensionDefersBodyErrors
  testOrdinaryComprehensionPropagatesBodyErrors
  testGuaranteedComprehensionFailureHasNoNormalResult
  IO.println "RuleFixpoint tests passed"

end Pylate.Tests.Fixpoint
