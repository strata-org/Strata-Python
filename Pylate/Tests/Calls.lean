import Pylate.Transfers.Calls

namespace Pylate.Tests.Calls

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.Calls

abbrev CallServices := Pylate.RuleDriven.Calls.Services

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def containsTag (value : AbsVal) (tag : Tag) : Bool :=
  decide (tag ∈ value.tags)

def position (id : Nat) : Pos :=
  { id := NodeId.root.child id, line := id, col := 0 }

def markerBody (id : Nat) : List Stmt :=
  [.pass (position id)]

def normalCase (flow : Flow) : IO (AbsVal × AState) :=
  match flow.normal with
  | some normal => pure normal
  | none => throw (IO.userError "expected normal completion")

def raisedCase (flow : Flow) (cls : String) : IO RaisedCase :=
  match flow.raised.cases.find? (·.cls == cls) with
  | some raised => pure raised
  | none => throw (IO.userError s!"expected raised {cls}")

def hasObligation (context : Actx) (kind : String) : Bool :=
  context.obligations.any (·.kind == kind)

def auditContext (classes : ClassTable := [])
    (functions : List (String × FuncDef) := []) : Actx :=
  { policy := Policy.audit, classes, funcs := functions }

def buildClasses (definitions : List ClassDef) : IO ClassTable :=
  match buildClassTable definitions with
  | .ok table => pure table
  | .error _ => throw (IO.userError "test class table failed to build")

def oneParamFunction (name : String) (annotation : Option Ann := none)
    (returnAnnotation : Option Ann := none)
    (default : Option Expr := none) : FuncDef :=
  {
    p := position 10
    name
    params := [{ name := "x", ann := annotation, default }]
    retAnn := returnAnnotation
    body := markerBody 11
  }

def testRuleDataAndAnnotatedCall : IO Unit := do
  let function := oneParamFunction "narrow"
    (some (.atom "int")) (some (.atom "int"))
  let rule := compileUserCallRule "narrow" function
  ensure (rule.completion == .ordinary)
    "ordinary function compiled with the wrong completion rule"
  ensure (rule.signature.parameters.length == 1 &&
      rule.signature.parameters.head!.required)
    "required parameter was not explicit in the call rule"
  ensure rule.parameters.head!.annotation.isSome
    "parameter annotation was not retained in first-order rule data"
  ensure rule.returnAnnotation.isSome
    "return annotation was not retained in first-order rule data"

  let services : CallServices := {
    executeBody := fun _ state =>
      pure {
        returned := some
          (state.envGet "x", state.envSet "calleeOnly" (V [.tstr]))
      }
  }
  let caller := ({} : AState).envSet "caller" (V [.tbool])
  let argument := V [.tint, .tstr]
  let (flow, context) :=
    (execute services (position 100) (.userCall rule)
      { arguments := [argument] } caller).run (auditContext)
  let (value, output) <- normalCase flow
  ensure (containsTag value .tint && !containsTag value .tstr)
    "annotation assume did not narrow the parameter and return"
  ensure (containsTag (output.envGet "caller") .tbool)
    "callee completion did not restore the caller environment"
  ensure (containsTag (output.envGet "calleeOnly") .tunbound)
    "callee-local binding escaped through the call boundary"
  ensure (hasObligation context "param-annotation")
    "failed parameter entailment did not emit its check"
  ensure (!hasObligation context "return-annotation")
    "narrowed return unexpectedly failed its annotation"
  ensure (context.called.contains "narrow")
    "call rule did not mark the function as reached"
  ensure (context.callStack.isEmpty && context.localScopes.isEmpty &&
      context.ctxStack.isEmpty)
    "ordinary call frame was not removed"

def testBindingFailureHasNoNormalFlow : IO Unit := do
  let function := oneParamFunction "required"
  let services : CallServices := {
    executeBody := fun _ state =>
      pure (.ofNormal (state.envSet "entered" (V [.tbool])))
  }
  let caller := ({} : AState).envSet "caller" (V [.tint])
  let (flow, _) :=
    (invokeUser services (position 101) "required" function [] [] caller)
      |>.run (auditContext)
  ensure flow.normal.isNone
    "missing required argument retained a normal completion"
  let raised <- raisedCase flow "TypeError"
  ensure (containsTag (raised.state.envGet "caller") .tint)
    "signature TypeError lost the incoming state"
  ensure (containsTag (raised.state.envGet "entered") .tunbound)
    "function body ran after signature binding failed"

def testDefaultSummary : IO Unit := do
  let defaultExpression := Expr.const (position 12) (.cint 7)
  let function := oneParamFunction "with_default"
    (default := some defaultExpression)
  let services : CallServices := {
    executeBody := fun _ state =>
      pure { returned := some (state.envGet "x", state) }
  }
  let (flow, context) :=
    (invokeUser services (position 102) "with_default" function [] [] {})
      |>.run (auditContext)
  let (value, _) <- normalCase flow
  ensure (containsTag value .tany)
    "uncaptured definition-time default was not conservatively abstracted"
  ensure (hasObligation context "default-arg")
    "abstract default use was not made explicit"

def testDistinctExceptionalStates : IO Unit := do
  let function : FuncDef := {
    p := position 20
    name := "fails"
    params := []
    body := markerBody 21
  }
  let location : Loc :=
    { site := 500, cls := .list, recent := true }
  let services : CallServices := {
    executeBody := fun _ state =>
      pure {
        raised := {
          cases := [
            {
              cls := "ValueError"
              value := V [.tobj "ValueError"]
              state := (state.envSet "calleeOnly" (V [.tbool]))
                |>.heapSet location .elem (V [.tint])
              origin := {}
            },
            {
              cls := "TypeError"
              value := V [.tobj "TypeError"]
              state := (state.envSet "calleeOnly" (V [.tbool]))
                |>.heapSet location .elem (V [.tstr])
              origin := {}
            }
          ]
        }
      }
  }
  let caller := ({} : AState).envSet "caller" (V [.tfloat])
  let (flow, _) :=
    (invokeUser services (position 103) "fails" function [] [] caller)
      |>.run (auditContext)
  ensure flow.normal.isNone
    "guaranteed failing function acquired a normal completion"
  let valueError <- raisedCase flow "ValueError"
  let typeError <- raisedCase flow "TypeError"
  ensure (containsTag (valueError.state.heapGet location .elem) .tint &&
      !containsTag (valueError.state.heapGet location .elem) .tstr)
    "ValueError lost its exact raise-point heap"
  ensure (containsTag (typeError.state.heapGet location .elem) .tstr &&
      !containsTag (typeError.state.heapGet location .elem) .tint)
    "TypeError lost its exact raise-point heap"
  for raised in [valueError, typeError] do
    ensure (containsTag (raised.state.envGet "caller") .tfloat)
      "exception did not restore the caller environment"
    ensure (containsTag (raised.state.envGet "calleeOnly") .tunbound)
      "callee local escaped through an exception"

def testRecursionFailsClosed : IO Unit := do
  let function : FuncDef := {
    p := position 30
    name := "recur"
    params := []
    retAnn := some (.atom "int")
    body := markerBody 31
  }
  let services : CallServices := {
    executeBody := fun _ _ =>
      pure {
        raised := {
          cases := [{
            cls := "AssertionError"
            value := AbsVal.bot
            state := {}
            origin := {}
          }]
        }
      }
  }
  let initial := {
    (auditContext) with callStack := ["recur"]
  }
  let (flow, context) :=
    (invokeUser services (position 104) "recur" function [] [] {})
      |>.run initial
  -- Re-entry fails closed: no normal completion. Summarising it as the declared
  -- return annotation with no raise would assume the deeper levels return within
  -- the annotation, raise nothing and write nothing, and all three are false in
  -- general -- see `../doc/RECURSION_CONTRACTS.md`. Until a checked contract can
  -- state a callee's result, raises and frame, the honest answer is to stop.
  ensure flow.normal.isNone
    "recursive re-entry still produced a normal completion"
  ensure (flow.raised.cases.any (·.cls == "RecursionError"))
    "recursive re-entry did not fail closed"
  ensure (hasObligation context "recursion-unsupported")
    "recursive re-entry was not disclosed"

def testGeneratorSummary : IO Unit := do
  let function : FuncDef := {
    p := position 40
    name := "items"
    params := []
    body := markerBody 41
    isGen := true
  }
  let sideEffect : Loc :=
    { site := 501, cls := .dict, recent := true }
  let services : CallServices := {
    executeBody := fun _ state => do
      modify fun context =>
        match context.yields with
        | _ :: rest =>
          { context with yields := [V [.tint], V [.tstr]] :: rest }
        | [] => context
      pure {
        normal := some (state.heapSet sideEffect .dictValues (V [.tbool]))
        raised := {
          cases := [
            {
              cls := "StopIteration"
              value := AbsVal.bot
              state := state.heapSet sideEffect .dictValues (V [.tint])
              origin := {}
            },
            {
              cls := "ValueError"
              value := AbsVal.bot
              state := state.heapSet sideEffect .dictValues (V [.tstr])
              origin := {}
            }
          ]
        }
      }
  }
  let callPosition := position 105
  let (flow, context) :=
    (invokeUser services callPosition "items" function [] [] {})
      |>.run (auditContext)
  let (value, output) <- normalCase flow
  let generator : Loc :=
    { site := callPosition.id, cls := .gen, recent := true }
  ensure (containsTag value .tgen && value.locs.contains generator)
    "generator call did not allocate its summary object"
  let elements := output.heapGet generator .elem
  ensure (containsTag elements .tint && containsTag elements .tstr)
    "generator summary lost yielded element alternatives"
  let exceptions := (context.genExc.find? (·.1 == callPosition.id))
    |>.map (·.2) |>.getD []
  ensure (exceptions.contains "RuntimeError" &&
      exceptions.contains "ValueError" &&
      !exceptions.contains "StopIteration")
    "generator exception summary did not apply PEP 479 wrapping"
  ensure flow.raised.cases.isEmpty
    "eager generator-body exceptions escaped at call time"
  ensure (hasObligation context "special-method")
    "eager generator approximation was not disclosed"
  ensure (context.callStack.isEmpty && context.yields.isEmpty)
    "generator call frame or yield collector leaked"

def testFrozenDataclassConstruction : IO Unit := do
  let definition : ClassDef := {
    p := position 50
    name := "FrozenPoint"
    bases := []
    fields := [{
      name := "x"
      ann := some (.atom "int")
      required := true
    }]
    methods := []
    isDataclass := true
  }
  let classes <- buildClasses [definition]
  let initial := auditContext classes
  let (planned, _) :=
    (compileConstructionRule "FrozenPoint").run initial
  match planned with
  | .userClass rule =>
    ensure rule.frozenDataclass
      "frozen dataclass fact is absent from construction rule data"
    match rule.initializer with
    | none => throw (IO.userError "generated dataclass initializer missing")
    | some initializer =>
      ensure (initializer.call.qualifiedName == "FrozenPoint.__init__")
        "generated initializer rule has the wrong call identity"
  | _ => throw (IO.userError "dataclass compiled as the wrong construction rule")

  let services : CallServices := {
    executeBody := fun _ state => do
      let context <- get
      let self := state.envGet "self"
      let argument := state.envGet "x"
      let output :=
        if context.callStack.contains "FrozenPoint.__init__" then
          self.locs.foldl
            (fun current location =>
              current.heapSet location (.field "x") argument) state
        else
          state
      pure (.ofNormal output)
  }
  let callPosition := position 106
  let (flow, context) :=
    (constructClass services callPosition "FrozenPoint"
      [V [.tint]] [] {}).run initial
  let (value, output) <- normalCase flow
  let objectLocation : Loc :=
    { site := callPosition.id, cls := .obj "FrozenPoint", recent := true }
  ensure (containsTag value (.tobj "FrozenPoint") &&
      value.locs.contains objectLocation)
    "class construction did not return the fresh instance"
  ensure (containsTag (output.heapGet objectLocation (.field "x")) .tint)
    "generated dataclass initializer did not initialize its field"
  ensure (!hasObligation context "init-missing" &&
      !hasObligation context "init-conditional")
    "initialized frozen dataclass failed definite initialization"
  ensure (context.called.contains "FrozenPoint.__init__")
    "generated initializer was not invoked as a user method"

def testTypedDictConstruction : IO Unit := do
  let definition : ClassDef := {
    p := position 60
    name := "Movie"
    bases := []
    fields := [
      {
        name := "year"
        ann := some (.atom "int")
        required := true
      },
      {
        name := "label"
        ann := some (.atom "str")
        required := false
        readOnly := true
      }
    ]
    methods := []
    isTypedDict := true
    total := false
  }
  let classes <- buildClasses [definition]
  let initial := auditContext classes
  let (planned, _) := (compileConstructionRule "Movie").run initial
  match planned with
  | .typedDict rule =>
    ensure (rule.fields.length == 2 &&
        rule.fields.any (fun field =>
          field.name == "label" && !field.required && field.readOnly))
      "TypedDict required/read-only metadata was lost from rule data"
  | _ => throw (IO.userError "TypedDict compiled as the wrong rule")

  let services : CallServices := {
    executeBody := fun _ state => pure (.ofNormal state)
  }
  let callPosition := position 107
  let (flow, context) :=
    (constructClass services callPosition "Movie" []
      [("year", V [.tbool])] {}).run initial
  let (value, output) <- normalCase flow
  let location : Loc :=
    { site := callPosition.id, cls := .td "Movie", recent := true }
  ensure (containsTag value .tdict && value.locs.contains location)
    "TypedDict construction did not return a dict-tagged shape location"
  ensure (containsTag (output.heapGet location (.literalKey "year")) .tbool)
    "TypedDict required field lost its checked value"
  ensure (containsTag (output.heapGet location (.literalKey "label")) .tmissing)
    "missing NotRequired field was not represented as absent"
  let keys := output.heapGet location .dictKeys
  ensure (keys.strLits.contains "year" && keys.strLits.contains "label" &&
      !keys.strOpen)
    "TypedDict generic dict key edge lost the declared finite key set"
  ensure (containsTag (output.heapGet location .dictValues) .tbool)
    "TypedDict generic dict value edge was not initialized"
  ensure (!hasObligation context "type-error" &&
      !hasObligation context "key-membership")
    "valid TypedDict construction emitted a shape/type failure"

  let source : Loc :=
    { site := 700, cls := .dict, recent := true }
  let positionalCall := position 113
  let (positionalFlow, positionalContext) :=
    (constructClass services positionalCall "Movie"
      [V [.tdict] [source]] [] {}).run initial
  let (_, positionalState) <- normalCase positionalFlow
  let positionalResult : Loc :=
    { site := positionalCall.id, cls := .td "Movie", recent := true }
  let optional := positionalState.heapGet positionalResult (.literalKey "label")
  ensure (containsTag optional .tany && containsTag optional .tmissing)
    "positional mapping lost present/absent alternatives for an optional key"
  let _ <- raisedCase positionalFlow "TypeError"
  ensure (hasObligation positionalContext "mapping-constructor" &&
      hasObligation positionalContext "shape-contract")
    "positional TypedDict mapping abstraction was not made explicit"

def testExceptionConstruction : IO Unit := do
  let services : CallServices := {
    executeBody := fun _ state => pure (.ofNormal state)
  }
  let callPosition := position 108
  let (flow, _) :=
    (constructBuiltinException services callPosition "ValueError" {})
      |>.run (auditContext)
  let (value, _) <- normalCase flow
  let location : Loc :=
    { site := callPosition.id, cls := .obj "ValueError", recent := true }
  ensure (containsTag value (.tobj "ValueError") &&
      value.locs.contains location)
    "builtin exception construction returned the wrong abstract object"

def testConstructionSignaturesAndInitReturn : IO Unit := do
  let initializer : FuncDef := {
    p := position 80
    name := "__init__"
    params := [{ name := "self" }]
    body := markerBody 81
  }
  let definitions : List ClassDef := [
    {
      p := position 82
      name := "EmptyNoInit"
      bases := []
      fields := []
      methods := []
    },
    {
      p := position 83
      name := "BadInit"
      bases := []
      fields := [{ name := "touched" }]
      methods := [initializer]
    }
  ]
  let classes <- buildClasses definitions
  let initial := auditContext classes
  let services : CallServices := {
    executeBody := fun _ state =>
      let self := state.envGet "self"
      let output := self.locs.foldl
        (fun current location =>
          current.heapSet location (.field "touched") (V [.tint])) state
      pure { returned := some (V [.tint], output) }
  }

  let (emptyFlow, _) :=
    (constructClass services (position 110) "EmptyNoInit"
      [V [.tint]] [] {}).run initial
  ensure emptyFlow.normal.isNone
    "object.__init__ accepted an unexpected positional argument"
  let _ <- raisedCase emptyFlow "TypeError"

  let badPosition := position 111
  let (badFlow, _) :=
    (constructClass services badPosition "BadInit" [] [] {}).run initial
  ensure badFlow.normal.isNone
    "non-None __init__ return retained a constructed instance"
  let badRaise <- raisedCase badFlow "TypeError"
  let badLocation : Loc :=
    { site := badPosition.id, cls := .obj "BadInit", recent := true }
  ensure (containsTag
      (badRaise.state.heapGet badLocation (.field "touched")) .tint)
    "__init__ return TypeError lost effects performed before the failure"

  let exceptionRule := Rule.construct
    (.builtinException (builtinExceptionRule "ValueError"))
  let (keywordFlow, _) :=
    (execute services (position 112) exceptionRule
      { keywords := [("x", V [.tint])] } {}).run initial
  ensure keywordFlow.normal.isNone
    "builtin exception constructor accepted a keyword argument"
  let _ <- raisedCase keywordFlow "TypeError"

def testFirstClassDispatchPlanAndExecution : IO Unit := do
  let function : FuncDef := {
    p := position 70
    name := "make_int"
    params := []
    body := markerBody 71
  }
  let classDefinition : ClassDef := {
    p := position 72
    name := "Empty"
    bases := []
    fields := []
    methods := []
  }
  let classes <- buildClasses [classDefinition]
  let initial := auditContext classes [("make_int", function)]
  let callee := V [.tfunc, .ttype, .tint]
    (funcs := ["make_int"]) (classes := ["Empty"])
  let (planned, _) :=
    (compileValueDispatchRule "callee(...)" callee).run initial
  ensure (planned.rows.length == 3)
    "union callee did not produce one row per callable/error alternative"
  ensure (planned.rows.any fun row =>
      match row.outcome with | .userCall _ => true | _ => false)
    "dispatch plan omitted the user function row"
  ensure (planned.rows.any fun row =>
      match row.outcome with | .construct _ => true | _ => false)
    "dispatch plan omitted the class construction row"
  ensure (planned.rows.any fun row =>
      match row.outcome with | .typeError => true | _ => false)
    "dispatch plan omitted the non-callable TypeError row"

  let services : CallServices := {
    executeBody := fun _ state =>
      pure { returned := some (V [.tint], state) }
  }
  let callPosition := position 109
  let (flow, context) :=
    (execute services callPosition (.dispatch planned) {} {})
      |>.run initial
  let (value, _) <- normalCase flow
  ensure (containsTag value .tint && containsTag value (.tobj "Empty"))
    "dispatch execution lost a feasible normal outcome"
  let _ <- raisedCase flow "TypeError"
  match context.residuals.find? (·.1 == callPosition.id) with
  | none => throw (IO.userError "dispatch execution did not record a residual")
  | some (_, residual) =>
    ensure (residual.cases.length == 2 && residual.errors.length == 1)
      "residual table does not reflect the three explicit dispatch rows"

def runAll : IO Unit := do
  testRuleDataAndAnnotatedCall
  testBindingFailureHasNoNormalFlow
  testDefaultSummary
  testDistinctExceptionalStates
  testRecursionFailsClosed
  testGeneratorSummary
  testFrozenDataclassConstruction
  testTypedDictConstruction
  testExceptionConstruction
  testConstructionSignaturesAndInitReturn
  testFirstClassDispatchPlanAndExecution
  IO.println "RuleCalls tests passed"

end Pylate.Tests.Calls
