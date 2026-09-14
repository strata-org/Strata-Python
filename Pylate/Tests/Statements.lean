import Pylate.Transfers.Statements

namespace Pylate.Tests.Statements

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.Statements

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def containsTag (value : AbsVal) (tag : Tag) : Bool :=
  decide (tag ∈ value.tags)

def position (id : Nat) (line : Nat := id) : Pos := ⟨NodeId.root.child id, line, 0⟩

def intExpr (id value : Nat) : Expr :=
  .const (position id) (.cint value)

def strExpr (id : Nat) (value : String) : Expr :=
  .const (position id) (.cstr value)

def boolExpr (id : Nat) (value : Bool) : Expr :=
  .const (position id) (.cbool value)

def nameExpr (id : Nat) (name : String) : Expr :=
  .name (position id) name

def raisedFlow (cls : String) (state : AState)
    (value : AbsVal := AbsVal.bot) : Flow :=
  {
    raised := {
      cases := [{ cls, value, state, origin := {} }]
    }
  }

def constValue : Const -> AbsVal
  | .cint _ => V [.tint]
  | .cbool _ => V [.tbool]
  | .cfloat _ => V [.tfloat]
  | .cstr _ => V [.tstr]
  | .cnone => V [.tnone]

def testEvalExpr (expression : Expr) (state : AState) : M Flow := do
  match expression.pos.id.path with
  | [700] =>
    modify fun context => { context with ordCtr := context.ordCtr + 1 }
    pure (Flow.ofNormal (V [.tbool]) state)
  | [900] =>
    pure (raisedFlow "ValueError"
      (state.envSet "rhs_effect" (V [.tbool]))
      (V [.tobj "ValueError"]))
  | [901] =>
    pure {
      normal := some (V [.tint],
        state.envSet "rhs_effect" (V [.tbool]))
      raised := {
        cases := [{
          cls := "KeyError"
          value := V [.tobj "KeyError"]
          origin := {}
          state := state.envSet "rhs_effect" (V [.tbool])
        }]
      }
    }
  | [930] =>
    pure {
      normal := some (V [.tstr],
        state.envSet "argument_evaluated" (V [.tbool]))
      raised := {
        cases := [{
          cls := "KeyError"
          value := V [.tobj "KeyError"]
          origin := {}
          state := state.envSet "argument_evaluated" (V [.tbool])
        }]
      }
    }
  | _ =>
    match expression with
    | .const _ constant =>
      pure (Flow.ofNormal (constValue constant) state)
    | .name _ name =>
      pure (Flow.ofNormal (state.envGet name) state)
    | _ =>
      pure (Flow.ofNormal anyV state)

def testTruth (expression : Expr) (value : AbsVal)
    (state : AState) : M TruthFlow := do
  let state :=
    if expression.pos.id == 400 then
      state.envSet "truth_completed" (V [.tbool])
    else state
  let raised :=
    if expression.pos.id == 401 then
      (raisedFlow "TypeError" state (V [.tobj "TypeError"])).raised
    else {}
  pure {
    truthy := some (value, state)
    falsy := some (value, state)
    raised
  }

def testRefine (expression : Expr) (state : AState) :
    M (Option AState × Option AState) := do
  match expression.pos.id.path with
  | [400] =>
    modify fun context => { context with ordCtr := context.ordCtr + 1 }
    let ordered :=
      containsTag (state.envGet "truth_completed") .tbool
    let marker := if ordered then V [.tbool] else V [.tstr]
    pure (
      some ((state.envSet "refined_after_truth" marker).envSet
        "branch" (V [.tint])),
      some ((state.envSet "refined_after_truth" marker).envSet
        "branch" (V [.tstr])))
  | [500] =>
    pure (
      some (state.envSet "assert_side" (V [.tbool])),
      some (state.envSet "assert_side" (V [.tstr])))
  | _ =>
    pure (some state, some state)

def targetName : Target -> Option (Pos × String)
  | .tname pos name => some (pos, name)
  | _ => none

def testExecuteTarget (action : TargetAction) (state : AState) : M Flow := do
  match action with
  | .bind target value =>
    match targetName target with
    | some (pos, name) =>
      modify fun context =>
        { context with called := Fset.insert s!"bind:{name}" context.called }
      if pos.id == 910 then
        pure (raisedFlow "TypeError" state (V [.tobj "TypeError"]))
      else
        pure (Flow.ofNormal value (state.envSet name value))
    | none =>
      pure (Flow.ofNormal value state)
  | .delete target =>
    match targetName target with
    | some (pos, name) =>
      modify fun context =>
        { context with called := Fset.insert s!"delete:{name}" context.called }
      if pos.id == 920 then
        pure (raisedFlow "UnboundLocalError" state
          (V [.tobj "UnboundLocalError"]))
      else
        pure (Flow.ofNormal (V [.tnone]) (state.envKill name))
    | none =>
      pure (Flow.ofNormal (V [.tnone]) state)

def testConstructException (request : ExceptionConstruction)
    (state : AState) : M Flow := do
  modify fun context =>
    { context with called :=
        Fset.insert s!"construct:{request.className}" context.called }
  if request.className == "BrokenException" then
    pure (raisedFlow "TypeError" state (V [.tobj "TypeError"]))
  else
    let (value, allocated) :=
      allocate state request.position.id (.obj request.className) []
    let ordered :=
      containsTag (allocated.envGet "argument_evaluated") .tbool
    let postState := allocated.envSet "constructed_after_argument"
      (if ordered then V [.tbool] else V [.tstr])
    pure (Flow.ofNormal value postState)

def testExecuteLoop (loop : LoopSpec) (state : AState) : M AMulti := do
  let marker := match loop with
    | .whileLoop .. => V [.tint]
    | .forLoop .. => V [.tstr]
  pure (.ofNormal (state.envSet "loop_adapter" marker))

def services : Statements.Services where
  evalExpr := testEvalExpr
  truth := testTruth
  refine := testRefine
  executeTarget := testExecuteTarget
  constructException := testConstructException
  executeLoop := testExecuteLoop

def context : Actx := { policy := Policy.audit }

def runStatement (statement : Stmt) (state : AState := {}) :
    Completion × Actx :=
  (executeStatement services statement state).run context

def runBody (body : List Stmt) (state : AState := {}) :
    Completion × Actx :=
  (executeBody services body state).run context

def findRaised (flow : Completion) (cls : String) : IO RaisedCase :=
  match flow.raised.cases.find? (·.cls == cls) with
  | some raised => pure raised
  | none => throw (IO.userError s!"expected raised {cls}")

def expectNoRaised (flow : Completion) (message : String) : IO Unit :=
  ensure flow.raised.cases.isEmpty message

def stateAtLine (context : Actx) (line : Nat) : IO AState :=
  match (lineStates context)[line]? with
  | some state => pure state
  | none => throw (IO.userError s!"expected snapshot at line {line}")

def testBodyDriverSnapshots : IO Unit := do
  let body : List Stmt := [
    .assign (position 10 10) (.tname (position 11 10) "x")
      (intExpr 12 1),
    .ret (position 13 11) (some (nameExpr 14 "x")),
    .assign (position 15 12) (.tname (position 16 12) "dead")
      (strExpr 17 "unreachable")
  ]
  let (result, finalContext) := runBody body
  ensure result.normal.isNone "return retained normal fallthrough"
  match result.returned with
  | some (value, _) =>
    ensure (containsTag value .tint) "return lost the assigned value"
  | none => throw (IO.userError "body lost return completion")
  let beforeAssign <- stateAtLine finalContext 10
  ensure (containsTag (beforeAssign.envGet "x") .tunbound)
    "assignment snapshot was not its input state"
  let beforeReturn <- stateAtLine finalContext 11
  ensure (containsTag (beforeReturn.envGet "x") .tint)
    "next statement snapshot missed the assignment"
  ensure ((lineStates finalContext)[12]?).isNone
    "unreachable statement was snapshotted"

def testNormalOnlySequencing : IO Unit := do
  let normalState := ({} : AState).envSet "route" (V [.tint])
  let returnState := ({} : AState).envSet "route" (V [.tstr])
  let breakState := ({} : AState).envSet "route" (V [.tbool])
  let continueState := ({} : AState).envSet "route" (V [.tfloat])
  let raiseState := ({} : AState).envSet "route" (V [.tnone])
  let first : Completion := {
    normal := some normalState
    returned := some (V [.tstr], returnState)
    broke := some breakState
    continued := some continueState
    raised := {
      cases := [{
        cls := "ValueError"
        value := V [.tobj "ValueError"]
        origin := {}
        state := raiseState
      }]
    }
  }
  let (result, _) := (sequence first fun state =>
    pure (.ofNormal (state.envSet "sequenced" (V [.tbool])))).run context
  match result.normal with
  | none => throw (IO.userError "normal continuation was lost")
  | some state =>
    ensure (containsTag (state.envGet "sequenced") .tbool)
      "normal completion did not enter the continuation"
  let unsequenced := fun state =>
    containsTag (state.envGet "sequenced") .tunbound
  match result.returned with
  | some (_, state) =>
    ensure (unsequenced state) "return entered the normal continuation"
  | none => throw (IO.userError "return completion was lost")
  match result.broke with
  | some state =>
    ensure (unsequenced state) "break entered the normal continuation"
  | none => throw (IO.userError "break completion was lost")
  match result.continued with
  | some state =>
    ensure (unsequenced state) "continue entered the normal continuation"
  | none => throw (IO.userError "continue completion was lost")
  ensure (unsequenced (← findRaised result "ValueError").state)
    "raise entered the normal continuation"

def testExceptionalAssignments : IO Unit := do
  let initial := ({} : AState).envSet "x" (V [.tstr])
  let assignment : Stmt :=
    .assign (position 100) (.tname (position 101) "x")
      (intExpr 900 1)
  let (assigned, assignContext) := runStatement assignment initial
  ensure assigned.normal.isNone
    "guaranteed failing RHS retained normal assignment flow"
  let assignRaise <- findRaised assigned "ValueError"
  ensure (containsTag (assignRaise.state.envGet "x") .tstr &&
      !containsTag (assignRaise.state.envGet "x") .tint)
    "failed RHS performed its assignment"
  ensure (!assignContext.called.contains "bind:x")
    "failed RHS invoked target binding"

  let annotated : Stmt :=
    .annAssign (position 102) "x" (some (intExpr 900 1))
  let (annResult, annContext) := runStatement annotated initial
  ensure annResult.normal.isNone
    "failed annotated assignment retained normal flow"
  ensure (!annContext.called.contains "bind:x")
    "failed annotated RHS invoked target binding"
  ensure (containsTag
      ((← findRaised annResult "ValueError").state.envGet "x") .tstr)
    "failed annotated assignment changed boundness/value"

  let targetFailure : Stmt :=
    .assign (position 103) (.tname (position 910) "x")
      (intExpr 104 1)
  let (targetResult, _) := runStatement targetFailure initial
  ensure targetResult.normal.isNone "failing target retained normal flow"
  let targetRaise <- findRaised targetResult "TypeError"
  ensure (containsTag (targetRaise.state.envGet "x") .tstr)
    "target failure committed a binding update"

def testExpressionReturnAndSimpleCompletions : IO Unit := do
  let expression : Stmt := .exprS (position 110) (intExpr 901 1)
  let (exprResult, _) := runStatement expression
  ensure exprResult.normal.isSome
    "mixed expression result lost normal completion"
  let _ <- findRaised exprResult "KeyError"

  let returning : Stmt := .ret (position 111) (some (intExpr 901 1))
  let (returnResult, _) := runStatement returning
  ensure returnResult.normal.isNone
    "return expression created normal fallthrough"
  ensure returnResult.returned.isSome
    "mixed return expression lost its return completion"
  let _ <- findRaised returnResult "KeyError"

  let failedReturn : Stmt :=
    .ret (position 112) (some (intExpr 900 1))
  let (failedResult, _) := runStatement failedReturn
  ensure failedResult.returned.isNone
    "failing return operand fabricated a return"
  let _ <- findRaised failedResult "ValueError"

  ensure (runStatement (.pass (position 113))).1.normal.isSome
    "pass did not fall through"
  ensure (runStatement (.brk (position 114))).1.broke.isSome
    "break completion missing"
  ensure (runStatement (.cont (position 115))).1.continued.isSome
    "continue completion missing"
  match (runStatement (.ret (position 116) none)).1.returned with
  | some (value, _) =>
    ensure (containsTag value .tnone) "bare return did not return None"
  | none => throw (IO.userError "bare return completion missing")

def testDeleteSemantics : IO Unit := do
  let initial := ({} : AState).envSet "x" (V [.tint])
  let deleting : Stmt :=
    .delS (position 120) (.tname (position 121) "x")
  let (deleted, _) := runStatement deleting initial
  match deleted.normal with
  | some state =>
    ensure (containsTag (state.envGet "x") .tunbound)
      "successful del did not update boundness"
  | none => throw (IO.userError "successful del lost normal flow")

  let failing : Stmt :=
    .delS (position 122) (.tname (position 920) "x")
  let (failed, _) := runStatement failing initial
  ensure failed.normal.isNone "failing del retained normal flow"
  let raised <- findRaised failed "UnboundLocalError"
  ensure (containsTag (raised.state.envGet "x") .tint)
    "failing del committed its boundness update"

def testIfTruthThenRefine : IO Unit := do
  let condition := boolExpr 400 true
  let statement : Stmt :=
    .ifS (position 130) condition
      [.annAssign (position 131) "route" (some (intExpr 132 1))]
      [.annAssign (position 133) "route" (some (strExpr 134 "s"))]
  let (result, finalContext) := runStatement statement
  expectNoRaised result "ordinary if unexpectedly raised"
  ensure (finalContext.ordCtr == 1)
    "if refinement was not called exactly once"
  match result.normal with
  | none => throw (IO.userError "if lost both normal branches")
  | some state =>
    let route := state.envGet "route"
    ensure (containsTag route .tint && containsTag route .tstr)
      "if failed to join both refined branches"
    ensure (containsTag (state.envGet "refined_after_truth") .tbool &&
        !containsTag (state.envGet "refined_after_truth") .tstr)
      "refine did not receive the post-truth state"

  let truthFailure : Stmt :=
    .ifS (position 135) (boolExpr 401 true)
      [.pass (position 136)] [.pass (position 137)]
  let (mixed, _) := runStatement truthFailure
  ensure mixed.normal.isSome
    "truth protocol exception incorrectly removed its normal alternatives"
  let _ <- findRaised mixed "TypeError"

def testAssertRouting : IO Unit := do
  let assertion : Stmt :=
    .assertS (position 140) (boolExpr 500 true)
  let (result, finalContext) := runStatement assertion
  match result.normal with
  | some state =>
    ensure (containsTag (state.envGet "assert_side") .tbool)
      "assert true side did not use refined state"
  | none => throw (IO.userError "assert lost feasible true side")
  let failed <- findRaised result "AssertionError"
  ensure (containsTag (failed.state.envGet "assert_side") .tstr)
    "AssertionError did not retain the refined false state"
  ensure (finalContext.obligations.any (·.kind == "assert"))
    "assertion obligation was not recorded"

  let evalFailure : Stmt :=
    .assertS (position 141) (boolExpr 900 true)
  let (failedEval, _) := runStatement evalFailure
  ensure failedEval.normal.isNone
    "failed assert operand retained normal flow"
  let _ <- findRaised failedEval "ValueError"
  ensure (failedEval.raised.cases.find?
      (·.cls == "AssertionError")).isNone
    "assertion failure was fabricated after operand failure"

def testExplicitAndBareRaise : IO Unit := do
  let explicit : Stmt :=
    .raiseS (position 150) (some "ValueError")
      (some (strExpr 930 "message"))
  let (result, finalContext) := runStatement explicit
  ensure result.normal.isNone "raise retained normal flow"
  let explicitCase <- findRaised result "ValueError"
  ensure (containsTag explicitCase.value (.tobj "ValueError"))
    "explicit raise lost its constructed exception"
  ensure (containsTag
      (explicitCase.state.envGet "constructed_after_argument") .tbool)
    "exception construction ran before argument evaluation"
  let _ <- findRaised result "KeyError"
  ensure (finalContext.called.contains "construct:ValueError")
    "explicit exception constructor was not invoked"

  let broken : Stmt :=
    .raiseS (position 154) (some "BrokenException") none
  let (brokenResult, _) := runStatement broken
  let _ <- findRaised brokenResult "TypeError"
  ensure (brokenResult.raised.cases.find?
      (·.cls == "BrokenException")).isNone
    "failed exception construction fabricated the requested raise"

  let failedArgument : Stmt :=
    .raiseS (position 151) (some "ValueError")
      (some (strExpr 900 "message"))
  let (failed, failedContext) := runStatement failedArgument
  let _ <- findRaised failed "ValueError"
  ensure (!failedContext.called.contains "construct:ValueError")
    "exception constructor ran after guaranteed argument failure"

  let (outside, outsideContext) :=
    runStatement (.raiseS (position 152) none none)
  let _ <- findRaised outside "RuntimeError"
  ensure (outsideContext.machineRaises.any
      (fun site => site.node == 152 && site.exc == "RuntimeError"))
    "bare raise outside a handler was not a machine RuntimeError"

  let activeContext : Actx := {
    policy := Policy.audit
    handling := [["ValueError", "TypeError"]]
  }
  let (reraised, _) :=
    (executeStatement services (.raiseS (position 153) none none) {}).run
      activeContext
  let _ <- findRaised reraised "ValueError"
  let _ <- findRaised reraised "TypeError"
  ensure (reraised.raised.cases.find?
      (·.cls == "RuntimeError")).isNone
    "bare re-raise inside handler fabricated RuntimeError"

def testGroupedFirstMatchHandlers : IO Unit := do
  let handlers : List Handler := [
    .mk (position 161 61) (some "ValueError") (some "err") [
      .exprS (position 162 62) (boolExpr 700 true),
      .assign (position 163 63) (.tname (position 164 63) "alias")
        (nameExpr 165 "err")
    ],
    .mk (position 166 66) (some "Exception") none [
      .annAssign (position 167 67) "fallback"
        (some (strExpr 168 "wrong"))
    ]
  ]
  let body : Completion := {
    raised := {
      cases := [
        {
          cls := "ValueError"
          value := AbsVal.bot
          origin := {}
          state := ({} : AState).envSet "origin" (V [.tint])
        },
        {
          cls := "UnicodeError"
          value := AbsVal.bot
          origin := {}
          state := ({} : AState).envSet "origin" (V [.tstr])
        }
      ]
    }
  }
  let (result, finalContext) :=
    (routeHandlers services (executeBody services) (position 160 60)
      handlers body).run context
  expectNoRaised result "caught exceptions still escaped"
  -- Both classes match the first clause -- `UnicodeError` subclasses
  -- `ValueError` -- so first-match routing still sends them to one clause. But
  -- they are two reaching completions with two different states, so the clause
  -- runs once per completion, from that completion's own state, rather than once
  -- from their join. Asserting `1` here was asserting the clumping.
  ensure (finalContext.ordCtr == 2)
    "clause did not run once per reaching completion"
  ensure finalContext.handling.isEmpty
    "handler stack was not restored"
  match result.normal with
  | none => throw (IO.userError "matching handler did not complete normally")
  | some state =>
    let alias := state.envGet "alias"
    ensure (containsTag alias (.tobj "ValueError") &&
        containsTag alias (.tobj "UnicodeError"))
      "bound handler target did not allocate every caught exception class"
    ensure (containsTag (state.envGet "err") .tunbound)
      "handler target was not deleted on normal exit"
    ensure (containsTag (state.envGet "fallback") .tunbound)
      "later matching clause also executed"
  match finalContext.handlerTables.find? (·.1 == 160) with
  | none => throw (IO.userError "handler table was not recorded")
  | some (_, line, rows) =>
    ensure (line == 60) "handler table recorded the wrong try line"
    ensure (rows == [
      ("ValueError", some ("ValueError", 61)),
      ("UnicodeError", some ("ValueError", 61))
    ]) "handler table did not record first subclass matches"

def testUnmatchedHandlerPropagation : IO Unit := do
  let handlers : List Handler := [
    .mk (position 169 68) (some "Exception") none [
      .pass (position 1691 681)
    ]
  ]
  let body := raised {} "KeyboardInterrupt"
    (V [.tobj "KeyboardInterrupt"]) {}
  let (result, finalContext) :=
    (routeHandlers services (executeBody services) (position 1692 67)
      handlers body).run context
  let _ <- findRaised result "KeyboardInterrupt"
  ensure result.normal.isNone
    "unmatched BaseException subclass entered an Exception handler"
  match finalContext.handlerTables.find? (·.1 == 1692) with
  | some (_, _, [("KeyboardInterrupt", none)]) => pure ()
  | _ =>
    throw (IO.userError
      "handler table did not record unmatched exception propagation")

def testHandlerReraiseAndCleanup : IO Unit := do
  let handlers : List Handler := [
    .mk (position 170 70) (some "Exception") (some "err") [
      .assign (position 171 71) (.tname (position 172 71) "alias")
        (nameExpr 173 "err"),
      .raiseS (position 174 72) none none
    ]
  ]
  let body : Completion := {
    raised := {
      cases := [
        {
          cls := "KeyError"
          value := AbsVal.bot
          origin := {}
          state := {}
        },
        {
          cls := "TypeError"
          value := AbsVal.bot
          origin := {}
          state := {}
        }
      ]
    }
  }
  let (result, _) :=
    (routeHandlers services (executeBody services) (position 175 69)
      handlers body).run context
  ensure result.normal.isNone "bare re-raise retained handler fallthrough"
  for cls in ["KeyError", "TypeError"] do
    let raised <- findRaised result cls
    ensure (containsTag (raised.state.envGet "err") .tunbound)
      s!"handler target survived {cls} re-raise cleanup"
    let alias := raised.state.envGet "alias"
    -- The alias survives cleanup, and it holds *this* case's exception only.
    -- Handlers run per completion rather than once over the join, so the alias is
    -- exact: an alias carrying both classes would mean the two re-raises had been
    -- merged.
    let other := if cls == "KeyError" then "TypeError" else "KeyError"
    ensure (containsTag alias (.tobj cls))
      s!"cleanup destroyed the alias to the {cls} exception object"
    ensure (!containsTag alias (.tobj other))
      s!"alias after {cls} still carried {other} from another raise"

def testHandlerCleanupOnControlCompletions : IO Unit := do
  let handlers : List Handler := [
    .mk (position 176 76) (some "Exception") (some "err") [
      .assign (position 177 77) (.tname (position 178 77) "alias")
        (nameExpr 179 "err"),
      .ifS (position 1761 78) (boolExpr 1762 true)
        [.ret (position 1763 79) none]
        [
          .ifS (position 1764 80) (boolExpr 1765 true)
            [.brk (position 1766 81)]
            [.cont (position 1767 82)]
        ]
    ]
  ]
  let body := raised {} "ValueError" (V [.tobj "ValueError"]) {}
  let (result, _) :=
    (routeHandlers services (executeBody services) (position 1768 75)
      handlers body).run context
  let checkCleanup := fun label (state : AState) => do
    ensure (containsTag (state.envGet "err") .tunbound)
      s!"handler target survived {label}"
    ensure (containsTag (state.envGet "alias") (.tobj "ValueError"))
      s!"handler alias was destroyed on {label}"
  match result.returned with
  | some (_, state) => checkCleanup "return" state
  | none => throw (IO.userError "handler return completion missing")
  match result.broke with
  | some state => checkCleanup "break" state
  | none => throw (IO.userError "handler break completion missing")
  match result.continued with
  | some state => checkCleanup "continue" state
  | none => throw (IO.userError "handler continue completion missing")

def testElseExceptionsBypassHandlers : IO Unit := do
  let statement : Stmt :=
    .tryS (position 180 80)
      [.pass (position 181 81)]
      [
        .mk (position 182 82) (some "Exception") none [
          .annAssign (position 183 83) "caught"
            (some (boolExpr 184 true))
        ]
      ]
      [.raiseS (position 185 85) (some "KeyError") none]
      []
  let (result, _) := runStatement statement
  ensure result.normal.isNone
    "exception from else retained normal flow"
  let raised <- findRaised result "KeyError"
  ensure (containsTag (raised.value) (.tobj "KeyError"))
    "else exception value was not preserved"
  ensure (containsTag (raised.state.envGet "caught") .tunbound)
    "exception from else entered a preceding handler"

def finalNormalBody : List Stmt := [
  .annAssign (position 301 301) "finalized" (some (boolExpr 302 true))
]

def finalRaiseBody : List Stmt := [
  .raiseS (position 303 303) (some "RuntimeError") none
]

def finalReturnBody : List Stmt := [
  .ret (position 304 304) (some (strExpr 305 "replacement"))
]

def finalBreakBody : List Stmt := [.brk (position 306 306)]

def finalContinueBody : List Stmt := [.cont (position 307 307)]

def runFinallyWith (pending : Completion) (body : List Stmt) :
    Completion :=
  ((runFinally (executeBody services) (position 1) body pending).run context).1

def testFinallyResumesEveryPendingCompletion : IO Unit := do
  let returnResult := runFinallyWith
    (returned (V [.tint]) {}) finalNormalBody
  match returnResult.returned with
  | some (value, state) =>
    ensure (containsTag value .tint) "finally changed the return value"
    ensure (containsTag (state.envGet "finalized") .tbool)
      "return did not resume from post-finally state"
  | none => throw (IO.userError "normal finally swallowed return")

  let raiseResult := runFinallyWith
    (raised {} "ValueError" (V [.tobj "ValueError"]) {}) finalNormalBody
  let raised <- findRaised raiseResult "ValueError"
  ensure (containsTag (raised.state.envGet "finalized") .tbool)
    "raise did not resume from post-finally state"

  let breakResult := runFinallyWith (broke {}) finalNormalBody
  match breakResult.broke with
  | some state =>
    ensure (containsTag (state.envGet "finalized") .tbool)
      "break did not resume from post-finally state"
  | none => throw (IO.userError "normal finally swallowed break")

  let continueResult := runFinallyWith (continued {}) finalNormalBody
  match continueResult.continued with
  | some state =>
    ensure (containsTag (state.envGet "finalized") .tbool)
      "continue did not resume from post-finally state"
  | none => throw (IO.userError "normal finally swallowed continue")

def testFinallyReplacesEveryPendingCompletion : IO Unit := do
  let returnReplaced := runFinallyWith
    (returned (V [.tint]) {}) finalRaiseBody
  ensure returnReplaced.returned.isNone
    "raising finally failed to replace return"
  let _ <- findRaised returnReplaced "RuntimeError"

  let raiseReplaced := runFinallyWith
    (raised {} "ValueError" (V [.tobj "ValueError"]) {}) finalReturnBody
  ensure raiseReplaced.raised.cases.isEmpty
    "returning finally failed to replace raise"
  ensure raiseReplaced.returned.isSome
    "returning finally did not produce return"

  let breakReplaced := runFinallyWith (broke {}) finalContinueBody
  ensure breakReplaced.broke.isNone
    "continuing finally failed to replace break"
  ensure breakReplaced.continued.isSome
    "continuing finally did not produce continue"

  let continueReplaced := runFinallyWith (continued {}) finalBreakBody
  ensure continueReplaced.continued.isNone
    "breaking finally failed to replace continue"
  ensure continueReplaced.broke.isSome
    "breaking finally did not produce break"

def finallyOrderEval (expression : Expr) (state : AState) : M Flow := do
  if expression.pos.id != 710 then
    testEvalExpr expression state
  else
    let mode := state.envGet "mode"
    let label :=
      if containsTag mode .tint then "normal"
      else if containsTag mode .tbool then "break"
      else if containsTag mode .tfloat then "continue"
      else if containsTag mode .tstr then "return"
      else "raised"
    modify fun context =>
      { context with callStack := context.callStack ++ [label] }
    pure (Flow.ofNormal (V [.tnone]) state)

def orderServices : Statements.Services := {
  services with
  evalExpr := finallyOrderEval
}

def testFinallyOracleOrderAndCollapsedExceptions : IO Unit := do
  let pending : Completion := {
    normal := some (({} : AState).envSet "mode" (V [.tint]))
    broke := some (({} : AState).envSet "mode" (V [.tbool]))
    continued := some (({} : AState).envSet "mode" (V [.tfloat]))
    returned := some (V [.tnone],
      ({} : AState).envSet "mode" (V [.tstr]))
    raised := {
      cases := [
        {
          cls := "ValueError"
          value := V [.tobj "ValueError"]
          origin := {}
          state := ({} : AState).envSet "mode" (V [.tnone])
        },
        {
          cls := "TypeError"
          value := V [.tobj "TypeError"]
          origin := {}
          state := ({} : AState).envSet "mode" (V [.tcomplex])
        }
      ]
    }
  }
  let finalBody : List Stmt := [
    .exprS (position 711 711) (boolExpr 710 true),
    .annAssign (position 712 712) "finalized" (some (boolExpr 713 true))
  ]
  let (result, finalContext) :=
    (runFinally (executeBody orderServices) (position 1) finalBody pending).run context
  -- Order is unchanged -- normal, break, continue, return, then the raises --
  -- but the raised phase now runs once per pending case rather than once from
  -- their joined state. Two cases are pending here with different `mode`
  -- states, so `raised` appears twice. Expecting one entry was expecting the
  -- collapse.
  ensure (finalContext.callStack ==
      ["normal", "break", "continue", "return", "raised", "raised"])
    "finally paths did not execute in order, once per pending completion"
  -- Each pending raise resumes from the finalizer run *it* entered, so it keeps
  -- its own `mode` and not the other's. Requiring both tags on both classes was
  -- requiring the collapse: one joined state re-attached to every case.
  for (cls, mine, theirs) in
      [("ValueError", Tag.tnone, Tag.tcomplex),
       ("TypeError", Tag.tcomplex, Tag.tnone)] do
    let raised <- findRaised result cls
    ensure (containsTag (raised.state.envGet "mode") mine)
      s!"{cls} did not resume from its own finally run"
    ensure (!containsTag (raised.state.envGet "mode") theirs)
      s!"{cls} resumed carrying another raise's state"
    ensure (containsTag (raised.state.envGet "finalized") .tbool)
      "collapsed exceptional flow did not run finally"

def testLoopCompatibilityBoundary : IO Unit := do
  let whileStatement : Stmt :=
    .whileS (position 800) (boolExpr 801 true)
      [.pass (position 802)] []
  let (whileResult, _) := runStatement whileStatement
  match whileResult.normal with
  | some state =>
    ensure (containsTag (state.envGet "loop_adapter") .tint)
      "while did not cross the typed loop compatibility adapter"
  | none => throw (IO.userError "while compatibility flow was lost")

  let forStatement : Stmt :=
    .forS (position 803) (.tname (position 804) "x")
      (nameExpr 805 "xs") [.pass (position 806)] []
  let (forResult, _) := runStatement forStatement
  match forResult.normal with
  | some state =>
    ensure (containsTag (state.envGet "loop_adapter") .tstr)
      "for did not cross the typed loop compatibility adapter"
  | none => throw (IO.userError "for compatibility flow was lost")

def runAll : IO Unit := do
  testBodyDriverSnapshots
  testNormalOnlySequencing
  testExceptionalAssignments
  testExpressionReturnAndSimpleCompletions
  testDeleteSemantics
  testIfTruthThenRefine
  testAssertRouting
  testExplicitAndBareRaise
  testGroupedFirstMatchHandlers
  testUnmatchedHandlerPropagation
  testHandlerReraiseAndCleanup
  testHandlerCleanupOnControlCompletions
  testElseExceptionsBypassHandlers
  testFinallyResumesEveryPendingCompletion
  testFinallyReplacesEveryPendingCompletion
  testFinallyOracleOrderAndCollapsedExceptions
  testLoopCompatibilityBoundary
  IO.println "RuleStatements tests passed"

end Pylate.Tests.Statements
