/-
Statement and five-completion routing for the rule interpreter.

This module owns every non-loop statement.  The service boundary supplies
expression, target, refinement, and exception-construction semantics.  Until
the fixpoint driver lands, `while` and `for` alone use `executeLoop`; its
legacy `AMulti` result is converted immediately through RuleCompatibility.

Adapter requirements:

* `evalExpr`, `truth`, `executeTarget`, and `constructException` must
  preserve Python evaluation order and retain the state at each exceptional
  exit.
* `refine` is pure with respect to Python execution.  It is called only after
  truth conversion has a normal result and receives that post-truth state.
* A target operation changes boundness, aliases, and heap cells only in its
  normal result.  Its exceptional cases retain their own pre-failure states.
* `executeLoop` receives a closed `LoopSpec`, never an arbitrary statement.
  Replacing this hook with the checked fixpoint driver removes the last
  statement-level legacy boundary.

Snapshots and handler tables are written directly to `Actx`, so an eventual
RuleAnalyzer adapter must not record them a second time.
-/
import Pylate.Transfers.Compatibility
import Pylate.Rules.SyntaxPlans

namespace Pylate.RuleDriven.Statements

open Pylate
open Pylate.RuleDriven

inductive TargetAction
  | bind (target : Target) (value : AbsVal)
  | delete (target : Target)
deriving Inhabited

structure ExceptionConstruction where
  position  : Pos
  className : String
  arguments : List AbsVal
deriving Inhabited

inductive LoopSpec
  | whileLoop (position : Pos) (condition : Expr)
      (body elseBody : List Stmt)
  | forLoop (position : Pos) (target : Target) (iterable : Expr)
      (body elseBody : List Stmt)
deriving Inhabited

structure Services where
  evalExpr : Expr -> AState -> M Flow
  truth : Expr -> AbsVal -> AState -> M TruthFlow
  refine : Expr -> AState -> M (Option AState × Option AState)
  executeTarget : TargetAction -> AState -> M Flow
  constructException : ExceptionConstruction -> AState -> M Flow
  executeLoop : LoopSpec -> AState -> M AMulti

abbrev BodyExecutor := List Stmt -> AState -> M Completion

private def completionOfRaised (raised : RaisedFlow) : Completion :=
  { raised }

private def completionOfFlow (flow : Flow) : Completion :=
  {
    normal := flow.normal.map (·.2)
    raised := flow.raised
  }

private def completionOfExc (fallback : AState) (exception : Exc) :
    Completion :=
  completionOfRaised {
    cases := exception.tags.map fun cls =>
      {
        cls
        value := AbsVal.bot
        state := exception.st.getD fallback
        -- From the joined `Exc` view, which has no raise site.
        origin := {}
      }
  }

private def withoutNormal (flow : Completion) : Completion :=
  { flow with normal := none }

private def abnormalOnly (flow : Completion) : Completion :=
  { flow with normal := none }

private def mapRaisedStates (raised : RaisedFlow)
    (update : AState -> AState) : RaisedFlow :=
  {
    cases := raised.cases.map fun raised =>
      { raised with state := update raised.state }
  }

def mapStates (flow : Completion) (update : AState -> AState) : Completion :=
  {
    normal := flow.normal.map update
    returned := flow.returned.map fun (value, state) => (value, update state)
    broke := flow.broke.map update
    continued := flow.continued.map update
    raised := mapRaisedStates flow.raised update
  }

/-- Execute `next` only after normal fallthrough.  Every other completion from
    `first` bypasses it and is retained at its own state. -/
def sequence (first : Completion)
    (next : AState -> M Completion) : M Completion := do
  match first.normal with
  | none => pure first
  | some state =>
    let rest <- next state
    pure ((withoutNormal first).join rest)

def normal (state : AState) : Completion :=
  .ofNormal state

def returned (value : AbsVal) (state : AState) : Completion :=
  { returned := some (value, state) }

def broke (state : AState) : Completion :=
  { broke := some state }

def continued (state : AState) : Completion :=
  { continued := some state }

def raised (origin : Pos) (cls : String) (value : AbsVal) (state : AState)
    (from? : Provenance := .machine) : Completion :=
  {
    raised := {
      cases := [{ cls, value, state, origin, from? }]
    }
  }

def raisedClasses (origin : Pos) (classes : Fset String) (value : AbsVal)
    (state : AState) (from? : Provenance := .machine) : Completion :=
  completionOfRaised {
    cases := classes.map fun cls => { cls, value, state, origin, from? }
  }

private def machineRaised (position : Pos) (classes : Fset String)
    (state : AState) : M Completion := do
  pure (completionOfExc state (← mraise position {} state classes))

/-- Turn every normal construction result into the requested exception class
    while retaining exceptions raised during construction. An explicit `raise`
    is user provenance: the policy never applies to it, and it is not a dispatch
    site, so it has no residual row. -/
def raiseFromFlow (origin : Pos) (cls : String) (flow : Flow) : Completion :=
  let explicit := match flow.normal with
    | none => ({} : Completion)
    | some (value, state) => raised origin cls value state .user
  { explicit with raised := explicit.raised.join flow.raised }

/-- Explicit raises evaluate their argument before constructing the exception.
    Bare raises reuse the innermost active handler class set; outside a
    handler they produce the policy-controlled RuntimeError machine raise. -/
def raiseStatement (services : Services) (position : Pos)
    (cls : Option String) (argument : Option Expr)
    (state : AState) : M Completion := do
  let mut priorRaised : RaisedFlow := {}
  let mut normalInput : Option (List AbsVal × AState) := some ([], state)
  if let some expression := argument then
    let evaluated <- services.evalExpr expression state
    priorRaised := evaluated.raised
    normalInput := evaluated.normal.map fun (value, postState) =>
      ([value], postState)
  match normalInput with
  | none => pure (completionOfRaised priorRaised)
  | some (arguments, postState) =>
    let raisedNow <- match cls with
      | some className =>
        pure (raiseFromFlow position className
          (← services.constructException
            { position, className, arguments } postState))
      | none =>
        match (← get).handling with
        | active :: _ =>
          pure (raisedClasses position active AbsVal.bot postState .user)
        | [] =>
          machineRaised position ["RuntimeError"] postState
    pure {
      raisedNow with
      raised := priorRaised.join raisedNow.raised
    }

private def normalStateOfTruth (flow : TruthFlow) : Option AState :=
  joinOpt (flow.truthy.map (·.2)) (flow.falsy.map (·.2))

structure LoopBoundary where
  /-- Normal body fallthrough and `continue` return to the loop header. -/
  backedge : Option AState := none
  /-- `break` becomes normal loop exit; return and raise escape unchanged. -/
  escaped : Completion := {}
deriving Repr, Inhabited

/-- Consume the loop-local meanings of `break` and `continue`. -/
def consumeLoopBoundary (body : Completion) : LoopBoundary :=
  {
    backedge := joinOpt body.normal body.continued
    escaped := {
      normal := body.broke
      returned := body.returned
      raised := body.raised
    }
  }

/-- Join a break exit with normal exhaustion.  The caller runs a loop `else`
    only on `exhausted`; break paths bypass it. -/
def finishLoop (escaped : Completion)
    (exhausted : Completion) : Completion :=
  escaped.join exhausted

private def handlerMatches (classes : ClassTable) (raisedClass : String) :
    Handler -> Bool
  | .mk _ none _ _ => true
  | .mk _ (some handlerClass) _ _ =>
    excCaught classes raisedClass handlerClass

private def firstMatchingHandler? (classes : ClassTable)
    (raisedClass : String) (handlers : List Handler) : Option Handler :=
  handlers.find? (handlerMatches classes raisedClass)

private def handlerPosition : Handler -> Pos
  | .mk position _ _ _ => position

private def sameHandler (left right : Handler) : Bool :=
  (handlerPosition left).id == (handlerPosition right).id

private def cleanupHandlerTarget (name : Option String)
    (flow : Completion) : Completion :=
  match name with
  | none => flow
  | some name => mapStates flow (·.envKill name)

private def recordHandlerTable (tryPosition : Pos)
    (rows : List (String × Option (String × Nat))) : M Unit :=
  modify fun context =>
    match context.handlerTables.find? (·.1 == tryPosition.id) with
    | some (_, _, old) =>
      let merged := rows.foldl (fun result (raisedClass, target) =>
        if result.any (·.1 == raisedClass) then result
        else result ++ [(raisedClass, target)]) old
      {
        context with
        handlerTables := context.handlerTables.map
          (fun (node, line, existing) =>
            if node == tryPosition.id then
              (node, line, merged)
            else
              (node, line, existing))
      }
    | none =>
      {
        context with
        handlerTables := context.handlerTables ++
          [(tryPosition.id, tryPosition.line, rows)]
      }

private def matchingCases (classes : ClassTable) (handlers : List Handler)
    (selected : Handler) (cases : List RaisedCase) : List RaisedCase :=
  -- The direct oracle accumulates each handler's finite class set by front
  -- insertion.  Reverse the source exception order to preserve that profile.
  (cases.filter fun raised =>
    match firstMatchingHandler? classes raised.cls handlers with
    | some handler => sameHandler handler selected
    | none => false).reverse

private def uncaughtCases (classes : ClassTable) (handlers : List Handler)
    (cases : List RaisedCase) : List RaisedCase :=
  (cases.filter fun raised =>
    (firstMatchingHandler? classes raised.cls handlers).isNone).reverse

private def handlerRows (classes : ClassTable) (handlers : List Handler)
    (cases : List RaisedCase) :
    List (String × Option (String × Nat)) :=
  cases.map fun raised =>
    let target := (firstMatchingHandler? classes raised.cls handlers).map
      fun handler =>
        match handler with
        | .mk position cls _ _ => (cls.getD "bare", position.line)
    (raised.cls, target)

private def bindHandlerException (services : Services) (position : Pos)
    (target : Option String) (cases : List RaisedCase) (state : AState) :
    M Flow := do
  match target with
  | none => pure (Flow.ofNormal (V [.tnone]) state)
  | some name =>
    let mut postState := state
    let mut value := AbsVal.bot
    for raised in cases do
      let (fresh, allocated) :=
        allocate postState position.id (.obj raised.cls) []
      postState := allocated
      value := value.join fresh
    services.executeTarget (.bind (.tname position name) value) postState

/-- One clause, entered by one reaching completion, from that completion's own
    state. Was `executeHandlerGroup`, which took a whole group and a single
    joined entry state; the group is gone because grouping was the clumping. -/
private def executeHandlerCase (services : Services)
    (executeBody : BodyExecutor) (tryPosition : Pos) (clause : Nat)
    (raisedCase : RaisedCase) (handler : Handler) : M Completion := do
  let cases := [raisedCase]
  let entryState := raisedCase.state
  -- The state this clause is entered with, per raise reaching it. One run of the
  -- clause per reaching completion, so the entry point accumulates the join of
  -- the raises it actually catches -- which is the claim a handler obligation
  -- would be about.
  snapJoin (.handlerEntry clause) tryPosition entryState
  match handler with
  | .mk position _ target body =>
    let bound <- bindHandlerException services position target cases entryState
    let mut result := completionOfRaised bound.raised
    match bound.normal with
    | none => pure (cleanupHandlerTarget target result)
    | some (_, handlerState) =>
      -- The class a bare `raise` in this body re-raises is *this* case's class,
      -- not the whole clause's class set.
      let active := cases.map (·.cls)
      modify fun context =>
        { context with handling := active :: context.handling }
      let handled <- executeBody body handlerState
      modify fun context =>
        { context with handling := context.handling.drop 1 }
      result := result.join handled
      pure (cleanupHandlerTarget target result)

/-- Partition reaching exceptions by their first matching clause, record the
    routing table, and execute each nonempty clause exactly once.  Exceptions
    raised while binding or running a handler are outgoing and are never
    reconsidered by later clauses of this `try`.

    CLAIM handler-matches-subclass: a handler catches subclasses of the class
    it names, by the exception MRO.
    CLAIM handler-target-cleanup: the `except ... as name` target is unbound
    when the handler ends, after any alias has captured the exception.
-/
def routeHandlers (services : Services) (executeBody : BodyExecutor)
    (tryPosition : Pos) (handlers : List Handler)
    (body : Completion) : M Completion := do
  if handlers.isEmpty || body.raised.cases.isEmpty then
    return body
  let classes := (← get).classes
  recordHandlerTable tryPosition
    (handlerRows classes handlers body.raised.cases)
  let uncaught := uncaughtCases classes handlers body.raised.cases
  let mut result : Completion := {
    normal := body.normal
    returned := body.returned
    broke := body.broke
    continued := body.continued
    raised := { cases := uncaught }
  }
  -- One run of the clause per reaching completion, each from *its own* raise
  -- state. This used to join every case -- including ones another clause
  -- catches -- into a single entry state, so a handler could not tell which
  -- raise it was entered from: in
  --
  --     x = A() if b else B()
  --     try:
  --       raise AException() if isinstance(x, A) else BException()
  --     except AException as e: x.tag()
  --
  -- `x` arrived as `A | B` even though only the `A` raise can reach that
  -- clause, and the call split two ways instead of devirtualizing.
  --
  -- The number of runs is bounded by the raise sites reaching this `try`, which
  -- is syntactic, so a loop fixpoint still converges.
  for (handler, clause) in handlers.zipIdx do
    for raised in matchingCases classes handlers handler body.raised.cases do
      result := result.join
        (← executeHandlerCase services executeBody tryPosition clause raised
          handler)
  -- Where the clauses and the uncaught remainder come back together.
  if let some merged := result.normal then
    snapJoin .handlerMerge tryPosition merged
  pure result

/-- `else` receives only normal fallthrough from the try body.  In particular,
    exceptions raised by `else` bypass this try's handlers.

    CLAIM try-else-only-on-normal: `else` runs exactly when the body completed
    normally, never after a handler.
-/
def tryExceptElse (services : Services) (executeBody : BodyExecutor)
    (tryPosition : Pos) (body : Completion) (handlers : List Handler)
    (elseBody : List Stmt) : M Completion := do
  let routed <- routeHandlers services executeBody tryPosition handlers
    { body with normal := none }
  match body.normal with
  | none => pure routed
  | some state =>
    let elseResult <-
      if elseBody.isEmpty then pure (Completion.ofNormal state)
      else executeBody elseBody state
    pure (routed.join elseResult)

private def runFinallyOn (executeBody : BodyExecutor)
    (finalBody : List Stmt) (state : AState)
    (resume : AState -> Completion) : M Completion := do
  let finalResult <- executeBody finalBody state
  let resumed := match finalResult.normal with
    | none => ({} : Completion)
    | some finalState => resume finalState
  -- Any non-normal completion of finally replaces the pending completion.
  pure (resumed.join (abnormalOnly finalResult))

private def resumeRaised (pending : RaisedFlow) (state : AState) :
    Completion :=
  completionOfRaised {
    cases := pending.cases.map fun raised => { raised with state }
  }

/-- Run `finally` in the direct oracle's observable order: normal, break,
    continue, return, then one joined exceptional state.  A normal finalizer
    resumes the pending completion; an abnormal finalizer replaces it.

    CLAIM finally-on-every-completion: `finally` runs on all five completions:
    normal, raised, returned, broken, continued.
-/
def runFinally (executeBody : BodyExecutor) (tryPosition : Pos)
    (finalBody : List Stmt) (pending : Completion) : M Completion := do
  if finalBody.isEmpty then return pending
  -- `finally` runs once per pending completion, but it is one program point, so
  -- the entry accumulates the join of every completion that reaches it.
  if let some state := pending.normal then
    snapJoin .finallyEntry tryPosition state
  let mut result : Completion := {}
  if let some state := pending.normal then
    result := result.join
      (← runFinallyOn executeBody finalBody state Completion.ofNormal)
  if let some state := pending.broke then
    result := result.join
      (← runFinallyOn executeBody finalBody state broke)
  if let some state := pending.continued then
    result := result.join
      (← runFinallyOn executeBody finalBody state continued)
  if let some (value, state) := pending.returned then
    result := result.join
      (← runFinallyOn executeBody finalBody state (returned value))
  -- One run per pending raise, from that raise's own state. `state?` folded them
  -- into one, so a `finally` reached by two raises saw their states merged and
  -- re-attached that single merged state to every pending case: the classes
  -- survived, the states did not.
  for raised in pending.raised.cases do
    result := result.join
      (← runFinallyOn executeBody finalBody raised.state
        (resumeRaised { cases := [raised] }))
  pure result

def tryExceptElseFinally (services : Services)
    (executeBody : BodyExecutor) (tryPosition : Pos)
    (body : Completion) (handlers : List Handler)
    (elseBody finalBody : List Stmt) : M Completion := do
  let routed <- tryExceptElse services executeBody tryPosition body handlers
    elseBody
  let finished <- runFinally executeBody tryPosition finalBody routed
  if let some merged := finished.normal then
    snapJoin .finallyMerge tryPosition merged
  pure finished

mutual

/-- Execute a source body in order.  A statement receives only normal
    fallthrough; all four abnormal modes accumulate and bypass later
    statements.  Every reachable statement is snapped at its input state. -/
partial def executeBody (services : Services) (statements : List Stmt)
    (state : AState) : M Completion := do
  let mut result := Completion.ofNormal state
  for statement in statements do
    result <- sequence result fun current => do
      snap statement.pos current
      executeStatement services statement current
  pure result

/-- Execute a statement through its structural plan, when the table has one.

    The statement counterpart of the expression dispatch. A plan finishing with
    `returnWith`, `breakLoop` or `continueLoop` becomes the matching completion
    through `toCompletion`, which is what those three exist for. Only forms whose
    children are expressions are routed: a body or an assignment target is not an
    expression and the effects to evaluate them do not exist yet, so
    `stmtFramesOf` declines and the core below runs.

    This sits inside the kernel rather than in the caller because the caller
    reaches statements through `executeBody`, so a dispatch installed there would
    never run -- which is a mistake this file's history already contains. -/
partial def statementPlan? (services : Services) (statement : Stmt)
    (state : AState) : M (Option Completion) := do
  match Syntax.compiledSyntaxRules? with
  | none => pure none
  | some table =>
    match CompiledRules.find? table (.stmt (StmtKind.of statement)) with
    | none => pure none
    | some rule =>
      -- A declared engine body defers to the core transfer by design (section
      -- 1.6), checked explicitly rather than left to `stmtFramesOf` declining.
      match rule.body with
      | .engine _ => pure none
      | _ =>
      match Syntax.stmtFramesOf statement with
      | none => pure none
      | some frame =>
        let planServices : RuleDriven.Services := {
          invoke := fun callPos operation receiver arguments keywords st =>
            RuleDriven.Services.opaque.invoke callPos operation receiver arguments
              keywords st
          truth := fun _ value st =>
            pure { truthy := some (value, st), falsy := some (value, st) }
          evalSubterm := fun _ subterm st =>
            match subterm with
            | .expr child => services.evalExpr child st
            | _ => pure (Flow.ofNormal anyV st)
          truthSubterm := fun _ subterm value st =>
            match subterm with
            | .expr child => services.truth child value st
            | _ => pure { truthy := some (value, st), falsy := some (value, st) }
          refineSubterm := fun _ subterm st =>
            match subterm with
            | .expr child => services.refine child st
            | _ => pure (some st, some st)
          recordObligation := fun obligePos kind detail =>
            oblige obligePos kind detail
          executeBodyPlan := fun _ body st => executeBody services body st
          bindTargetValue := fun _ target value st =>
            services.executeTarget (.bind target value) st
          deleteTargetAt := fun _ target st =>
            services.executeTarget (.delete target) st
          engineTransfer := fun enginePos name _ _ => do
            oblige enginePos "engine-transfer-missing"
              s!"no engine transfer installed for {name}"
            pure {} }
        let planned <- executePlan planServices statement.pos rule.body frame
          state
        pure (some planned.toCompletion)

/-- Transfer for every non-loop statement.  Loops are deliberately the
    only compatibility case while their checked fixpoint driver is developed
    independently. -/
partial def executeStatement (services : Services) (statement : Stmt)
    (state : AState) : M Completion := do
  let reportedBefore := reportedClasses (<- get)
  let result <- match <- statementPlan? services statement state with
    | some completion => pure completion
    | none => executeStatementCore services statement state
  -- Attribution to a particular operand site is the transfer's business; what
  -- must not happen is an outcome no site reports at all.
  -- Only interpreter-raised outcomes need a dispatch row: an explicit `raise`
  -- is not a dispatch site.
  verifyReported statement.pos reportedBefore
    (result.raised.cases.foldr (fun raised out =>
      if raised.from? == .machine then Fset.insert raised.cls out else out) [])
  pure result

partial def executeStatementCore (services : Services) (statement : Stmt)
    (state : AState) : M Completion := do
  match statement with
  -- Routed through the structural-plan table (`RuleSyntax`), so
  -- `executeStatement` returns before reaching here. Kept to keep the match total
  -- and to fail closed: a missing plan yields an obligation and no completion,
  -- not a silent second implementation.
  | .assign .. | .annAssign .. | .exprS .. | .ifS .. | .ret .. | .brk ..
  | .cont .. | .pass .. | .assertS .. | .delS .. => do
    oblige statement.pos "syntax-rule-missing"
      s!"{(StmtKind.of statement).render} is routed but its plan was not found"
    pure {}
  | .whileS position condition body elseBody =>
    pure (RuleDriven.Compatibility.completionOfAMulti state
      (← services.executeLoop
        (.whileLoop position condition body elseBody) state))
  | .forS position target iterable body elseBody =>
    pure (RuleDriven.Compatibility.completionOfAMulti state
      (← services.executeLoop
        (.forLoop position target iterable body elseBody) state))
  | .tryS position body handlers elseBody finalBody => do
    -- The body runs with this try's caught classes active, so the abort policy
    -- does not prune an exception the program demonstrably handles.
    -- A bare `except:` catches everything, recorded as BaseException.
    let caught := handlers.foldl (fun classes handler =>
      match handler with
      | .mk _ (some handlerClass) _ _ => Fset.insert handlerClass classes
      | .mk _ none _ _ => Fset.insert "BaseException" classes) []
    modify fun context =>
      { context with activeHandlers := caught :: context.activeHandlers }
    let bodyResult <- executeBody services body state
    modify fun context =>
      { context with activeHandlers := context.activeHandlers.drop 1 }
    tryExceptElseFinally services (executeBody services) position bodyResult
      handlers elseBody finalBody
  | .raiseS position cls argument =>
    raiseStatement services position cls argument state
end

end Pylate.RuleDriven.Statements
