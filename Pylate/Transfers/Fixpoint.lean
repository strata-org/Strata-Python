/-
Checked loop and comprehension fixpoints for the rule interpreter.

The only recursion below is an ascending lattice iteration.  There is no
fuel-based successful exit: `close` returns only after the newly computed
backedge is below the current invariant.
-/
import Pylate.Transfers.Statements

namespace Pylate.RuleDriven.Fixpoint

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.Statements

structure BranchFlow where
  truthy : Option AState := none
  falsy  : Option AState := none
  raised : RaisedFlow := {}
deriving Repr, Inhabited

/-- Services that require recursive source evaluation.  Allocation, recency,
    state joins, snapshots, and completion routing remain in this module. -/
structure Services where
  evalExpr : Expr -> AState -> M Flow
  /-- Execute the one-time `iter(value)` protocol.  The normal value is the
      resulting iterator; its `elem` edge is read by the fixpoint. -/
  iterate : Pos -> AbsVal -> AState -> M Flow
  truth : Expr -> AbsVal -> AState -> M TruthFlow
  refine : Expr -> TruthFlow -> M BranchFlow
  bindTarget : Target -> AbsVal -> AState -> M Flow
  executeBody : List Stmt -> AState -> M Completion
  requireHashable : Pos -> AbsVal -> AState -> M Flow
  generatorExceptions : AbsVal -> M (Fset String)

structure WhileSpec where
  position : Pos
  condition : Expr
  body : List Stmt
  elseBody : List Stmt := []
deriving Inhabited

structure ForSpec where
  position : Pos
  target : Target
  iterable : Expr
  body : List Stmt
  elseBody : List Stmt := []
deriving Inhabited

inductive ComprehensionForm
  | list (element : Expr)
  | set (element : Expr)
  | dict (key value : Expr)
  | generator (element : Expr)
deriving Inhabited

def ComprehensionForm.kind : ComprehensionForm -> CompKind
  | .list _ => .clist
  | .set _ => .cset
  | .dict _ _ => .cdict
  | .generator _ => .cgen

structure ComprehensionSpec where
  position : Pos
  form : ComprehensionForm
  target : String
  iterable : Expr
  filters : List Expr := []
deriving Inhabited

private inductive IterationSpec
  | whileBody (condition : Expr) (body : List Stmt)
  | forBody (target : Target) (element : AbsVal) (body : List Stmt)
  | comprehensionBody
      (position : Pos)
      (form : ComprehensionForm)
      (target : String)
      (source : AbsVal)
      (filters : List Expr)
      (location : Loc)

/-- Adapter for the existing state-only refinement operation.  Truth-protocol
    states remain separate, so effects performed by `__bool__`/`__len__` are
    not collapsed before refinement. -/
def refineTruthWith
    (refineState : Expr -> AState ->
      M (Option AState × Option AState))
    (expression : Expr) (truth : TruthFlow) : M BranchFlow := do
  let mut truthy : Option AState := none
  let mut falsy : Option AState := none
  if let some (_, state) := truth.truthy then
    let (yes, _) <- refineState expression state
    truthy := joinOpt truthy yes
  if let some (_, state) := truth.falsy then
    let (_, no) <- refineState expression state
    falsy := joinOpt falsy no
  pure { truthy, falsy }

def evaluateCondition (services : Services) (condition : Expr)
    (state : AState) : M BranchFlow := do
  let evaluated <- services.evalExpr condition state
  let mut result : BranchFlow := { raised := evaluated.raised }
  match evaluated.normal with
  | none => pure result
  | some (value, postState) =>
    let truth <- services.truth condition value postState
    let refined <- services.refine condition truth
    pure {
      truthy := refined.truthy
      falsy := refined.falsy
      raised := (result.raised.join truth.raised).join refined.raised
    }

structure Step where
  /-- Normal fallthrough and `continue` return to the loop header. -/
  backedge : Option AState := none
  /-- Break, return, and exceptions leave this iteration. -/
  escaped : Completion := {}
  /-- At least one normal comprehension element was produced. -/
  produced : Bool := false
deriving Repr, Inhabited

structure Result where
  invariant : AState
  escaped   : Completion := {}
  produced  : Bool := false
  progressed : Bool := false
  rounds    : Nat := 0
deriving Repr, Inhabited

private def completionOfRaised (raised : RaisedFlow) : Completion :=
  { raised }

private def normalizeGeneratorException (cls : String) : String :=
  if cls == "StopIteration" then "RuntimeError" else cls

/-- A generator body's exceptions, attributed to the point that consumes it --
    which is where they surface, and where two different generators consumed at
    different sites must not share a bucket. -/
def generatorRaisedAt (origin : Pos) (classes : Fset String)
    (state : AState) : RaisedFlow :=
  classes.foldl (fun raised cls =>
    raised.add {
      cls := normalizeGeneratorException cls
      value := AbsVal.bot
      state
      origin
    }) {}

def recordGeneratorExceptions (site : NodeId) (raised : RaisedFlow) : M Unit := do
  let classes := raised.cases.foldl (fun out raised =>
    Fset.insert (normalizeGeneratorException raised.cls) out) []
  if classes.isEmpty then return
  modify fun context =>
    match context.genExc.find? (·.1 == site) with
    | some _ =>
      { context with genExc := context.genExc.map fun (oldSite, old) =>
          if oldSite == site
          then (oldSite, Fset.union classes old)
          else (oldSite, old) }
    | none => { context with genExc := context.genExc ++ [(site, classes)] }

def definitelyNonempty (value : AbsVal) (state : AState) : Bool :=
  !value.locs.isEmpty &&
    value.locs.all fun location =>
      state.emptinessGet location == .nonempty

/--CLAIM generator-raises-at-consumption: a generator body's exception
    surfaces where it is consumed, not where it is created.
-/
def exhaustGenerators (value : AbsVal) (state : AState) : AState :=
  value.locs.foldl (fun current location =>
    if location.cls == .gen
    then strongEmptinessUpdate current location .empty
    else current) state

private def executeElse (services : Services) (body : List Stmt)
    (state : AState) : M Completion :=
  if body.isEmpty then
    pure (.ofNormal state)
  else
    services.executeBody body state

private def whileStep (services : Services) (position : Pos) (condition : Expr)
    (body : List Stmt) (invariant : AState) : M Step := do
  let branch <- evaluateCondition services condition invariant
  let mut escaped := completionOfRaised branch.raised
  let mut backedge : Option AState := none
  if let some bodyState := branch.truthy then
    let bodyResult <- services.executeBody body bodyState
    -- Where a `continue` lands. `consumeLoopBoundary` folds it into the backedge,
    -- so this is the only place the continued state is still separable.
    if let some continuedState := bodyResult.continued then
      snapJoin .continueTarget position continuedState
    let boundary := consumeLoopBoundary bodyResult
    backedge := boundary.backedge
    escaped := escaped.join boundary.escaped
  pure { backedge, escaped }

private def iterationElement (state : AState) (source : AbsVal) : AbsVal :=
  { elemOf state source with witness := true }

private def forStep (services : Services) (position : Pos) (target : Target)
    (element : AbsVal) (body : List Stmt)
    (invariant : AState) : M Step := do
  let bound <- services.bindTarget target element invariant
  let mut escaped := completionOfRaised bound.raised
  let mut backedge : Option AState := none
  match bound.normal with
  | none => pure ()
  | some (_, bodyState) =>
    let bodyResult <- services.executeBody body bodyState
    if let some continuedState := bodyResult.continued then
      snapJoin .continueTarget position continuedState
    let boundary := consumeLoopBoundary bodyResult
    backedge := boundary.backedge
    escaped := escaped.join boundary.escaped
  pure { backedge, escaped }

private def compClass : ComprehensionForm -> LocCls
  | .list _ => .list
  | .set _ => .set
  | .dict _ _ => .dict
  | .generator _ => .gen

private def appendResult (location : Loc) (cell : CellSelector)
    (value : AbsVal) (state : AState) : AState :=
  state.heapJoin location cell value

private def hashThenAppend (services : Services) (position : Pos)
    (location : Loc) (cell : CellSelector) (value : AbsVal)
    (state : AState) : M (Option AState × RaisedFlow) := do
  let hashed <- services.requireHashable position value state
  let normal := hashed.normal.map fun (_, postState) =>
    appendResult location cell value postState
  pure (normal, hashed.raised)

private def produceComprehension (services : Services) (position : Pos)
    (form : ComprehensionForm)
    (location : Loc) (state : AState) :
    M (Option AState × RaisedFlow × Bool) := do
  let keyExpr := match form with
    | .list element | .set element | .generator element => element
    | .dict key _ => key
  let key <- services.evalExpr keyExpr state
  let mut raised := key.raised
  match key.normal with
  | none => pure (none, raised, false)
  | some (keyValue, keyState) =>
    match form with
    | .list _ | .generator _ =>
      pure (some (appendResult location .elem keyValue keyState),
        raised, true)
    | .set _ =>
      let (normal, hashRaised) <-
        hashThenAppend services position location .elem keyValue keyState
      pure (normal, raised.join hashRaised, normal.isSome)
    | .dict _ valueExpr =>
      -- CPython evaluates key, then value, then MAP_ADD hashes the key.
      let value <- services.evalExpr valueExpr keyState
      raised := raised.join value.raised
      match value.normal with
      | none => pure (none, raised, false)
      | some (valueValue, valueState) =>
        let hashed <-
          services.requireHashable position keyValue valueState
        raised := raised.join hashed.raised
        let normal := hashed.normal.map fun (_, hashState) =>
          (appendResult location .dictKeys keyValue hashState).heapJoin location .dictValues valueValue
        pure (normal, raised, normal.isSome)

private def comprehensionStep (services : Services) (position : Pos)
    (form : ComprehensionForm)
    (target : String) (source : AbsVal) (filters : List Expr)
    (location : Loc) (invariant : AState) : M Step := do
  let element := iterationElement invariant source
  let mut selected : Option AState :=
    if element.isBot && !(Tag.tany ∈ source.tags)
    then none
    else some (invariant.envSet target element)
  let mut skipped : Option AState := none
  let mut raised : RaisedFlow := {}
  for filter in filters do
    match selected with
    | none => pure ()
    | some current =>
      let branch <- evaluateCondition services filter current
      raised := raised.join branch.raised
      selected := branch.truthy
      skipped := joinOpt skipped branch.falsy
  let mut completed := skipped
  let mut produced := false
  if let some current := selected then
    let (normal, producedRaised, didProduce) <-
      produceComprehension services position form location current
    completed := joinOpt completed normal
    raised := raised.join producedRaised
    produced := didProduce
  pure {
    backedge := completed
    escaped := completionOfRaised raised
    produced
  }

private def executeIteration (services : Services) (position : Pos)
    (spec : IterationSpec) (invariant : AState) : M Step :=
  match spec with
  | .whileBody condition body =>
    whileStep services position condition body invariant
  | .forBody target element body =>
    forStep services position target element body invariant
  | .comprehensionBody position form target source filters location =>
    comprehensionStep services position form target source filters
      location invariant

/-- Least ascending post-fixpoint for a closed iteration specification.
    `rounds` is diagnostic only and never controls termination. -/
private partial def close (services : Services) (position : Pos)
    (spec : IterationSpec)
    (invariant : AState) (escaped : Completion := {})
    (produced : Bool := false) (progressed : Bool := false)
    (rounds : Nat := 0) : M Result := do
  -- The loop head is the widening point, and now has a name: every round's
  -- invariant is recorded against it rather than against the enclosing line,
  -- which is what used to overwrite the statement's own snapshot.
  snapJoin .loopHead position invariant
  let step <- executeIteration services position spec invariant
  let escaped := escaped.join step.escaped
  let produced := produced || step.produced
  let progressed := progressed || step.backedge.isSome
  let next := match step.backedge with
    | none => invariant
    | some backedge => invariant.join backedge
  if next.le invariant then
    pure (Result.mk invariant escaped produced progressed (rounds + 1))
  else
    close services position spec next escaped produced progressed (rounds + 1)

/-- Python `while`: only normal body completion and `continue` form the
    backedge; `break` exits without running `else`; only false-condition
    exhaustion runs `else`.

    CLAIM loop-fixpoint-widens: a variable assigned different types across
    iterations holds their join after the loop.
-/
def whileFixpoint (services : Services) (spec : WhileSpec)
    (state : AState) : M Completion := do
  let iteration := IterationSpec.whileBody spec.condition spec.body
  let fixed <- close services spec.position iteration state
  let exhaustion <-
    evaluateCondition services spec.condition fixed.invariant
  let mut result :=
    fixed.escaped.join (completionOfRaised exhaustion.raised)
  -- Where a `break` lands. `fixed.escaped` is exactly the completion the loop
  -- body escaped with, so this is the break target and nothing else.
  if let some escapedState := fixed.escaped.normal then
    snapJoin .breakTarget spec.position escapedState
  if let some exhaustedState := exhaustion.falsy then
    result := result.join
      (← executeElse services spec.elseBody exhaustedState)
  -- Normal fall-through past the loop, after `else` if there is one.
  if let some exitState := result.normal then
    snapJoin .loopExit spec.position exitState
  pure result

/-- Python `for`: iterable evaluation precedes target binding, binding
    failures retain their exact state, and generator-body summaries surface
    at the stabilized iteration state. -/
def forFixpoint (services : Services) (spec : ForSpec)
    (state : AState) : M Completion := do
  let source <- services.evalExpr spec.iterable state
  let mut result := completionOfRaised source.raised
  match source.normal with
  | none => pure result
  | some (sourceValue, sourceState) =>
    let iterator <- services.iterate spec.position sourceValue sourceState
    result := result.join (completionOfRaised iterator.raised)
    match iterator.normal with
    | none => pure result
    | some (iteratorValue, iteratorState) =>
      let definitelyHasElement :=
        definitelyNonempty iteratorValue iteratorState
      let iterState := exhaustGenerators iteratorValue iteratorState
      let element := iterationElement iterState iteratorValue
      let generatorClasses <-
        services.generatorExceptions iteratorValue
      if element.isBot && !(Tag.tany ∈ iteratorValue.tags) then
        result := result.join
          (completionOfRaised
            (generatorRaisedAt spec.position generatorClasses iterState))
        result := result.join
          (← executeElse services spec.elseBody iterState)
        pure result
      else
        let iteration :=
          IterationSpec.forBody spec.target element spec.body
        let fixed <-
          close services spec.position iteration iterState
        result := result.join fixed.escaped
        result := result.join
          (completionOfRaised
            (generatorRaisedAt spec.position generatorClasses fixed.invariant))
        if !definitelyHasElement || fixed.progressed then
          result := result.join
            (← executeElse services spec.elseBody fixed.invariant)
        pure result

/-- One-generator list/set/dict/generator comprehension.  The result object
    is allocated before iteration, so repeated allocations in element
    expressions are folded through the ordinary recency abstraction.

    CLAIM comprehension-scope: a comprehension's target is scoped to it and
    does not leak; a failing element leaves the enclosing assignment untouched.
-/
def comprehension (services : Services) (spec : ComprehensionSpec)
    (state : AState) : M Flow := do
  let source <- services.evalExpr spec.iterable state
  match source.normal with
  | none => pure { raised := source.raised }
  | some (sourceValue, sourceState) =>
    let iterator <- services.iterate spec.position sourceValue sourceState
    let immediateRaised := source.raised.join iterator.raised
    match iterator.normal with
    | none => pure { raised := immediateRaised }
    | some (iteratorValue, iteratorState) =>
      let saved := iteratorState.envGet spec.target
      let definitelyHasElement :=
        definitelyNonempty iteratorValue iteratorState
      let cls := compClass spec.form
      let (resultValue, allocated) :=
        allocate iteratorState spec.position.id cls []
      let location : Loc := ⟨spec.position.id, cls, true⟩
      let iteration := IterationSpec.comprehensionBody
        spec.position spec.form spec.target iteratorValue spec.filters
          location
      let fixed <-
        close services spec.position iteration allocated
      let generatorClasses <-
        services.generatorExceptions iteratorValue
      let iterationRaised := fixed.escaped.raised.join
        (generatorRaisedAt spec.position generatorClasses fixed.invariant)
      let mut finalState := fixed.invariant.envSet spec.target saved
      if spec.filters.isEmpty && fixed.produced &&
          definitelyHasElement &&
          (spec.form.kind != .cgen || iterationRaised.cases.isEmpty) then
        finalState := strongEmptinessUpdate finalState location .nonempty
      finalState := exhaustGenerators iteratorValue finalState
      match spec.form with
      | .generator _ =>
        recordGeneratorExceptions spec.position.id iterationRaised
        oblige spec.position "special-method"
          "generator expression analyzed eagerly: suspension interleaving asserted away"
        pure {
          normal := some (resultValue, finalState)
          raised := immediateRaised
        }
      | .list _ | .set _ | .dict _ _ =>
        let canComplete := !definitelyHasElement || fixed.progressed
        pure {
          normal :=
            if canComplete then some (resultValue, finalState) else none
          raised := immediateRaised.join iterationRaised
        }

end Pylate.RuleDriven.Fixpoint
