/-
Source-ordered structural expressions for the rule interpreter.

This module handles expression forms whose semantics are primarily evaluation
order, allocation, and control routing. Protocol operations remain in the
operation-level modules. The enclosing interpreter supplies recursive
expression evaluation, closed branch refinement, and admitted user-function
execution through the narrow Services boundary. Truth protocols and object
target writes reuse their explicit engines directly.

Deliberate gaps are not claimed as complete semantics here:

* comprehensions belong to their own fixpoint/provenance family;
* f-string lowering currently erases conversion and format-spec protocols;
* yield-from records an element abstraction, but does not yet execute the
  complete send/throw/close/StopIteration delegation protocol;
* tuple target binding uses the iterable element summary, without exact
  unpack arity, positional slots, or iterator-protocol failures;
* set/dict literal hashing and key equality currently emit obligations rather
  than executing effectful user protocols and splitting every failure.
-/
import Pylate.Transfers.Expressions
import Pylate.Transfers.Objects
import Pylate.Rules.SyntaxPlans

namespace Pylate.RuleDriven.StructuralExpressions

open Pylate
open Pylate.RuleDriven

structure Services where
  /-- Recursive evaluation of a child expression. -/
  evalExpr : Expr -> AState -> M Flow
  /-- Execute the caller's closed, side-effect-free refinement plan. It may
      only narrow the supplied state or rule a branch out; protocol effects
      have already occurred in the state passed to it. -/
  refine : Expr -> AState -> M (Option AState × Option AState)
  /-- Recursive execution of an admitted user function. Protocol checks and
      mutations remain in the closed operation modules. -/
  invokeUser : Pos -> String -> FuncDef -> List AbsVal ->
    List (String × AbsVal) -> AState -> M Flow

private def expressionServices (services : Services) :
    Expressions.Services :=
  { invokeUser := services.invokeUser }

private def objectServices (services : Services) : Objects.Services :=
  { invokeUser := services.invokeUser }

inductive SequenceLiteralKind
  | list
  | tuple
  | set
deriving Repr, Inhabited, DecidableEq

/-- Closed, first-order structural plan. Operation expressions and
    comprehensions are owned by other rule families and therefore do not
    compile to this plan. -/
inductive StructuralPlan
  | constant (value : Const)
  | name (position : Pos) (name : String)
  | boolOp (isAnd : Bool) (values : List Expr)
  | sequenceLiteral (kind : SequenceLiteralKind) (position : Pos)
      (values : List Expr)
  | dictLiteral (position : Pos) (items : List (Expr × Expr))
  | conditional (condition yes no : Expr)
  | fstring (parts : List Expr)
  | yieldValue (value : Option Expr)
  | yieldFrom (value : Expr)
deriving Inhabited

inductive TruthKnowledge
  | alwaysTruthy
  | alwaysFalsy
  | unknown
deriving Repr, Inhabited, DecidableEq

/-- Value-sensitive truth facts available directly from closed source syntax.
    Dynamic values still use the explicit protocol dispatcher. -/
def truthKnowledge : Expr -> TruthKnowledge
  | .const _ (.cbool true) => .alwaysTruthy
  | .const _ (.cbool false) => .alwaysFalsy
  | .const _ (.cint value) =>
    if value == 0 then .alwaysFalsy else .alwaysTruthy
  | .const _ (.cfloat value) =>
    if value == "0" || value == "0.0" then .alwaysFalsy else .unknown
  | .const _ (.cstr value) =>
    if value.isEmpty then .alwaysFalsy else .alwaysTruthy
  | .const _ .cnone => .alwaysFalsy
  | .listlit _ values | .tuplelit _ values | .setlit _ values =>
    if values.isEmpty then .alwaysFalsy else .alwaysTruthy
  | .dictlit _ items =>
    if items.isEmpty then .alwaysFalsy else .alwaysTruthy
  | _ => .unknown

private def applyTruthKnowledge (knowledge : TruthKnowledge)
    (flow : TruthFlow) : TruthFlow :=
  match knowledge with
  | .alwaysTruthy => { flow with falsy := none }
  | .alwaysFalsy => { flow with truthy := none }
  | .unknown => flow

private def refineTruthBranch (services : Services) (expression : Expr)
    (selectTruthy : Bool) (branch : Option Normal) : M (Option Normal) := do
  match branch with
  | none => pure none
  | some (value, state) =>
    let (truthyState, falsyState) <- services.refine expression state
    let selected := if selectTruthy then truthyState else falsyState
    pure (selected.map fun refined => (value, refined))

private def refineTruth (services : Services) (expression : Expr)
    (flow : TruthFlow) : M TruthFlow := do
  let truthy <- refineTruthBranch services expression true flow.truthy
  let falsy <- refineTruthBranch services expression false flow.falsy
  pure { truthy, falsy, raised := flow.raised }

private def evalTruth (services : Services) (expression : Expr)
    (value : AbsVal) (state : AState) : M TruthFlow := do
  let flow <- Expressions.truth (expressionServices services)
    expression.pos value state
  refineTruth services expression
    (applyTruthKnowledge (truthKnowledge expression) flow)

structure EvalSequence (α : Type) where
  values : List α := []
  normal : Option AState := none
  raised : RaisedFlow := {}
deriving Repr, Inhabited

private def raisedOfExc (fallback : AState) (exception : Exc) : RaisedFlow :=
  exception.tags.foldl (fun raised cls =>
    raised.add {
      cls
      value := AbsVal.bot
      state := exception.st.getD fallback
      -- Expanded from the joined `Exc` view, which carries no raise site.
      origin := {}
    }) {}

private def machineRaise (position : Pos) (cls : String)
    (state : AState) : M Flow := do
  let exception <- mraise position {} state [cls]
  pure { raised := raisedOfExc state exception }

private def withRaised (flow : Flow) (raised : RaisedFlow) : Flow :=
  { flow with raised := raised.join flow.raised }

private def joinValues (values : List AbsVal) : AbsVal :=
  values.foldl AbsVal.join AbsVal.bot

private def checkHashable (position : Pos) (value : AbsVal) : M Unit := do
  let bad := value.tags.filter fun tag =>
    tag == .tlist || tag == .tdict || tag == .tset
  if !bad.isEmpty then
    oblige position "hashability"
      s!"unhashable tags {bad.map Tag.render} at a key or element position"

def evalConstant (constant : Const) (state : AState) : Flow :=
  let value := constV constant
  Flow.ofNormal value state

/-- Read a local, global, or closed builtin name. Unbound alternatives split
    before the normal path is narrowed, retaining the original raise state. -/
def evalName (position : Pos) (name : String) (state : AState) : M Flow := do
  let context <- get
  let isLocal := (context.localScopes.headD []).contains name
  let value <- if isLocal then pure (state.envGet name)
    else readName state name
  if value.tags == [.tunbound] then
    oblige position "definitely-unbound"
      s!"read of {name}: no binding reaches this point"
    let cls := if isLocal then "UnboundLocalError" else "NameError"
    resCase position "name" s!"read {name}" "unbound" s!"!{cls}"
    machineRaise position cls state
  else if .tunbound ∈ value.tags then
    oblige position "maybe-unbound"
      s!"read of {name}: unbound on some path"
    let normalValue := value.withoutTags [.tunbound]
    let normal := Flow.ofNormal normalValue
      (state.envSet name normalValue)
    let cls := if isLocal then "UnboundLocalError" else "NameError"
    resCase position "name" s!"read {name}" "unbound" s!"!{cls}"
    pure (normal.join (← machineRaise position cls state))
  else
    pure (Flow.ofNormal value state)

/-- Evaluate expressions left-to-right. A child that has no normal completion
    prevents every later child from being evaluated. -/
def evalExpressions (services : Services) (expressions : List Expr)
    (state : AState) : M (EvalSequence AbsVal) := do
  let mut normal : Option AState := some state
  let mut raised : RaisedFlow := {}
  let mut values : List AbsVal := []
  for expression in expressions do
    match normal with
    | none => pure ()
    | some current =>
      let result <- services.evalExpr expression current
      raised := raised.join result.raised
      match result.normal with
      | none => normal := none
      | some (value, nextState) =>
        values := values ++ [value]
        normal := some nextState
  pure { values, normal, raised }

/-- Python `and`/`or`: truth-test every operand except the last, return the
    selected operand value, and evaluate the suffix only on the continuing
    truth branch.

    CLAIM boolop-shortcircuits: `and`/`or` do not evaluate the right operand
    when the left decides, and yield an operand rather than a bool.
-/
partial def evalBoolOp (services : Services) (isAnd : Bool)
    (expressions : List Expr) (state : AState) : M Flow := do
  match expressions with
  | [] => pure (Flow.ofNormal (V [.tbool]) state)
  | [expression] => services.evalExpr expression state
  | expression :: rest =>
    let evaluated <- services.evalExpr expression state
    let mut result : Flow := { raised := evaluated.raised }
    match evaluated.normal with
    | none => pure result
    | some (value, postState) =>
      let truth <- evalTruth services expression value postState
      result := { result with
        raised := result.raised.join truth.raised }
      let stopped := if isAnd then truth.falsy else truth.truthy
      let continued := if isAnd then truth.truthy else truth.falsy
      if let some (selected, selectedState) := stopped then
        let selected :=
          if isAnd then selected else selected.withoutTags [.tnone]
        result := result.join (Flow.ofNormal selected selectedState)
      if let some (_, continuedState) := continued then
        result := result.join
          (← evalBoolOp services isAnd rest continuedState)
      pure result

def evalListLiteral (services : Services) (position : Pos)
    (elements : List Expr) (state : AState) : M Flow := do
  let evaluated <- evalExpressions services elements state
  match evaluated.normal with
  | none => pure { raised := evaluated.raised }
  | some postState =>
    let (value, allocated) := allocate postState position.id .list []
    let location : Loc := ⟨position.id, .list, true⟩
    let initialized := allocated.heapSet location .elem
      (joinValues evaluated.values)
    -- The count, not just non-emptiness: a literal knows how many elements it
    -- has, and that is what settles `xs[0]` without a `bounds` obligation.
    -- `allocate` already recorded `exact 0`, so the empty case needs nothing.
    let initialized := if elements.isEmpty then initialized
      else strongSizeUpdate initialized location (.exact elements.length)
    pure (withRaised (Flow.ofNormal value initialized) evaluated.raised)

def evalTupleLiteral (services : Services) (position : Pos)
    (elements : List Expr) (state : AState) : M Flow := do
  let evaluated <- evalExpressions services elements state
  match evaluated.normal with
  | none => pure { raised := evaluated.raised }
  | some postState =>
    let (value, allocated) := allocate postState position.id .tuple []
    let location : Loc := ⟨position.id, .tuple, true⟩
    let mut initialized := allocated.heapSet location .elem
      (joinValues evaluated.values)
    for h : index in [0:evaluated.values.length] do
      initialized := initialized.heapSet location (.tupleSlot index)
        evaluated.values[index]
    if !elements.isEmpty then
      initialized := strongEmptinessUpdate initialized location .nonempty
    pure (withRaised (Flow.ofNormal value initialized) evaluated.raised)

def evalSetLiteral (services : Services) (position : Pos)
    (elements : List Expr) (state : AState) : M Flow := do
  let evaluated <- evalExpressions services elements state
  match evaluated.normal with
  | none => pure { raised := evaluated.raised }
  | some postState =>
    let elementValue := joinValues evaluated.values
    checkHashable position elementValue
    let (value, allocated) := allocate postState position.id .set []
    let location : Loc := ⟨position.id, .set, true⟩
    let initialized := allocated.heapSet location .elem elementValue
    let initialized := if elements.isEmpty then initialized
      else strongEmptinessUpdate initialized location .nonempty
    pure (withRaised (Flow.ofNormal value initialized) evaluated.raised)

private structure DictSequence where
  keys : AbsVal := AbsVal.bot
  values : AbsVal := AbsVal.bot
  literalFields : List (String × AbsVal) := []
  normal : Option AState := none
  raised : RaisedFlow := {}
deriving Inhabited

private def addLiteralField (fields : List (String × AbsVal))
    (key : String) (value : AbsVal) : List (String × AbsVal) :=
  match fields.find? (·.1 == key) with
  | some _ => fields.map fun (oldKey, oldValue) =>
      if oldKey == key then (oldKey, oldValue.join value)
      else (oldKey, oldValue)
  | none => fields ++ [(key, value)]

private def evalDictItems (services : Services)
    (items : List (Expr × Expr)) (state : AState) : M DictSequence := do
  let mut result : DictSequence := { normal := some state }
  for (keyExpression, valueExpression) in items do
    match result.normal with
    | none => pure ()
    | some current =>
      let key <- services.evalExpr keyExpression current
      result := { result with raised := result.raised.join key.raised }
      match key.normal with
      | none => result := { result with normal := none }
      | some (keyValue, keyState) =>
        let value <- services.evalExpr valueExpression keyState
        result := { result with raised := result.raised.join value.raised }
        match value.normal with
        | none => result := { result with normal := none }
        | some (itemValue, nextState) =>
          let mut fields := result.literalFields
          if .tstr ∈ keyValue.tags && !keyValue.strOpen then
            for keyLiteral in keyValue.strLits do
              fields := addLiteralField fields keyLiteral itemValue
          result := {
            keys := result.keys.join keyValue
            values := result.values.join itemValue
            literalFields := fields
            normal := some nextState
            raised := result.raised
          }
  pure result

def evalDictLiteral (services : Services) (position : Pos)
    (items : List (Expr × Expr)) (state : AState) : M Flow := do
  let evaluated <- evalDictItems services items state
  match evaluated.normal with
  | none => pure { raised := evaluated.raised }
  | some postState =>
    checkHashable position evaluated.keys
    let (value, allocated) := allocate postState position.id .dict []
    let location : Loc := ⟨position.id, .dict, true⟩
    let mut initialized :=
      (allocated.heapSet location .dictKeys evaluated.keys).heapSet location .dictValues evaluated.values
    for (key, fieldValue) in evaluated.literalFields do
      initialized := initialized.heapSet location (.literalKey key) fieldValue
    if !items.isEmpty then
      initialized := strongEmptinessUpdate initialized location .nonempty
    pure (withRaised (Flow.ofNormal value initialized) evaluated.raised)

/-- Conditional expression. Only the selected branch is evaluated from each
    truth partition. -/
def evalConditional (services : Services) (condition yes no : Expr)
    (state : AState) : M Flow := do
  let evaluated <- services.evalExpr condition state
  let mut result : Flow := { raised := evaluated.raised }
  match evaluated.normal with
  | none => pure result
  | some (value, postState) =>
    let truth <- evalTruth services condition value postState
    result := { result with
      raised := result.raised.join truth.raised }
    if let some (_, trueState) := truth.truthy then
      result := result.join (← services.evalExpr yes trueState)
    if let some (_, falseState) := truth.falsy then
      result := result.join (← services.evalExpr no falseState)
    pure result

/--CLAIM fstring-formats: an f-string interpolation formats each value and the
    result is always a `str`.
-/
def evalFString (services : Services) (parts : List Expr)
    (state : AState) : M Flow := do
  let evaluated <- evalExpressions services parts state
  match evaluated.normal with
  | none => pure { raised := evaluated.raised }
  | some postState =>
    pure (withRaised
      (Flow.ofNormal (V [.tstr]) postState) evaluated.raised)

private def recordYield (value : AbsVal) : M Unit :=
  modify fun context =>
    match context.yields with
    | values :: rest =>
      { context with yields := (value :: values) :: rest }
    | [] => context

def evalYield (services : Services) (expression : Option Expr)
    (state : AState) : M Flow := do
  match expression with
  | none =>
    recordYield (V [.tnone])
    pure (Flow.ofNormal (V [.tnone]) state)
  | some expression =>
    let evaluated <- services.evalExpr expression state
    match evaluated.normal with
    | none => pure evaluated
    | some (value, postState) =>
      recordYield value
      pure {
        normal := some (V [.tnone], postState)
        raised := evaluated.raised
      }

def evalYieldFrom (services : Services) (expression : Expr)
    (state : AState) : M Flow := do
  let evaluated <- services.evalExpr expression state
  match evaluated.normal with
  | none => pure evaluated
  | some (value, postState) =>
    recordYield (elemOf postState value)
    pure {
      normal := some (V [.tnone], postState)
      raised := evaluated.raised
    }

private def literalKey : Expr -> Option String
  | .const _ (.cstr key) => some key
  | _ => none

private def literalIndex : Expr -> Option Nat
  | .const _ (.cint index) =>
    if index >= 0 then some index.toNat else none
  | _ => none

private def preserveValue (value : AbsVal) (flow : Flow) : Flow :=
  { flow with normal := flow.normal.map fun (_, state) => (value, state) }

mutual

/-- Execute a target through its structural plan. Installed inside `bindTarget`
    rather than at its callers, because there are four of those and a dispatch at
    one of them would be reached from a quarter of the stores. The value being
    bound travels in `Frame.receiver`, which is what lets the target plans name it
    without an argument convention. -/
partial def targetPlan? (services : Services) (target : Target)
    (value : AbsVal) (state : AState) : M (Option Flow) := do
  match Syntax.compiledSyntaxRules? with
  | none => pure none
  | some table =>
    match CompiledRules.find? table (.target (TargetKind.of target)) with
    | none => pure none
    | some rule =>
      match rule.body with
      | .engine _ => pure none
      | _ =>
      match Syntax.targetFramesOf target with
      | none => pure none
      | some frame =>
        let planServices : RuleDriven.Services := {
          invoke := fun callPos operation receiver arguments keywords st =>
            match operation, receiver with
            | .attributeWrite field, some target =>
              Objects.attributeWrite (objectServices services) callPos target
                field (arguments.headD AbsVal.bot) st
            | .itemWriteAt literalKey literalIndex, some target =>
              let index := arguments.headD AbsVal.bot
              let stored := (arguments.drop 1).headD AbsVal.bot
              Objects.itemWrite (objectServices services) callPos target index
                stored literalKey literalIndex st
            | _, _ =>
              RuleDriven.Services.opaque.invoke callPos operation receiver arguments
                keywords st
          truth := RuleDriven.Services.opaque.truth
          evalSubterm := fun _ subterm st =>
            match subterm with
            | .expr child => services.evalExpr child st
            | _ => pure (Flow.ofNormal anyV st)
          storeNameValue := fun _ name bound st => pure (st.envSet name bound)
          bindTargetValue := fun _ nested bound st =>
            bindTarget services nested bound st }
        let planned <- executePlan planServices (Syntax.targetPos target) rule.body
          { frame with receiver := value } state
        -- The attribute store's source text, which the hand-written arm set with
        -- `resExpr`. Without it the site has no `expr` and a soundness assertion
        -- that looks the site up by its source text cannot find it -- which is
        -- how this was caught. Still dispatcher bookkeeping: debt two.
        match target with
        | .tattr position receiver field =>
          resExpr position s!"{exprText receiver}.{field} ="
        | _ => pure ()
        pure (some planned.flow)

/-- Bind one assignment target. Receiver and index expressions run in Python
    source order, and tuple targets bind left-to-right. -/
partial def bindTarget (services : Services) (target : Target)
    (value : AbsVal) (state : AState) : M Flow := do
  match <- targetPlan? services target value state with
  | some flow => pure flow
  | none =>
  match target with
  -- Routed through the structural-plan table, so `targetPlan?` returns before
  -- reaching here. Kept total and fail-closed for the same reason as the
  -- expression and statement matches.
  | .tname .. | .tattr .. | .tsub .. | .ttuple .. => do
    oblige (Syntax.targetPos target) "syntax-rule-missing"
      s!"{(TargetKind.of target).render} target is routed but its plan was not found"
    pure {}
end

/-- Compile source syntax to the closed structural plan. -/
def compile? (expression : Expr) : Option StructuralPlan :=
  match expression with
  | .const _ constant => some (.constant constant)
  | .name position name => some (.name position name)
  | .boolop _ isAnd values =>
    some (.boolOp isAnd values)
  | .listlit position values =>
    some (.sequenceLiteral .list position values)
  | .tuplelit position values =>
    some (.sequenceLiteral .tuple position values)
  | .setlit position values =>
    some (.sequenceLiteral .set position values)
  | .dictlit position items =>
    some (.dictLiteral position items)
  | .ifexp _ condition yes no =>
    some (.conditional condition yes no)
  | .fstr _ parts =>
    some (.fstring parts)
  | .yieldE _ value =>
    some (.yieldValue value)
  | .yieldFrom _ value =>
    some (.yieldFrom value)
  | .binop .. | .cmp .. | .notE .. | .unary .. | .attr ..
  | .subscr .. | .call .. | .comp .. =>
    none

/-- Generic executor for the closed structural plan. -/
partial def execute (services : Services) (plan : StructuralPlan)
    (state : AState) : M Flow := do
  match plan with
  | .constant constant =>
    pure (evalConstant constant state)
  | .name position name =>
    evalName position name state
  | .boolOp isAnd values =>
    evalBoolOp services isAnd values state
  | .sequenceLiteral kind position values =>
    match kind with
    | .list => evalListLiteral services position values state
    | .tuple => evalTupleLiteral services position values state
    | .set => evalSetLiteral services position values state
  | .dictLiteral position items =>
    evalDictLiteral services position items state
  | .conditional condition yes no =>
    evalConditional services condition yes no state
  | .fstring parts =>
    evalFString services parts state
  | .yieldValue value =>
    evalYield services value state
  | .yieldFrom value =>
    evalYieldFrom services value state

/-- Evaluate a structural expression, or return `none` when another
    operation family owns the node. Comprehensions are deliberately excluded. -/
partial def evaluate? (services : Services) (expression : Expr)
    (state : AState) : M (Option Flow) := do
  match compile? expression with
  | none => pure none
  | some plan => pure (some (← execute services plan state))

end Pylate.RuleDriven.StructuralExpressions
