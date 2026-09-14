/-
The rule-driven interpreter. Its structural semantics are synchronized
with the direct interpreter, which remains the differential oracle. Migrated
families enter ordered plans at one compatibility boundary; all other
operations retain the procedural transfer as a fallback.
-/
import Pylate.Tables.Binary
import Pylate.Rules.Builtins
import Pylate.Transfers.Calls
import Pylate.Transfers.Compatibility
import Pylate.Transfers.Dict
import Pylate.Transfers.Expressions
import Pylate.Transfers.Iteration
import Pylate.Transfers.Fixpoint
import Pylate.Transfers.Objects
import Pylate.Rules.Opaque
import Pylate.Transfers.Protocols
import Pylate.Transfers.Statements
import Pylate.Transfers.StructuralExpressions
import Pylate.Rules.SyntaxPlans

namespace Pylate.RuleDriven

class RuleProvider where
  compiledRules : RuleDriven.CompiledRules

section

variable [RuleProvider]

-- `KeyCases` and `keyCases` live in `RuleKeys`. The copy here was identical
-- apart from variable names; a namespace level had hidden the duplication.

structure EvalSeq (α : Type) where
  values : List α := []
  normal : Option AState := none
  exc    : Exc := {}
deriving Inhabited

structure StateRes where
  normal : Option AState := none
  exc    : Exc := {}
deriving Inhabited

partial def targetLocalNames : Target → Fset String
  | .tname _ name => [name]
  | .ttuple _ targets =>
    targets.foldl (fun names target =>
      Fset.union (targetLocalNames target) names) []
  | .tattr .. | .tsub .. => []

mutual

partial def stmtLocalNames : Stmt → Fset String
  | .assign _ target _ => targetLocalNames target
  | .annAssign _ name _ => [name]
  | .ifS _ _ yes no | .whileS _ _ yes no =>
    Fset.union (bodyLocalNames yes) (bodyLocalNames no)
  | .forS _ target _ body orelse =>
    Fset.union (targetLocalNames target)
      (Fset.union (bodyLocalNames body) (bodyLocalNames orelse))
  | .tryS _ body handlers orelse finalbody =>
    let handlerNames := handlers.foldl (fun names handler =>
      match handler with
      | .mk _ _ target handlerBody =>
        let names := Fset.union (bodyLocalNames handlerBody) names
        match target with
        | some name => Fset.insert name names
        | none => names) []
    Fset.union (bodyLocalNames body) <|
      Fset.union handlerNames <|
        Fset.union (bodyLocalNames orelse) (bodyLocalNames finalbody)
  | .delS _ target => targetLocalNames target
  | .exprS .. | .ret .. | .brk .. | .cont .. | .pass ..
  | .raiseS .. | .assertS .. => []

partial def bodyLocalNames (body : List Stmt) : Fset String :=
  body.foldl (fun names stmt =>
    Fset.union (stmtLocalNames stmt) names) []

end

def functionLocalNames (fd : FuncDef) : Fset String :=
  Fset.union (fd.params.map (·.name)) (bodyLocalNames fd.body)

/-- Key partition used by TypedDict operations. A user object may compare
    equal to a declared string through reflected equality, and may also be
    unhashable; exact builtin non-string values cannot equal a string key. -/
def typedDictKeys (ci : ClassInfo) : AbsVal :=
  ci.fields.foldl (fun out field => out.join (strLitV field.name)) AbsVal.bot

def typedDictValues (ci : ClassInfo) (l : Loc) (st : AState) : AbsVal :=
  ci.fields.foldl (fun out field =>
    out.join ((st.heapGet l (.literalKey field.name)).withoutTags [.tmissing]))
    AbsVal.bot

def definitelyNonempty (value : AbsVal) (st : AState) : Bool :=
  !value.locs.isEmpty &&
    value.locs.all (fun location =>
      st.emptinessGet location == .nonempty)

def clearGeneratorNonempty (value : AbsVal) (st : AState) : AState :=
  value.locs.foldl (fun state location =>
    if location.cls == LocCls.gen then
      strongEmptinessUpdate state location .empty
    else state) st

private instance : Nonempty RuleDriven.Calls.Services :=
  ⟨{
    executeBody := fun _ state =>
      pure (RuleDriven.Completion.ofNormal state)
  }⟩

private instance : Nonempty RuleDriven.Expressions.Services :=
  ⟨{
    invokeUser := fun _ _ _ _ _ state =>
      pure (Flow.ofNormal anyV state)
  }⟩

private instance : Nonempty RuleDriven.StructuralExpressions.Services :=
  ⟨{
    evalExpr := fun _ state =>
      pure (Flow.ofNormal anyV state)
    refine := fun _ state => pure (some state, some state)
    invokeUser := fun _ _ _ _ _ state =>
      pure (Flow.ofNormal anyV state)
  }⟩

private instance : Nonempty RuleDriven.Iteration.Services :=
  ⟨{
    classInfo := fun _ => pure none
    resolveMethod := fun _ _ => pure none
    invokeUser := fun _ _ _ _ _ state =>
      pure (Flow.ofNormal anyV state)
    exceptionSubclass := fun _ _ => pure false
    hashKey := fun _ value state => pure (Flow.ofNormal value state)
    equalKeys := fun _ _ _ state =>
      pure (Flow.ofNormal (V [.tbool]) state)
    checkAnnotation := fun _ _ _ value state =>
      pure (Flow.ofNormal value state)
  }⟩

private instance : Nonempty RuleDriven.Contracts.Services :=
  ⟨{
    classInfo := fun _ => pure none
    resolveMethod := fun _ _ => pure none
    invokeUser := fun _ _ _ _ _ state =>
      pure (Flow.ofNormal anyV state)
    unknownProtocol := fun _ _ _ state =>
      pure (Flow.ofNormal anyV state)
    truthValue := fun _ _ state =>
      pure (Flow.ofNormal (V [.tbool]) state)
    consumeElements := fun _ value _ state =>
      pure (Flow.ofNormal value state)
    invokeCallable := fun _ _ _ state =>
      pure (Flow.ofNormal anyV state)
    consumeMappingPairs := fun _ _ state =>
      pure (Flow.ofNormal anyV state)
    recursiveAnnotation := fun _ _ value state =>
      pure (Flow.ofNormal value state)
  }⟩

private instance : Nonempty RuleDriven.Protocols.Services :=
  ⟨{
    resolveMethod := fun _ _ => pure none
    invokeUser := fun _ _ _ _ _ state =>
      pure (Flow.ofNormal anyV state)
    generatorExceptions := fun _ => pure []
  }⟩

private instance : Nonempty RuleDriven.Fixpoint.Services :=
  ⟨{
    evalExpr := fun _ state =>
      pure (Flow.ofNormal anyV state)
    iterate := fun _ _ state =>
      pure (Flow.ofNormal anyV state)
    truth := fun _ value state =>
      pure {
        truthy := some (value, state)
        falsy := some (value, state)
      }
    refine := fun _ truth =>
      pure {
        truthy := truth.truthy.map (·.2)
        falsy := truth.falsy.map (·.2)
        raised := truth.raised
      }
    bindTarget := fun _ value state =>
      pure (Flow.ofNormal value state)
    executeBody := fun _ state =>
      pure (RuleDriven.Completion.ofNormal state)
    requireHashable := fun _ value state =>
      pure (Flow.ofNormal value state)
    generatorExceptions := fun _ => pure []
  }⟩

private instance : Nonempty RuleDriven.Statements.Services :=
  ⟨{
    evalExpr := fun _ state =>
      pure (Flow.ofNormal anyV state)
    truth := fun _ value state =>
      pure {
        truthy := some (value, state)
        falsy := some (value, state)
      }
    refine := fun _ state => pure (some state, some state)
    executeTarget := fun _ state =>
      pure (Flow.ofNormal (V [.tnone]) state)
    constructException := fun _ state =>
      pure (Flow.ofNormal anyV state)
    executeLoop := fun _ state => pure (.ofNormal state)
  }⟩

/-- The state on one exceptional edge, narrowed to the receiver value that
    produced it. See `RuleObjects.narrowReceiver`: the transfer knows which tag
    failed but not which variable held the receiver, so it takes the receiver's
    syntax. A plain name is narrowed; anything else is left alone, which is the
    over-approximation and therefore safe. -/
def narrowReceiverExpr (recvExpr : Option Expr) (narrowed : AbsVal)
    (st : AState) : AState :=
  match recvExpr with
  | some (.name _ x) => if (st.envGet x).isBot then st else st.envSet x narrowed
  | _ => st

mutual

partial def v2CallServices : RuleDriven.Calls.Services :=
  {
    executeBody := fun statements state =>
      RuleDriven.Statements.executeBody v2StatementServices statements state
  }

partial def v2InvokeUser (position : Pos) (qualifiedName : String)
    (function : FuncDef) (arguments : List AbsVal)
    (keywords : List (String × AbsVal)) (state : AState) : M Flow := do
  let flow ← RuleDriven.Calls.invokeUser v2CallServices position qualifiedName function
    arguments keywords state
  -- Whatever escapes an invoked hook escapes the operation that invoked it.
  for raised in flow.raised.cases do
    resCaseAt position "call" s!"{qualifiedName}(..)" "code" s!"!{raised.cls}"
  pure flow

partial def v2ExpressionServices : RuleDriven.Expressions.Services :=
  { invokeUser := v2InvokeUser }

partial def v2StructuralServices : RuleDriven.StructuralExpressions.Services :=
  {
    evalExpr := evalExprFlow
    refine := refine
    invokeUser := v2InvokeUser
  }

partial def v2ProtocolServices : RuleDriven.Protocols.Services :=
  {
    resolveMethod := resolveMethodM
    invokeUser := v2InvokeUser
    generatorExceptions := genExcOf
  }

partial def classInfoM (name : String) : M (Option ClassInfo) := do
  pure ((← get).classes.getCls? name)

/-- Assert then assume one recursive annotation. This is a proof boundary, so
    a violation records an obligation instead of raising. -/
partial def v2CheckAnnotationLabelled (position : Pos) (label : String)
    (annotation : Ann) (value : AbsVal) (state : AState) : M Flow := do
  let context ← get
  if !annEntailedDeep 16 context.classes state value annotation then
    oblige position "type-error"
      s!"{label}: value does not satisfy the declared type"
  pure (Flow.ofNormal (assumeAnn context.classes value annotation) state)

partial def v2CheckAnnotation (position : Pos) (annotation : Ann)
    (value : AbsVal) (state : AState) : M Flow :=
  v2CheckAnnotationLabelled position "value" annotation value state

/-- Hash one key: the hashability contract plus the user hook's own effects. -/
partial def v2HashKey (position : Pos) (key : AbsVal)
    (state : AState) : M Flow :=
  requireHashableFlow position key state

/-- Compare a stored key with an incoming key, retaining hook effects. -/
partial def v2EqualKeys (position : Pos) (stored incoming : AbsVal)
    (state : AState) : M Flow :=
  RuleDriven.Expressions.comparison v2ExpressionServices position .eq stored
    incoming state "key equality"

/-- An unknown value's protocol hook may run any admitted code. -/
partial def v2UnknownProtocol (position : Pos)
    (protocol : RuleDriven.Contracts.UnknownProtocol) (value : AbsVal)
    (state : AState) : M Flow := do
  oblige position "dispatch-any"
    s!"unknown value reaching the {protocol.label} protocol"
  pure (Flow.ofNormal anyV (← havocReachable position [value] state))

/-- Truth conversion as a contract service: the bool result plus every hook
    effect and exception the conversion produced. -/
partial def v2TruthValue (position : Pos) (value : AbsVal)
    (state : AState) : M Flow := do
  let truth ← RuleDriven.Expressions.truth v2ExpressionServices position value state
  let mut output : Flow := { raised := truth.raised }
  for branch in [truth.truthy, truth.falsy] do
    if let some (_, branchState) := branch then
      output := output.join (Flow.ofNormal (V [.tbool]) branchState)
  pure output

/-- Invoke a callable value with `arity` unknown arguments. -/
partial def v2InvokeCallable (position : Pos) (callee : AbsVal)
    (arity : Nat) (state : AState) : M Flow := do
  let context ← get
  let arguments := List.replicate arity anyV
  let mut output : Flow := {}
  let mut handled := false
  for name in callee.funcs do
    if let some (_, function) := context.funcs.find? (·.1 == name) then
      handled := true
      output := output.join
        (← v2InvokeUser position name function arguments [] state)
  for tag in callee.tags do
    if let .tobj className := tag then
      if let some (owner, function) ← resolveMethodM className "__call__" then
        handled := true
        output := output.join
          (← v2InvokeUser position s!"{owner}.__call__" function
            (callee.restrictTags [tag] :: arguments) [] state)
  if !handled then
    oblige position "dispatch-any"
      "callback is not a resolvable admitted callable"
    output := output.join (Flow.ofNormal anyV state)
  pure output

partial def v2IterationServices : RuleDriven.Iteration.Services :=
  {
    classInfo := classInfoM
    resolveMethod := resolveMethodM
    invokeUser := v2InvokeUser
    exceptionSubclass := excCaughtM
    hashKey := v2HashKey
    equalKeys := v2EqualKeys
    checkAnnotation := v2CheckAnnotationLabelled
  }

partial def v2ContractServices : RuleDriven.Contracts.Services :=
  RuleDriven.Iteration.install
    {
      classInfo := classInfoM
      resolveMethod := resolveMethodM
      invokeUser := v2InvokeUser
      unknownProtocol := v2UnknownProtocol
      truthValue := v2TruthValue
      consumeElements := fun _ value _ state =>
        pure (Flow.ofNormal value state)
      invokeCallable := v2InvokeCallable
      consumeMappingPairs := fun _ _ state =>
        pure (Flow.ofNormal anyV state)
      recursiveAnnotation := v2CheckAnnotation
    }
    v2IterationServices

partial def evalTruthFlow (expression : Expr) (value : AbsVal)
    (state : AState) : M RuleDriven.TruthFlow :=
  RuleDriven.Expressions.truth v2ExpressionServices expression.pos value state

partial def requireHashableFlow (position : Pos) (value : AbsVal)
    (state : AState) : M Flow := do
  checkHashable position value
  pure (Flow.ofNormal value state)

partial def deleteTargetFlow (target : Target)
    (state : AState) : M Flow := do
  match target with
  | .tname _ name =>
    pure (Flow.ofNormal (V [.tnone]) (state.envKill name))
  | .tattr position _ field =>
    oblige position "shape-break"
      s!"deleting attribute {field} would invalidate the admitted object shape"
    pure (Flow.ofNormal (V [.tnone]) state)
  | .tsub position _ _ =>
    oblige position "shape-break"
      "deleting a subscript requires the collection-specific shape rule"
    pure (Flow.ofNormal (V [.tnone]) state)
  | .ttuple position _ =>
    oblige position "shape-break"
      "tuple deletion target is outside the subset"
    pure (Flow.ofNormal (V [.tnone]) state)

partial def executeTargetFlow (action : RuleDriven.Statements.TargetAction)
    (state : AState) : M Flow :=
  match action with
  | .bind target value =>
    RuleDriven.StructuralExpressions.bindTarget v2StructuralServices target value
      state
  | .delete target =>
    deleteTargetFlow target state

partial def v2FixpointServices : RuleDriven.Fixpoint.Services :=
  {
    evalExpr := evalExprFlow
    -- A builtin container stands in for its own iterator: its `.elem` cell
    -- already holds the element summary, which is what `forFixpoint` reads.
    --
    -- An instance does not have that cell, and passing one through unchanged
    -- made `elemOf` bottom, which `forFixpoint` reads as an already-exhausted
    -- iterator. So a `for` or comprehension over a class with `__iter__` or
    -- `__getitem__` ran zero times, silently: no obligation, no raise, and the
    -- body never analysed, which discharges every obligation inside it
    -- vacuously. Instances go through the same protocol as an explicit
    -- `iter(...)`, which allocates an iterator whose element is the one
    -- `__iter__` yields, or `any` for the `__getitem__` sequence fallback.
    iterate := fun position value state => do
      let objectTags := value.tags.filter fun tag =>
        match tag with | .tobj _ => true | _ => false
      if objectTags.isEmpty then
        pure (Flow.ofNormal value state)
      else
        let others := value.withoutTags objectTags
        let mut result : Flow :=
          if others.isBot then {} else Flow.ofNormal others state
        result := result.join
          (← RuleDriven.Protocols.iter v2ProtocolServices position
            [value.restrictTags objectTags] [] state)
        pure result
    truth := evalTruthFlow
    refine := RuleDriven.Fixpoint.refineTruthWith refine
    bindTarget := fun target value state =>
      RuleDriven.StructuralExpressions.bindTarget v2StructuralServices target value
        state
    executeBody := fun statements state =>
      RuleDriven.Statements.executeBody v2StatementServices statements state
    requireHashable := requireHashableFlow
    generatorExceptions := genExcOf
  }

partial def executeLoopV2 (spec : RuleDriven.Statements.LoopSpec)
    (state : AState) : M AMulti := do
  let completion <- match spec with
    | .whileLoop position condition body elseBody =>
      RuleDriven.Fixpoint.whileFixpoint v2FixpointServices
        { position, condition, body, elseBody } state
    | .forLoop position target iterable body elseBody =>
      let services := {
        v2FixpointServices with
        bindTarget := fun target value state =>
          RuleDriven.StructuralExpressions.bindTarget v2StructuralServices target
            { value with witness := false } state
      }
      RuleDriven.Fixpoint.forFixpoint services
        { position, target, iterable, body, elseBody } state
  pure (RuleDriven.Compatibility.aMultiOfCompletion completion)

partial def v2StatementServices : RuleDriven.Statements.Services :=
  {
    evalExpr := evalExprFlow
    truth := evalTruthFlow
    refine := refine
    executeTarget := executeTargetFlow
    constructException := fun request state =>
      RuleDriven.Calls.constructClass v2CallServices request.position
        request.className request.arguments [] state
    executeLoop := executeLoopV2
  }

/-- The name read, as a service the `readName` plan effect calls. Extracted from
    the hand-written arm unchanged, so the routed and unrouted paths cannot
    disagree about which of `NameError` and `UnboundLocalError` a scope raises. -/
partial def nameReadFlow (p : Pos) (x : String) (st : AState) : M Flow := do
  let c ← get
  let isLocal := (c.localScopes.headD []).contains x
  let v ← if isLocal then pure (st.envGet x) else readName st x
  if v.tags == [Tag.tunbound] then
    oblige p "definitely-unbound" s!"read of {x}: no binding reaches this point"
    let cls := if isLocal then "UnboundLocalError" else "NameError"
    resCase p "name" s!"read {x}" "unbound" s!"!{cls}"
    pure (Flow.of (AbsVal.bot) (st) ((← mraise p {} st [cls])))
  else if Tag.tunbound ∈ v.tags then
    oblige p "maybe-unbound" s!"read of {x}: unbound on some path"
    let normal := v.withoutTags [Tag.tunbound]
    let cls := if isLocal then "UnboundLocalError" else "NameError"
    resCase p "name" s!"read {x}" "unbound" s!"!{cls}"
    pure (Flow.of (normal) (st.envSet x normal) ((← mraise p {} st [cls])))
  else
    pure (Flow.of (v) (st) ({}))

partial def evalExprFlow (expression : Expr)
    (state : AState) : M Flow := do
  match <- syntaxDispatch? expression state with
  | some flow => pure flow
  | none =>
  match expression with
  | .comp position kind element value target iterable filters =>
    let form : RuleDriven.Fixpoint.ComprehensionForm := match kind with
      | .clist => .list element
      | .cset => .set element
      | .cdict => .dict element (value.getD element)
      | .cgen => .generator element
    let result <- RuleDriven.Fixpoint.comprehension v2FixpointServices
      { position, form, target, iterable, filters } state
    modify fun after => {
      after with
      obligations := match kind with
        | .cgen =>
          after.obligations.filter fun obligation =>
            obligation.node != position.id ||
              obligation.kind != "special-method"
        | _ => after.obligations
    }
    pure result
  | _ =>
    match <- RuleDriven.StructuralExpressions.evaluate? v2StructuralServices
        expression state with
    | some result => pure result
    | none =>
      pure ((<- evalExprCore expression state))

/-- Execute a syntax node through its structural plan, when the table has one.

    This is the routing section 1 asks for: the plan states which children to
    evaluate and in what order, and `executeChildren` supplies the ordering and
    abandon-on-exception, so the arm below is not consulted for a routed kind.
    `evalSubterm` is this interpreter's own expression evaluator, which is what
    closes the recursion without the plan knowing anything about it. -/
partial def syntaxDispatch? (expression : Expr) (state : AState) :
    M (Option Flow) := do
  match RuleDriven.Syntax.compiledSyntaxRules? with
  | none => pure none
  | some table =>
    match RuleDriven.CompiledRules.find? table (.expr (RuleDriven.ExprKind.of expression)) with
    | none => pure none
    | some rule =>
      -- A declared engine body defers to the hand-written transfer by design
      -- (a declared engine escape). Checked explicitly rather than relying on `framesOf`
      -- happening to decline for these nodes.
      match rule.body with
      | .engine _ => pure none
      | _ =>
      match RuleDriven.Syntax.framesOf expression with
      | none => pure none
      | some frame =>
        let services : RuleDriven.Services := {
          invoke := fun callPos operation receiver arguments keywords st => do
            match operation, receiver with
            | .binary op, _ =>
              -- The plan has already evaluated both operands, so this is the
              -- value-level transfer, not the operand-evaluating one.
              let left := arguments.headD AbsVal.bot
              let right := (arguments.drop 1).headD AbsVal.bot
              RuleDriven.Expressions.binary v2ExpressionServices callPos op left right st
            | .attributeRead field, some target =>
              -- The receiver's syntax narrows the exceptional edge, and the
              -- dispatcher still derives it from the node rather than reading it
              -- from the frame: that is debt one, unpaid.
              let receiverExpr := match expression with
                | .attr _ receiver _ => some receiver
                | _ => none
              RuleDriven.Objects.attributeRead { invokeUser := v2InvokeUser } callPos
                target field st receiverExpr
            | .compare op, _ =>
              let left := arguments.headD AbsVal.bot
              let right := (arguments.drop 1).headD AbsVal.bot
              RuleDriven.Expressions.comparison v2ExpressionServices callPos op left
                right st (exprText expression)
            | .membership negated, _ =>
              let element := arguments.headD AbsVal.bot
              let container := (arguments.drop 1).headD AbsVal.bot
              RuleDriven.Expressions.membership v2ExpressionServices callPos negated
                element container st
            | .unary op, _ =>
              RuleDriven.Expressions.unaryOp v2ExpressionServices op callPos
                (arguments.headD AbsVal.bot) st
            | .itemReadAt literalKey literalIndex, some target =>
              -- The literal travels with the operation, resolved from the frame,
              -- so this reads what the node knows instead of re-deriving it.
              let index := arguments.headD AbsVal.bot
              let itemFlow <- RuleDriven.Objects.itemRead { invokeUser := v2InvokeUser }
                callPos target index literalKey literalIndex st
              -- The item protocol reports what escapes it, as the hand-written
              -- `subscrRead` did. The operator transfers do not, because a
              -- failure raised while evaluating an operand is the operand's
              -- outcome and not the operator's.
              reportEscapes callPos "getitem" "[..]" "code" itemFlow
              pure itemFlow
            | _, _ =>
              RuleDriven.Services.opaque.invoke callPos operation receiver arguments
                keywords st
          truth := fun truthPos value st =>
            RuleDriven.Expressions.truth v2ExpressionServices truthPos value st
          evalSubterm := fun _ subterm st =>
            match subterm with
            | .expr child => evalExpr child st
            | _ => pure (Flow.ofNormal anyV st)
          truthSubterm := fun _ subterm value st =>
            match subterm with
            | .expr child => evalTruthFlow child value st
            | _ => pure { truthy := some (value, st), falsy := some (value, st) }
          refineSubterm := fun _ subterm st =>
            match subterm with
            | .expr child => refine child st
            | _ => pure (some st, some st)
          recordObligation := fun obligePos kind detail =>
            oblige obligePos kind detail
          readNameValue := fun namePos x st => nameReadFlow namePos x st
          engineTransfer := fun enginePos name _ _ => do
            oblige enginePos "engine-transfer-missing"
              s!"no engine transfer installed for {name}"
            pure {} }
        let planned <- RuleDriven.executePlan services expression.pos rule.body frame state
        -- An expression rule cannot finish by returning, breaking or continuing;
        -- if one does, the plan is wrong and the page must not quietly drop it.
        if planned.returned.isSome || planned.broke.isSome
            || planned.continued.isSome then
          oblige expression.pos "statement-completion-in-expression"
            s!"{(RuleDriven.ExprKind.of expression).render} plan produced a statement completion"
        let flow := planned.flow
        -- The bookkeeping the hand-written arms did: the page still needs the
        -- node's source text, its result, and the state it fired in.
        resExpr expression.pos (exprText expression)
        resResult expression.pos flow.val
        resAt expression.pos state
        pure (some flow)

/-- A thin alias. The structural-plan dispatch lives in `evalExprFlow`, because
    every `Services.evalExpr` binds that directly: a dispatch installed only here
    is reached from almost nowhere. -/
partial def evalExpr (expression : Expr) (state : AState) : M Flow :=
  evalExprFlow expression state

partial def evalExprCore (e : Expr) (st : AState) : M Flow := do
  match e with
  -- Routed through the structural-plan table (`RuleSyntax`), so `evalExprFlow`
  -- returns before reaching here. The arm survives only to keep the match total
  -- and to fail closed: a missing plan yields an obligation and no value, not a
  -- silent fallback to a second implementation of the same node.
  | .const .. | .name .. | .binop .. | .cmp .. | .notE .. | .unary .. | .attr ..
  | .subscr .. | .listlit .. | .tuplelit .. | .setlit .. | .dictlit ..
  | .ifexp .. | .fstr .. => do
    oblige e.pos "syntax-rule-missing"
      s!"{(RuleDriven.ExprKind.of e).render} is routed but its plan was not found"
    pure {}
  | .boolop _ isAnd vals => evalBoolop isAnd vals st
  | .call p f args kws => evalCall p f args kws st
  | .comp p kind elt eltVal var iter conds => do
    let ri ← evalExpr iter st
    if !ri.hasNormal then return ri
    let saved := (ri.stateOr st).envGet var
    let cls : LocCls := match kind with
      | .clist => .list
      | .cgen => .gen
      | .cset => .set
      | .cdict => .dict
    -- allocate the result before iterating the body so its element edge
    -- lives in the state: allocations inside the element expression then
    -- fold, and the edge covers both the recent block and the summary
    -- (an element built on an earlier concrete iteration is an older
    -- object of its site, and must be reachable through the summary)
    let (v, st0) := allocate (ri.stateOr st) p.id cls []
    let l : Loc := ⟨p.id, cls, true⟩
    let mut inv := st0
    let mut exc := ri.exc
    let mut stable := false
    let mut produced := false
    while !stable do
      let elemv := { elemOf inv ri.val with witness := true }
      let mut selected : Option AState := some (inv.envSet var elemv)
      let mut skipped : Option AState := none
      for cnd in conds do
        match selected with
        | none => pure ()
        | some current =>
          let rc ← evalExpr cnd current
          exc := exc.joinE rc.exc
          if !rc.hasNormal then
            selected := none
          else
            let truth ← evalTruth cnd.pos rc.val (rc.stateOr st)
            exc := exc.joinE truth.exc
            if !truth.hasNormal then
              selected := none
            else
              let (tside, fside) ← refine cnd (truth.stateOr st)
              selected := tside
              skipped := joinOpt skipped fside
      let mut completed := skipped
      match selected with
      | none => pure ()
      | some current =>
        let re ← evalExpr elt current
        exc := exc.joinE re.exc
        if re.hasNormal then
          match kind with
          | .cset =>
            checkHashable p re.val
            produced := true
            completed := joinOpt completed
              (some ((re.stateOr st).heapJoin l .elem re.val))
          | .cdict =>
            checkHashable p re.val
            match eltVal with
            | some ev =>
              let rv ← evalExpr ev (re.stateOr st)
              exc := exc.joinE rv.exc
              if rv.hasNormal then
                produced := true
                completed := joinOpt completed
                  (some (((rv.stateOr st).heapJoin l .dictKeys re.val).heapJoin l .dictValues rv.val))
            | none =>
              produced := true
              completed := joinOpt completed
                (some ((re.stateOr st).heapJoin l .dictKeys re.val))
          | _ =>
            produced := true
            completed := joinOpt completed
              (some ((re.stateOr st).heapJoin l .elem re.val))
      let next := match completed with
        | some done => inv.join done
        | none => inv
      if next.le inv then stable := true else inv := next
    -- the comprehension target does not leak
    let mut st4 := inv.envSet var saved
    if conds.isEmpty && produced && definitelyNonempty ri.val (ri.stateOr st) then
      st4 := strongEmptinessUpdate st4 l .nonempty
    st4 := clearGeneratorNonempty ri.val st4
    pure (Flow.of (v) (st4) (exc))
  | .yieldE _ e => do
    match e with
    | some e => do
      let r ← evalExpr e st
      if !r.hasNormal then return r
      modify fun c => match c.yields with
        | ys :: rest => { c with yields := (r.val :: ys) :: rest }
        | [] => c
      pure (Flow.of (V [.tnone]) ((r.stateOr st)) (r.exc))
    | none => do
      modify fun c => match c.yields with
        | ys :: rest => { c with yields := (V [.tnone] :: ys) :: rest }
        | [] => c
      pure (Flow.of (V [.tnone]) (st) ({}))
  | .yieldFrom _ e => do
    let r ← evalExpr e st
    if !r.hasNormal then return r
    let ev := elemOf (r.stateOr st) r.val
    modify fun c => match c.yields with
      | ys :: rest => { c with yields := (ev :: ys) :: rest }
      | [] => c
    pure (Flow.of (V [.tnone]) ((r.stateOr st)) (r.exc))

partial def evalList (es : List Expr) (st : AState) :
    M (EvalSeq AbsVal) := do
  let mut normal : Option AState := some st
  let mut exc : Exc := {}
  let mut vs : List AbsVal := []
  for e in es do
    match normal with
    | none => pure ()
    | some current =>
      let r ← evalExpr e current
      exc := exc.joinE r.exc
      if r.hasNormal then
        normal := some (r.stateOr st)
        vs := vs ++ [r.val]
      else
        normal := none
  pure ⟨vs, normal, exc⟩

partial def evalTruth (p : Pos) (value : AbsVal) (st : AState) : M Flow := do
  let result ← RuleDriven.Expressions.truth v2ExpressionServices p value st
  let normal := joinOpt (result.truthy.map (·.2)) (result.falsy.map (·.2))
  pure (Flow.of (if normal.isSome then V [.tbool] else AbsVal.bot) (normal.getD st) (result.raised.toExc))

partial def checkHashable (p : Pos) (v : AbsVal) : M Unit := do
  let bad := v.tags.filter (fun t =>
    t == .tlist || t == .tdict || t == .tset)
  if !bad.isEmpty then
    oblige p "hashability"
      s!"unhashable tags {bad.map Tag.render} at a key or element position"

/-- Report a transfer's exceptional outcomes at its own site. Attribution is the
    transfer's business; what must not happen is an outcome no site reports. -/
partial def reportEscapes (p : Pos) (kind desc tag : String)
    (flow : Flow) : M Unit := do
  for raised in flow.raised.cases do
    if raised.from? != .internal then
      resCaseAt p kind desc tag s!"!{raised.cls}"

partial def subscrRead (p : Pos) (recv idx : AbsVal)
    (litKey : Option String) (litIdx : Option Nat) (st : AState) :
    M (AbsVal × AState × Exc) := do
  let services : RuleDriven.Objects.Services := { invokeUser := v2InvokeUser }
  let flow ←
    RuleDriven.Objects.itemRead services p recv idx litKey litIdx st
  reportEscapes p "getitem" "[..]" "code" flow
  pure (flow.val, (flow.stateOr st), flow.exc)

partial def builtinOrderedCmp (left right : Tag) : Bool :=
  let numeric := fun tag =>
    tag == .tbool || tag == .tint || tag == .tfloat
  (numeric left && numeric right) ||
    (left == .tstr && right == .tstr) ||
    (left == .tlist && right == .tlist) ||
    (left == .ttuple && right == .ttuple) ||
    (left == .tset && right == .tset)

partial def evalMembership (p : Pos) (op : CmpOp) (item container : AbsVal)
    (st : AState) (initialExc : Exc) : M Flow := do
  let flow ← RuleDriven.Expressions.membership v2ExpressionServices p
    (op == .notInOp) item container st
  let result := flow
  pure { result with raised := (initialExc : RaisedFlow).join result.raised }

partial def evalBoolop (isAnd : Bool) (vals : List Expr) (st : AState) :
    M Flow := do
  match vals with
  | [] => pure (Flow.of (V [.tbool]) (st) ({}))
  | [e] => evalExpr e st
  | e :: rest => do
    let r ← evalExpr e st
    if !r.hasNormal then return r
    let truth ← evalTruth e.pos r.val (r.stateOr st)
    if !truth.hasNormal then
      return (Flow.of (AbsVal.bot) (st) (r.exc.joinE truth.exc))
    let (ts, fs) ← refine e (truth.stateOr st)
    if isAnd then
      -- rest evaluated when e is truthy
      let mut out := r.val
      let mut outSt := fs
      let mut exc := r.exc.joinE truth.exc
      if let some s := ts then
        let rr ← evalBoolop isAnd rest s
        out := out.join rr.val
        if rr.hasNormal then outSt := joinOpt outSt (some (rr.stateOr st))
        exc := exc.joinE rr.exc
      pure (Flow.of (out.reduce) (outSt.getD (truth.stateOr st)) (exc))
    else
      -- e's truthy part, or rest evaluated on e's falsy side
      let truthy := r.val.withoutTags [.tnone]
      let mut out := truthy
      let mut outSt := ts
      let mut exc := r.exc.joinE truth.exc
      if let some s := fs then
        let rr ← evalBoolop isAnd rest s
        out := out.join rr.val
        if rr.hasNormal then outSt := joinOpt outSt (some (rr.stateOr st))
        exc := exc.joinE rr.exc
      pure (Flow.of (out.reduce) (outSt.getD (truth.stateOr st)) (exc))

-- --------------------------------------------------------------- calls

partial def evalCall (p : Pos) (f : Expr) (args : List Expr)
    (kws : List (String × Expr)) (st : AState) : M Flow := do
  match f with
  | .attr _ recvE m => do
    -- `super().m(..)`, which `Check.lean` lowers to the synthetic receiver
    -- `@super:<Owner>`. Handled before the receiver is evaluated, because there
    -- is no such binding to evaluate: the owner is carried in the name and the
    -- receiver is the enclosing method's `self`.
    if let .name _ syntheticName := recvE then
      if syntheticName.startsWith "@super:" then
        return (← superCall p (syntheticName.drop 7).toString m args kws st)
    let rr ← evalExpr recvE st
    if !rr.hasNormal then return rr
    let argRs ← evalList args (rr.stateOr st)
    let some st1 := argRs.normal
      | return (Flow.of (AbsVal.bot) (st) (rr.exc.joinE argRs.exc))
    let kwRs ← evalKws kws st1
    let some st2 := kwRs.normal
      | return (Flow.of (AbsVal.bot) (st) ((rr.exc.joinE argRs.exc).joinE kwRs.exc))
    let avs := argRs.values
    let kvs := kwRs.values
    let lit := match args with
      | (.const _ (.cstr k)) :: _ => some k
      | _ => none
    let r ← methodCall p rr.val m avs kvs st2
      (rr.exc.joinE (argRs.exc.joinE kwRs.exc)) lit (some recvE)
    resExpr p s!"{exprText recvE}.{m}(..)"
    resResult p r.val
    resAt p st2
    pure r
  | .name np n => do
    let c ← get
    let inEnv := (st.envGet n).tags != [Tag.tunbound]
    let rf ← evalExpr (.name np n) st
    if !rf.hasNormal then return rf
    let argRs ← evalList args (rf.stateOr st)
    let some st1 := argRs.normal
      | return (Flow.of (AbsVal.bot) (st) (rf.exc.joinE argRs.exc))
    let kwRs ← evalKws kws st1
    let some st2 := kwRs.normal
      | return (Flow.of (AbsVal.bot) (st) ((rf.exc.joinE argRs.exc).joinE kwRs.exc))
    let avs := argRs.values
    let kvs := kwRs.values
    let exc0 := (rf.exc.joinE argRs.exc).joinE kwRs.exc
    if !inEnv then
      match c.funcs.find? (·.1 == n) with
      | some (_, fd) =>
        resCase p "call" s!"{n}(..)" "func" n
        let r ← inlineFunc p n fd avs kvs st2
        resResult p r.val
        resAt p st2
        return (Flow.of (r.val) ((r.stateOr st)) (exc0.joinE r.exc))
      | none =>
        if (c.classes.find? (·.1 == n)).isSome then
          -- direct construction: statically resolved, no residual row
          let r ← construct p n avs kvs st2
          return (Flow.of (r.val) ((r.stateOr st)) (exc0.joinE r.exc))
        else if builtinExcs.contains n then
          let r ← construct p n avs kvs st2
          return (Flow.of (r.val) ((r.stateOr st)) (exc0.joinE r.exc))
        else if builtinFuncs.contains n then
          resCase p "call" s!"{n}(..)" "func" s!"builtin {n}"
          let r ← builtinCall p n avs kvs args st2
          resResult p r.val
          resAt p st2
          return (Flow.of (r.val) ((r.stateOr st)) (exc0.joinE r.exc))
        else
          oblige np "definitely-unbound" s!"call of unknown name {n}"
          return (Flow.of (anyV) (st2) (exc0))
    else
      let r ← dispatchValueCall p s!"{n}(..)" rf.val avs kvs st2 exc0
      resResult p r.val
      resAt p st2
      pure r
  | _ => do
    let rf ← evalExpr f st
    if !rf.hasNormal then return rf
    let argRs ← evalList args (rf.stateOr st)
    let some st1 := argRs.normal
      | return (Flow.of (AbsVal.bot) (st) (rf.exc.joinE argRs.exc))
    let kwRs ← evalKws kws st1
    let some st2 := kwRs.normal
      | return (Flow.of (AbsVal.bot) (st) ((rf.exc.joinE argRs.exc).joinE kwRs.exc))
    dispatchValueCall p "(..)(..)" rf.val argRs.values kwRs.values st2
      ((rf.exc.joinE argRs.exc).joinE kwRs.exc)

partial def evalKws (kws : List (String × Expr)) (st : AState) :
    M (EvalSeq (String × AbsVal)) := do
  let mut normal : Option AState := some st
  let mut exc : Exc := {}
  let mut out : List (String × AbsVal) := []
  for (k, e) in kws do
    match normal with
    | none => pure ()
    | some current =>
      let r ← evalExpr e current
      exc := exc.joinE r.exc
      if r.hasNormal then
        normal := some (r.stateOr st)
        out := out ++ [(k, r.val)]
      else
        normal := none
  pure ⟨out, normal, exc⟩

/-- Call through a first-class value: functions, classes, unknowns.
    Each live case runs from the same incoming state; results join. -/
partial def dispatchValueCall (p : Pos) (desc : String) (fv : AbsVal)
    (avs : List AbsVal) (kvs : List (String × AbsVal)) (st : AState)
    (exc0 : Exc) : M Flow := do
  let flow <- RuleDriven.Calls.invokeValue v2CallServices p desc fv avs kvs st
  for raised in flow.raised.cases do
    resCaseAt p "call" desc "code" s!"!{raised.cls}"
  pure { flow with raised := (exc0 : RaisedFlow).join flow.raised }

partial def fallbackMethodCall (p : Pos) (recv : AbsVal) (m : String)
    (avs : List AbsVal) (kvs : List (String × AbsVal)) (st : AState)
    (exc0 : Exc) (litKey : Option String := none)
    (recvExpr : Option Expr := none) : M Flow := do
  let c ← get
  let desc := s!".{m}(..)"
  let mut out : AbsVal := AbsVal.bot
  let mut outSt : Option AState := none
  let mut exc := exc0
  for t in recv.tags do
    match t with
    | .tobj cn =>
      let ci? := c.classes.find? (·.1 == cn)
      let layout := (ci?.map (·.2.layout)).getD []
      if layout.contains m then
        -- field shadows method: calling a stored value
        resCase p "call" desc (Tag.render t) "field"
        oblige p "dispatch-any" s!"call of instance field {cn}.{m}"
        out := out.join anyV
        outSt := joinOpt outSt (some st)
      else
        match ← resolveMethodM cn m with
        | some (d, fd) =>
          resCase p "call" desc (Tag.render t) s!"{d}.{m}"
          let r ← inlineFunc p s!"{d}.{m}" fd
            ((recv.restrictTags [t]) :: avs) kvs st
          out := out.join r.val
          if r.hasNormal then outSt := joinOpt outSt (some (r.stateOr st))
          exc := exc.joinE r.exc
        | none =>
          resCase p "call" desc (Tag.render t) "!AttributeError"
          -- Only this tag can reach the handler, so the edge carries the state
          -- narrowed to it. The success edge already restricts the receiver the
          -- same way when it inlines; this is the failure edge catching up.
          exc ← mraise p exc
            (narrowReceiverExpr recvExpr (recv.restrictTags [t]) st)
            ["AttributeError"]
    | .tlist | .tdict | .tset | .tstr | .tbytes | .ttuple | .trange
    | .tgen =>
      let r ← builtinMethod p t recv m avs kvs litKey st
      match r with
      | some r =>
        resCase p "call" desc (Tag.render t) s!"builtin {Tag.render t}.{m}"
        out := out.join r.val
        if r.hasNormal then outSt := joinOpt outSt (some (r.stateOr st))
        exc := exc.joinE r.exc
      | none =>
        if (knownMethods t).contains m then
          resCase p "call" desc (Tag.render t) s!"builtin {Tag.render t}.{m} (opaque)"
          oblige p "external-havoc"
            s!"builtin {Tag.render t}.{m} is real but not modeled: result widened, receiver havocked"
          let st' ← havocReachable p (recv :: avs) st
          out := out.join anyV
          outSt := joinOpt outSt (some st')
        else
          resCase p "call" desc (Tag.render t) "!AttributeError"
          exc ← mraise p exc st ["AttributeError"]
    | .tany =>
      resCase p "call" desc "any" "deferred"
      oblige p "dispatch-any" s!"method .{m} on an unknown value"
      out := out.join anyV
      outSt := joinOpt outSt (some st)
    | .tnone =>
      resCase p "call" desc "none" "!AttributeError"
      exc ← mraise p exc st ["AttributeError"]
    | .tunbound | .tuninit => pure ()
    | _ =>
      resCase p "call" desc (Tag.render t) "!AttributeError"
      exc ← mraise p exc st ["AttributeError"]
  pure (Flow.of (out.reduce) (outSt.getD st) (exc))

/-- A zero-argument `super().m(..)` inside a method of `owner`.

    The receiver is the enclosing method's `self`, and resolution runs per
    receiver tag against `resolveMethodAfter`, so a cooperative diamond gets the
    arm CPython would take rather than `owner`'s own base. One arm per candidate
    class, like every other dispatch site.

    Falling off the end of the chain means `object` is next. `object.__init__` is
    a no-op accepting no arguments, which is the one case that completes
    normally; anything else there is an `AttributeError`. -/
partial def superCall (p : Pos) (owner m : String) (args : List Expr)
    (kws : List (String × Expr)) (st : AState) : M Flow := do
  let recv := st.envGet "self"
  let argRs ← evalList args st
  let some st1 := argRs.normal
    | return (Flow.of AbsVal.bot st argRs.exc)
  let kwRs ← evalKws kws st1
  let some st2 := kwRs.normal
    | return (Flow.of AbsVal.bot st (argRs.exc.joinE kwRs.exc))
  let avs := argRs.values
  let kvs := kwRs.values
  let desc := s!"super().{m}(..)"
  let mut out : AbsVal := AbsVal.bot
  let mut outSt : Option AState := none
  let mut exc := argRs.exc.joinE kwRs.exc
  for t in recv.tags do
    match t with
    | .tobj cn =>
      match ← resolveMethodAfterM cn owner m with
      | some (d, fd) =>
        resCase p "call" desc (Tag.render t) s!"{d}.{m} after {owner}"
        let r ← inlineFunc p s!"{d}.{m}" fd
          ((recv.restrictTags [t]) :: avs) kvs st2
        out := out.join r.val
        if r.hasNormal then outSt := joinOpt outSt (some (r.stateOr st2))
        exc := exc.joinE r.exc
      | none =>
        if m == "__init__" && avs.isEmpty && kvs.isEmpty then
          resCase p "call" desc (Tag.render t) "object.__init__ (inert)"
          out := out.join (V [.tnone])
          outSt := joinOpt outSt (some st2)
        else
          resCase p "call" desc (Tag.render t) "!AttributeError"
          exc ← mraise p exc st2 ["AttributeError"]
    | .tunbound | .tuninit => pure ()
    | _ =>
      resCase p "call" desc (Tag.render t) "!AttributeError"
      exc ← mraise p exc st2 ["AttributeError"]
  resExpr p desc
  resResult p out
  resAt p st2
  pure (Flow.of (out.reduce) (outSt.getD st2) exc)

partial def methodCall (p : Pos) (recv : AbsVal) (m : String)
    (avs : List AbsVal) (kvs : List (String × AbsVal)) (st : AState)
    (exc0 : Exc) (litKey : Option String := none)
    (recvExpr : Option Expr := none) : M Flow := do
  let rules := RuleProvider.compiledRules
  let hasMigratedRule := recv.tags.any fun tag =>
    (RuleDriven.CompiledRules.find? rules (.method tag m)).isSome
  if !hasMigratedRule then
    fallbackMethodCall p recv m avs kvs st exc0 litKey recvExpr
  else
    let desc := s!".{m}(..)"
    for tag in recv.tags do
      if let some rule := RuleDriven.CompiledRules.find? rules (.method tag m) then
        let suffix := if rule.isOpaque then " (opaque)" else ""
        resCase p "call" desc tag.render s!"builtin {tag.render}.{m}{suffix}"
    let fallback : RuleDriven.Services := {
      invoke := fun callPos operation receiver arguments keywords state => do
        match operation, receiver with
        | .method name, some target =>
          let result ← fallbackMethodCall callPos target name arguments
            keywords state {} litKey
          pure (result)
        | .dictMethod method, some target =>
          RuleDriven.Dict.execute callPos method target arguments keywords litKey state
        | .opaqueBuiltinMethod method, some target =>
          RuleDriven.Opaque.execute callPos method target arguments state
        | _, _ =>
          RuleDriven.Services.opaque.invoke callPos operation receiver arguments
            keywords state
      truth := RuleDriven.Services.opaque.truth
      applyContracts := RuleDriven.Contracts.applyContracts v2ContractServices
    }
    let services := RuleDriven.CompiledRules.services rules fallback
    let flow ← services.invoke p (.method m) (some recv) avs kvs st
    let result := flow
    pure { result with raised := (exc0 : RaisedFlow).join result.raised }

/-- The fifth copy of this predicate, now delegating to the one definition in
    `Cells/State.lean`. Still a `partial def` rather than an `abbrev` because it
    sits inside this file's mutual recursion group, which cannot mix the two. -/
partial def isSoleRecentTarget (recv : AbsVal) (l : Loc) : Bool :=
  strongUpdateTarget recv l

partial def soleRecent (recv : AbsVal) (cls : LocCls) : Option Loc :=
  match recv.locs with
  | [l] => if l.cls == cls && isSoleRecentTarget recv l then some l else none
  | _ => none

/-- One definition, in `Machine.lean`. Still a `partial def` rather than an
    abbreviation because it sits inside this file's mutual recursion group. -/
partial def updateTypedDictField (p : Pos) (recv : AbsVal) (l : Loc)
    (tn k : String) (ci : ClassInfo) (value : AbsVal) (definite : Bool)
    (st : AState) : M AState :=
  Pylate.updateTypedDictField .update p recv l tn k ci value definite st

partial def builtinMethod (p : Pos) (t : Tag) (recv : AbsVal) (m : String)
    (avs : List AbsVal) (kvs : List (String × AbsVal))
    (litKey : Option String) (st : AState) :
    M (Option Flow) := do
  let c ← get
  let arg0 := avs.headD AbsVal.bot
  let elemJoin := fun (cls : LocCls) (edge : CellSelector) (v : AbsVal)
      (st : AState) => Id.run do
    let mut st := st
    for l in recv.locs do
      if l.cls == cls then st := st.heapJoin l edge v
    return st
  let edgeRead := fun (cls : LocCls) (edge : CellSelector) (st : AState) =>
    Id.run do
      let mut v : AbsVal := AbsVal.bot
      for l in recv.locs do
        if l.cls == cls || (cls == LocCls.dict && l.cls.tag == .tdict) then
          v := v.join (st.heapGet l edge)
      return v
  let edgeRead' := fun (v : AbsVal) (edge : CellSelector) (st : AState) =>
    Id.run do
      let mut out : AbsVal := AbsVal.bot
      for l in v.locs do
        if l.cls.tag == .tdict then out := out.join (st.heapGet l edge)
      return out
  let freshList := fun (ev : AbsVal) (st : AState) =>
    let (lv, st') := allocate st p.id .list []
    (lv, st'.heapSet ⟨p.id, .list, true⟩ .elem ev)
  let freshView := fun (cls : LocCls) (ev : AbsVal) (st : AState) =>
    let (vv, st') := allocate st p.id cls []
    (vv, st'.heapSet ⟨p.id, cls, true⟩ .elem ev)
  match t, m with
  | .tlist, "append" | .tlist, "insert" =>
    let v := if m == "insert" then avs[1]?.getD AbsVal.bot else arg0
    pure (some (Flow.of (V [.tnone]) (elemJoin .list .elem v st) ({})))
  | .tlist, "extend" =>
    pure (some (Flow.of (V [.tnone]) (elemJoin .list .elem (elemOf st arg0) st) ({})))
  | .tlist, "pop" =>
    pure (some (Flow.of (elemOf st recv) (st) ((← mraise p {} st ["IndexError"]))))
  | .tlist, "remove" =>
    pure (some (Flow.of (V [.tnone]) (st) ((← mraise p {} st ["ValueError"]))))
  | .tlist, "clear" | .tset, "clear" =>
    -- count 1 and all elements touched: the one strong element update
    let cls : LocCls := if t == .tlist then .list
      else .set
    let st := match soleRecent recv cls with
      | some l =>
        st.heapSet l .elem AbsVal.bot
      | none => st
    pure (some (Flow.of (V [.tnone]) (st) ({})))
  | .tlist, "copy" =>
    let (lv, st') := freshList (elemOf st recv) st
    pure (some (Flow.of (lv) (st') ({})))
  | .tlist, "count" | .ttuple, "count" | .tstr, "count"
  | .trange, "count" =>
    pure (some (Flow.of (V [.tint]) (st) ({})))
  | .tlist, "index" | .ttuple, "index" | .trange, "index" =>
    pure (some (Flow.of (V [.tint]) (st) ((← mraise p {} st ["ValueError"]))))
  | .tlist, "sort" | .tlist, "reverse" =>
    pure (some (Flow.of (V [.tnone]) (st) ({})))
  | .tset, "add" =>
    checkHashable p arg0
    pure (some (Flow.of (V [.tnone]) (elemJoin .set .elem arg0 st) ({})))
  | .tset, "discard" =>
    pure (some (Flow.of (V [.tnone]) (st) ({})))
  | .tset, "remove" | .tset, "pop" =>
    let exc ← mraise p {} st ["KeyError"]
    pure (some (Flow.of (if m == "pop" then elemOf st recv else V [.tnone]) (st) (exc)))
  | .tset, "union" | .tset, "intersection" | .tset, "difference"
  | .tset, "symmetric_difference" | .tset, "copy" =>
    let (v, st') := allocate st p.id .set []
    let ev := (elemOf st recv).join (elemOf st arg0)
    pure (some (Flow.of (v) (st'.heapSet ⟨p.id, .set, true⟩ .elem ev) ({})))
  | .tset, "update" =>
    pure (some (Flow.of (V [.tnone]) (elemJoin .set .elem (elemOf st arg0) st) ({})))
  | .tset, "issubset" | .tset, "issuperset" | .tset, "isdisjoint" =>
    pure (some (Flow.of (V [.tbool]) (st) ({})))
  | .tdict, "get" =>
    let dflt := avs[1]?.getD (V [.tnone])
    let mut v : AbsVal := AbsVal.bot
    let mut exc : Exc := {}
    let keys := keyCases arg0
    for l in recv.locs do
      match l.cls with
      | .td tn =>
        match c.classes.getCls? tn with
        | some ci =>
          for k in keys.literals do
            match ci.fields.find? (·.name == k) with
            | some _ =>
              let fv := st.heapGet l (.literalKey k)
              v := v.join (fv.withoutTags [.tmissing])
              if Tag.tmissing ∈ fv.tags then v := v.join dflt
            | none => v := v.join dflt
          if keys.openString || keys.userEquality then
            if keys.userEquality then
              oblige p "special-method"
                s!"key equality/hash against TypedDict {tn} succeeds without side effects"
            v := v.join (typedDictValues ci l st) |>.join dflt
          if keys.absent then v := v.join dflt
          if keys.unhashable then
            exc ← mraise p exc st ["TypeError"]
          if keys.unknown then
            oblige p "dispatch-any" s!"unknown key passed to {tn}.get"
            v := v.join anyV
            exc ← mraise p exc st ["TypeError"]
        | none => v := v.join (st.heapGet l .dictValues)
      | .dict =>
        v := v.join (st.heapGet l .dictValues) |>.join dflt
        if keys.unhashable || keys.unknown then
          exc ← mraise p exc st ["TypeError"]
      | _ => pure ()
    pure (some (Flow.of (v.reduce) (st) (exc)))
  | .tdict, "pop" =>
    let mut v : AbsVal := AbsVal.bot
    let mut exc : Exc := {}
    let mut st := st
    let dflt? := avs[1]?
    let keys := keyCases arg0
    for l in recv.locs do
      match l.cls with
      | .td tn =>
        match c.classes.getCls? tn with
        | some ci =>
          for k in keys.literals do
            match ci.fields.find? (·.name == k) with
            | some field =>
              let fv := st.heapGet l (.literalKey k)
              v := v.join (fv.withoutTags [.tmissing])
              if let some detail := shapeObligation .pop tn field then
                oblige p "shape-break" detail
              else
                let sole := isSoleRecentTarget recv l
                let missing := V [.tmissing]
                st := if sole then st.heapSet l (.literalKey k) missing
                  else st.heapJoin l (.literalKey k) missing
              if Tag.tmissing ∈ fv.tags then
                match dflt? with
                | some d => v := v.join d
                | none => exc ← mraise p exc st ["KeyError"]
            | none =>
              match dflt? with
              | some d => v := v.join d
              | none => exc ← mraise p exc st ["KeyError"]
          if keys.openString || keys.userEquality || keys.unknown then
            if let some detail := unresolvedKeyObligation .pop tn then
              oblige p "shape-break" detail
            v := v.join (typedDictValues ci l st)
            match dflt? with
            | some d => v := v.join d
            | none => exc ← mraise p exc st ["KeyError"]
        | none => v := v.join (st.heapGet l .dictValues)
      | .dict =>
        v := v.join (st.heapGet l .dictValues)
        match dflt? with
        | some d => v := v.join d
        | none => exc ← mraise p exc st ["KeyError"]
      | _ => pure ()
    if keys.absent then
      match dflt? with
      | some d => v := v.join d
      | none => exc ← mraise p exc st ["KeyError"]
    if keys.unhashable || keys.unknown then
      exc ← mraise p exc st ["TypeError"]
    pure (some (Flow.of (v.reduce) (st) (exc)))
  | .tdict, "keys" | .tdict, "values" =>
    let mut elems : AbsVal := AbsVal.bot
    for l in recv.locs do
      match l.cls with
      | .td tn =>
        match c.classes.getCls? tn with
        | some ci =>
          elems := elems.join (if m == "keys" then typedDictKeys ci
            else typedDictValues ci l st)
        | none => elems := elems.join (st.heapGet l (if m == "keys" then .dictKeys else .dictValues))
      | .dict =>
        elems := elems.join (st.heapGet l (if m == "keys" then .dictKeys else .dictValues))
      | _ => pure ()
    let cls := if m == "keys" then LocCls.dictkeys else LocCls.dictvalues
    let (vv, st') := freshView cls elems st
    pure (some (Flow.of (vv) (st') ({})))
  | .tdict, "items" =>
    let (tv, st1) := allocate st p.id .tuple []
    let tl : Loc := ⟨p.id, .tuple, true⟩
    let mut keyV : AbsVal := AbsVal.bot
    let mut valV : AbsVal := AbsVal.bot
    for l in recv.locs do
      match l.cls with
      | .td tn =>
        match c.classes.getCls? tn with
        | some ci =>
          keyV := keyV.join (typedDictKeys ci)
          valV := valV.join (typedDictValues ci l st)
        | none => pure ()
      | .dict =>
        keyV := keyV.join (st.heapGet l .dictKeys)
        valV := valV.join (st.heapGet l .dictValues)
      | _ => pure ()
    let st1 := ((st1.heapSet tl (.tupleSlot 0) keyV).heapSet tl (.tupleSlot 1) valV)
      |>.heapSet tl .elem (keyV.join valV)
    let (vv, st2) := freshView .dictitems tv st1
    pure (some (Flow.of (vv) (st2) ({})))
  | .tdict, "setdefault" =>
    let dflt := avs[1]?.getD (V [.tnone])
    checkHashable p arg0
    let mut st := st
    let mut out : AbsVal := AbsVal.bot
    for l in recv.locs do
      match l.cls, litKey, c.classes.getCls? (match l.cls with
        | .td tn => tn | _ => "") with
      | .td tn, some k, some ci =>
        match ci.fields.find? (·.name == k) with
        | some field =>
          -- Behaviour preserved: unlike the transfer this arm has no
          -- may-insert guard, so it obliges whenever the field is read-only even
          -- when the key is definitely present and `setdefault` would not write.
          -- That is imprecise in the safe direction. Aligning it is a behaviour
          -- change and is tracked separately, so it is not folded into this
          -- table wiring -- zero drift is what makes the wiring checkable.
          if let some detail := shapeObligation .setDefault tn field then
            oblige p "shape-break" detail
          if let some a := field.ann then
            if !annEntailedDeep 16 c.classes st dflt a then
              oblige p "type-error"
                s!"{tn}.{k}: setdefault does not satisfy the declared type"
          let fv := st.heapGet l (.literalKey k)
          let present := fv.withoutTags [.tmissing]
          let inserted := match field.ann with
            | some a => assumeAnn c.classes dflt a
            | none => dflt
          let result := if Tag.tmissing ∈ fv.tags
            then present.join inserted else present
          st := if isSoleRecentTarget recv l then
              st.heapSet l (.literalKey k) result
            else
              st.heapJoin l (.literalKey k) result
          st := st.heapJoin l .dictValues result
          out := out.join result
        | none =>
          if let some detail := undeclaredKeyObligation .setDefault tn k then
            oblige p "shape-break" detail
          out := out.join dflt
      | .td tn, none, _ =>
        oblige p "key-membership"
          s!"dynamic setdefault key on TypedDict {tn}"
        out := out.join ((st.heapGet l .dictValues).withoutTags [.tmissing])
          |>.join dflt
      | .dict, _, _ =>
        st := (st.heapJoin l .dictKeys arg0).heapJoin l .dictValues dflt
        out := out.join (st.heapGet l .dictValues)
      | _, _, _ => pure ()
    pure (some (Flow.of (out.reduce) (st) ({})))
  | .tdict, "update" =>
    let inputSt := st
    let mut st := elemJoin .dict .dictKeys (edgeRead' arg0 .dictKeys inputSt)
      (elemJoin .dict .dictValues (edgeRead' arg0 .dictValues inputSt) inputSt)
    for l in recv.locs do
      if let .td tn := l.cls then
        match c.classes.getCls? tn with
        | some ci =>
          for (k, value) in kvs do
            st ← updateTypedDictField p recv l tn k ci value true st
          for source in arg0.locs do
            match source.cls with
            | .td sourceName =>
              match c.classes.getCls? sourceName with
              | some sourceInfo =>
                for sourceField in sourceInfo.fields do
                  let value := (inputSt.heapGet source (.literalKey sourceField.name)).withoutTags [.tmissing]
                  if !value.isBot then
                    st ← updateTypedDictField p recv l tn sourceField.name
                      ci value false st
              | none => pure ()
            | .dict =>
              let keys := keyCases (inputSt.heapGet source .dictKeys)
              for k in keys.literals do
                let exact := inputSt.heapGet source (.literalKey k)
                let value := if exact.isBot then
                    inputSt.heapGet source .dictValues
                  else exact
                st ← updateTypedDictField p recv l tn k ci value false st
              if keys.openString || keys.userEquality || keys.unknown then
                oblige p "key-membership"
                  s!"dynamic mapping update on TypedDict {tn} uses declared keys"
                let value := inputSt.heapGet source .dictValues
                for field in ci.fields do
                  st ← updateTypedDictField p recv l tn field.name ci value
                    false st
              if keys.absent || keys.unhashable then
                if let some detail := unresolvedKeyObligation .update tn then
                  oblige p "shape-break" detail
            | _ => pure ()
          if arg0.tags.any (· != Tag.tdict) then
            oblige p "dispatch-any"
              s!"non-dictionary update source for TypedDict {tn} is widened"
            for field in ci.fields do
              st ← updateTypedDictField p recv l tn field.name ci anyV false st
        | none => pure ()
    pure (some (Flow.of (V [.tnone]) (st) ({})))
  | .tdict, "copy" =>
    let mut out : AbsVal := AbsVal.bot
    let mut outSt := st
    let mut seen : Fset LocCls := []
    for src in recv.locs do
      if src.cls.tag == .tdict && !(src.cls ∈ seen) then
        seen := Fset.insert src.cls seen
        match src.cls with
        | .td tn =>
          let (v, st') := allocate outSt p.id (.td tn) []
          out := out.join v
          outSt := st'
          let dst : Loc := ⟨p.id, .td tn, true⟩
          match c.classes.getCls? tn with
          | some ci =>
            for field in ci.fields do
              let mut fv : AbsVal := AbsVal.bot
              for source in recv.locs do
                if source.cls == LocCls.td tn then
                  fv := fv.join (st.heapGet source (.literalKey field.name))
              outSt := outSt.heapSet dst (.literalKey field.name) fv
            outSt := (outSt.heapSet dst .dictKeys (typedDictKeys ci)).heapSet dst .dictValues (typedDictValues ci dst outSt)
          | none => pure ()
        | .dict =>
          let (v, st') := allocate outSt p.id .dict []
          out := out.join v
          let dst : Loc := ⟨p.id, .dict, true⟩
          outSt := (st'.heapSet dst .dictKeys (edgeRead .dict .dictKeys st)).heapSet dst .dictValues (edgeRead .dict .dictValues st)
        | _ => pure ()
    pure (some (Flow.of (out.reduce) (outSt) ({})))
  | .tdict, "fromkeys" =>
    let (v, st') := allocate st p.id .dict []
    let l : Loc := ⟨p.id, .dict, true⟩
    let keys := elemOf st arg0
    let value := avs[1]?.getD (V [.tnone])
    pure (some (Flow.of (v) ((st'.heapSet l .dictKeys keys).heapSet l .dictValues value) ({})))
  | .tdict, "clear" =>
    let mut st := st
    for l in recv.locs do
      match l.cls with
      | .td tn =>
        match c.classes.getCls? tn with
        | some ci =>
          if ci.fields.any (fun f => f.required || f.readOnly) then
            if let some detail := wholesaleRemovalObligation .clear tn "" then
              oblige p "shape-break" detail
          else
            if isSoleRecentTarget recv l then
              for field in ci.fields do
                st := st.heapSet l (.literalKey field.name) (V [.tmissing])
              st := st.heapSet l .dictValues AbsVal.bot
            else
              for field in ci.fields do
                st := st.heapJoin l (.literalKey field.name) (V [.tmissing])
        | none => pure ()
      | .dict =>
        if let some only := soleRecent recv .dict then
          st := (st.heapSet only .dictKeys AbsVal.bot).heapSet only .dictValues AbsVal.bot
      | _ => pure ()
    pure (some (Flow.of (V [.tnone]) (st) ({})))
  | .tstr, "upper" | .tstr, "lower" | .tstr, "strip" | .tstr, "lstrip"
  | .tstr, "rstrip" | .tstr, "title" | .tstr, "capitalize"
  | .tstr, "casefold" | .tstr, "swapcase" | .tstr, "replace"
  | .tstr, "join" | .tstr, "format" | .tstr, "removeprefix"
  | .tstr, "removesuffix" | .tstr, "ljust" | .tstr, "rjust"
  | .tstr, "center" | .tstr, "zfill" | .tstr, "expandtabs" =>
    pure (some (Flow.of (V [.tstr]) (st) ({})))
  | .tstr, "startswith" | .tstr, "endswith" | .tstr, "isalnum"
  | .tstr, "isalpha" | .tstr, "isascii" | .tstr, "isdecimal"
  | .tstr, "isdigit" | .tstr, "isidentifier" | .tstr, "islower"
  | .tstr, "isnumeric" | .tstr, "isprintable" | .tstr, "isspace"
  | .tstr, "istitle" | .tstr, "isupper" =>
    pure (some (Flow.of (V [.tbool]) (st) ({})))
  | .tstr, "find" | .tstr, "rfind" =>
    pure (some (Flow.of (V [.tint]) (st) ({})))
  | .tstr, "index" | .tstr, "rindex" =>
    pure (some (Flow.of (V [.tint]) (st) ((← mraise p {} st ["ValueError"]))))
  | .tstr, "split" | .tstr, "rsplit" | .tstr, "splitlines" =>
    let (lv, st') := freshList (V [.tstr]) st
    pure (some (Flow.of (lv) (st') ({})))
  | _, _ => pure none

partial def fallbackBuiltinCall (p : Pos) (n : String) (avs : List AbsVal)
    (argEs : List Expr) (st : AState) : M Flow := do
  let arg0 := avs.headD AbsVal.bot
  match n with
  | "len" => do
    let mut normal : Option AState := none
    let mut exc : Exc := {}
    for tag in arg0.tags do
      match tag with
      | .tlist | .ttuple | .tdict | .tset | .tstr | .trange
      | .tdictkeys | .tdictitems | .tdictvalues =>
        resCase p "call" "len(..)" (Tag.render tag) "builtin __len__"
        normal := joinOpt normal (some st)
      | .tobj className =>
        match ← resolveMethodM className "__len__" with
        | some (owner, fn) =>
          resCase p "call" "len(..)" (Tag.render tag) s!"{owner}.__len__"
          let result ← inlineFunc p s!"{owner}.__len__" fn
            [arg0.restrictTags [tag]] [] st
          exc := exc.joinE result.exc
          let valid := result.val.restrictTags [.tbool, .tint]
          let invalid := result.val.withoutTags [.tbool, .tint]
          if !valid.isBot then
            normal := joinOpt normal (some (result.stateOr st))
            exc ← mraise p exc (result.stateOr st) ["ValueError"]
          if !invalid.isBot then
            resCase p "call" "len(..)" (Tag.render tag) "!TypeError"
            exc ← mraise p exc (result.stateOr st) ["TypeError"]
        | none =>
          resCase p "call" "len(..)" (Tag.render tag) "!TypeError"
          exc ← mraise p exc st ["TypeError"]
      | .tany =>
        resCase p "call" "len(..)" "any" "deferred"
        oblige p "dispatch-any" "len() of an unknown value"
        normal := joinOpt normal (some st)
      | .tunbound | .tuninit | .tmissing => pure ()
      | _ =>
        resCase p "call" "len(..)" (Tag.render tag) "!TypeError"
        exc ← mraise p exc st ["TypeError"]
    pure (Flow.of (if normal.isSome then V [.tint] else AbsVal.bot) (normal.getD st) (exc))
  | "str" | "repr" => do
    let validArity := if n == "str" then avs.length <= 1
      else avs.length == 1
    if !validArity then
      return (Flow.of (AbsVal.bot) (st) ((← mraise p {} st ["TypeError"])))
    if avs.isEmpty then
      return (Flow.of (V [.tstr]) (st) ({}))
    let mut normal : Option AState := none
    let mut exc : Exc := {}
    for tag in arg0.tags do
      match tag with
      | .tobj className =>
        let primary := if n == "str" then "__str__" else "__repr__"
        let mut resolved ← resolveMethodM className primary
        -- object.__str__ delegates to the representation slot.
        if n == "str" && resolved.isNone then
          resolved ← resolveMethodM className "__repr__"
        match resolved with
        | some (owner, fn) =>
          resCase p "call" s!"{n}(..)" (Tag.render tag)
            s!"{owner}.{fn.name}"
          let result ← inlineFunc p s!"{owner}.{fn.name}" fn
            [arg0.restrictTags [tag]] [] st
          exc := exc.joinE result.exc
          let good := result.val.restrictTags [.tstr]
          let bad := result.val.withoutTags [.tstr]
          if !good.isBot then
            normal := joinOpt normal (some (result.stateOr st))
          if !bad.isBot then
            resCase p "call" s!"{n}(..)" (Tag.render tag) "!TypeError"
            exc ← mraise p exc (result.stateOr st) ["TypeError"]
        | none =>
          normal := joinOpt normal (some st)
      | .tany =>
        resCase p "call" s!"{n}(..)" "any" "deferred"
        oblige p "dispatch-any" s!"{n}() of an unknown value"
        normal := joinOpt normal (some st)
        exc ← mraise p exc st ["TypeError"]
      | .tunbound | .tuninit | .tmissing => pure ()
      | _ => normal := joinOpt normal (some st)
    pure (Flow.of (if normal.isSome then V [.tstr] else AbsVal.bot) (normal.getD st) (exc))
  | "range" =>
    -- trange is a reference tag: without a location the value reduces
    -- to bot (the ledger caught exactly that), so allocate one
    let (v, st') := allocate st p.id .range []
    pure (Flow.of (v) (st') ({}))
  | "print" => pure (Flow.of (V [.tnone]) (st) ({}))
  | "isinstance" => pure (Flow.of (V [.tbool]) (st) ({}))
  | "iter" => do
    let mut out : AbsVal := AbsVal.bot
    let mut normal : Option AState := none
    let mut exc : Exc := {}
    for tag in arg0.tags do
      match tag with
      | .tgen =>
        resCase p "call" "iter(..)" "gen" "identity"
        out := out.join (arg0.restrictTags [tag])
        normal := joinOpt normal (some st)
      | .tlist | .ttuple | .tdict | .tset | .tstr | .trange
      | .tdictkeys | .tdictitems | .tdictvalues =>
        resCase p "call" "iter(..)" (Tag.render tag) "builtin __iter__"
        let (generator, nextSt) := allocate st p.id .gen []
        let location : Loc := ⟨p.id, .gen, true⟩
        out := out.join generator
        let nextSt := nextSt.heapSet location .elem
          (elemOf st (arg0.restrictTags [tag]))
        let nextSt := if definitelyNonempty
            (arg0.restrictTags [tag]) st then
          strongEmptinessUpdate nextSt location .nonempty
        else nextSt
        normal := joinOpt normal
          (some nextSt)
      | .tobj className =>
        match ← resolveMethodM className "__iter__" with
        | some (owner, fn) =>
          resCase p "call" "iter(..)" (Tag.render tag) s!"{owner}.__iter__"
          let result ← inlineFunc p s!"{owner}.__iter__" fn
            [arg0.restrictTags [tag]] [] st
          exc := exc.joinE result.exc
          let mut valid : AbsVal := result.val.restrictTags [.tgen, .tany]
          for resultTag in result.val.tags do
            if let .tobj resultClass := resultTag then
              if (← resolveMethodM resultClass "__next__").isSome then
                valid := valid.join (result.val.restrictTags [resultTag])
          let invalid := result.val.withoutTags valid.tags
          if !valid.isBot then
            out := out.join valid
            normal := joinOpt normal (some (result.stateOr st))
          if !invalid.isBot then
            resCase p "call" "iter(..)" (Tag.render tag) "!TypeError"
            exc ← mraise p exc (result.stateOr st) ["TypeError"]
        | none =>
          match ← resolveMethodM className "__getitem__" with
          | some (owner, _) =>
            resCase p "call" "iter(..)" (Tag.render tag)
              s!"sequence iterator via {owner}.__getitem__"
            oblige p "special-method"
              s!"iter({className}) defers indexed __getitem__ calls to next()"
            let (generator, nextSt) := allocate st p.id .gen []
            let location : Loc := ⟨p.id, .gen, true⟩
            out := out.join generator
            normal := joinOpt normal
              (some (nextSt.heapSet location .elem anyV))
          | none =>
            resCase p "call" "iter(..)" (Tag.render tag) "!TypeError"
            exc ← mraise p exc st ["TypeError"]
      | .tany =>
        resCase p "call" "iter(..)" "any" "deferred"
        oblige p "dispatch-any" "iter() of an unknown value"
        out := out.join anyV
        normal := joinOpt normal (some st)
      | .tunbound | .tuninit | .tmissing => pure ()
      | _ =>
        resCase p "call" "iter(..)" (Tag.render tag) "!TypeError"
        exc ← mraise p exc st ["TypeError"]
    pure (Flow.of (out.reduce) (normal.getD st) (exc))
  | "next" => do
    let dflt := if avs.length >= 2 then avs[1]! else AbsVal.bot
    let hasDefault := avs.length >= 2
    let mut out : AbsVal := AbsVal.bot
    let mut normal : Option AState := none
    let mut exc : Exc := {}
    for tag in arg0.tags do
      match tag with
      | .tgen =>
        resCase p "call" "next(..)" "gen" "builtin __next__"
        let generator := arg0.restrictTags [tag]
        let mustYield := definitelyNonempty generator st
        let ge ← genExcOf generator
        let bodyTags := excsAfterGen ge
        exc := Exc.add exc st (Fset.diff bodyTags ["StopIteration"])
        let element := elemOf st generator
        let consumed := clearGeneratorNonempty generator st
        out := out.join element
        if !element.isBot then normal := joinOpt normal (some consumed)
        if !mustYield then
          if hasDefault then
            out := out.join dflt
            normal := joinOpt normal (some consumed)
          else
            exc ← mraise p exc consumed ["StopIteration"]
      | .tobj className =>
        match ← resolveMethodM className "__next__" with
        | some (owner, fn) =>
          resCase p "call" "next(..)" (Tag.render tag) s!"{owner}.__next__"
          let result ← inlineFunc p s!"{owner}.__next__" fn
            [arg0.restrictTags [tag]] [] st
          let leaked := Fset.diff result.exc.tags ["StopIteration"]
          exc := exc.joinE { result.exc with
            tags := leaked
            st := if leaked.isEmpty then none else result.exc.st }
          if result.hasNormal then
            out := out.join result.val
            normal := joinOpt normal (some (result.stateOr st))
          if result.exc.tags.contains "StopIteration" then
            if hasDefault then
              out := out.join dflt
              normal := joinOpt normal result.exc.st
            else
              exc := Exc.add exc (result.exc.st.getD st) ["StopIteration"]
        | none =>
          resCase p "call" "next(..)" (Tag.render tag) "!TypeError"
          exc ← mraise p exc st ["TypeError"]
      | .tany =>
        resCase p "call" "next(..)" "any" "deferred"
        oblige p "dispatch-any" "next() of an unknown value"
        out := out.join anyV
        normal := joinOpt normal (some st)
        if !hasDefault then exc ← mraise p exc st ["StopIteration"]
      | .tunbound | .tuninit | .tmissing => pure ()
      | _ =>
        resCase p "call" "next(..)" (Tag.render tag) "!TypeError"
        exc ← mraise p exc st ["TypeError"]
    pure (Flow.of (out.reduce) (normal.getD st) (exc))
  | "list" | "tuple" | "set" => do
    let cls : LocCls := if n == "list" then .list
      else if n == "set" then .set else .tuple
    let (v, st') := allocate st p.id cls []
    let l : Loc := ⟨p.id, cls, true⟩
    let ev := if avs.isEmpty then AbsVal.bot else elemOf st arg0
    if n == "set" then checkHashable p ev
    let st' := st'.heapSet l .elem ev
    let st' := if !avs.isEmpty && definitelyNonempty arg0 st then
      strongEmptinessUpdate st' l .nonempty
    else st'
    pure (Flow.of (v) (st') ({}))
  | "dict" => do
    let (v, st') := allocate st p.id .dict []
    let _ := argEs
    pure (Flow.of (v) (st') ({}))
  | _ => pure (Flow.of (anyV) (st) ({}))

partial def builtinCall (p : Pos) (n : String) (avs : List AbsVal)
    (kvs : List (String × AbsVal)) (argEs : List Expr) (st : AState) :
    M Flow := do
  let rules := RuleProvider.compiledRules
  if (RuleDriven.CompiledRules.find? rules (.function n)).isNone then
    fallbackBuiltinCall p n avs argEs st
  else
    let fallback : RuleDriven.Services := {
      invoke := fun callPos operation _ arguments keywords state => do
        match operation with
        | .function name =>
          pure ((← fallbackBuiltinCall callPos name arguments argEs state))
        | .builtinLen =>
          RuleDriven.Protocols.len v2ProtocolServices callPos arguments keywords state
        | .builtinStr =>
          RuleDriven.Protocols.str v2ProtocolServices callPos arguments keywords state
        | .builtinRepr =>
          RuleDriven.Protocols.repr v2ProtocolServices callPos arguments keywords state
        | .builtinIter =>
          RuleDriven.Protocols.iter v2ProtocolServices callPos arguments keywords state
        | .builtinNext =>
          RuleDriven.Protocols.next v2ProtocolServices callPos arguments keywords state
        | _ =>
          RuleDriven.Services.opaque.invoke callPos operation none arguments [] state
      truth := RuleDriven.Services.opaque.truth
      applyContracts := RuleDriven.Contracts.applyContracts v2ContractServices
    }
    let services := RuleDriven.CompiledRules.services rules fallback
    let flow ← services.invoke p (.function n) none avs kvs st
    pure (flow)

partial def constructBuiltinExc (p : Pos) (cn : String) (st : AState) :
    M Flow := do
  pure ((<- RuleDriven.Calls.constructBuiltinException v2CallServices p cn st))

/-- TypedDict construction: at runtime a plain dict is built and no
    shape is enforced; the analysis allocates a td location whose
    declared key set drives dispatch, checks the keyword set against
    the declaration, and stores per-key edges plus the smashed
    key/val edges so the generic dict interface keeps working. -/
partial def tdConstruct (p : Pos) (ci : ClassInfo) (avs : List AbsVal)
    (kvs : List (String × AbsVal)) (st : AState) : M Flow := do
  pure ((<- RuleDriven.Calls.constructTypedDict v2CallServices p ci avs kvs st))

partial def construct (p : Pos) (cn : String) (avs : List AbsVal)
    (kvs : List (String × AbsVal)) (st : AState) : M Flow := do
  pure ((<- RuleDriven.Calls.constructClass v2CallServices p cn avs kvs st))

/-- Whatever escapes a callee escapes its call site, so the site reports it. -/
partial def inlineFunc (p : Pos) (qname : String) (fd : FuncDef)
    (avs : List AbsVal) (kvs : List (String × AbsVal)) (st : AState) :
    M Flow := do
  let flow <- RuleDriven.Calls.invokeUser v2CallServices p qname fd avs kvs st
  for raised in flow.raised.cases do
    resCaseAt p "call" s!"{qname}(..)" "code" s!"!{raised.cls}"
  pure flow

-- --------------------------------------------------------- refinement

partial def refine (e : Expr) (st : AState) :
    M (Option AState × Option AState) := do
  let c ← get
  match e with
  | .const _ (.cbool b) => pure (if b then (some st, none) else (none, some st))
  | .const _ (.cint n) => pure (if n == 0 then (none, some st) else (some st, none))
  | .const _ .cnone => pure (none, some st)
  | .const _ (.cstr s) =>
    pure (if s.isEmpty then (none, some st) else (some st, none))
  | .name _ x =>
    let v := st.envGet x
    if v.tags == [Tag.tunbound] then pure (some st, some st)
    else
      let vTrue := v.withoutTags [.tnone]
      -- objects of classes with no __bool__/__len__ are always truthy
      let mut falseDrop : Fset Tag := []
      for t in v.tags do
        if let .tobj cn := t then
          if alwaysTruthyObj c.classes cn then
            falseDrop := Fset.insert t falseDrop
          else
            oblige e.pos "special-method"
              s!"truthiness of {cn} via one-step __bool__/__len__"
      let vFalse := v.withoutTags falseDrop
      let tSt := if vTrue.isBot then none else some (st.envSet x vTrue)
      let fSt := if vFalse.isBot then none else some (st.envSet x vFalse)
      pure (tSt, fSt)
  | .notE _ inner => do
    let (t, f) ← refine inner st
    pure (f, t)
  | .cmp _ op (.name _ x) (.const _ .cnone)
  | .cmp _ op (.const _ .cnone) (.name _ x) =>
    if op == .isOp || op == .isNotOp then
      let v := st.envGet x
      let yes := v.restrictTags [.tnone]
      let no := v.withoutTags [.tnone]
      let tSt := if yes.isBot then none else some (st.envSet x yes)
      let fSt := if no.isBot then none else some (st.envSet x no)
      pure (if op == .isOp then (tSt, fSt) else (fSt, tSt))
    else pure (some st, some st)
  | .call _ (.name _ "isinstance") [(.name _ x), clsE] _ =>
    let v := st.envGet x
    let keep ← isinstanceTagsM clsE
    if keep.isEmpty then pure (some st, some st)
    else
      let vT := v.restrictTags (Fset.insert Tag.tany keep)
      let vF := v.withoutTags keep
      pure (if vT.isBot then none else some (st.envSet x vT),
            if vF.isBot then none else some (st.envSet x vF))
  | .boolop _ true vals => do
    -- and: true side threads every conjunct's true state
    let mut tSt : Option AState := some st
    let mut fSt : Option AState := none
    for v in vals do
      match tSt with
      | some s =>
        let (t, f) ← refine v s
        tSt := t
        fSt := joinOpt fSt f
      | none => pure ()
    pure (tSt, fSt)
  | .boolop _ false vals => do
    let mut fSt : Option AState := some st
    let mut tSt : Option AState := none
    for v in vals do
      match fSt with
      | some s =>
        let (t, f) ← refine v s
        fSt := f
        tSt := joinOpt tSt t
      | none => pure ()
    pure (tSt, fSt)
  | _ => pure (some st, some st)

-- --------------------------------------------------------- statements

partial def bindTarget (tgt : Target) (v : AbsVal) (st : AState) :
    M StateRes := do
  let flow <-
    RuleDriven.StructuralExpressions.bindTarget v2StructuralServices tgt v st
  pure ⟨flow.normal.map (·.2), flow.raised.toExc⟩

partial def setAttr (p : Pos) (recv : AbsVal) (f : String) (v : AbsVal)
    (st : AState) : M StateRes := do
  let services : RuleDriven.Objects.Services := { invokeUser := v2InvokeUser }
  let flow ← RuleDriven.Objects.attributeWrite services p recv f v st
  reportEscapes p "setattr" s!".{f} =" "code" flow
  let result := flow
  pure ⟨flow.normal.map (·.2), result.exc⟩

partial def execBody (ss : List Stmt) (st : AState) : M AMulti := do
  pure (RuleDriven.Compatibility.aMultiOfCompletion
    (<- RuleDriven.Statements.executeBody v2StatementServices ss st)
  )



end

-- ---------------------------------------- contract entry materialization

/-- Build a fresh abstract value satisfying a recursive boundary contract.
    Locations make reference tags usable by the heap analysis; the depth
    bound protects recursive nominal/container contracts while preserving
    their outer shape. -/
partial def materializeAnn (fuel : Nat) (site : NodeId) (a : Ann) (st : AState) :
    M (AbsVal × AState) := do
  if fuel == 0 then return (anyV, st)
  let c ← get
  match a with
  | .any => pure (anyV, st)
  | .required inner | .notRequired inner | .readOnly inner =>
    materializeAnn (fuel - 1) site inner st
  | .union members => do
    let mut out : AbsVal := AbsVal.bot
    let mut st := st
    for (member, i) in members.zipIdx do
      let (v, st') ← materializeAnn (fuel - 1)
        (site.synth (i + 1)) member st
      out := out.join v
      st := st'
    pure (out.reduce, st)
  | .literal values =>
    let value := values.foldl
      (fun out literal => out.join (constV literal)) AbsVal.bot
    pure (value.reduce, st)
  | .generic name args variadic => do
    let cls : Option LocCls := match name with
      | "list" | "List" => some .list
      | "dict" | "Dict" => some .dict
      | "set" | "Set" => some .set
      | "tuple" | "Tuple" => some .tuple
      | _ => none
    match cls with
    | none => pure (anyV, st)
    | some cls =>
      let (v, st') := allocate st site cls []
      let l : Loc := ⟨site, cls, true⟩
      let mut st := st'
      match cls with
      | .list | .set =>
        let (elem, st') ← materializeAnn (fuel - 1) (site.synth 1)
          (args.headD .any) st
        st := st'.heapSet l .elem elem
      | .dict =>
        let (key, st1) ← materializeAnn (fuel - 1) (site.synth 1)
          (args.headD .any) st
        let (value, st2) ← materializeAnn (fuel - 1) (site.synth 2)
          (args[1]?.getD .any) st1
        st := (st2.heapSet l .dictKeys key).heapSet l .dictValues value
      | .tuple =>
        let tupleArgs := if variadic then [args.headD .any] else args
        let mut elem : AbsVal := AbsVal.bot
        for (slotAnn, i) in tupleArgs.zipIdx do
          let (slot, st') ← materializeAnn (fuel - 1)
            (site.synth (i + 1)) slotAnn st
          st := st'.heapSet l (.tupleSlot i) slot
          elem := elem.join slot
        st := st.heapSet l .elem elem
      | _ => pure ()
      -- An annotated container has unknown cardinality.
      st := strongEmptinessUpdate st l .top
      pure (v, st)
  | .atom name =>
    match c.classes.getCls? name with
    | some ci =>
      let cls := if ci.isTypedDict then LocCls.td name else LocCls.obj name
      let (v, st') := allocate st site cls
        (if ci.isTypedDict then [] else ci.layout)
      let l : Loc := ⟨site, cls, true⟩
      let mut st := st'
      let mut valueJoin : AbsVal := AbsVal.bot
      if ci.isTypedDict then
        for (field, i) in ci.fields.zipIdx do
          let (fieldValue, st') ← match field.ann with
            | some fieldAnn =>
              materializeAnn (fuel - 1) (site.synth (i + 1)) fieldAnn st
            | none => pure (anyV, st)
          let fieldValue := if field.required then fieldValue
            else fieldValue.join (V [.tmissing])
          st := st'.heapSet l (.literalKey field.name) fieldValue
          valueJoin := valueJoin.join (fieldValue.withoutTags [.tmissing])
        st := (st.heapSet l .dictKeys (typedDictKeys ci)).heapSet l .dictValues valueJoin
      else
        for (fieldName, i) in ci.layout.zipIdx do
          let field? := ci.fields.find? (·.name == fieldName)
          let (fieldValue, st') ← match field?.bind (·.ann) with
            | some fieldAnn =>
              materializeAnn (fuel - 1) (site.synth (i + 1)) fieldAnn st
            | none => pure (anyV, st)
          st := st'.heapSet l (.field fieldName) fieldValue
      pure (v, st)
    | none =>
      -- A bare container annotation needs a location: a reference tag with no
      -- allocation reduces to bottom, and the parameter would vanish.
      match name with
      | "list" | "List" | "dict" | "Dict" | "set" | "Set"
      | "tuple" | "Tuple" =>
        materializeAnn (fuel - 1) site (.generic name [] false) st
      | _ =>
        let v := match annAtomTags c.classes name with
          | some tags =>
            let v := V tags
            if v.isBot && !tags.isEmpty then anyV else v
          | none => anyV
        pure (v, st)

-- ------------------------------------------------------------- driver

def runProgram (prog : Program) : M AMulti := do
  let cds := prog.items.filterMap (fun i => match i with
    | .cdef c => some c | _ => none)
  let fds := prog.items.filterMap (fun i => match i with
    | .fdef f => some f | _ => none)
  let .ok table := buildClassTable cds
    | return {}
  let glb :=
    fds.map (fun f => (f.name, V [.tfunc] (funcs := [f.name]))) ++
    cds.map (fun c => (c.name, V [.ttype] (classes := [c.name])))
  modify fun c => { c with
    classes := table
    funcs := fds.map (fun f => (f.name, f))
    glb }
  let stmts := prog.items.filterMap (fun i => match i with
    | .stmt s => some s | _ => none)
  let moduleResult ← execBody stmts {}
  -- Every annotated top-level function is a verification boundary, even
  -- when no module-level call reaches it. Analyze it from a fresh contract
  -- state so the residual dashboard never reports a vacuous zero-site pass.
  for (fd, functionIndex) in fds.zipIdx do
    if !fd.params.all (·.ann.isSome) then continue
    let mut rootSt : AState := {}
    let mut args : List AbsVal := []
    for (param, paramIndex) in fd.params.zipIdx do
      let (value, nextSt) ← match param.ann with
        | some ann =>
          -- A parameter of a root-level function has no node of its own to
          -- allocate against, so the site is synthetic: reserved marker, then the
          -- function and parameter indices. This replaced
          -- `100000000 + functionIndex * 100000 + paramIndex * 1000`, whose
          -- spacing was chosen so the ranges would probably not overlap.
          materializeAnn 12
            ((NodeId.root.synth functionIndex).child paramIndex)
            ann rootSt
        | none => pure (anyV, rootSt)
      args := args ++ [value]
      rootSt := nextSt
    -- This is a verification boundary, not a call: there is no call
    -- expression at `fd.p`, which is the `def` line. Claim the site as a
    -- contract row first, so an exception escaping the body attaches to that
    -- instead of manufacturing a `call` residual that reads, on the definition
    -- line, as though calling the function always raises.
    resSite fd.p "contract" s!"{fd.name} entry"
    let _ ← inlineFunc fd.p fd.name fd args [] rootSt
  pure moduleResult

end

def runProgramWith (rules : RuleDriven.CompiledRules) (prog : Program) : M AMulti :=
  letI : RuleProvider := ⟨rules⟩
  runProgram prog

def runProgramDefault (prog : Program) : M AMulti :=
  runProgramWith RuleDriven.compiledInitialLiveRules prog

end Pylate.RuleDriven
