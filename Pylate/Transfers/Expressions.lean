/-
Operation-level expression transfers for the rule interpreter.

Operands have already been evaluated, so these APIs only model Python
protocol dispatch and its effects.  User code is reachable through the narrow
Services boundary below; this module never calls the procedural analyzer.
-/
import Pylate.Tables.Binary
import Pylate.Transfers.Flow

namespace Pylate.RuleDriven.Expressions

open Pylate

structure Services where
  invokeUser : Pos -> String -> FuncDef -> List AbsVal ->
    List (String × AbsVal) -> AState -> M Flow

private def inertTag : Tag -> Bool
  | .tunbound | .tuninit | .tmissing => true
  | _ => false

private def raisedOfExc (fallback : AState) (exception : Exc) : RaisedFlow :=
  exception.tags.foldl (fun raised cls =>
    raised.add {
      cls
      value := AbsVal.bot
      state := exception.st.getD fallback
      -- From the joined `Exc` view: no raise site survives it.
      origin := {}
    }) {}

private def machineRaises (p : Pos) (classes : Fset String)
    (state : AState) : M Flow := do
  let exception ← mraise p {} state classes
  pure { raised := raisedOfExc state exception }

private def addMachineRaises (p : Pos) (flow : Flow)
    (classes : Fset String) (state : AState) : M Flow := do
  pure (flow.join (← machineRaises p classes state))

private def addRaisedToTruth (truth : TruthFlow)
    (raised : RaisedFlow) : TruthFlow :=
  { truth with raised := truth.raised.join raised }

private def normalTruth (value : AbsVal) (state : AState)
    (mayTruthy mayFalsy : Bool) : TruthFlow :=
  {
    truthy := if mayTruthy then some (value, state) else none
    falsy := if mayFalsy then some (value, state) else none
  }

private def normalStateOfTruth (truth : TruthFlow) : Option AState :=
  joinOpt (truth.truthy.map (·.2)) (truth.falsy.map (·.2))

private def boolFlowOfTruth (truth : TruthFlow) : Flow :=
  {
    normal := (normalStateOfTruth truth).map fun state => (V [.tbool], state)
    raised := truth.raised
  }

-- Both chains are rows of `DunderProtocol.chain` in `BuiltinOutcomes.lean`, where
-- `RuleValidate` can count them. `__getitem__` is the legacy sequence scan, and
-- its `IndexError` is the protocol's stop signal rather than an escape.
def truthChain : List String := DunderProtocol.truth.chain

def membershipChain : List String := DunderProtocol.membership.chain

private def builtinTruth (value : AbsVal) (tag : Tag)
    (state : AState) : TruthFlow :=
  let input := value.restrictTags [tag]
  match tag with
  | .tunbound | .tuninit | .tmissing => {}
  -- Match the direct oracle: evalTruth proves only that conversion returned,
  -- while expression-level refine performs any later truth-side narrowing.
  | _ => normalTruth input state true true

/-- Python truth conversion over an already evaluated value.  User
    `__bool__` and `__len__` execute before result validation, so all their
    exceptions and validation failures retain the post-hook state.

    CLAIM truth-bool-then-len: `__bool__` decides truth; with none, `__len__`;
    with neither, true.
-/
partial def truth (services : Services) (p : Pos) (value : AbsVal)
    (state : AState) : M TruthFlow := do
  let mut result : TruthFlow := {}
  for tag in value.tags do
    let input := value.restrictTags [tag]
    match tag with
    | .tobj className =>
      -- The chain order is data. It was nesting, where the sequence was implied
      -- by indentation and a third step could be inserted in the wrong place
      -- without anything noticing.
      match ← firstDefinedDunder className truthChain with
      | some (hit, owner, function) =>
        resCase p "truth" "truthiness" tag.render s!"{owner}.{hit}"
        let called ← services.invokeUser p s!"{owner}.{hit}" function
          [input] [] state
        result := addRaisedToTruth result called.raised
        if let some (returned, postState) := called.normal then
          -- `__bool__` must return `bool`; `__len__` may return any int, and a
          -- negative one is a `ValueError` that the magnitude is not tracked
          -- closely enough to rule out.
          let accepted : List Tag :=
            if hit == "__bool__" then [.tbool] else [.tbool, .tint]
          let valid := returned.restrictTags accepted
          let invalid := returned.withoutTags accepted
          if !valid.isBot then
            result := result.join (normalTruth input postState true true)
            if hit == "__len__" then
              let raised ← machineRaises p ["ValueError"] postState
              result := addRaisedToTruth result raised.raised
          if !invalid.isBot then
            resCase p "truth" "truthiness" tag.render "!TypeError"
            let raised ← machineRaises p ["TypeError"] postState
            result := addRaisedToTruth result raised.raised
      | none =>
        resCase p "truth" "truthiness" tag.render "truthy"
        result := result.join (normalTruth input state true true)
    | .tany =>
      resCase p "truth" "truthiness" "any" "deferred"
      oblige p "dispatch-any" "truthiness of an unknown value"
      result := result.join (builtinTruth input tag state)
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      resCase p "truth" "truthiness" tag.render "builtin bool"
      result := result.join (builtinTruth input tag state)
  pure result

/-- Logical `not`. -/
def logicalNot (services : Services) (p : Pos) (value : AbsVal)
    (state : AState) : M Flow := do
  let converted ← truth services p value state
  pure (boolFlowOfTruth converted)

/-- The literal set of an int-valued unary result.

    Computing new literals is normally what makes a value domain
    non-terminating, and the rule elsewhere is to set the open marker instead.
    These three are the exception because they are *closed* on a finite set:
    `+` is the identity, `-` is an involution, and `~` is one too
    (`~~n = n`), so the closure of a program's literals under them is at most
    twice their number. The unbounded case is `n = n - 1` in a loop, and that is
    a binary operator, which keeps setting the marker.

    Worth having because `xs[-1]` is ordinary Python, and without it the index
    is an unknown int and every such subscript owes a bounds obligation. -/
private def unaryLits (op : UnOp) (produced : Tag) (input : AbsVal) : AbsVal :=
  let intLike := fun (tag : Tag) => tag == Tag.tint || tag == Tag.tbool
  if produced != Tag.tint || !input.tags.all intLike ||
      input.litsOpen.any intLike then
    V [produced]
  else
    let sources : Fset Int := input.lits.filterMap fun l =>
      match l with
      | .lint i => some i
      | .lbool b => some (if b then 1 else 0)
      | _ => none
    if sources.isEmpty then V [produced]
    else
      let apply := fun (i : Int) => match op with
        | .pos => i
        | .neg => -i
        | .invert => -i - 1
      { tags := [produced], lits := (sources.map apply).map Lit.lint }

/-- Unary `-`, `+` and `~`. The three differ only in the dunder they resolve
    and in whether they accept inexact operands: `~` is a bit operation, so
    float and complex fall through to the `TypeError` case rather than
    reproducing their own type. `bool` widens to `int` for all three. -/
partial def unaryOp (services : Services) (op : UnOp) (p : Pos)
    (value : AbsVal) (state : AState) : M Flow := do
  let desc := s!"unary {op.astName}"
  let dunder := op.dunder
  resSite p "unary" desc
  let mut result : Flow := {}
  for tag in value.tags do
    let input := value.restrictTags [tag]
    let numeric : Option Tag := match tag with
      | .tbool | .tint => some .tint
      | .tfloat => if op.acceptsInexact then some .tfloat else none
      | .tcomplex => if op.acceptsInexact then some .tcomplex else none
      | _ => none
    match numeric, tag with
    | some produced, _ =>
      resCase p "unary" desc tag.render
        s!"builtin {(produced.render)}.{dunder}"
      result := result.join
        (Flow.ofNormal (unaryLits op produced input) state)
    | none, .tobj className =>
      match ← resolveMethodM className dunder with
      | some (owner, function) =>
        let called ← services.invokeUser p s!"{owner}.{dunder}" function
          [input] [] state
        resCase p "unary" desc tag.render s!"{owner}.{function.name}"
        for raised in called.raised.classes do
          resCase p "unary" desc tag.render s!"!{raised}"
        result := result.join called
      | none =>
        resCase p "unary" desc tag.render "!TypeError"
        result ← addMachineRaises p result ["TypeError"] state
    | none, .tany =>
      resCase p "unary" desc "any" "deferred"
      oblige p "dispatch-any"
        s!"unary {op.render} has an unknown operand"
      result := result.join (Flow.ofNormal anyV state)
    | none, _ =>
      resCase p "unary" desc tag.render "!TypeError"
      result ← addMachineRaises p result ["TypeError"] state
  pure result

/-- Unary `-`, kept as a name for the call sites that only negate. -/
partial def negate (services : Services) (p : Pos) (value : AbsVal)
    (state : AState) : M Flow :=
  unaryOp services .neg p value state

private def legacyInline (services : Services) : Binary.InlineFn :=
  fun p label function arguments keywords state => do
    let flow ← services.invokeUser p label function arguments keywords state
    pure flow

private structure CandidateStep where
  flow : Flow := {}
  nextState : Option AState := none
  route : Option String := none
  raised : Fset String := []

private def builtinStepFlow (fallback : AState)
    (step : Binary.Step) : Flow :=
  {
    normal := match step.normalSt with
      | some normalState =>
        if step.val.isBot then none else some (step.val.reduce, normalState)
      | none => none
    raised := raisedOfExc fallback step.exc
  }

private partial def executeBinaryCandidate (services : Services) (p : Pos)
    (candidate : Binary.Candidate) (operator : BinOp)
    (left right : AbsVal) (leftTag rightTag : Tag)
    (state : AState) : M CandidateStep := do
  match candidate with
  | .user label function self other =>
    let called ← services.invokeUser p label function [self, other] [] state
    let (normal, nextState) := match called.normal with
      | none => (none, none)
      | some (returned, postState) =>
        let ordinary := returned.withoutTags [.tnotimpl]
        (if ordinary.isBot then none else some (ordinary, postState),
         if Tag.tnotimpl ∈ returned.tags then some postState else none)
    pure {
      flow := { normal, raised := called.raised }
      nextState
      raised := called.raised.classes
    }
  | .builtin _ =>
    let step ← Binary.executeCandidate (legacyInline services) p candidate
      operator left right leftTag rightTag state
    pure {
      flow := builtinStepFlow state step
      nextState := step.continueSt
      route := step.route
      raised := step.raised
    }

private partial def binaryPair (services : Services) (p : Pos)
    (operator : BinOp) (left right : AbsVal) (leftTag rightTag : Tag)
    (state : AState) : M Flow := do
  let desc := s!"binop {operator.astName}"
  let pair := s!"({leftTag.render},{rightTag.render})"
  if leftTag == .tany || rightTag == .tany then
    resCase p "binop" desc pair "deferred"
    oblige p "dispatch-any"
      s!"operator {operator.render} has an unknown operand"
    return Flow.ofNormal anyV state
  let leftValue := left.restrictTags [leftTag]
  let rightValue := right.restrictTags [rightTag]
  let candidates ←
    Binary.candidates operator leftTag rightTag leftValue rightValue
  let mut result : Flow := {}
  let mut active : Option AState := some state
  for candidate in candidates do
    if let some candidateState := active then
      let step ← executeBinaryCandidate services p candidate operator
        leftValue rightValue leftTag rightTag candidateState
      if step.flow.normal.isSome then
        resCase p "binop" desc pair
          (step.route.getD candidate.label)
      for raised in step.raised do
        resCase p "binop" desc pair s!"!{raised}"
      result := result.join step.flow
      active := step.nextState
  if let some fallbackState := active then
    if let some implementation :=
        Binary.fallbackImpl operator leftTag rightTag then
      let candidate := Binary.Candidate.builtin implementation
      let step ← executeBinaryCandidate services p
        candidate operator leftValue rightValue
        leftTag rightTag fallbackState
      if step.flow.normal.isSome then
        resCase p "binop" desc pair
          (step.route.getD candidate.label)
      for raised in step.raised do
        resCase p "binop" desc pair s!"!{raised}"
      result := result.join step.flow
      active := step.nextState
  if let some terminalState := active then
    resCase p "binop" desc pair "!TypeError"
    result ← addMachineRaises p result ["TypeError"] terminalState
  pure result

/-- All Python binary operators over already evaluated operands.  Each tag
    pair starts from the same input state; protocol candidates themselves are
    sequenced in CPython order and only `NotImplemented` advances the chain.

    CLAIM binop-reflected-on-notimplemented: a `NotImplemented` from the left
    operand's dunder hands the operation to the right operand's reflected one;
    both declining is the `TypeError`.
    CLAIM binop-subclass-reflected-first: when the right operand's class
    derives from the left's and overrides the reflected dunder, the reflected
    call goes first.
-/
partial def binary (services : Services) (p : Pos) (operator : BinOp)
    (left right : AbsVal) (state : AState) : M Flow := do
  -- Claim the site before any operand hook can record against this node.
  resSite p "binop" s!"binop {operator.astName}"
  let mut result : Flow := {}
  for leftTag in left.tags do
    for rightTag in right.tags do
      result := result.join
        (← binaryPair services p operator left right leftTag rightTag state)
  pure result

private def builtinOrderedComparison (left right : Tag) : Bool :=
  let numeric := fun tag =>
    tag == .tbool || tag == .tint || tag == .tfloat
  (numeric left && numeric right) ||
    (left == .tstr && right == .tstr) ||
    (left == .tlist && right == .tlist) ||
    (left == .ttuple && right == .ttuple) ||
    (left == .tset && right == .tset)

private structure ComparisonCandidate where
  label : String
  function : FuncDef
  self : AbsVal
  other : AbsVal

private partial def comparisonCandidates (operator : CmpOp)
    (left right : AbsVal) (leftTag rightTag : Tag) :
    M (List ComparisonCandidate) := do
  let context ← get
  let mut forward : Option ComparisonCandidate := none
  let mut reflected : Option ComparisonCandidate := none
  if let .tobj className := leftTag then
    if let some (owner, function) ←
        resolveMethodM className operator.dunder then
      forward := some {
        label := s!"{owner}.{operator.dunder}"
        function
        self := left.restrictTags [leftTag]
        other := right.restrictTags [rightTag]
      }
  if let .tobj className := rightTag then
    if let some (owner, function) ←
        resolveMethodM className operator.reflectedDunder then
      reflected := some {
        label := s!"{owner}.{operator.reflectedDunder}"
        function
        self := right.restrictTags [rightTag]
        other := left.restrictTags [leftTag]
      }
  let reflectedFirst : Bool := match leftTag, rightTag with
    | .tobj leftClass, .tobj rightClass =>
      !(leftClass == rightClass) &&
        (context.classes.getCls? rightClass).any (·.mro.contains leftClass)
    | _, _ => false
  pure <| if reflectedFirst then
    [reflected, forward].filterMap id
  else
    [forward, reflected].filterMap id

private partial def comparisonPair (services : Services) (p : Pos)
    (operator : CmpOp) (left right : AbsVal) (leftTag rightTag : Tag)
    (state : AState) : M Flow := do
  let desc := s!"comparison {operator.astName}"
  let pair := s!"({leftTag.render},{rightTag.render})"
  if leftTag == .tany || rightTag == .tany then
    resCase p "comparison" desc pair "deferred"
    oblige p "dispatch-any"
      s!"comparison {operator.render} has an unknown operand"
    return Flow.ofNormal anyV state
  let candidates ←
    comparisonCandidates operator left right leftTag rightTag
  let mut result : Flow := {}
  let mut active : Option AState := some state
  for candidate in candidates do
    if let some candidateState := active then
      resCase p "comparison" desc pair candidate.label
      let called ← services.invokeUser p candidate.label candidate.function
        [candidate.self, candidate.other] [] candidateState
      result := { result with
        raised := result.raised.join called.raised }
      match called.normal with
      | none => active := none
      | some (returned, postState) =>
        let ordinary := returned.withoutTags [.tnotimpl]
        if !ordinary.isBot then
          result := result.join (Flow.ofNormal ordinary postState)
        active := if Tag.tnotimpl ∈ returned.tags
          then some postState else none
  if let some fallbackState := active then
    if operator == .eq || operator == .ne ||
        builtinOrderedComparison leftTag rightTag then
      resCase p "comparison" desc pair "builtin bool"
      result := result.join (Flow.ofNormal (V [.tbool]) fallbackState)
      if (leftTag == .tlist && rightTag == .tlist) ||
          (leftTag == .ttuple && rightTag == .ttuple) then
        result ← addMachineRaises p result ["TypeError"] fallbackState
    else
      resCase p "comparison" desc pair "!TypeError"
      result ← addMachineRaises p result ["TypeError"] fallbackState
  pure result

private def checkHashableOracle (p : Pos) (value : AbsVal) : M Unit := do
  let bad := value.tags.filter fun tag =>
    tag == .tlist || tag == .tdict || tag == .tset
  if !bad.isEmpty then
    oblige p "hashability"
      s!"unhashable tags {bad.map Tag.render} at a key or element position"

-- `stringProbeTags` is one row set in `BuiltinOutcomes.lean`.

private def builtinMembership (p : Pos) (item : AbsVal) (desc : String)
    (containerTag : Tag) (state : AState) : M Flow := do
  -- Oracle precision debt: CPython raises TypeError for an unhashable
  -- dict/set probe, but the direct analyzer currently records only an
  -- obligation and keeps the normal bool flow.  Keep this until both engines
  -- are strengthened together after differential landing.
  if containerTag == .tdict || containerTag == .tset then
    checkHashableOracle p item
  let accepted := stringProbeTags containerTag
  if accepted.isEmpty then
    return Flow.ofNormal (V [.tbool]) state
  let mut result : Flow := {}
  if item.isBot || item.tags.any (accepted.contains ·) then
    result := result.join (Flow.ofNormal (V [.tbool]) state)
    if containerTag == .tbytes &&
        item.tags.any (fun tag => tag == .tint || tag == .tbool) then
      -- The int's magnitude is not tracked, so `range(0, 256)` cannot be
      -- discharged here and the caller owes it.
      oblige p "bounds" "membership probe against bytes is a single byte"
      resCase p "membership" desc containerTag.render "!ValueError"
      result ← addMachineRaises p result ["ValueError"] state
  if item.tags.any (fun tag => !accepted.contains tag && !inertTag tag) then
    resCase p "membership" desc containerTag.render "!TypeError"
    result ← addMachineRaises p result ["TypeError"] state
  pure result

/-- `in`/`not in` after both operands have been evaluated.

    CLAIM membership-contains-then-iter-then-getitem: `in` tries
    `__contains__`, then `__iter__`, then `__getitem__` from 0.
    CLAIM membership-getitem-stop-is-false: an `IndexError` or subclass from
    the `__getitem__` walk means absent, not an error.
-/
partial def membership (services : Services) (p : Pos) (negated : Bool)
    (item container : AbsVal) (state : AState) : M Flow := do
  let operator := if negated then CmpOp.notInOp else CmpOp.inOp
  let desc := s!"comparison {operator.astName}"
  resSite p "membership" desc
  let mut result : Flow := {}
  for tag in container.tags do
    let receiver := container.restrictTags [tag]
    match tag with
    | .tobj className =>
      -- Three steps, and the order was three levels of nesting. As data, the
      -- sequence is stated once and each step's post-processing reads flat.
      match ← firstDefinedDunder className membershipChain with
      | some ("__contains__", owner, function) =>
        resCase p "membership" desc tag.render s!"{owner}.__contains__"
        let called ← services.invokeUser p s!"{owner}.__contains__" function
          [receiver, item] [] state
        result := { result with raised := result.raised.join called.raised }
        if let some (returned, postState) := called.normal then
          result := result.join
            (boolFlowOfTruth (← truth services p returned postState))
      | some ("__iter__", owner, function) =>
        resCase p "membership" desc tag.render s!"{owner}.__iter__"
        let called ← services.invokeUser p s!"{owner}.__iter__" function
          [receiver] [] state
        result := { result with raised := result.raised.join called.raised }
        if let some (_, postState) := called.normal then
          oblige p "special-method"
            s!"membership through {className}.__iter__: element comparisons are summarized"
          result := result.join (Flow.ofNormal (V [.tbool]) postState)
      | some ("__getitem__", owner, function) =>
        resCase p "membership" desc tag.render s!"{owner}.__getitem__"
        let called ← services.invokeUser p s!"{owner}.__getitem__" function
          [receiver, V [.tint]] [] state
        -- `IndexError` is this protocol's stop signal, not an escape: the scan
        -- ran off the end, which means "not found", so it becomes a normal bool.
        -- Every other class still escapes.
        let mut leaked : RaisedFlow := {}
        for raised in called.raised.cases do
          -- Subclasses count, following the exception MRO. CPython's `in` catches
          -- them: a `__getitem__` raising a subclass of `IndexError` yields
          -- `False`, it does not propagate. Matching the class name exactly let
          -- such a subclass escape here while the iteration transfer, which does
          -- follow the MRO, correctly treated it as end-of-sequence -- the same
          -- signal getting two different verdicts.
          if (← excMroM raised.cls).contains "IndexError" then
            result := result.join (Flow.ofNormal (V [.tbool]) raised.state)
          else
            leaked := leaked.add raised
        result := { result with raised := result.raised.join leaked }
        if let some (_, postState) := called.normal then
          oblige p "special-method"
            s!"membership through {className}.__getitem__: repeated indices are summarized"
          result := result.join (Flow.ofNormal (V [.tbool]) postState)
      | _ =>
        resCase p "membership" desc tag.render "!TypeError"
        result ← addMachineRaises p result ["TypeError"] state
    | .tany =>
      resCase p "membership" desc "any" "deferred"
      oblige p "dispatch-any" "membership on an unknown container"
      result := result.join (Flow.ofNormal (V [.tbool]) state)
    | _ =>
      -- Which tags support `in` comes from the table rather than from a list
      -- written here. The list omitted `bytes`, so `1 in b"ab"` was reported as
      -- always raising where CPython returns `False`.
      let outcome := builtinOutcome tag .membership
      if outcome.admitsNormal then
        resCase p "membership" desc tag.render "builtin contains"
        result := result.join (← builtinMembership p item desc tag state)
      else if !inertTag tag then
        for cls in outcome.raises do
          resCase p "membership" desc tag.render s!"!{cls}"
          result ← addMachineRaises p result [cls] state
  pure result

/-- Rich comparison, identity, and membership over evaluated operands.

    CLAIM comparison-reflected: an ordering declines to its mirror on the other
    operand; `==` with no dunder falls back to identity.
-/
partial def comparison (services : Services) (p : Pos)
    (operator : CmpOp) (left right : AbsVal)
    (state : AState) (source : String) : M Flow := do
  -- Membership and identity claim their own residual kinds below.
  if operator != .inOp && operator != .notInOp &&
      operator != .isOp && operator != .isNotOp then
    resSite p "comparison" s!"comparison {operator.astName}"
  if operator == .inOp || operator == .notInOp then
    return ← membership services p (operator == .notInOp)
      left right state
  if operator == .isOp || operator == .isNotOp then
    let leftTags := "|".intercalate (left.tags.map Tag.render)
    let rightTags := "|".intercalate (right.tags.map Tag.render)
    resCase p "identity" source s!"({leftTags},{rightTags})" "bool"
    return Flow.ofNormal (V [.tbool]) state
  let mut result : Flow := {}
  for leftTag in left.tags do
    for rightTag in right.tags do
      result := result.join
        (← comparisonPair services p operator left right
          leftTag rightTag state)
  pure result

end Pylate.RuleDriven.Expressions
