/-
Typed transfers for user calls and construction.

The service boundary contains only recursive body execution. Argument binding,
annotation checks, dispatch rows, completion routing, allocation, class
lookup, and summary bookkeeping are explicit first-order rule data interpreted
by the generic executor below.
-/
import Pylate.RuleLang.Plan
import Pylate.Transfers.Statements

namespace Pylate.RuleDriven.Calls

open Pylate
open Pylate.RuleDriven

structure Services where
  executeBody : List Stmt -> AState -> M Completion

inductive CallCompletionRule
  | ordinary
  | eagerGenerator
  /-- No body to run: answer from the declared return annotation, having checked
      the arguments against the parameter annotations. -/
  | contractOnly
deriving Repr, Inhabited, BEq

structure ParameterRule where
  name       : String
  annotation : Option Ann
  default    : Option Expr
deriving Inhabited

structure UserCallRule where
  qualifiedName   : String
  signature       : Signature
  parameters      : List ParameterRule
  returnAnnotation : Option Ann
  body            : List Stmt
  locals          : Fset String
  completion      : CallCompletionRule
deriving Inhabited

structure TypedDictConstructionRule where
  name      : String
  signature : Signature
  fields    : List FieldDecl
deriving Inhabited

structure BuiltinExceptionConstructionRule where
  className : String
  signature : Signature
deriving Inhabited

structure InitializerRule where
  owner              : String
  call               : UserCallRule
  requiresNoneReturn : Bool
deriving Inhabited

structure ClassConstructionRule where
  name            : String
  layout          : Fset String
  frozenDataclass : Bool
  initializer     : Option InitializerRule
  fallbackSignature : Signature
deriving Inhabited

inductive ConstructionRule
  | builtinException (rule : BuiltinExceptionConstructionRule)
  | typedDict (rule : TypedDictConstructionRule)
  | userClass (rule : ClassConstructionRule)
  | unresolved (className : String)
deriving Inhabited

inductive DispatchOutcome
  | userCall (rule : UserCallRule)
  | construct (rule : ConstructionRule)
  | deferred (detail : String)
  | typeError
  | inert
deriving Inhabited

structure DispatchRow where
  selector : String
  outcome  : DispatchOutcome
deriving Inhabited

structure ValueDispatchRule where
  description : String
  rows        : List DispatchRow
deriving Inhabited

inductive Rule
  | userCall (rule : UserCallRule)
  | construct (rule : ConstructionRule)
  | dispatch (rule : ValueDispatchRule)
deriving Inhabited

structure Input where
  arguments : List AbsVal := []
  keywords  : List (String × AbsVal) := []
deriving Inhabited

private def machineRaise (position : Pos) (cls : String)
    (state : AState) : M Flow := do
  let modeled <- mraise position {} state [cls]
  let raisedState := modeled.st.getD state
  pure {
    raised := {
      cases := modeled.tags.map fun raisedClass => {
        cls := raisedClass
        value := AbsVal.bot
        state := raisedState
        origin := position
      }
    }
  }

/-- Only the environment is caller-local: the heap and the emptiness
    component are keyed by location and survive the call. -/
private def restoreCaller (caller callee : AState) : AState :=
  { env := caller.env, heap := callee.heap, sizes := callee.sizes }

private def restoreRaised (caller : AState)
    (raised : RaisedFlow) : RaisedFlow :=
  {
    cases := raised.cases.map fun raisedCase =>
      { raisedCase with state := restoreCaller caller raisedCase.state }
  }

private def typedDictKeys (fields : List FieldDecl) : AbsVal :=
  fields.foldl
    (fun result field => result.join (strLitV field.name))
    AbsVal.bot

-- -------------------------------------------------------------- local scope

private partial def targetLocalNames : Target -> Fset String
  | .tname _ name => [name]
  | .ttuple _ targets =>
    targets.foldl
      (fun names target => Fset.union (targetLocalNames target) names) []
  | .tattr .. | .tsub .. => []

mutual
  private partial def statementLocalNames : Stmt -> Fset String
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

  private partial def bodyLocalNames (body : List Stmt) : Fset String :=
    body.foldl
      (fun names statement =>
        Fset.union (statementLocalNames statement) names) []
end

private def functionLocalNames (function : FuncDef) : Fset String :=
  Fset.union (function.params.map (·.name))
    (bodyLocalNames function.body)

/--CLAIM call-binds-positional-then-keyword: arguments bind positionally then
    by keyword; a duplicate, an unexpected keyword, and a missing parameter are
    each a `TypeError`.
-/
def compileUserCallRule (qualifiedName : String)
    (function : FuncDef) : UserCallRule :=
  {
    qualifiedName
    signature := {
      parameters := function.params.map fun parameter => {
        name := parameter.name
        kind := .positionalOrKeyword
        required := parameter.default.isNone
      }
    }
    parameters := function.params.map fun parameter => {
      name := parameter.name
      annotation := parameter.ann
      default := parameter.default
    }
    returnAnnotation := function.retAnn
    body := function.body
    locals := functionLocalNames function
    completion :=
      if function.isStub then .contractOnly
      else if function.isGen then .eagerGenerator else .ordinary
  }

private def enterCall (position : Pos) (rule : UserCallRule) : M Unit :=
  modify fun context => {
    context with
    callStack := rule.qualifiedName :: context.callStack
    localScopes := rule.locals :: context.localScopes
    ctxStack := s!"{rule.qualifiedName}:{position.line}" :: context.ctxStack
    -- The same frame, as a node path rather than a rendered line, so two calls on
    -- one source line are two contexts.
    ctxFrames :=
      (position.id, mixHash (ctxDigest context) position.id.digest)
        :: context.ctxFrames
  }

private def leaveCall : M Unit :=
  modify fun context => {
    context with
    callStack := context.callStack.drop 1
    localScopes := context.localScopes.drop 1
    ctxStack := context.ctxStack.drop 1
    ctxFrames := context.ctxFrames.drop 1
  }

-- --------------------------------------------------------- argument binding

private def bindParameters (position : Pos) (rule : UserCallRule)
    (arguments : List AbsVal) (keywords : List (String × AbsVal))
    (state : AState) : M (Except BindError (List (String × AbsVal))) := do
  let input : CallInput := { positional := arguments, keywords }
  match rule.signature.bind input with
  | .error error => pure (.error error)
  | .ok bound =>
    let mut environment : List (String × AbsVal) := []
    let context <- get
    for parameter in rule.parameters do
      let mut value := (bound.parameters.find? (·.1 == parameter.name))
        |>.map (·.2) |>.getD AbsVal.bot
      if value.isBot then
        match parameter.default with
        | some _ =>
          oblige position "default-arg"
            s!"{rule.qualifiedName}: parameter {parameter.name} takes its default"
          -- Defaults are evaluated once at definition time, but the current
          -- syntax stores only their expression, not the captured value.
          value := anyV
        | none => pure ()
      if let some annotation := parameter.annotation then
        -- Interface annotations are assume-guarantee: asserted at the call,
        -- assumed in the body. `assumeAnn` keeps the slice of the argument that
        -- satisfies the annotation, and that slice is what the body is analysed
        -- against -- which is what makes the analysis modular, one analysis per
        -- function rather than one per caller.
        --
        -- The slice that does *not* satisfy it aborts. That is a declared
        -- semantics, not a claim about CPython: CPython accepts the ill-typed
        -- argument and only raises later, if the body ever uses it in a way that
        -- raises. We stop at the call instead, because continuing would mean
        -- either believing the annotation of a value that violates it or
        -- widening the parameter back to what actually arrived, and the second
        -- gives up the modularity the annotation buys. Uncatchable, and never
        -- modelled as an edge, for the reason `uncatchableCategories` records.
        --
        -- Three outcomes, matching the three cases the caller can be in:
        --   entailed  -- nothing to prove
        --   partial   -- the good slice continues, the bad slice aborts
        --   disjoint  -- everything aborts, and the extra obligation says so,
        --                because a body analysed against bottom yields bottom
        --                and would make the rest of the caller vacuously fine
        let assumed := assumeAnn context.classes value annotation
        if !annEntailedDeep 16 context.classes state value annotation then
          if assumed.isBot && !value.isBot then
            oblige position "param-annotation-violated"
              s!"{rule.qualifiedName}: no value the caller can pass satisfies the annotation on {parameter.name}"
          else
            oblige position "param-annotation"
              s!"{rule.qualifiedName}: argument for {parameter.name} must satisfy its annotation"
          -- The `Exc` is discarded, and soundly: `contract` is absent from
          -- `policyCategories`, so `Policy.aborts` takes its fail-closed branch
          -- under every preset and `mraise` returns the input unchanged. The
          -- Lean suite pins that rather than leaving it incidental.
          let _ ← mraise position {} state ["TypeError"] (some "contract")
        value := assumed
      environment := environment ++ [(parameter.name, value.reduce)]
    pure (.ok environment)

-- -------------------------------------------------------------- completions

private def joinedCompletionState (completion : Completion) : Option AState :=
  Id.run do
    let mut state := completion.normal
    if let some (_, returnedState) := completion.returned then
      state := joinOpt state (some returnedState)
    state := joinOpt state completion.broke
    state := joinOpt state completion.continued
    for raised in completion.raised.cases do
      state := joinOpt state (some raised.state)
    return state

private def normalFunctionResult (caller : AState)
    (completion : Completion) : Option Normal :=
  let fellThrough := completion.normal.map fun state =>
    (V [.tnone], restoreCaller caller state)
  let returned := completion.returned.map fun (value, state) =>
    (value, restoreCaller caller state)
  joinNormal fellThrough returned

private def finishFunction (position : Pos) (rule : UserCallRule)
    (caller : AState)
    (completion : Completion) : M Flow := do
  if completion.broke.isSome then
    oblige position "invalid-completion"
      s!"{rule.qualifiedName}: break escaped the function body"
  if completion.continued.isSome then
    oblige position "invalid-completion"
      s!"{rule.qualifiedName}: continue escaped the function body"
  let raised := restoreRaised caller completion.raised
  match normalFunctionResult caller completion with
  | none => pure { raised }
  | some (rawValue, normalState) =>
    let mut value := rawValue
    if let some annotation := rule.returnAnnotation then
      let context <- get
      if !annEntailedDeep 16 context.classes normalState value annotation then
        oblige position "return-annotation"
          s!"{rule.qualifiedName}: returned value must satisfy the return annotation"
      value := assumeAnn context.classes value annotation
    pure {
      normal := (Flow.ofNormal value normalState).normal
      raised
    }

-- ---------------------------------------------------------- recursion calls

private def recursionValue (rule : UserCallRule) : M AbsVal := do
  match rule.returnAnnotation with
  | none => pure anyV
  | some annotation =>
    let context <- get
    match annTags context.classes annotation with
    | none => pure anyV
    | some tags =>
      let value := (V tags).reduce
      if value.isBot && !tags.isEmpty then
        pure anyV
      else if tags.any (fun tag => tag.isRef) then
        -- The annotation tag alone has no allocation witness.
        pure anyV
      else
        pure value

-- -------------------------------------------------------------- generators

private def recordGeneratorExceptions (site : NodeId)
    (classes : Fset String) : M Unit :=
  modify fun context => {
    context with
    genExc :=
      match context.genExc.find? (·.1 == site) with
      | some _ =>
        context.genExc.map fun (oldSite, oldClasses) =>
          if oldSite == site then
            (oldSite, Fset.union classes oldClasses)
          else
            (oldSite, oldClasses)
      | none => context.genExc ++ [(site, classes)]
  }

private def finishGenerator (position : Pos) (qualifiedName : String)
    (caller : AState) (completion : Completion)
    (yielded : List AbsVal) : M Flow := do
  let element := yielded.foldl AbsVal.join AbsVal.bot
  let bodyState := (joinedCompletionState completion).getD caller
  let postBody : AState :=
    { env := caller.env, heap := bodyState.heap
      sizes := bodyState.sizes }
  let (generator, allocated) := allocate postBody position.id .gen []
  let location : Loc :=
    { site := position.id, cls := .gen, recent := true }
  let initialized := allocated.heapSet location .elem element
  recordGeneratorExceptions position.id
    (excsAfterGen completion.raised.classes)
  oblige position "special-method"
    s!"generator {qualifiedName} analyzed eagerly: suspension interleaving asserted away"
  pure (Flow.ofNormal generator initialized)

-- ------------------------------------------------------------ rule planning

def builtinExceptionRule
    (className : String) : BuiltinExceptionConstructionRule :=
  {
    className
    signature := { varPos := true }
  }

def typedDictRule (info : ClassInfo) : TypedDictConstructionRule :=
  {
    name := info.name
    signature := {
      parameters := [{
        name := "mapping"
        kind := .positionalOnly
        required := false
      }]
      varKw := true
    }
    fields := info.fields
  }

def compileConstructionRule (className : String) : M ConstructionRule := do
  let context <- get
  match context.classes.getCls? className with
  | none =>
    if builtinExcs.contains className then
      pure (.builtinException (builtinExceptionRule className))
    else
      pure (.unresolved className)
  | some info =>
    if info.isTypedDict then
      pure (.typedDict (typedDictRule info))
    else
      let resolved <- resolveMethodM className "__init__"
      let initializer := resolved.map fun (owner, function) => {
        owner
        call := compileUserCallRule s!"{owner}.__init__" function
        requiresNoneReturn := true
      }
      pure (.userClass {
        name := className
        layout := info.layout
        frozenDataclass := info.isDataclass
        initializer
        fallbackSignature := if info.isExc then { varPos := true } else {}
      })

def compileValueDispatchRule (description : String)
    (callee : AbsVal) : M ValueDispatchRule := do
  let context <- get
  let mut rows : List DispatchRow := []
  for tag in callee.tags do
    match tag with
    | .tfunc =>
      for functionName in callee.funcs do
        let outcome := match context.funcs.find? (·.1 == functionName) with
          | some (_, function) =>
            DispatchOutcome.userCall
              (compileUserCallRule functionName function)
          | none => .deferred s!"unresolved function {functionName}"
        rows := rows ++ [{ selector := "func", outcome }]
    | .ttype =>
      for className in callee.classes do
        rows := rows ++ [{
          selector := s!"type:{className}"
          outcome := .construct (<- compileConstructionRule className)
        }]
    | .tany =>
      rows := rows ++ [{
        selector := "any"
        outcome := .deferred "unknown callable"
      }]
    | .tunbound | .tuninit =>
      rows := rows ++ [{ selector := tag.render, outcome := .inert }]
    | _ =>
      rows := rows ++ [{ selector := tag.render, outcome := .typeError }]
  pure { description, rows }

private def dispatchOutcomeText : DispatchOutcome -> String
  | .userCall rule => rule.qualifiedName
  | .construct (.builtinException rule) =>
    s!"construct {rule.className}"
  | .construct (.typedDict rule) => s!"construct {rule.name}"
  | .construct (.userClass rule) => s!"construct {rule.name}"
  | .construct (.unresolved className) =>
    s!"construct unresolved {className}"
  | .deferred _ => "deferred"
  | .typeError => "!TypeError"
  | .inert => "inert"

-- ----------------------------------------------------------- generic engine

private def checkInitializedFields (position : Pos)
    (rule : ClassConstructionRule) (location : Loc)
    (state : AState) : M Unit := do
  for field in rule.layout do
    let value := state.heapGet location (.field field)
    if Tag.tuninit ∈ value.tags then
      if (value.withoutTags [.tuninit]).isBot then
        oblige position "init-missing"
          s!"{rule.name}.{field}: no path through __init__ initializes this field"
      else
        oblige position "init-conditional"
          s!"{rule.name}.{field}: some path through __init__ leaves this field uninitialized"

mutual
  /-- Generic interpreter for closed call, construction, and dispatch rules. -/
  partial def execute (services : Services) (position : Pos)
      (rule : Rule) (input : Input) (state : AState) : M Flow := do
    match rule with
    | .userCall call =>
      executeUserCall services position call input state
    | .construct construction =>
      executeConstruction services position construction input state
    | .dispatch dispatch =>
      executeDispatch services position dispatch input state

  private partial def executeUserCall (services : Services) (position : Pos)
      (rule : UserCallRule) (input : Input) (state : AState) : M Flow := do
    markCalled rule.qualifiedName
    let bound <- bindParameters position rule input.arguments input.keywords state
    let .ok environment := bound
      | resCase position "call" s!"{rule.qualifiedName}(...)"
          "signature" "!TypeError"
        return <- machineRaise position "TypeError" state
    let context <- get
    if context.callStack.contains rule.qualifiedName then
      -- Fail closed. `Syntax/Check.lean` rejects the cycles it can see, so this
      -- only fires for one reached through a computed callee. Assuming the
      -- declared return annotation here was optimistic in three ways at once:
      -- it assumed the deeper levels raise nothing, write nothing, and return
      -- something the annotation covers. Measured, all three are false --
      -- `../doc/RECURSION_CONTRACTS.md` has the cases.
      oblige position "recursion-unsupported"
        s!"recursive re-entry of {rule.qualifiedName} through a computed callee: no checked contract exists to summarise it"
      resCase position "call" s!"{rule.qualifiedName}(...)" "func" "!recursion"
      return <- machineRaise position "RecursionError" state
    if rule.completion == .contractOnly then
      -- The arguments were bound and their annotations checked above; there is no
      -- body to enter. `recursionValue` is the same "assume the declared return
      -- annotation" step the recursion cut-off uses, which is exactly what a
      -- contract-only call means.
      resCase position "call" s!"{rule.qualifiedName}(...)" "func" "contract only"
      oblige position "stub-contract"
        s!"{rule.qualifiedName} has no body: its declared types are assumed"
      return Flow.ofNormal (<- recursionValue rule) state
    enterCall position rule
    -- `bindParameters` builds the frame as an ordered list, because binding order
    -- is part of the signature; the state stores it as a map.
    let calleeState : AState :=
      { env := environment.foldl
          (init := ({} : Std.HashMap String AbsVal))
          (fun acc (name, value) => acc.insert name value)
        heap := state.heap, sizes := state.sizes }
    match rule.completion with
    | .eagerGenerator =>
      modify fun current => { current with yields := [] :: current.yields }
      let completion <- services.executeBody rule.body calleeState
      let afterBody <- get
      let yielded := afterBody.yields.headD []
      modify fun current => { current with yields := current.yields.drop 1 }
      leaveCall
      finishGenerator position rule.qualifiedName state completion yielded
    | .ordinary =>
      let completion <- services.executeBody rule.body calleeState
      leaveCall
      finishFunction position rule state completion
    | .contractOnly =>
      -- Unreachable: taken before `enterCall` above. Kept so the match is total
      -- and fail-closed, rather than relying on that ordering staying true.
      leaveCall
      pure (Flow.ofNormal (<- recursionValue rule) state)

  private partial def executeTypedDict (position : Pos)
      (rule : TypedDictConstructionRule) (input : Input)
      (state : AState) : M Flow := do
    match rule.signature.bind {
        positional := input.arguments
        keywords := input.keywords
      } with
    | .error _ =>
      resCase position "call" s!"{rule.name}(...)" "signature" "!TypeError"
      return <- machineRaise position "TypeError" state
    | .ok _ => pure ()
    let hasPositionalMapping := !input.arguments.isEmpty
    let mut delayedRaises : RaisedFlow := {}
    if !input.arguments.isEmpty then
      oblige position "mapping-constructor"
        s!"{rule.name} positional mapping values are widened to the declared field contracts"
      oblige position "shape-contract"
        s!"{rule.name} positional mapping contains only declared keys"
      delayedRaises := (<- machineRaise position "TypeError" state).raised
    let (value, allocated) :=
      allocate state position.id (.td rule.name) []
    let location : Loc :=
      { site := position.id, cls := .td rule.name, recent := true }
    let mut outputState := allocated
    let mut joinedValues := AbsVal.bot
    let context <- get
    for field in rule.fields do
      let stored <- match input.keywords.find? (·.1 == field.name) with
        | some (_, argument) => do
          if let some annotation := field.ann then
            if !annEntailedDeep 16 context.classes outputState
                argument annotation then
              oblige position "type-error"
                s!"{rule.name}.{field.name}: value does not satisfy the declared type"
          pure <| match field.ann with
            | some annotation =>
              assumeAnn context.classes argument annotation
            | none => argument
        | none => do
          if field.required then
            oblige position "key-membership"
              s!"{rule.name} construction misses required key {field.name}"
          pure <| if field.required then
            match field.ann with
            | some annotation =>
              assumeAnn context.classes anyV annotation
            | none => anyV
          else if hasPositionalMapping then
            anyV.join (V [.tmissing])
          else
            V [.tmissing]
      outputState := outputState.heapSet location (.literalKey field.name) stored
      joinedValues := joinedValues.join (stored.withoutTags [.tmissing])
    for (key, _) in input.keywords do
      if !(rule.fields.any (·.name == key)) then
        oblige position "attr-missing"
          s!"{rule.name} construction passes undeclared key {key}"
    outputState :=
      (outputState.heapSet location .dictKeys (typedDictKeys rule.fields))
        |>.heapSet location .dictValues joinedValues
    pure {
      (Flow.ofNormal value outputState) with
      raised := delayedRaises
    }

  private partial def executeUserClass (services : Services) (position : Pos)
      (rule : ClassConstructionRule) (input : Input)
      (state : AState) : M Flow := do
    let (objectValue, allocated) :=
      allocate state position.id (.obj rule.name) rule.layout
    let location : Loc :=
      { site := position.id, cls := .obj rule.name, recent := true }
    match rule.initializer with
    | none =>
      match rule.fallbackSignature.bind {
          positional := input.arguments
          keywords := input.keywords
        } with
      | .error _ =>
        resCase position "call" s!"{rule.name}(...)"
          "object.__init__ signature" "!TypeError"
        return <- machineRaise position "TypeError" allocated
      | .ok _ => pure ()
      for field in rule.layout do
        oblige position "init-missing"
          s!"{rule.name}.{field}: class has no __init__"
      pure (Flow.ofNormal objectValue allocated)
    | some initializer =>
      let called <- execute services position (.userCall initializer.call) {
        arguments := objectValue :: input.arguments
        keywords := input.keywords
      } allocated
      let mut result : Flow := { raised := called.raised }
      if let some (initializerResult, initialized) := called.normal then
        let mayReturnNone :=
          Tag.tnone ∈ initializerResult.tags ||
            Tag.tany ∈ initializerResult.tags
        let mayReturnOther :=
          Tag.tany ∈ initializerResult.tags ||
            !(initializerResult.withoutTags [.tnone]).isBot
        if !initializer.requiresNoneReturn || mayReturnNone then
          checkInitializedFields position rule location initialized
          result := {
            result with
            normal := (Flow.ofNormal objectValue initialized).normal
          }
        if initializer.requiresNoneReturn && mayReturnOther then
          resCase position "call" s!"{rule.name}(...)" "__init__ return"
            "!TypeError"
          result := result.join
            (<- machineRaise position "TypeError" initialized)
      pure result

  private partial def executeConstruction (services : Services)
      (position : Pos) (rule : ConstructionRule) (input : Input)
      (state : AState) : M Flow := do
    match rule with
    | .builtinException exceptionRule =>
      match exceptionRule.signature.bind {
          positional := input.arguments
          keywords := input.keywords
        } with
      | .error _ =>
        resCase position "call" s!"{exceptionRule.className}(...)"
          "signature" "!TypeError"
        return <- machineRaise position "TypeError" state
      | .ok _ => pure ()
      let (value, outputState) :=
        allocate state position.id (.obj exceptionRule.className) []
      pure (Flow.ofNormal value outputState)
    | .typedDict typedDict =>
      executeTypedDict position typedDict input state
    | .userClass userClass =>
      executeUserClass services position userClass input state
    | .unresolved className =>
      oblige position "dispatch-any"
        s!"construction of unresolved class {className}"
      pure (Flow.ofNormal anyV state)

  private partial def executeDispatch (services : Services) (position : Pos)
      (rule : ValueDispatchRule) (input : Input)
      (state : AState) : M Flow := do
    let mut result : Flow := {}
    for row in rule.rows do
      resCase position "call" rule.description row.selector
        (dispatchOutcomeText row.outcome)
      match row.outcome with
      | .userCall call =>
        result := result.join
          (<- execute services position (.userCall call) input state)
      | .construct construction =>
        result := result.join
          (<- execute services position (.construct construction) input state)
      | .deferred detail =>
        oblige position "dispatch-any" s!"call of {detail}"
        result := result.join (Flow.ofNormal anyV state)
      | .typeError =>
        result := result.join (<- machineRaise position "TypeError" state)
      | .inert => pure ()
    pure result
end

-- --------------------------------------------------------------- entry APIs

/-- Invoke a top-level function or an already-resolved user method. Method
    callers prepend the receiver to `arguments`, so both use one rule form. -/
def invokeUser (services : Services) (position : Pos)
    (qualifiedName : String) (function : FuncDef)
    (arguments : List AbsVal) (keywords : List (String × AbsVal))
    (state : AState) : M Flow :=
  execute services position
    (.userCall (compileUserCallRule qualifiedName function))
    { arguments, keywords } state

def constructBuiltinException (services : Services) (position : Pos)
    (className : String) (state : AState) : M Flow :=
  execute services position
    (.construct (.builtinException (builtinExceptionRule className))) {} state

def constructTypedDict (services : Services) (position : Pos)
    (info : ClassInfo) (arguments : List AbsVal)
    (keywords : List (String × AbsVal)) (state : AState) : M Flow :=
  execute services position
    (.construct (.typedDict (typedDictRule info)))
    { arguments, keywords } state

/--CLAIM call-constructs-instance: calling a class runs `__init__` under its
    own signature and yields an instance.
-/
def constructClass (services : Services) (position : Pos)
    (className : String) (arguments : List AbsVal)
    (keywords : List (String × AbsVal)) (state : AState) : M Flow := do
  execute services position (.construct (<- compileConstructionRule className))
    { arguments, keywords } state

def invokeValue (services : Services) (position : Pos)
    (description : String) (callee : AbsVal)
    (arguments : List AbsVal) (keywords : List (String × AbsVal))
    (state : AState) : M Flow := do
  execute services position
    (.dispatch (<- compileValueDispatchRule description callee))
    { arguments, keywords } state

/-
Current representation boundaries:

* `Param` does not retain positional-only versus positional-or-keyword syntax;
  varargs and keyword-only parameters are rejected by admission.
* A default stores its source expression, not its definition-time value or
  effects, so an omitted default is explicitly widened to `any`.
* Recursive re-entry has only a return annotation. Precise recursive heap
  effects and escaping exceptions require effect/escape contracts.
* Eager generator summaries retain yielded values and exception classes, but
  `Actx.genExc` has no slot for per-exception values or raise-point states and
  cannot represent suspension interleavings.
* A TypedDict positional mapping is conservatively widened to declared fields,
  optional presence, and a possible TypeError; its iterable/mapping protocol
  is not yet executed key by key.
* Builtin exception instances currently retain identity and class only, not
  the concrete `.args` tuple.
-/

end Pylate.RuleDriven.Calls
