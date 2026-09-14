/-
Reusable runtime contracts for the rule interpreter.

Contracts are closed, first-order data. Their executor owns tag splitting,
protocol ordering, result validation, and failure routing. Operations that
depend on the enclosing Python interpreter cross the explicit Services
boundary: MRO lookup, admitted user-function invocation, unknown-value
protocol effects, and recursive source-annotation checking.

The normal value is the value produced by the contract:

* predicate contracts return the accepted input partition;
* SupportsIndex returns int;
* Iterable returns the iterator selected or allocated by the protocol;
* MappingOrIterablePairs returns the destination populated in source order;
* RecursiveAnnotation returns exactly the value supplied by its service.
-/
import Pylate.RuleLang.Plan

namespace Pylate.RuleDriven.Contracts

open Pylate
open Pylate.RuleDriven

-- --------------------------------------------------------------- contracts

-- `ArgContract`, `ContractArgument`, and `ContractArguments` are rule data and
-- live in `RulePlan`; this module is their executor.

/-- Named protocol sites used only when the incoming abstract value contains
    `any`. The service's normal value is the protocol-hook result; its raised
    cases retain exact post-hook states. The executor separately includes
    effect-free builtin success and failure alternatives. -/
inductive UnknownProtocol
  | supportsIndex
  | iterable
  | hashable
deriving Repr, Inhabited, BEq

def UnknownProtocol.label : UnknownProtocol -> String
  | .supportsIndex => "__index__"
  | .iterable => "__iter__"
  | .hashable => "__hash__"

inductive MappingRoute
  | mapping
  | iterablePairs
  | unknown
deriving Repr, Inhabited, BEq

def MappingRoute.label : MappingRoute -> String
  | .mapping => "mapping keys/getitem"
  | .iterablePairs => "iterable pairs"
  | .unknown => "unknown mapping-or-pairs"

structure MappingTarget where
  value : AbsVal
deriving Repr, Inhabited

structure MappingRequest where
  route  : MappingRoute
  source : AbsVal
  target : MappingTarget
deriving Repr, Inhabited

structure Services where
  classInfo : String -> M (Option ClassInfo)
  resolveMethod : String -> String -> M (Option (String × FuncDef))
  invokeUser : Pos -> String -> FuncDef -> List AbsVal ->
    List (String × AbsVal) -> AState -> M Flow
  unknownProtocol : Pos -> UnknownProtocol -> AbsVal -> AState -> M Flow
  /-- Truth conversion of one value, retaining hook effects and exceptions. -/
  truthValue : Pos -> AbsVal -> AState -> M Flow
  /-- Consume an iterable for its effects, optionally checking each element.
      Normal completion is iterator exhaustion. -/
  consumeElements : Pos -> AbsVal ->
    Option (Pos -> AbsVal -> AState -> M Flow) -> AState -> M Flow
  /-- Invoke a callable argument with `arity` unknown arguments, retaining its
      effects and exceptions. -/
  invokeCallable : Pos -> AbsVal -> Nat -> AState -> M Flow
  /-- Consume a mapping or iterable of pairs into an explicit destination.
      This is the trusted boundary for keys()/getitem, iter/next, pair arity,
      key hashing/equality, and partial destination mutation. It must return
      the request target on normal completion. Pair arity is checked before
      hashing that pair; every raise state retains earlier successful writes
      and the failing operation's own effects. -/
  consumeMappingPairs : Pos -> MappingRequest -> AState -> M Flow
  /-- Annotation contracts are proof boundaries, not Python runtime checks.
      A caller typically asserts the recursive annotation and returns its
      assume-refined value normally; it must not fabricate Python TypeError. -/
  recursiveAnnotation : Pos -> Ann -> AbsVal -> AState -> M Flow

-- Canonical contracts used by several rule families.

def literalElement : ArgContract := .hashable
def sequenceIndex : ArgContract := .supportsIndex
def typedDictKey : ArgContract := .hashable
def unpackSource : ArgContract := .iterable
def callback : ArgContract := .callableOrNone
def mappingSource : ArgContract := .mappingOrIterablePairs

-- --------------------------------------------------------------- utilities

private def inertTag : Tag -> Bool
  | .tunbound | .tuninit | .tmissing => true
  | _ => false

private def expandedRuntimeTags (tags : Fset Tag) : Fset Tag :=
  let tags :=
    if Tag.tcomplex ∈ tags then
      Fset.insert Tag.tfloat (Fset.insert Tag.tint tags)
    else tags
  let tags :=
    if Tag.tfloat ∈ tags then Fset.insert Tag.tint tags else tags
  if Tag.tint ∈ tags then Fset.insert Tag.tbool tags else tags

private def onlyTag (value : AbsVal) (tag : Tag) : AbsVal :=
  value.restrictTags [tag]

private def tupleAt (value : AbsVal) (location : Loc) : AbsVal :=
  { value with tags := [.ttuple], locs := [location] } |>.reduce

private def objectAt (value : AbsVal) (className : String)
    (location : Loc) : AbsVal :=
  { value with tags := [.tobj className], locs := [location] } |>.reduce

private def tupleSlots (state : AState) (location : Loc) : List AbsVal :=
  let count := state.tupleSlotCount location
  (List.range count).map fun index =>
    state.heapGet location (.tupleSlot index)

private def tupleChecks (state : AState) (location : Loc) : List AbsVal :=
  let slots := tupleSlots state location
  if slots.isEmpty then
    let elements := state.heapGet location .elem
    if elements.isBot then [] else [elements]
  else slots

private def tupleMayBeEmpty (state : AState) (location : Loc) : Bool :=
  (tupleSlots state location).isEmpty &&
    state.emptinessGet location != .nonempty

private def iteratorResult (position : Pos) (source : AbsVal)
    (state : AState) : AbsVal × AState :=
  if source.tags == [.tgen] then
    (source, state)
  else
    let (iterator, allocated) := allocate state position.id .gen []
    let location : Loc := ⟨position.id, .gen, true⟩
    let initialized :=
      allocated.heapSet location .elem (elemOf state source)
    let initialized :=
      if !source.locs.isEmpty &&
          source.locs.all (fun sourceLocation =>
            state.emptinessGet sourceLocation == .nonempty) then
        strongEmptinessUpdate initialized location .nonempty
      else initialized
    (iterator, initialized)

private def machineTypeError (position : Pos) (state : AState) : M Flow :=
  executeRaise position (RaiseSpec.machine "TypeError") {} state

private def machineValueError (position : Pos) (state : AState) : M Flow :=
  executeRaise position (RaiseSpec.machine "ValueError") {} state

private def addTypeError (position : Pos) (flow : Flow)
    (state : AState) : M Flow := do
  pure (flow.join (← machineTypeError position state))

/-- Only contract failures reach the residual table: an accepted argument is
    not a dispatch alternative of the enclosing call and must not change its
    devirtualization status. The tag is namespaced by argument path so the row
    is not read as a receiver tag. -/
private def record (position : Pos) (contract path tag outcome : String) :
    M Unit :=
  if outcome.startsWith "!" then
    resCase position "contract" s!"{path}: {contract}" s!"{path}:{tag}" outcome
  else pure ()

private def recordFailure (position : Pos) (contract path tag : String) :
    M Unit :=
  record position contract path tag "!TypeError"

private def recordRaised (position : Pos) (contract path tag : String)
    (raised : RaisedFlow) : M Unit := do
  for raisedCase in raised.cases do
    record position contract path tag s!"!{raisedCase.cls}"

private def scalarMaterialization (tags : Fset Tag) : AbsVal :=
  if tags.any Tag.isRef then anyV else V tags

private def flowWithRaised (normal : Option Normal)
    (raised : RaisedFlow) : Flow :=
  { normal, raised }

-- ---------------------------------------------------------- result checking

private partial def validateIndexResult (_services : Services)
    (position : Pos) (path : String) (result : AbsVal)
    (state : AState) : M Flow := do
  let mut output : Flow := {}
  let valid := result.restrictTags [.tbool, .tint]
  if !valid.isBot then
    output := output.join (Flow.ofNormal (V [.tint]) state)
  let invalid := result.withoutTags [.tbool, .tint]
  if !invalid.isBot then
    recordFailure position "SupportsIndex" path
      (invalid.tags.map Tag.render |> "|".intercalate)
    output ← addTypeError position output state
  if Tag.tany ∈ result.tags then
    oblige position "dispatch-any"
      "unknown __index__ result is split into int and TypeError"
    output := output.join (Flow.ofNormal (V [.tint]) state)
    output ← addTypeError position output state
  pure output

private partial def validateIteratorResult (services : Services)
    (position : Pos) (path : String) (result : AbsVal)
    (state : AState) : M Flow := do
  let mut output : Flow := {}
  for tag in result.tags do
    match tag with
    | .tgen =>
      output := output.join
        (Flow.ofNormal (onlyTag result tag) state)
    | .tobj className =>
      if (← services.resolveMethod className "__next__").isSome then
        output := output.join
          (Flow.ofNormal (onlyTag result tag) state)
      else
        recordFailure position "Iterable" path tag.render
        output ← addTypeError position output state
    | .tany =>
      oblige position "dispatch-any"
        "unknown __iter__ result is split into iterator and TypeError"
      output := output.join (Flow.ofNormal anyV state)
      output ← addTypeError position output state
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      recordFailure position "Iterable" path tag.render
      output ← addTypeError position output state
  pure output

private partial def validateHashResult (_services : Services)
    (position : Pos) (path : String) (accepted result : AbsVal)
    (state : AState) : M Flow := do
  let mut output : Flow := {}
  let valid := result.restrictTags [.tbool, .tint]
  if !valid.isBot then
    output := output.join (Flow.ofNormal accepted state)
  let invalid := result.withoutTags [.tbool, .tint]
  if !invalid.isBot then
    recordFailure position "Hashable" path
      (invalid.tags.map Tag.render |> "|".intercalate)
    output ← addTypeError position output state
  if Tag.tany ∈ result.tags then
    oblige position "dispatch-any"
      "unknown __hash__ result is split into int and TypeError"
    output := output.join (Flow.ofNormal accepted state)
    output ← addTypeError position output state
  pure output

-- --------------------------------------------------------------- execution

mutual

partial def executeFuel (services : Services) (fuel : Nat)
    (position : Pos) (contract : ArgContract) (value : AbsVal)
    (state : AState) (path : String) : M Flow := do
  if value.isBot then return {}
  match contract with
  | .any =>
    record position contract.label path
      (value.tags.map Tag.render |> "|".intercalate) "accept"
    pure (Flow.ofNormal value state)
  | .runtimeTags tags =>
    executeRuntimeTags services position tags value state path
  | .optional inner =>
    executeOptional services fuel position inner value state path
  | .supportsIndex =>
    executeSupportsIndex services position value state path
  | .iterable => do
    -- Acquire the iterator, then run it: `__next__` executes during the
    -- operation, so its effects and exceptions belong to this call.
    let acquired ← executeIterable services position value state path
    match acquired.normal with
    | none => pure acquired
    | some (iterator, iteratorState) =>
      let consumed ←
        services.consumeElements position iterator none iteratorState
      pure {
        normal := consumed.normal.map fun (_, postState) =>
          (iterator, postState)
        raised := acquired.raised.join consumed.raised
      }
  | .hashable =>
    executeHashable services fuel position value state path
  | .string =>
    executeString services position value state path
  | .stringOrTupleOfStrings =>
    executeStringOrTuple services fuel position value state path
  | .callableOrNone =>
    executeCallableOrNone services position value state path
  | .mappingOrIterablePairs | .mappingPairsInto =>
    executeMappingFresh services position value state path
  | .iterableOf inner => do
    let mut summaryRaised : RaisedFlow := {}
    let acquired ← executeIterable services position value state path
    match acquired.normal with
    | none => pure acquired
    | some (iterator, iteratorState) =>
      let consumed ← services.consumeElements position iterator
        (some (fun elementPosition element elementState =>
          executeFuel services fuel elementPosition inner element elementState
            s!"{path}.element")) iteratorState
      -- The element summary is also checked directly: a source whose iterator
      -- state is only summarised must still fail on an invalid element.
      let summary := elemOf iteratorState value
      if !summary.isBot then
        let checked ← executeFuel services fuel position inner summary
          iteratorState s!"{path}.element"
        summaryRaised := checked.raised
      pure {
        normal := consumed.normal.map fun (_, postState) =>
          (iterator, postState)
        raised := acquired.raised.join
          (consumed.raised.join summaryRaised)
      }
  | .setElement => do
    -- `set.remove({1})` is a frozenset lookup, not a hashing failure.
    let sets := value.restrictTags [.tset]
    let rest := value.withoutTags [.tset]
    let mut output : Flow := {}
    if !sets.isBot then
      record position "SetElement" path "set" "frozenset lookup"
      output := output.join (Flow.ofNormal sets state)
    if !rest.isBot then
      output := output.join
        (← executeHashable services fuel position rest state path)
    pure output
  | .truthValue => do
    record position "TruthValue" path
      (value.tags.map Tag.render |> "|".intercalate) "bool"
    services.truthValue position value state
  | .invokesHook method => do
    -- Only a user object can carry the hook; every other value accepts.
    let mut output : Flow := {}
    let mut plain : AbsVal := AbsVal.bot
    for tag in value.tags do
      match tag with
      | .tobj className =>
        match ← services.resolveMethod className method with
        | some (owner, function) =>
          record position (ArgContract.invokesHook method).label path
            tag.render s!"{owner}.{method}"
          -- Every parameter after `self` is unknown at this boundary.
          let extra := (function.params.drop 1).map (fun _ => anyV)
          let called ← services.invokeUser position s!"{owner}.{method}"
            function (onlyTag value tag :: extra) [] state
          recordRaised position (ArgContract.invokesHook method).label path
            tag.render called.raised
          output := output.join {
            normal := called.normal.map fun (_, postState) =>
              (onlyTag value tag, postState)
            raised := called.raised
          }
        | none => plain := plain.join (onlyTag value tag)
      | .tany =>
        oblige position "dispatch-any"
          s!"unknown value may define {method}"
        output := output.join
          (← services.unknownProtocol position .supportsIndex value state)
        plain := plain.join (onlyTag value tag)
      | _ => plain := plain.join (onlyTag value tag)
    if !plain.isBot then
      output := output.join (Flow.ofNormal plain state)
    pure output
  | .fillCharacter =>
    executeFillCharacter services position value state path
  | .separatorString kind =>
    executeSeparatorString services position kind value state path
  | .recursiveAnnotation annotation =>
    record position contract.label path
      (value.tags.map Tag.render |> "|".intercalate) "proof boundary"
    services.recursiveAnnotation position annotation value state

partial def executeRuntimeTags (_services : Services) (position : Pos)
    (accepted : Fset Tag) (value : AbsVal) (state : AState)
    (path : String) : M Flow := do
  let accepted := expandedRuntimeTags accepted
  let mut output : Flow := {}
  for tag in value.tags do
    if tag ∈ accepted then
      record position (ArgContract.runtimeTags accepted).label path
        tag.render "accept"
      output := output.join (Flow.ofNormal (onlyTag value tag) state)
    else
      match tag with
      | .tany =>
        oblige position "dispatch-any"
          s!"unknown value checked against {(ArgContract.runtimeTags accepted).label}"
        record position (ArgContract.runtimeTags accepted).label path
          "any" "accept | TypeError"
        output := output.join
          (Flow.ofNormal (scalarMaterialization accepted) state)
        recordFailure position (ArgContract.runtimeTags accepted).label
          path "any"
        output ← addTypeError position output state
      | _ =>
        if !inertTag tag then
          recordFailure position (ArgContract.runtimeTags accepted).label
            path tag.render
          output ← addTypeError position output state
  pure output

partial def executeOptional (services : Services) (fuel : Nat)
    (position : Pos) (inner : ArgContract) (value : AbsVal)
    (state : AState) (path : String) : M Flow := do
  let mut output : Flow := {}
  if Tag.tnone ∈ value.tags then
    record position (ArgContract.optional inner).label path "none" "accept"
    output := output.join
      (Flow.ofNormal (onlyTag value .tnone) state)
  if Tag.tany ∈ value.tags then
    -- `any` may denote None independently of the inner-contract branch.
    output := output.join (Flow.ofNormal (V [.tnone]) state)
  let remainder := value.withoutTags [.tnone]
  if !remainder.isBot then
    output := output.join
      (← executeFuel services fuel position inner remainder state
        s!"{path}.some")
  pure output

partial def executeSupportsIndex (services : Services) (position : Pos)
    (value : AbsVal) (state : AState) (path : String) : M Flow := do
  let mut output : Flow := {}
  for tag in value.tags do
    match tag with
    | .tbool | .tint =>
      record position "SupportsIndex" path tag.render "builtin int"
      output := output.join (Flow.ofNormal (V [.tint]) state)
    | .tobj className =>
      let accepted := onlyTag value tag
      match ← services.resolveMethod className "__index__" with
      | none =>
        recordFailure position "SupportsIndex" path tag.render
        output ← addTypeError position output state
      | some (owner, function) =>
        record position "SupportsIndex" path tag.render
          s!"{owner}.__index__"
        let called ← services.invokeUser position
          s!"{owner}.__index__" function [accepted] [] state
        recordRaised position "SupportsIndex" path tag.render called.raised
        output := { output with
          raised := output.raised.join called.raised }
        if let some (result, postState) := called.normal then
          output := output.join
            (← validateIndexResult services position
              s!"{path}.__index__.result" result postState)
    | .tany =>
      oblige position "dispatch-any"
        "SupportsIndex on an unknown value"
      record position "SupportsIndex" path "any" "deferred"
      output := output.join (Flow.ofNormal (V [.tint]) state)
      recordFailure position "SupportsIndex" path "any"
      output ← addTypeError position output state
      let hooked ← services.unknownProtocol position
        .supportsIndex (onlyTag value tag) state
      recordRaised position "SupportsIndex" path "any" hooked.raised
      output := { output with
        raised := output.raised.join hooked.raised }
      if let some (result, postState) := hooked.normal then
        output := output.join
          (← validateIndexResult services position
            s!"{path}.unknown.__index__.result" result postState)
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      recordFailure position "SupportsIndex" path tag.render
      output ← addTypeError position output state
  pure output

partial def executeIterable (services : Services) (position : Pos)
    (value : AbsVal) (state : AState) (path : String) : M Flow := do
  let mut output : Flow := {}
  for tag in value.tags do
    match tag with
    | .tlist | .ttuple | .tdict | .tdictkeys | .tdictitems
    | .tdictvalues | .tset | .tstr | .trange | .tgen =>
      record position "Iterable" path tag.render "builtin __iter__"
      let (iterator, postState) :=
        iteratorResult position (onlyTag value tag) state
      output := output.join (Flow.ofNormal iterator postState)
    | .tobj className =>
      let accepted := onlyTag value tag
      match ← services.resolveMethod className "__iter__" with
      | some (owner, function) =>
        record position "Iterable" path tag.render
          s!"{owner}.__iter__"
        let called ← services.invokeUser position
          s!"{owner}.__iter__" function [accepted] [] state
        recordRaised position "Iterable" path tag.render called.raised
        output := { output with
          raised := output.raised.join called.raised }
        if let some (iterator, postState) := called.normal then
          output := output.join
            (← validateIteratorResult services position
              s!"{path}.__iter__.result" iterator postState)
      | none =>
        match ← services.resolveMethod className "__getitem__" with
        | some (owner, _) =>
          record position "Iterable" path tag.render
            s!"sequence iterator via {owner}.__getitem__"
          let (iterator, postState) :=
            iteratorResult position anyV state
          output := output.join (Flow.ofNormal iterator postState)
        | none =>
          recordFailure position "Iterable" path tag.render
          output ← addTypeError position output state
    | .tany =>
      oblige position "dispatch-any" "Iterable on an unknown value"
      record position "Iterable" path "any" "deferred"
      output := output.join (Flow.ofNormal anyV state)
      recordFailure position "Iterable" path "any"
      output ← addTypeError position output state
      let hooked ← services.unknownProtocol position
        .iterable (onlyTag value tag) state
      recordRaised position "Iterable" path "any" hooked.raised
      output := { output with
        raised := output.raised.join hooked.raised }
      if let some (iterator, postState) := hooked.normal then
        output := output.join
          (← validateIteratorResult services position
            s!"{path}.unknown.__iter__.result" iterator postState)
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      recordFailure position "Iterable" path tag.render
      output ← addTypeError position output state
  pure output

partial def executeHashable (services : Services) (fuel : Nat)
    (position : Pos) (value : AbsVal) (state : AState)
    (path : String) : M Flow := do
  let mut output : Flow := {}
  for tag in value.tags do
    match tag with
    | .tnone | .tbool | .tint | .tfloat | .tcomplex | .tstr | .tbytes
    | .tdictvalues | .trange | .tgen | .ttype | .tunion | .tfunc
    | .tnotimpl =>
      record position "Hashable" path tag.render "builtin hash"
      output := output.join
        (Flow.ofNormal (onlyTag value tag) state)
    | .ttuple =>
      output := output.join
        (← executeHashableTuple services fuel position
          (onlyTag value tag) state path)
    | .tobj className =>
      let accepted := onlyTag value tag
      match ← services.resolveMethod className "__hash__" with
      | none =>
        match ← services.classInfo className with
        | some info =>
          if info.isDataclass then
            record position "Hashable" path tag.render
              "generated dataclass __hash__"
            output := output.join
              (← executeDataclassHash services fuel position className
                info accepted state path)
          else
            -- Admission rejects the Python
            -- `__eq__`-without-`__hash__` shape, so an admitted ordinary
            -- class with no hook inherits identity hashing.
            record position "Hashable" path tag.render "identity hash"
            output := output.join (Flow.ofNormal accepted state)
        | none =>
          record position "Hashable" path tag.render "identity hash"
          output := output.join (Flow.ofNormal accepted state)
      | some (owner, function) =>
        record position "Hashable" path tag.render
          s!"{owner}.__hash__"
        let called ← services.invokeUser position
          s!"{owner}.__hash__" function [accepted] [] state
        recordRaised position "Hashable" path tag.render called.raised
        output := { output with
          raised := output.raised.join called.raised }
        if let some (result, postState) := called.normal then
          output := output.join
            (← validateHashResult services position
              s!"{path}.__hash__.result" accepted result postState)
    | .tany =>
      oblige position "dispatch-any" "Hashable on an unknown value"
      record position "Hashable" path "any" "deferred"
      output := output.join
        (Flow.ofNormal (onlyTag value tag) state)
      recordFailure position "Hashable" path "any"
      output ← addTypeError position output state
      let hooked ← services.unknownProtocol position
        .hashable (onlyTag value tag) state
      recordRaised position "Hashable" path "any" hooked.raised
      output := { output with
        raised := output.raised.join hooked.raised }
      if let some (result, postState) := hooked.normal then
        output := output.join
          (← validateHashResult services position
            s!"{path}.unknown.__hash__.result"
            (onlyTag value tag) result postState)
    | .tlist | .tdict | .tdictkeys | .tdictitems | .tset =>
      recordFailure position "Hashable" path tag.render
      output ← addTypeError position output state
    | .tunbound | .tuninit | .tmissing => pure ()
  pure output

partial def executeDataclassHash (services : Services) (fuel : Nat)
    (position : Pos) (className : String) (info : ClassInfo)
    (value : AbsVal) (state : AState) (path : String) : M Flow := do
  if fuel == 0 then
    oblige position "contract-depth"
      "dataclass hashability recursion reached its finite analysis bound"
    let output := Flow.ofNormal value state
    return ← addTypeError position output state
  let locations := value.locs.filter (·.cls == .obj className)
  if locations.isEmpty then
    oblige position "object-shape"
      s!"generated {className}.__hash__ has no allocation witness"
    let output := Flow.ofNormal value state
    return ← addTypeError position output state
  let mut output : Flow := {}
  for location in locations do
    let selected := objectAt value className location
    let fields := info.fields.map fun field =>
      state.heapGet location (.field field.name)
    let checked ← executeOrdered services (fuel - 1) position
      .hashable fields selected state
      s!"{path}.{className}.__hash__"
    output := output.join checked
  pure output

partial def executeHashableTuple (services : Services) (fuel : Nat)
    (position : Pos) (tuple : AbsVal) (state : AState)
    (path : String) : M Flow := do
  if fuel == 0 then
    oblige position "contract-depth"
      "tuple hashability recursion reached its finite analysis bound"
    let output := Flow.ofNormal tuple state
    return ← addTypeError position output state
  let locations := tuple.locs.filter (·.cls == .tuple)
  if locations.isEmpty then
    oblige position "tuple-shape"
      "tuple hashability has no allocation witness"
    let output := Flow.ofNormal tuple state
    return ← addTypeError position output state
  let mut output : Flow := {}
  for location in locations do
    let selected := tupleAt tuple location
    if tupleMayBeEmpty state location then
      output := output.join (Flow.ofNormal selected state)
    let checks := tupleChecks state location
    let checked ← executeOrdered services (fuel - 1) position
      .hashable checks selected state s!"{path}.{location.render}"
    output := output.join checked
  pure output

partial def executeString (_services : Services) (position : Pos)
    (value : AbsVal) (state : AState) (path : String) : M Flow := do
  let mut output : Flow := {}
  for tag in value.tags do
    match tag with
    | .tstr =>
      record position "String" path "str" "accept"
      output := output.join
        (Flow.ofNormal (onlyTag value tag) state)
    | .tany =>
      oblige position "dispatch-any" "String on an unknown value"
      record position "String" path "any" "str | TypeError"
      output := output.join (Flow.ofNormal (V [.tstr]) state)
      recordFailure position "String" path "any"
      output ← addTypeError position output state
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      recordFailure position "String" path tag.render
      output ← addTypeError position output state
  pure output

/-- A fill character is a string of length exactly one; every other value,
    including a longer or empty string, raises TypeError. -/
partial def executeFillCharacter (_services : Services) (position : Pos)
    (value : AbsVal) (state : AState) (path : String) : M Flow := do
  let mut output : Flow := {}
  let mut invalid := false
  for tag in value.tags do
    match tag with
    | .tstr =>
      let mayBeOne := value.strOpen || value.strLits.any (·.length == 1)
      let mayBeOther := value.strOpen || value.strLits.any (·.length != 1)
      if mayBeOne then
        output := output.join (Flow.ofNormal (onlyTag value tag) state)
      if mayBeOther then
        recordFailure position "FillCharacter" path "str"
        invalid := true
    | .tany =>
      oblige position "dispatch-any" "FillCharacter on an unknown value"
      output := output.join (Flow.ofNormal (V [.tstr]) state)
      recordFailure position "FillCharacter" path "any"
      invalid := true
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      recordFailure position "FillCharacter" path tag.render
      invalid := true
  if invalid then
    output ← addTypeError position output state
  pure output

/-- A separator must be a string of `kind`, and an empty one is a ValueError.

    Only `str` carries tracked literals, so only a `str` separator can be shown
    non-empty; a `bytes` separator may always be empty and keeps both the normal
    completion and the ValueError. -/
partial def executeSeparatorString (_services : Services) (position : Pos)
    (kind : Tag) (value : AbsVal) (state : AState) (path : String) : M Flow := do
  let label := (ArgContract.separatorString kind).label
  let mut output : Flow := {}
  let mut wrongType := false
  let mut empty := false
  for tag in value.tags do
    if tag == kind then
      let mayBeNonempty := tag != .tstr || value.strOpen ||
        value.strLits.any (!·.isEmpty)
      let mayBeEmpty := tag != .tstr || value.strOpen ||
        value.strLits.any (·.isEmpty) || value.strLits.isEmpty
      if mayBeNonempty then
        output := output.join (Flow.ofNormal (onlyTag value tag) state)
      if mayBeEmpty then
        record position label path tag.render "!ValueError"
        empty := true
    else
      match tag with
      | .tany =>
        oblige position "dispatch-any" s!"{label} on an unknown value"
        output := output.join (Flow.ofNormal (V [kind]) state)
        recordFailure position label path "any"
        wrongType := true
        empty := true
      | .tunbound | .tuninit | .tmissing => pure ()
      | _ =>
        recordFailure position label path tag.render
        wrongType := true
  if wrongType then
    output ← addTypeError position output state
  if empty then
    output := output.join (← machineValueError position state)
  pure output

partial def executeStringOrTuple (services : Services) (fuel : Nat)
    (position : Pos) (value : AbsVal) (state : AState)
    (path : String) : M Flow := do
  let mut output : Flow := {}
  for tag in value.tags do
    match tag with
    | .tstr =>
      record position "StringOrTupleOfStrings" path "str" "accept"
      output := output.join
        (Flow.ofNormal (onlyTag value tag) state)
    | .ttuple =>
      output := output.join
        (← executeStringTuple services fuel position
          (onlyTag value tag) state path)
    | .tany =>
      oblige position "dispatch-any"
        "StringOrTupleOfStrings on an unknown value"
      record position "StringOrTupleOfStrings" path
        "any" "str | tuple[str,...] | TypeError"
      output := output.join
        (Flow.ofNormal (V [.tstr]) state)
      output := output.join
        (Flow.ofNormal (onlyTag value tag) state)
      recordFailure position "StringOrTupleOfStrings" path "any"
      output ← addTypeError position output state
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      recordFailure position "StringOrTupleOfStrings" path tag.render
      output ← addTypeError position output state
  pure output

partial def executeCallableOrNone (services : Services) (position : Pos)
    (value : AbsVal) (state : AState) (path : String) : M Flow := do
  let mut output : Flow := {}
  for tag in value.tags do
    match tag with
    | .tnone =>
      record position "CallableOrNone" path "none" "accept"
      output := output.join
        (Flow.ofNormal (onlyTag value tag) state)
    | .tfunc | .ttype =>
      record position "CallableOrNone" path tag.render "builtin callable"
      -- The operation calls it, so the callback's effects are the call's.
      let called ← services.invokeCallable position (onlyTag value tag) 1 state
      output := output.join {
        normal := called.normal.map fun (_, postState) =>
          (onlyTag value tag, postState)
        raised := called.raised
      }
    | .tobj className =>
      if (← services.resolveMethod className "__call__").isSome then
        record position "CallableOrNone" path tag.render "__call__"
        let called ← services.invokeCallable position (onlyTag value tag) 1
          state
        output := output.join {
          normal := called.normal.map fun (_, postState) =>
            (onlyTag value tag, postState)
          raised := called.raised
        }
      else
        recordFailure position "CallableOrNone" path tag.render
        output ← addTypeError position output state
    | .tany =>
      oblige position "dispatch-any"
        "CallableOrNone on an unknown value"
      record position "CallableOrNone" path "any"
        "callable | none | TypeError"
      output := output.join
        (Flow.ofNormal (onlyTag value tag) state)
      recordFailure position "CallableOrNone" path "any"
      output ← addTypeError position output state
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      recordFailure position "CallableOrNone" path tag.render
      output ← addTypeError position output state
  pure output

partial def executeMappingFresh (services : Services) (position : Pos)
    (source : AbsVal) (state : AState) (path : String) : M Flow := do
  let (target, allocated) := allocate state position.id .dict []
  executeMappingInto services position source target allocated path

partial def executeMappingInto (services : Services) (position : Pos)
    (source target : AbsVal) (state : AState) (path : String) : M Flow := do
  let mut output : Flow := {}
  for tag in source.tags do
    if !inertTag tag then
      let sourceCase := onlyTag source tag
      let route ← match tag with
        | .tdict => pure MappingRoute.mapping
        | .tobj className =>
          if (← services.resolveMethod className "keys").isSome then
            pure MappingRoute.mapping
          else if (← services.resolveMethod className "@get:keys").isSome ||
              (← services.classInfo className).any
                (·.layout.contains "keys") then
            pure MappingRoute.unknown
          else
            pure MappingRoute.iterablePairs
        | .tany => pure MappingRoute.unknown
        | _ => pure MappingRoute.iterablePairs
      if tag == .tany then
        oblige position "dispatch-any"
          "MappingOrIterablePairs on an unknown value"
      record position "MappingOrIterablePairs" path tag.render route.label
      let consumed ← services.consumeMappingPairs position {
        route
        source := sourceCase
        target := { value := target }
      } state
      recordRaised position "MappingOrIterablePairs" path
        tag.render consumed.raised
      output := output.join {
        normal := consumed.normal.map fun (_, outputState) =>
          (target, outputState)
        raised := consumed.raised
      }
  pure output

partial def executeStringTuple (services : Services) (fuel : Nat)
    (position : Pos) (tuple : AbsVal) (state : AState)
    (path : String) : M Flow := do
  if fuel == 0 then
    oblige position "contract-depth"
      "tuple-of-strings recursion reached its finite analysis bound"
    let output := Flow.ofNormal tuple state
    return ← addTypeError position output state
  let locations := tuple.locs.filter (·.cls == .tuple)
  if locations.isEmpty then
    oblige position "tuple-shape"
      "tuple-of-strings contract has no allocation witness"
    let output := Flow.ofNormal tuple state
    return ← addTypeError position output state
  let mut output : Flow := {}
  for location in locations do
    let selected := tupleAt tuple location
    if tupleMayBeEmpty state location then
      output := output.join (Flow.ofNormal selected state)
    let checks := tupleChecks state location
    let checked ← executeStringSearch services (fuel - 1) position
      checks selected state s!"{path}.{location.render}"
    output := output.join checked
  pure output

/-- CPython checks a startswith/endswith tuple from left to right and returns
    immediately on a match. With no string-value relation in this layer, every
    valid string may match or may let the search continue. Thus a valid prefix
    preserves a normal path even when a later tuple slot can raise TypeError. -/
partial def executeStringSearch (services : Services) (fuel : Nat)
    (position : Pos) (values : List AbsVal) (result : AbsVal)
    (state : AState) (path : String) : M Flow := do
  let mut searching : Option AState := some state
  let mut matched : Option AState := none
  let mut raised : RaisedFlow := {}
  for h : index in [0:values.length] do
    match searching with
    | none => pure ()
    | some current =>
      let checked ← executeFuel services fuel position .string
        values[index] current s!"{path}[{index}]"
      raised := raised.join checked.raised
      match checked.normal with
      | none => searching := none
      | some (_, nextState) =>
        matched := joinOpt matched (some nextState)
        searching := some nextState
  let completed := joinOpt matched searching
  pure (flowWithRaised (completed.map fun outputState =>
    (result, outputState)) raised)

partial def executeOrdered (services : Services) (fuel : Nat)
    (position : Pos) (contract : ArgContract) (values : List AbsVal)
    (result : AbsVal) (state : AState) (path : String) : M Flow := do
  let mut normal : Option AState := some state
  let mut raised : RaisedFlow := {}
  for h : index in [0:values.length] do
    match normal with
    | none => pure ()
    | some current =>
      let checked ← executeFuel services fuel position contract
        values[index] current s!"{path}[{index}]"
      raised := raised.join checked.raised
      normal := checked.normal.map (·.2)
  pure (flowWithRaised (normal.map fun outputState =>
    (result, outputState)) raised)

end

/-- Execute a semantic argument contract with the default finite recursion
    bound used elsewhere in the analyzer's recursive domains. -/
def execute (services : Services) (position : Pos)
    (contract : ArgContract) (value : AbsVal) (state : AState) : M Flow :=
  executeFuel services 16 position contract value state "argument"

/-- Consume into an existing dict or TypedDict destination. This is the entry
    used by mutating rules such as `dict.update`; exceptions retain all writes
    made before the failing lookup, pair, hash, or equality operation. -/
def executeMappingOrIterablePairsInto (services : Services)
    (position : Pos) (source target : AbsVal) (state : AState) : M Flow :=
  executeMappingInto services position source target state
    "argument.mapping"

/-- Run a builtin or method's semantic argument prelude in declaration order.
    Arguments have already been evaluated and signature-bound. A guaranteed
    failure suppresses every later contract; mixed failures are retained while
    the normal partition continues with the contract's converted value. -/
def executeArguments (services : Services) (position : Pos)
    (arguments : List ContractArgument) (state : AState) :
    M ContractArguments := do
  let mut normal : Option (List (String × AbsVal) × AState) :=
    some ([], state)
  let mut raised : RaisedFlow := {}
  for argument in arguments do
    match normal with
    | none => pure ()
    | some (values, current) =>
      let path := s!"argument.{argument.name}"
      let checked ← match argument.contract with
        | .mappingPairsInto =>
          executeMappingInto services position argument.value argument.target
            current path
        | contract =>
          executeFuel services 16 position contract argument.value current path
      raised := raised.join checked.raised
      normal := checked.normal.map fun (value, nextState) =>
        (values ++ [(argument.name, value)], nextState)
  pure { normal, raised }

/-- The prelude executor to install into `RulePlan.Services`. -/
def applyContracts (services : Services) :
    Pos -> List ContractArgument -> AState -> M ContractArguments :=
  executeArguments services

end Pylate.RuleDriven.Contracts
