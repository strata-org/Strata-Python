/-
Ordered iteration and mapping-pair consumption for the rule interpreter.

This module owns the control protocol around iterators.  Operations that may
execute admitted Python code remain behind `Services`: method resolution,
user calls, exception-subclass tests, hashing, equality, and recursive
annotation checks.  In particular, this module never calls either procedural
analyzer.

Iteration closes an ascending abstract-state fixpoint.  There is no fuel or
round limit that can be mistaken for successful exhaustion.  A normal result
exists only when `StopIteration` (including a subclass) is reachable.
-/
import Pylate.RuleLang.Contracts

namespace Pylate.RuleDriven.Iteration

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.Contracts

/-! ## Typed interpreter boundary -/

structure Services where
  classInfo : String -> M (Option ClassInfo)
  resolveMethod : String -> String -> M (Option (String × FuncDef))
  invokeUser : Pos -> String -> FuncDef -> List AbsVal ->
    List (String × AbsVal) -> AState -> M Flow
  /-- `exceptionSubclass raised expected` follows the admitted exception MRO. -/
  exceptionSubclass : String -> String -> M Bool
  /-- Hash one key.  Normal completion retains the key (or an equivalent
      accepted value); raised cases carry the exact post-hook state. -/
  hashKey : Pos -> AbsVal -> AState -> M Flow
  /-- Compare an existing dictionary key with an incoming key.  This hook
      includes rich-comparison and truth-conversion effects. -/
  equalKeys : Pos -> AbsVal -> AbsVal -> AState -> M Flow
  /-- Assert/assume one TypedDict field annotation.  This is a proof boundary,
      not a fabricated Python runtime type check.  The label names the field so
      the obligation is actionable. -/
  checkAnnotation : Pos -> String -> Ann -> AbsVal -> AState -> M Flow

abbrev ElementCallback :=
  Pos -> AbsVal -> AState -> M Flow

private abbrev iteratorSourceCell : CellSelector := .iteratorSource
private abbrev sequenceSourceCell : CellSelector := .sequenceSource

private def inertTag : Tag -> Bool
  | .tunbound | .tuninit | .tmissing => true
  | _ => false

private def onlyTag (value : AbsVal) (tag : Tag) : AbsVal :=
  value.restrictTags [tag]

private def raisedOnly (origin : Pos) (cls : String) (state : AState)
    (from? : Provenance := .machine) : RaisedFlow :=
  { cases := [{ cls, value := AbsVal.bot, state, origin, from? }] }

private def machineRaise (position : Pos) (cls : String)
    (state : AState) : M Flow := do
  let modeled ← mraise position {} state [cls]
  let raised := modeled.tags.foldl (fun current name =>
    current.add {
      cls := name
      value := AbsVal.bot
      state := modeled.st.getD state
      origin := position
    }) {}
  pure { raised }

private def addMachineRaise (position : Pos) (flow : Flow)
    (cls : String) (state : AState) : M Flow :=
  return flow.join (← machineRaise position cls state)

/-- Iterator exhaustion is an internal signal by provenance: the consuming
    operation catches it, so it never reaches the abort policy. A site that
    lets it escape re-raises it as a machine exception instead. -/
private def addExhaustion (position : Pos) (flow : Flow)
    (state : AState) : Flow :=
  flow.join { raised := raisedOnly position "StopIteration" state .internal }

private def record (position : Pos) (kind description tag outcome : String) :
    M Unit :=
  resCase position kind description tag outcome

/-! ## Iterator acquisition -/

-- The second copy of this list. One definition, in `BuiltinOutcomes.lean`.
private def builtinIterable (tag : Tag) : Bool :=
  (builtinOutcome tag .iterate).concrete

private def locationEmptiness (state : AState) (location : Loc)
    (element : AbsVal) : Emptiness :=
  let explicit := state.emptinessGet location
  if explicit != .bottom then explicit
  else if element.isBot then .empty
  else .top

private def tagEmptiness (state : AState) (source : AbsVal)
    (tag : Tag) : Emptiness :=
  match tag with
  | .tstr =>
    if source.strOpen then .top
    else if source.strLits.isEmpty ||
        source.strLits.all (·.isEmpty) then .empty
    else if source.strLits.all (!·.isEmpty) then .nonempty
    else .top
  | .trange => .top
  | _ =>
    let locations := source.locs.filter (·.cls.tag == tag)
    if locations.isEmpty then
      if (elemOf state source).isBot then .empty else .top
    else
      locations.foldl (fun result location =>
        result.join
          (locationEmptiness state location (elemOf state source)))
        .bottom

private def sourceEmptiness (state : AState) (source : AbsVal) : Emptiness :=
  let result := source.tags.foldl (fun current tag =>
    -- A generator is iterable, and the table says so with a deferred row, so the
    -- special case is gone: this is "any tag that can iterate at all".
    if (builtinOutcome tag .iterate).admitsNormal then
      current.join (tagEmptiness state (onlyTag source tag) tag)
    else current) .bottom
  if result == .bottom then .top else result

/-- `emptiness` overrides what the source's own container state implies.

    It exists for the `__getitem__` sequence fallback, where deriving it was
    wrong: a plain instance has no element cell, so `sourceEmptiness` read it as
    `.empty`, the iterator was strong-updated to empty, and `next` never yielded
    -- a `for` over a class with `__getitem__` ran zero times with no obligation
    and no raise, which is admitted code silently treated as unreachable. How
    many times such a sequence yields is decided by when `__getitem__` raises
    `IndexError`, which is not something the container abstraction can see. -/
private def allocateIterator (position : Pos) (cell : CellSelector)
    (source element : AbsVal) (state : AState)
    (emptiness : Option Emptiness := none) : AbsVal × AState :=
  let (iterator, allocated) := allocate state position.id .gen []
  let location : Loc := ⟨position.id, .gen, true⟩
  let initialized :=
    ((allocated.heapSet location cell source).heapSet location .elem element)
  let initialized :=
    strongEmptinessUpdate initialized location
      (emptiness.getD (sourceEmptiness state source))
  (iterator, initialized)

private partial def validateIteratorResult (services : Services)
    (position : Pos) (value : AbsVal) (state : AState) : M Flow := do
  let mut output : Flow := {}
  for tag in value.tags do
    match tag with
    | .tgen =>
      output := output.join (Flow.ofNormal (onlyTag value tag) state)
    | .tobj className =>
      if (← services.resolveMethod className "__next__").isSome then
        output := output.join (Flow.ofNormal (onlyTag value tag) state)
      else
        record position "iter" "iterator result" tag.render "!TypeError"
        output ← addMachineRaise position output "TypeError" state
    | .tany =>
      oblige position "dispatch-any"
        "unknown __iter__ result may or may not implement __next__"
      output := output.join (Flow.ofNormal (onlyTag value tag) state)
      output ← addMachineRaise position output "TypeError" state
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      record position "iter" "iterator result" tag.render "!TypeError"
      output ← addMachineRaise position output "TypeError" state
  pure output

/-- Native `iter(value)`.  Sequence fallback allocates a wrapper but does
    not execute `__getitem__` until `next`, matching CPython ordering.

    CLAIM iteration-getitem-fallback: a class with `__getitem__` and no
    `__iter__` is iterable, indexed from 0.
-/
partial def iter (services : Services) (position : Pos) (source : AbsVal)
    (state : AState) : M Flow := do
  let mut output : Flow := {}
  for tag in source.tags do
    let selected := onlyTag source tag
    match tag with
    | .tgen =>
      record position "iter" "iter(..)" tag.render "identity"
      output := output.join (Flow.ofNormal selected state)
    | .tobj className =>
      match ← services.resolveMethod className "__iter__" with
      | some (owner, function) =>
        record position "iter" "iter(..)" tag.render
          s!"{owner}.__iter__"
        let called ← services.invokeUser position s!"{owner}.__iter__"
          function [selected] [] state
        output := { output with
          raised := output.raised.join called.raised }
        if let some (iterator, postState) := called.normal then
          output := output.join
            (← validateIteratorResult services position iterator postState)
      | none =>
        match ← services.resolveMethod className "__getitem__" with
        | some (owner, _) =>
          record position "iter" "iter(..)" tag.render
            s!"sequence fallback via {owner}.__getitem__"
          let (iterator, postState) :=
            allocateIterator position sequenceSourceCell selected anyV state
              (some .top)
          output := output.join (Flow.ofNormal iterator postState)
        | none =>
          record position "iter" "iter(..)" tag.render "!TypeError"
          output ← addMachineRaise position output "TypeError" state
    | .tany =>
      oblige position "dispatch-any" "iter() of an unknown value"
      record position "iter" "iter(..)" "any" "iterator | TypeError"
      output := output.join (Flow.ofNormal selected state)
      output ← addMachineRaise position output "TypeError" state
    | _ =>
      if builtinIterable tag then
        record position "iter" "iter(..)" tag.render "builtin __iter__"
        let (iterator, postState) :=
          allocateIterator position iteratorSourceCell selected
            (elemOf state selected) state
        output := output.join (Flow.ofNormal iterator postState)
      else if !inertTag tag then
        record position "iter" "iter(..)" tag.render "!TypeError"
        output ← addMachineRaise position output "TypeError" state
  pure output

/-! ## One `next` operation -/

private def effectiveEmptiness (state : AState) (location : Loc)
    (element : AbsVal) : Emptiness :=
  let explicit := state.emptinessGet location
  if explicit != .bottom then explicit
  else if element.isBot then .empty
  else .top

private def afterAbstractYield (iterator : AbsVal) (location : Loc)
    (state : AState) : AState :=
  if isStrongCollectionTarget iterator location then
    strongEmptinessUpdate state location .top
  else
    weakEmptinessUpdate state location .top

private def abstractIteratorNext (position : Pos) (iterator : AbsVal)
    (location : Loc) (state : AState) : M Flow := do
  let element := state.heapGet location .elem
  let emptiness := effectiveEmptiness state location element
  let mut output : Flow := {}
  if emptiness.mayBeNonempty && !element.isBot then
    output := output.join
      (Flow.ofNormal { element with witness := true }
        (afterAbstractYield iterator location state))
  if emptiness.mayBeEmpty then
    output := addExhaustion position output state
  pure output

private partial def sequenceNext (services : Services) (position : Pos)
    (source : AbsVal) (state : AState) : M Flow := do
  let mut output : Flow := {}
  for tag in source.tags do
    let selected := onlyTag source tag
    match tag with
    | .tobj className =>
      match ← services.resolveMethod className "__getitem__" with
      | some (owner, function) =>
        record position "next" "sequence next" tag.render
          s!"{owner}.__getitem__"
        let called ← services.invokeUser position
          s!"{owner}.__getitem__" function
          [selected, V [.tint]] [] state
        if let some (value, postState) := called.normal then
          output := output.join (Flow.ofNormal value postState)
        for raised in called.raised.cases do
          let indexExhaustion ←
            services.exceptionSubclass raised.cls "IndexError"
          let stopExhaustion ←
            services.exceptionSubclass raised.cls "StopIteration"
          if indexExhaustion || stopExhaustion then
            -- The sequence protocol catches this itself, so it is exhaustion,
            -- not an escaping machine error: no policy may delete it.
            output := addExhaustion position output raised.state
          else
            output := output.addRaised raised
      | none =>
        output ← addMachineRaise position output "TypeError" state
    | .tany =>
      oblige position "dispatch-any"
        "sequence-fallback __getitem__ on an unknown receiver"
      output := output.join (Flow.ofNormal anyV state)
      output := addExhaustion position output state
      output ← addMachineRaise position output "TypeError" state
    | _ =>
      if !inertTag tag then
        output ← addMachineRaise position output "TypeError" state
  pure output

private partial def generatorNext (services : Services) (position : Pos)
    (iterator : AbsVal) (location : Loc) (state : AState) : M Flow := do
  let sequenceSource := state.heapGet location sequenceSourceCell
  let builtinSource := state.heapGet location iteratorSourceCell
  let mut output : Flow := {}
  if !sequenceSource.isBot then
    output := output.join
      (← sequenceNext services position sequenceSource state)
  if !builtinSource.isBot then
    output := output.join
      (← abstractIteratorNext position iterator location state)
  if sequenceSource.isBot && builtinSource.isBot then
    output := output.join
      (← abstractIteratorNext position iterator location state)
  pure output

/-- Native `next(iterator)`.  Exhaustion remains a raised
    `StopIteration` flow here; consumers decide where it is caught.

    CLAIM iteration-stopiteration-ends-loop: `StopIteration` is the end of the
    sequence, not an escaping exception.
-/
partial def next (services : Services) (position : Pos)
    (iterator : AbsVal) (state : AState) : M Flow := do
  let mut output : Flow := {}
  for tag in iterator.tags do
    let selected := onlyTag iterator tag
    match tag with
    | .tgen =>
      let locations := selected.locs.filter (·.cls == .gen)
      if locations.isEmpty then
        oblige position "iterator-shape"
          "generator/iterator value has no allocation witness"
        output := output.join (Flow.ofNormal anyV state)
        output := addExhaustion position output state
      else
        for location in locations do
          output := output.join
            (← generatorNext services position selected location state)
    | .tobj className =>
      match ← services.resolveMethod className "__next__" with
      | some (owner, function) =>
        record position "next" "next(..)" tag.render
          s!"{owner}.__next__"
        let called ← services.invokeUser position s!"{owner}.__next__"
          function [selected] [] state
        output := output.join called
      | none =>
        record position "next" "next(..)" tag.render "!TypeError"
        output ← addMachineRaise position output "TypeError" state
    | .tany =>
      oblige position "dispatch-any" "next() of an unknown iterator"
      record position "next" "next(..)" "any"
        "value | StopIteration | TypeError"
      output := output.join (Flow.ofNormal anyV state)
      output := addExhaustion position output state
      output ← addMachineRaise position output "TypeError" state
    | _ =>
      if !inertTag tag then
        record position "next" "next(..)" tag.render "!TypeError"
        output ← addMachineRaise position output "TypeError" state
  pure output

/-! ## Ordered consumption to a checked fixpoint -/

structure ExhaustionSplit where
  normal    : Option Normal := none
  exhausted : Option AState := none
  raised    : RaisedFlow := {}
deriving Repr, Inhabited

private partial def splitExhaustion (services : Services)
    (flow : Flow) : M ExhaustionSplit := do
  let mut exhausted : Option AState := none
  let mut raised : RaisedFlow := {}
  for failure in flow.raised.cases do
    if ← services.exceptionSubclass failure.cls "StopIteration" then
      exhausted := joinOpt exhausted (some failure.state)
    else
      raised := raised.add failure
  pure { normal := flow.normal, exhausted, raised }

structure ConsumptionStep where
  backedge  : Option AState := none
  exhausted : Option AState := none
  raised    : RaisedFlow := {}
deriving Repr, Inhabited

private partial def consumptionStep (services : Services)
    (position : Pos) (iterator : AbsVal) (callback : ElementCallback)
    (state : AState) : M ConsumptionStep := do
  let pulled ← next services position iterator state
  let split ← splitExhaustion services pulled
  let mut backedge : Option AState := none
  let mut raised := split.raised
  if let some (element, elementState) := split.normal then
    let applied ← callback position element elementState
    raised := raised.join applied.raised
    backedge := applied.normal.map (·.2)
  pure { backedge, exhausted := split.exhausted, raised }

structure ConsumptionResult where
  invariant : AState
  exhausted : Option AState := none
  raised    : RaisedFlow := {}
  rounds    : Nat := 0
deriving Repr, Inhabited

/-- Least ascending post-fixpoint for iterator/callback effects.  `rounds` is
    diagnostic only and never controls termination or creates exhaustion. -/
private partial def close (services : Services) (position : Pos)
    (iterator : AbsVal) (callback : ElementCallback)
    (invariant : AState) (exhausted : Option AState := none)
    (raised : RaisedFlow := {}) (rounds : Nat := 0) :
    M ConsumptionResult := do
  snapJoin .loopHead position invariant
  let step ← consumptionStep services position iterator callback invariant
  let exhausted := joinOpt exhausted step.exhausted
  let raised := raised.join step.raised
  let nextInvariant := match step.backedge with
    | none => invariant
    | some backedge => invariant.join backedge
  if nextInvariant.le invariant then
    pure {
      invariant
      exhausted
      raised
      rounds := rounds + 1
    }
  else
    close services position iterator callback nextInvariant
      exhausted raised (rounds + 1)

/-- Acquire and consume an iterable.  The callback executes once per abstract
    element in source order.  Its normal state is the sole backedge; callback
    exceptions never advance iteration. -/
partial def consume (services : Services) (position : Pos)
    (source result : AbsVal) (callback : ElementCallback)
    (state : AState) : M Flow := do
  let acquired ← iter services position source state
  let mut output : Flow := { raised := acquired.raised }
  if let some (iterator, iteratorState) := acquired.normal then
    let fixed ← close services position iterator callback iteratorState
    output := {
      normal := fixed.exhausted.map fun exhaustedState =>
        (result, exhaustedState)
      raised := output.raised.join fixed.raised
    }
  pure output

/-! ## Pair unpacking -/

structure PairNormal where
  key   : AbsVal
  value : AbsVal
  state : AState
deriving Repr, Inhabited

private def joinPairNormal :
    Option PairNormal -> Option PairNormal -> Option PairNormal
  | none, right => right
  | left, none => left
  | some left, some right =>
    some {
      key := left.key.join right.key
      value := left.value.join right.value
      state := left.state.join right.state
    }

structure PairFlow where
  normal : Option PairNormal := none
  raised : RaisedFlow := {}
deriving Repr, Inhabited

namespace PairFlow

private def join (left right : PairFlow) : PairFlow :=
  {
    normal := joinPairNormal left.normal right.normal
    raised := left.raised.join right.raised
  }

end PairFlow

private def indexedSlots (state : AState) (location : Loc) : List AbsVal :=
  let count := state.tupleSlotCount location
  (List.range count).map fun index =>
    state.heapGet location (.tupleSlot index)

private def pairError (position : Pos) (state : AState) : M PairFlow := do
  let failure ← machineRaise position "ValueError" state
  pure { raised := failure.raised }

private partial def unpackThird (services : Services) (position : Pos)
    (iterator key value : AbsVal) (state : AState) : M PairFlow := do
  let third ← splitExhaustion services
    (← next services position iterator state)
  let mut output : PairFlow := { raised := third.raised }
  if let some exhaustedState := third.exhausted then
    output := output.join {
      normal := some { key, value, state := exhaustedState }
    }
  if let some (_, extraState) := third.normal then
    output := output.join (← pairError position extraState)
  pure output

private partial def unpackSecond (services : Services) (position : Pos)
    (iterator key : AbsVal) (state : AState) : M PairFlow := do
  let second ← splitExhaustion services
    (← next services position iterator state)
  let mut output : PairFlow := { raised := second.raised }
  if let some exhaustedState := second.exhausted then
    output := output.join (← pairError position exhaustedState)
  if let some (value, valueState) := second.normal then
    output := output.join
      (← unpackThird services position iterator key value valueState)
  pure output

private partial def unpackFirst (services : Services) (position : Pos)
    (iterator : AbsVal) (state : AState) : M PairFlow := do
  let first ← splitExhaustion services
    (← next services position iterator state)
  let mut output : PairFlow := { raised := first.raised }
  if let some exhaustedState := first.exhausted then
    output := output.join (← pairError position exhaustedState)
  if let some (key, keyState) := first.normal then
    output := output.join
      (← unpackSecond services position iterator key keyState)
  pure output

private partial def unpackViaProtocol (services : Services)
    (position : Pos) (pair : AbsVal) (state : AState) : M PairFlow := do
  let acquired ← iter services position pair state
  let mut output : PairFlow := { raised := acquired.raised }
  if let some (iterator, iteratorState) := acquired.normal then
    output := output.join
      (← unpackFirst services position iterator iteratorState)
  pure output

/-- Unpack exactly two elements.  Concrete tuple/list slots are read directly;
    every other shape performs three ordered `next` probes.  The third probe
    is what distinguishes arity two from arity greater than two.

    CLAIM iteration-unpack-arity: unpacking checks arity: a wrong-length
    element is a `ValueError`.
-/
partial def unpackPair (services : Services) (position : Pos)
    (pair : AbsVal) (state : AState) : M PairFlow := do
  let mut output : PairFlow := {}
  for tag in pair.tags do
    let selected := onlyTag pair tag
    if tag == .ttuple || tag == .tlist then
      let locations := selected.locs.filter (·.cls.tag == tag)
      if locations.isEmpty then
        output := output.join
          (← unpackViaProtocol services position selected state)
      else
        for location in locations do
          let slots := indexedSlots state location
          if slots.isEmpty then
            let locationValue :=
              { selected with locs := [location] } |>.reduce
            output := output.join
              (← unpackViaProtocol services position locationValue state)
          else if slots.length == 2 then
            output := output.join {
              normal := some {
                key := slots[0]!
                value := slots[1]!
                state
              }
            }
          else
            output := output.join (← pairError position state)
    else
      output := output.join
        (← unpackViaProtocol services position selected state)
  pure output

/-! ## Mapping reads -/

private def typedDictKeys (info : ClassInfo) (location : Loc)
    (state : AState) : AbsVal :=
  info.fields.foldl (fun output field =>
    let stored := state.heapGet location (.literalKey field.name)
    let mayBePresent :=
      field.required || stored.isBot ||
        !(stored.withoutTags [.tmissing]).isBot
    if mayBePresent then output.join (strLitV field.name) else output)
    AbsVal.bot

private partial def mappingKeySummary (services : Services)
    (source : AbsVal) (state : AState) : M AbsVal := do
  let mut keys : AbsVal := AbsVal.bot
  for location in source.locs do
    match location.cls with
    | .dict =>
      keys := keys.join (state.heapGet location .dictKeys)
    | .td typeName =>
      match ← services.classInfo typeName with
      | some info =>
        keys := keys.join (typedDictKeys info location state)
      | none =>
        keys := keys.join (state.heapGet location .dictKeys)
    | _ => pure ()
  pure keys.reduce

private partial def builtinMappingKeys (services : Services)
    (position : Pos) (source : AbsVal) (state : AState) : M Flow := do
  let keys ← mappingKeySummary services source state
  let (view, allocated) := allocate state position.id .dictkeys []
  let location : Loc := ⟨position.id, .dictkeys, true⟩
  let initialized := allocated.heapSet location .elem keys
  let sourceEmpty := source.locs.foldl (fun current sourceLocation =>
    if sourceLocation.cls.tag == .tdict then
      current.join
        (locationEmptiness state sourceLocation
          (state.heapGet sourceLocation .dictKeys))
    else current) .bottom
  let inferred :=
    if sourceEmpty == .bottom then
      if keys.isBot then Emptiness.empty else Emptiness.top
    else sourceEmpty
  let initialized := strongEmptinessUpdate initialized location inferred
  pure (Flow.ofNormal view initialized)

private partial def mappingKeys (services : Services) (position : Pos)
    (source : AbsVal) (state : AState) : M Flow := do
  let mut output : Flow := {}
  for tag in source.tags do
    let selected := onlyTag source tag
    match tag with
    | .tdict =>
      record position "mapping" "mapping.keys()" tag.render
        "builtin keys"
      output := output.join
        (← builtinMappingKeys services position selected state)
    | .tobj className =>
      match ← services.resolveMethod className "keys" with
      | some (owner, function) =>
        record position "mapping" "mapping.keys()" tag.render
          s!"{owner}.keys"
        output := output.join
          (← services.invokeUser position s!"{owner}.keys"
            function [selected] [] state)
      | none =>
        record position "mapping" "mapping.keys()" tag.render "!TypeError"
        output ← addMachineRaise position output "TypeError" state
    | .tany =>
      oblige position "dispatch-any"
        "unknown mapping source may provide keys()"
      output := output.join (Flow.ofNormal anyV state)
      output ← addMachineRaise position output "TypeError" state
    | _ =>
      if !inertTag tag then
        output ← addMachineRaise position output "TypeError" state
  pure output

private def exactMappingValue (source : AbsVal) (key : AbsVal)
    (state : AState) : AbsVal := Id.run do
  let mut output : AbsVal := AbsVal.bot
  for location in source.locs do
    if location.cls.tag == .tdict then
      for literal in key.strLits do
        output := output.join
          ((state.heapGet location (.literalKey literal))
            |>.withoutTags [.tmissing])
      if key.strOpen || key.strLits.isEmpty then
        output := output.join (state.heapGet location .dictValues)
      if output.isBot then
        output := output.join (state.heapGet location .dictValues)
  return output.reduce

private partial def mappingGetItem (services : Services) (position : Pos)
    (source key : AbsVal) (state : AState) : M Flow := do
  let mut output : Flow := {}
  for tag in source.tags do
    let selected := onlyTag source tag
    match tag with
    | .tdict =>
      record position "mapping" "mapping[key]" tag.render
        "builtin __getitem__"
      let value := exactMappingValue selected key state
      if value.isBot then
        oblige position "mapping-shape"
          "mapping key came from keys() but has no represented value cell"
        output := output.join (Flow.ofNormal anyV state)
      else
        output := output.join (Flow.ofNormal value state)
    | .tobj className =>
      match ← services.resolveMethod className "__getitem__" with
      | some (owner, function) =>
        record position "mapping" "mapping[key]" tag.render
          s!"{owner}.__getitem__"
        output := output.join
          (← services.invokeUser position s!"{owner}.__getitem__"
            function [selected, key] [] state)
      | none =>
        output ← addMachineRaise position output "TypeError" state
    | .tany =>
      oblige position "dispatch-any"
        "unknown mapping __getitem__"
      output := output.join (Flow.ofNormal anyV state)
      output ← addMachineRaise position output "TypeError" state
    | _ =>
      if !inertTag tag then
        output ← addMachineRaise position output "TypeError" state
  pure output

/-! ## Ordered key insertion -/

private def targetKeys (target : AbsVal) (state : AState) : AbsVal :=
  target.locs.foldl (fun output location =>
    if location.cls.tag == .tdict then
      output.join (state.heapGet location .dictKeys)
    else output) AbsVal.bot

private def targetMayBeNonempty (target : AbsVal) (state : AState) : Bool :=
  target.locs.any fun location =>
    location.cls.tag == .tdict &&
      ((state.emptinessGet location).mayBeNonempty ||
        state.emptinessGet location == .nonempty ||
        !(state.heapGet location .dictKeys).isBot)

private def targetMayBeEmpty (target : AbsVal) (state : AState) : Bool :=
  target.locs.any fun location =>
    location.cls.tag == .tdict &&
      ((state.emptinessGet location).mayBeEmpty ||
        ((state.emptinessGet location) == .bottom &&
          (state.heapGet location .dictKeys).isBot))

private def setNonempty (target : AbsVal) (location : Loc)
    (state : AState) : AState :=
  if isStrongCollectionTarget target location then
    strongEmptinessUpdate state location .nonempty
  else
    weakEmptinessUpdate state location .nonempty

private def writeGenericLocation (target : AbsVal) (location : Loc)
    (key value : AbsVal) (state : AState) : AState :=
  let output :=
    (state.heapJoin location .dictKeys key).heapJoin location .dictValues value
  let output := key.strLits.foldl (fun current literal =>
    if key.strLits.length == 1 && !key.strOpen &&
        isStrongCollectionTarget target location then
      current.heapSet location (.literalKey literal) value
    else
      current.heapJoin location (.literalKey literal) value) output
  setNonempty target location output

private def storeTypedField (target : AbsVal) (location : Loc)
    (_field : FieldDecl) (keyName : String) (value : AbsVal)
    (state : AState) : AState :=
  let output :=
    if isStrongCollectionTarget target location then
      state.heapSet location (.literalKey keyName) value
    else
      state.heapJoin location (.literalKey keyName) value
  let output :=
    ((output.heapJoin location .dictKeys (strLitV keyName)).heapJoin location .dictValues value)
  setNonempty target location output

private partial def checkedTypedField (services : Services)
    (position : Pos) (target : AbsVal) (location : Loc)
    (typeName : String) (field : FieldDecl) (value : AbsVal)
    (state : AState) : M Flow := do
  if field.readOnly then
    oblige position "shape-break"
      s!"write to read-only TypedDict key {typeName}.{field.name}"
    return {}
  let checked ← match field.ann with
    | none => pure (Flow.ofNormal value state)
    | some annotation =>
      services.checkAnnotation position s!"{typeName}.{field.name}"
        annotation value state
  let mut output : Flow := { raised := checked.raised }
  if let some (stored, postState) := checked.normal then
    output := output.join
      (Flow.ofNormal target
        (storeTypedField target location field field.name stored postState))
  pure output

private partial def writeTypedLocation (services : Services)
    (position : Pos) (target : AbsVal) (location : Loc)
    (typeName : String) (key value : AbsVal)
    (state : AState) : M Flow := do
  let some info ← services.classInfo typeName
    | oblige position "typed-dict-shape"
        s!"missing declaration for TypedDict {typeName}"
      return {}
  let mut output : Flow := {}
  for literal in key.strLits do
    match info.fields.find? (·.name == literal) with
    | none =>
      oblige position "shape-break"
        s!"write of undeclared TypedDict key {typeName}.{literal}"
    | some field =>
      output := output.join
        (← checkedTypedField services position target location typeName
          field value state)
  if key.strOpen || Tag.tany ∈ key.tags then
    oblige position "key-membership"
      s!"dynamic key written to TypedDict {typeName} must be declared"
    for field in info.fields do
      output := output.join
        (← checkedTypedField services position target location typeName
          field value state)
  if key.tags.any fun tag =>
      tag != .tstr && tag != .tany && !inertTag tag then
    oblige position "shape-break"
      s!"non-string key cannot preserve TypedDict {typeName}"
  pure output

private partial def writeTarget (services : Services) (position : Pos)
    (target key value : AbsVal) (state : AState) : M Flow := do
  let mut output : Flow := {}
  for location in target.locs do
    match location.cls with
    | .dict =>
      output := output.join
        (Flow.ofNormal target
          (writeGenericLocation target location key value state))
    | .td typeName =>
      output := output.join
        (← writeTypedLocation services position target location typeName
          key value state)
    | _ => pure ()
  if output.normal.isNone && output.raised.cases.isEmpty then
    oblige position "mapping-target"
      "dictionary insertion has no represented target location"
  pure output

private partial def compareThenWrite (services : Services)
    (position : Pos) (target key value : AbsVal)
    (state : AState) : M Flow := do
  let existing := targetKeys target state
  let mut compared : Flow :=
    if targetMayBeEmpty target state || existing.isBot then
      Flow.ofNormal key state
    else {}
  if targetMayBeNonempty target state && !existing.isBot then
    let equality ← services.equalKeys position existing key state
    compared := compared.join equality
    -- A non-colliding hash skips equality.  Without a hash-value domain this
    -- branch is always feasible and must remain alongside hook effects.
    compared := compared.join (Flow.ofNormal key state)
  compared.bindNormal fun _ comparisonState =>
    writeTarget services position target key value comparisonState

private partial def insert (services : Services) (position : Pos)
    (target key value : AbsVal) (state : AState) : M Flow := do
  record position "mapping" "insert key/value"
    (key.tags.map Tag.render |> "|".intercalate) "hash"
  let hashed ← services.hashKey position key state
  hashed.bindNormal fun _ hashState =>
    compareThenWrite services position target key value hashState

/-! ## Mapping-or-pairs contract adapter -/

private partial def mappingElement (services : Services)
    (source target : AbsVal) : ElementCallback :=
  fun position key state => do
    let selected ← mappingGetItem services position source key state
    selected.bindNormal fun value lookupState =>
      insert services position target key value lookupState

private partial def pairElement (services : Services)
    (target : AbsVal) : ElementCallback :=
  fun position pair state => do
    let unpacked ← unpackPair services position pair state
    let mut output : Flow := { raised := unpacked.raised }
    if let some pair := unpacked.normal then
      output := output.join
        (← insert services position target pair.key pair.value pair.state)
    pure output

private partial def consumeMapping (services : Services) (position : Pos)
    (source target : AbsVal) (state : AState) : M Flow := do
  let keys ← mappingKeys services position source state
  let mut output : Flow := { raised := keys.raised }
  if let some (keyIterable, keyState) := keys.normal then
    output := output.join
      (← consume services position keyIterable target
        (mappingElement services source target) keyState)
  pure output

private partial def consumePairs (services : Services) (position : Pos)
    (source target : AbsVal) (state : AState) : M Flow :=
  consume services position source target
    (pairElement services target) state

/-- Production implementation of `Contracts.Services.consumeMappingPairs`.
    Unknown sources branch into mapping and iterable-of-pairs protocols from
    the same input state. -/
partial def consumeMappingPairs (services : Services) (position : Pos)
    (request : MappingRequest) (state : AState) : M Flow :=
  match request.route with
  | .mapping =>
    consumeMapping services position request.source request.target.value state
  | .iterablePairs =>
    consumePairs services position request.source request.target.value state
  | .unknown => do
    let mapping ←
      consumeMapping services position request.source request.target.value state
    let pairs ←
      consumePairs services position request.source request.target.value state
    pure (mapping.join pairs)

/-- Consume an iterable for its effects: `__iter__`, every `__next__`, and an
    optional per-element contract callback, with exhaustion as the normal
    completion. The value returned is the source itself. -/
partial def consumeElements (services : Services) (position : Pos)
    (source : AbsVal) (callback : Option ElementCallback)
    (state : AState) : M Flow :=
  consume services position source source
    (fun elementPosition element elementState =>
      match callback with
      | some run => run elementPosition element elementState
      | none => pure (Flow.ofNormal element elementState))
    state

/-- Field-compatible adapter for a `Contracts.Services` record. -/
def contractsConsumeMappingPairs (services : Services) :
    Pos -> MappingRequest -> AState -> M Flow :=
  consumeMappingPairs services

/-- Replace only the mapping-pairs boundary of an existing contract service. -/
def install (base : Contracts.Services) (services : Services) :
    Contracts.Services :=
  { base with
    consumeMappingPairs := contractsConsumeMappingPairs services
    consumeElements := fun position source elementContract state =>
      consumeElements services position source
        (elementContract.map fun run => fun elementPosition element elementState =>
          run elementPosition element elementState) state }

end Pylate.RuleDriven.Iteration
