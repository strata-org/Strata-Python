/-
Transfers for the builtin protocol functions.

Protocol selection and abstract effects live here.  The service boundary is
limited to operations that require the enclosing interpreter: resolving a
user special method, invoking its FuncDef, and looking up exceptions recorded
for an eagerly analyzed generator.
-/
import Pylate.RuleLang.Plan

namespace Pylate.RuleDriven.Protocols

open Pylate
open Pylate.RuleDriven

structure Services where
  resolveMethod : String -> String -> M (Option (String × FuncDef))
  invokeUser : Pos -> String -> FuncDef -> List AbsVal ->
    List (String × AbsVal) -> AState -> M Flow
  generatorExceptions : AbsVal -> M (Fset String)

private def definitelyNonempty (value : AbsVal) (state : AState) : Bool :=
  !value.locs.isEmpty &&
    value.locs.all (fun location =>
      state.emptinessGet location == .nonempty)

private def consumeGenerator (value : AbsVal) (state : AState) : AState :=
  value.locs.foldl (fun current location =>
    if location.cls == .gen then
      strongEmptinessUpdate current location .empty
    else current) state

private def addRaised (p : Pos) (flow : Flow) (cls : String)
    (state : AState) : Flow :=
  flow.addRaised {
    cls
    value := AbsVal.bot
    state
    origin := p
  }

private def addRaisedClasses (p : Pos) (flow : Flow) (classes : Fset String)
    (state : AState) : Flow :=
  classes.foldl (fun current cls => addRaised p current cls state) flow

private def machineRaise (p : Pos) (cls : String) (state : AState) :
    M Flow := do
  let modeled ← mraise p {} state [cls]
  pure <| if cls ∈ modeled.tags then addRaised p {} cls state else {}

private def withMachineRaise (p : Pos) (flow : Flow) (cls : String)
    (state : AState) : M Flow := do
  let raised ← machineRaise p cls state
  pure (flow.join raised)

private def wrongArity (p : Pos) (state : AState) : M Flow :=
  machineRaise p "TypeError" state

private def noKeywords (keywords : List (String × AbsVal)) : Bool :=
  keywords.isEmpty

private def record (p : Pos) (name : String) (tag outcome : String) : M Unit :=
  resCase p "call" s!"{name}(..)" tag outcome

-- Both lists come from `BuiltinOutcomes.lean` now. They were hand-maintained and
-- identical, and `builtinIterable` was written twice across two files -- the same
-- shape of duplication that let `bytes` go missing from the membership list.
private def builtinSized (tag : Tag) : Bool :=
  (builtinOutcome tag .length).concrete

private def builtinIterable (tag : Tag) : Bool :=
  (builtinOutcome tag .iterate).concrete

private def inertTag : Tag -> Bool
  | .tunbound | .tuninit | .tmissing => true
  | _ => false

/--CLAIM len-calls-dunder-len: `len` calls `__len__`; a negative result is a
    `ValueError`, a non-integer a `TypeError`, an absent one a `TypeError`.
-/
def len (services : Services) (p : Pos) (arguments : List AbsVal)
    (keywords : List (String × AbsVal)) (state : AState) : M Flow := do
  if arguments.length != 1 || !noKeywords keywords then
    return ← wrongArity p state
  let receiver := arguments.headD AbsVal.bot
  let mut result : Flow := {}
  for tag in receiver.tags do
    if builtinSized tag then
      record p "len" tag.render "builtin __len__"
      result := result.join (Flow.ofNormal (V [.tint]) state)
    else
      match tag with
      | .tobj className =>
        match ← services.resolveMethod className "__len__" with
        | some (owner, function) =>
          record p "len" tag.render s!"{owner}.__len__"
          let called ← services.invokeUser p s!"{owner}.__len__" function
            [receiver.restrictTags [tag]] [] state
          result := { result with
            raised := result.raised.join called.raised }
          match called.normal with
          | none => pure ()
          | some (value, postState) =>
            let valid := value.restrictTags [.tbool, .tint]
            let invalid := value.withoutTags [.tbool, .tint]
            if !valid.isBot then
              result := result.join (Flow.ofNormal (V [.tint]) postState)
              -- The integer domain does not track sign, so a negative
              -- __len__ result remains a possible ValueError.
              result ← withMachineRaise p result "ValueError" postState
            if !invalid.isBot then
              record p "len" tag.render "!TypeError"
              result ← withMachineRaise p result "TypeError" postState
        | none =>
          record p "len" tag.render "!TypeError"
          result ← withMachineRaise p result "TypeError" state
      | .tany =>
        record p "len" "any" "deferred"
        oblige p "dispatch-any" "len() of an unknown value"
        result := result.join (Flow.ofNormal (V [.tint]) state)
        result ← withMachineRaise p result "TypeError" state
      | _ =>
        if !inertTag tag then
          record p "len" tag.render "!TypeError"
          result ← withMachineRaise p result "TypeError" state
  pure result

private def stringProtocol (services : Services) (p : Pos) (name : String)
    (arguments : List AbsVal) (keywords : List (String × AbsVal))
    (state : AState) : M Flow := do
  let validArity :=
    noKeywords keywords &&
      (if name == "str" then arguments.length <= 1
       else arguments.length == 1)
  if !validArity then
    return ← wrongArity p state
  if arguments.isEmpty then
    return Flow.ofNormal (V [.tstr]) state
  let receiver := arguments.headD AbsVal.bot
  let mut result : Flow := {}
  for tag in receiver.tags do
    match tag with
    | .tobj className =>
      let primary := if name == "str" then "__str__" else "__repr__"
      let mut resolved ← services.resolveMethod className primary
      if name == "str" && resolved.isNone then
        resolved ← services.resolveMethod className "__repr__"
      match resolved with
      | some (owner, function) =>
        record p name tag.render s!"{owner}.{function.name}"
        let called ← services.invokeUser p s!"{owner}.{function.name}" function
          [receiver.restrictTags [tag]] [] state
        result := { result with
          raised := result.raised.join called.raised }
        match called.normal with
        | none => pure ()
        | some (value, postState) =>
          let valid := value.restrictTags [.tstr]
          let invalid := value.withoutTags [.tstr]
          if !valid.isBot then
            result := result.join (Flow.ofNormal (V [.tstr]) postState)
          if !invalid.isBot then
            record p name tag.render "!TypeError"
            result ← withMachineRaise p result "TypeError" postState
      | none =>
        result := result.join (Flow.ofNormal (V [.tstr]) state)
    | .tany =>
      record p name "any" "deferred"
      oblige p "dispatch-any" s!"{name}() of an unknown value"
      result := result.join (Flow.ofNormal (V [.tstr]) state)
      result ← withMachineRaise p result "TypeError" state
    | _ =>
      if !inertTag tag then
        result := result.join (Flow.ofNormal (V [.tstr]) state)
  pure result

/--CLAIM str-calls-dunder-str: `str` calls `__str__` when present and
    otherwise still yields a `str`.
-/
def str (services : Services) (p : Pos) (arguments : List AbsVal)
    (keywords : List (String × AbsVal)) (state : AState) : M Flow :=
  stringProtocol services p "str" arguments keywords state

def repr (services : Services) (p : Pos) (arguments : List AbsVal)
    (keywords : List (String × AbsVal)) (state : AState) : M Flow :=
  stringProtocol services p "repr" arguments keywords state

private def allocateIterator (p : Pos) (state : AState) (element : AbsVal)
    (knownNonempty : Bool) : Flow :=
  let (iterator, allocated) := allocate state p.id .gen []
  let location : Loc := ⟨p.id, .gen, true⟩
  let initialized := allocated.heapSet location .elem element
  let initialized :=
    if knownNonempty then
      strongEmptinessUpdate initialized location .nonempty
    else initialized
  Flow.ofNormal iterator initialized

private def validIteratorResult (services : Services) (value : AbsVal) :
    M AbsVal := do
  let mut valid := value.restrictTags [.tgen, .tany]
  for tag in value.tags do
    if let .tobj className := tag then
      if (← services.resolveMethod className "__next__").isSome then
        valid := valid.join (value.restrictTags [tag])
  pure valid

def iter (services : Services) (p : Pos) (arguments : List AbsVal)
    (keywords : List (String × AbsVal)) (state : AState) : M Flow := do
  if arguments.length != 1 || !noKeywords keywords then
    return ← wrongArity p state
  let receiver := arguments.headD AbsVal.bot
  let mut result : Flow := {}
  for tag in receiver.tags do
    match tag with
    | .tgen =>
      record p "iter" "gen" "identity"
      result := result.join
        (Flow.ofNormal (receiver.restrictTags [tag]) state)
    | .tobj className =>
      match ← services.resolveMethod className "__iter__" with
      | some (owner, function) =>
        record p "iter" tag.render s!"{owner}.__iter__"
        let called ← services.invokeUser p s!"{owner}.__iter__" function
          [receiver.restrictTags [tag]] [] state
        result := { result with
          raised := result.raised.join called.raised }
        match called.normal with
        | none => pure ()
        | some (value, postState) =>
          let valid ← validIteratorResult services value
          let invalid := value.withoutTags valid.tags
          if !valid.isBot then
            result := result.join (Flow.ofNormal valid postState)
          if !invalid.isBot then
            record p "iter" tag.render "!TypeError"
            result ← withMachineRaise p result "TypeError" postState
      | none =>
        match ← services.resolveMethod className "__getitem__" with
        | some (owner, _) =>
          record p "iter" tag.render
            s!"sequence iterator via {owner}.__getitem__"
          oblige p "special-method"
            s!"iter({className}) defers indexed __getitem__ calls to next()"
          result := result.join
            (allocateIterator p state anyV false)
        | none =>
          record p "iter" tag.render "!TypeError"
          result ← withMachineRaise p result "TypeError" state
    | .tany =>
      record p "iter" "any" "deferred"
      oblige p "dispatch-any" "iter() of an unknown value"
      result := result.join (Flow.ofNormal anyV state)
      result ← withMachineRaise p result "TypeError" state
    | _ =>
      if builtinIterable tag then
        record p "iter" tag.render "builtin __iter__"
        let source := receiver.restrictTags [tag]
        result := result.join <|
          allocateIterator p state (elemOf state source)
            (definitelyNonempty source state)
      else if !inertTag tag then
        record p "iter" tag.render "!TypeError"
        result ← withMachineRaise p result "TypeError" state
  pure result

private def generatorBodyExceptions (classes : Fset String) : Fset String :=
  classes.map (fun cls =>
    if cls == "StopIteration" then "RuntimeError" else cls)

private def handleStopIteration (p : Pos) (flow : Flow)
    (raisedState : AState) (hasDefault : Bool) (default : AbsVal) : M Flow :=
  if hasDefault then
    pure (flow.join (Flow.ofNormal default raisedState))
  else
    withMachineRaise p flow "StopIteration" raisedState

def next (services : Services) (p : Pos) (arguments : List AbsVal)
    (keywords : List (String × AbsVal)) (state : AState) : M Flow := do
  if arguments.isEmpty || arguments.length > 2 || !noKeywords keywords then
    return ← wrongArity p state
  let receiver := arguments.headD AbsVal.bot
  let hasDefault := arguments.length == 2
  let default := arguments[1]?.getD AbsVal.bot
  let mut result : Flow := {}
  for tag in receiver.tags do
    match tag with
    | .tgen =>
      record p "next" "gen" "builtin __next__"
      let generator := receiver.restrictTags [tag]
      let mustYield := definitelyNonempty generator state
      let recorded ← services.generatorExceptions generator
      let leaked := Fset.diff (generatorBodyExceptions recorded)
        ["StopIteration"]
      result := addRaisedClasses p result leaked state
      let element := elemOf state generator
      let consumed := consumeGenerator generator state
      if !element.isBot then
        result := result.join (Flow.ofNormal element consumed)
      if !mustYield then
        result ← handleStopIteration p result consumed hasDefault default
    | .tobj className =>
      match ← services.resolveMethod className "__next__" with
      | some (owner, function) =>
        record p "next" tag.render s!"{owner}.__next__"
        let called ← services.invokeUser p s!"{owner}.__next__" function
          [receiver.restrictTags [tag]] [] state
        if let some (value, postState) := called.normal then
          result := result.join (Flow.ofNormal value postState)
        for raised in called.raised.cases do
          if raised.cls == "StopIteration" then
            result ← handleStopIteration p result raised.state
              hasDefault default
          else
            result := result.addRaised raised
      | none =>
        record p "next" tag.render "!TypeError"
        result ← withMachineRaise p result "TypeError" state
    | .tany =>
      record p "next" "any" "deferred"
      oblige p "dispatch-any" "next() of an unknown value"
      result := result.join (Flow.ofNormal anyV state)
      result ← withMachineRaise p result "TypeError" state
      if !hasDefault then
        result ← withMachineRaise p result "StopIteration" state
    | _ =>
      if !inertTag tag then
        record p "next" tag.render "!TypeError"
        result ← withMachineRaise p result "TypeError" state
  pure result

def execute (services : Services) (p : Pos) (name : String)
    (arguments : List AbsVal) (keywords : List (String × AbsVal))
    (state : AState) : M Flow :=
  match name with
  | "len" => len services p arguments keywords state
  | "str" => str services p arguments keywords state
  | "repr" => repr services p arguments keywords state
  | "iter" => iter services p arguments keywords state
  | "next" => next services p arguments keywords state
  | _ => pure {}

end Pylate.RuleDriven.Protocols
