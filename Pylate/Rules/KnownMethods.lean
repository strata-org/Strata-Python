/-
Precise transfers for the portion of OpaqueBuiltinMethod representable by
the current abstract domains. Returning none is an explicit request to retain
the opaque fallback; in particular, this module does not fabricate bytes,
generator suspension state, or effects from user-defined protocols.
-/
import Pylate.RuleLang.Plan

namespace Pylate.RuleDriven.KnownMethods

open Pylate

private def machineRaise (p : Pos) (cls : String) (state : AState) : M Flow :=
  executeRaise p (RaiseSpec.machine cls) {} state

private def addMachineRaise (p : Pos) (cls : String) (state : AState)
    (raised : RaisedFlow) : M RaisedFlow := do
  pure (raised.join (← machineRaise p cls state).raised)

private def soleRecentSet (receiver : AbsVal) : Option Loc :=
  match receiver.locs with
  | [location] =>
    if location.cls == .set && completeStrongTarget receiver location then
      some location
    else
      none
  | _ => none

private def clearSet (receiver : AbsVal) (state : AState) : AState :=
  match soleRecentSet receiver with
  | some location =>
    strongEmptinessUpdate (state.heapSet location .elem AbsVal.bot)
      location .empty
  | none => state

private def growSet (receiver value : AbsVal) (state : AState) : AState :=
  receiver.locs.foldl (fun result location =>
    if location.cls == .set then
      result.heapJoin location .elem value
    else
      result) state

private def mustAliasSet (left right : AbsVal) : Bool :=
  left.tags == [.tset] && right.tags == [.tset] &&
    left.locs.length == 1 && left.locs == right.locs &&
    !left.witness && !right.witness

private def tagIsIterable : Tag -> Bool
  | .tlist | .tdict | .tdictkeys | .tdictitems | .tdictvalues
  | .tset | .ttuple | .trange | .tstr => true
  | _ => false

private def tagNeedsUnavailableIteration : Tag -> Bool
  | .tobj _ | .tany | .tgen => true
  | _ => false

private def tagDefinitelyUnhashable : Tag -> Bool
  | .tlist | .tdict | .tdictkeys | .tdictitems | .tdictvalues
  | .tset => true
  | _ => false

private partial def valueMayBeUnhashable (fuel : Nat) (state : AState)
    (value : AbsVal) : Bool :=
  value.tags.any fun tag =>
    if tagDefinitelyUnhashable tag then true
    else
      match tag with
      | .ttuple =>
        if fuel == 0 then true
        else
          value.locs.any fun location =>
            location.cls == .tuple &&
              valueMayBeUnhashable (fuel - 1) state
                (state.heapGet location .elem)
      | _ => false

private partial def valueDefinitelyUnhashable (fuel : Nat) (state : AState)
    (value : AbsVal) : Bool :=
  !value.tags.isEmpty && value.tags.all fun tag =>
    if tagDefinitelyUnhashable tag then true
    else
      match tag with
      | .ttuple =>
        if fuel == 0 then false
        else
          let locations := value.locs.filter (·.cls == .tuple)
          !locations.isEmpty && locations.all (fun location =>
            state.emptinessGet location == .nonempty &&
              valueDefinitelyUnhashable (fuel - 1) state
                (state.heapGet location .elem))
      | _ => false

private partial def valueNeedsUnavailableHash (fuel : Nat) (state : AState)
    (value : AbsVal) : Bool :=
  value.tags.any fun tag =>
    match tag with
    | .tobj _ | .tany | .tgen => true
    | .ttuple =>
      if fuel == 0 then true
      else
        value.locs.any fun location =>
          location.cls == .tuple &&
            valueNeedsUnavailableHash (fuel - 1) state
              (state.heapGet location .elem)
    | _ => false

private def iterableElements (tag : Tag) (value : AbsVal)
    (state : AState) : AbsVal :=
  elemOf state (value.restrictTags [tag])

private def tagMayContainUnhashable (tag : Tag) (value : AbsVal)
    (state : AState) : Bool :=
  match tag with
  | .tset | .tdict | .tdictkeys => false
  | _ => valueMayBeUnhashable 8 state (iterableElements tag value state)

private def tagElementsDefinitelyUnhashable (tag : Tag) (value : AbsVal)
    (state : AState) : Bool :=
  valueDefinitelyUnhashable 8 state (iterableElements tag value state)

private def removeDirectlyUnhashable (value : AbsVal) : AbsVal :=
  value.withoutTags [
    .tlist, .tdict, .tdictkeys, .tdictitems, .tdictvalues, .tset
  ]

private def tagDefinitelyNonempty (tag : Tag) (value : AbsVal)
    (state : AState) : Bool :=
  match tag with
  | .tstr =>
    !value.strOpen && !value.strLits.isEmpty &&
      value.strLits.all (fun literal => !literal.isEmpty)
  | .trange => false
  | _ =>
    let locations := value.locs.filter (fun location =>
      location.cls.tag == tag)
    !locations.isEmpty && locations.all (fun location =>
      state.emptinessGet location == .nonempty)

private def tagDefinitelyEmpty (tag : Tag) (value : AbsVal)
    (state : AState) : Bool :=
  match tag with
  | .tstr =>
    !value.strOpen && !value.strLits.isEmpty &&
      value.strLits.all String.isEmpty
  | .trange => false
  | _ =>
    let restricted := value.restrictTags [tag]
    !restricted.locs.isEmpty && (iterableElements tag value state).isBot

private structure ArgumentCases where
  normal          : Bool := false
  typeError       : Bool := false
  definitelyEmpty : Bool := false

private def argumentCases (argument : AbsVal) (state : AState) :
    ArgumentCases := Id.run do
  let mut normal := false
  let mut typeError := false
  let mut allEmpty := !argument.tags.isEmpty
  for tag in argument.tags do
    if tagIsIterable tag then
      let guaranteedHashFailure :=
        tagDefinitelyNonempty tag argument state &&
          tagElementsDefinitelyUnhashable tag argument state
      normal := normal || !guaranteedHashFailure
      typeError := typeError ||
        tagMayContainUnhashable tag argument state
      allEmpty := allEmpty && tagDefinitelyEmpty tag argument state
    else
      typeError := true
      allEmpty := false
  return {
    normal
    typeError
    definitelyEmpty := allEmpty && !typeError
  }

private def setTransferRepresentable (receiver : AbsVal)
    (arguments : List AbsVal) (state : AState) : Bool :=
  !valueNeedsUnavailableHash 8 state (elemOf state receiver) &&
    arguments.all (fun argument =>
      !argument.tags.isEmpty &&
      !argument.tags.any tagNeedsUnavailableIteration &&
      !valueNeedsUnavailableHash 8 state (elemOf state argument))

private def executeDifferenceUpdate (p : Pos) (receiver : AbsVal)
    (arguments : List AbsVal) (state : AState) : M (Option Flow) := do
  if !setTransferRepresentable receiver arguments state then
    return none
  let mut normalState : Option AState := some state
  let mut raised : RaisedFlow := {}
  for argument in arguments do
    match normalState with
    | none => pure ()
    | some current =>
      let cases := argumentCases argument current
      if cases.typeError then
        raised ← addMachineRaise p "TypeError" current raised
      if cases.normal then
        normalState := some (
          if mustAliasSet receiver argument then
            clearSet receiver current
          else
            current)
      else
        normalState := none
  pure (some {
    normal := normalState.map fun outputState =>
      (V [.tnone], outputState)
    raised
  })

private def executeIntersectionUpdate (p : Pos) (receiver : AbsVal)
    (arguments : List AbsVal) (state : AState) : M (Option Flow) := do
  if !setTransferRepresentable receiver arguments state then
    return none
  let mut hasNormal := true
  let mut emptiesResult := false
  let mut raised : RaisedFlow := {}
  for argument in arguments do
    if hasNormal then
      let cases := argumentCases argument state
      if cases.typeError then
        raised ← addMachineRaise p "TypeError" state raised
      hasNormal := cases.normal
      emptiesResult := emptiesResult || cases.definitelyEmpty
  let normal :=
    if hasNormal then
      let outputState :=
        if emptiesResult then clearSet receiver state else state
      some (V [.tnone], outputState)
    else
      none
  pure (some { normal, raised })

private def executeSymmetricDifferenceUpdate (p : Pos)
    (receiver : AbsVal) (arguments : List AbsVal)
    (state : AState) : M (Option Flow) := do
  let some argument := arguments[0]? | return none
  if arguments.length != 1 ||
      !setTransferRepresentable receiver [argument] state then
    return none
  let cases := argumentCases argument state
  let aliases := mustAliasSet receiver argument
  let partialState :=
    if aliases then
      clearSet receiver state
    else
      growSet receiver
        (removeDirectlyUnhashable (elemOf state argument)) state
  let mut raised : RaisedFlow := {}
  if cases.typeError then
    raised ← addMachineRaise p "TypeError" partialState raised
  pure (some {
    normal :=
      if cases.normal then some (V [.tnone], partialState) else none
    raised
  })

private def allocateTuple (p : Pos) (slots : List AbsVal)
    (state : AState) : AbsVal × AState :=
  let (value, outputState) := allocate state p.id .tuple []
  let location : Loc := ⟨p.id, .tuple, true⟩
  let outputState := slots.zipIdx.foldl
    (fun current (slot, index) =>
      current.heapSet location (.tupleSlot index) slot) outputState
  let elements := slots.foldl AbsVal.join AbsVal.bot
  let outputState :=
    strongEmptinessUpdate (outputState.heapSet location .elem elements)
      location (if slots.isEmpty then .empty else .nonempty)
  (value, outputState)

private structure StringCases where
  string    : Bool := false
  nonString : Bool := false

private def stringCases (value : AbsVal) : StringCases :=
  {
    string := Tag.tstr ∈ value.tags || Tag.tany ∈ value.tags
    nonString := Tag.tany ∈ value.tags ||
      value.tags.any (· != Tag.tstr)
  }

private def mayBeEmptyString (value : AbsVal) : Bool :=
  value.strOpen || value.strLits.contains "" || Tag.tany ∈ value.tags

private def mayBeNonemptyString (value : AbsVal) : Bool :=
  value.strOpen ||
    value.strLits.any (fun literal => !literal.isEmpty) ||
    Tag.tany ∈ value.tags

private def executePartition (p : Pos) (arguments : List AbsVal)
    (state : AState) : M (Option Flow) := do
  let some separator := arguments[0]? | return none
  if arguments.length != 1 then return none
  let cases := stringCases separator
  let mut result : Flow := {}
  if cases.string && mayBeNonemptyString separator then
    let (tuple, outputState) :=
      allocateTuple p [V [.tstr], V [.tstr], V [.tstr]] state
    result := result.join (Flow.ofNormal tuple outputState)
  if cases.string && mayBeEmptyString separator then
    result := result.join (← machineRaise p "ValueError" state)
  if cases.nonString then
    result := result.join (← machineRaise p "TypeError" state)
  pure (some result)

private def executePopitem (p : Pos) (receiver : AbsVal)
    (arguments : List AbsVal) (state : AState) : M (Option Flow) := do
  if !arguments.isEmpty || receiver.locs.isEmpty ||
      receiver.locs.any (fun location => location.cls.tag != .tdict) then
    return none
  let context ← get
  let mut keys : AbsVal := AbsVal.bot
  let mut values : AbsVal := AbsVal.bot
  let mut maySucceed := false
  let mut mayBeEmpty := false
  let mut typedAlternatives : Flow := {}
  let mut hasGeneric := false
  for location in receiver.locs do
    match location.cls with
    | .dict =>
      hasGeneric := true
      let locationKeys := state.heapGet location .dictKeys
      let definitelyNonempty :=
        state.emptinessGet location == .nonempty
      maySucceed := maySucceed || definitelyNonempty || !locationKeys.isBot
      mayBeEmpty := mayBeEmpty || !definitelyNonempty
      keys := keys.join locationKeys
      values := values.join (state.heapGet location .dictValues)
    | .td typeName =>
      match context.classes.getCls? typeName with
      | none =>
        hasGeneric := true
        let locationKeys := state.heapGet location .dictKeys
        maySucceed := maySucceed || !locationKeys.isBot
        mayBeEmpty := true
        keys := keys.join locationKeys
        values := values.join (state.heapGet location .dictValues)
      | some info =>
        let mut locationMayBeEmpty := true
        for field in info.fields do
          let stored := state.heapGet location (.literalKey field.name)
          let present := stored.withoutTags [.tmissing]
          if !present.isBot then
            if !(Tag.tmissing ∈ stored.tags) then
              locationMayBeEmpty := false
            if field.required || field.readOnly then
              if let some detail := shapeObligation .popItem typeName field then
                oblige p "shape-break" detail
            else
              let removed :=
                if completeStrongTarget receiver location then
                  state.heapSet location (.literalKey field.name) (V [.tmissing])
                else
                  state.heapJoin location (.literalKey field.name) (V [.tmissing])
              let (tuple, outputState) :=
                allocateTuple p [strLitV field.name, present] removed
              typedAlternatives := typedAlternatives.join
                (Flow.ofNormal tuple outputState)
        mayBeEmpty := mayBeEmpty || locationMayBeEmpty
    | _ => pure ()
  let mut result : Flow := typedAlternatives
  if hasGeneric && maySucceed && !keys.isBot && !values.isBot then
    let mutationState :=
      match receiver.locs with
      | [location] =>
        if location.cls == .dict &&
            completeStrongTarget receiver location then
          strongEmptinessUpdate state location .top
        else
          state
      | _ => state
    let (tuple, outputState) :=
      allocateTuple p [keys.reduce, values.reduce] mutationState
    result := result.join (Flow.ofNormal tuple outputState)
  if mayBeEmpty then
    result := result.join (← machineRaise p "KeyError" state)
  pure (some result)

private def lengthsMayAgree (left right : AbsVal) : Bool :=
  left.strOpen || right.strOpen ||
    Tag.tany ∈ left.tags || Tag.tany ∈ right.tags ||
    left.strLits.any fun x =>
      right.strLits.any fun y => x.length == y.length

private def lengthsMayDiffer (left right : AbsVal) : Bool :=
  left.strOpen || right.strOpen ||
    Tag.tany ∈ left.tags || Tag.tany ∈ right.tags ||
    left.strLits.any fun x =>
      right.strLits.any fun y => x.length != y.length

private structure TranslationKeyCases where
  normal     : Bool := false
  typeError  : Bool := false
  valueError : Bool := false

private def translationKeyCases (keys : AbsVal) : TranslationKeyCases :=
  if keys.isBot then
    { normal := true }
  else Id.run do
    let mut normal := false
    let mut typeError := false
    let mut valueError := false
    for tag in keys.tags do
      match tag with
      | .tint =>
        normal := true
      | .tstr =>
        normal := normal || keys.strOpen ||
          keys.strLits.any (fun key => key.length == 1)
        valueError := valueError || keys.strOpen ||
          keys.strLits.any (fun key => key.length != 1)
      | .tany =>
        normal := true
        typeError := true
        valueError := true
      | .tunbound | .tuninit | .tmissing =>
        pure ()
      | _ =>
        typeError := true
    return { normal, typeError, valueError }

private def executeMaketransMapping (p : Pos) (source : AbsVal)
    (state : AState) : M Flow := do
  let mut keys : AbsVal := AbsVal.bot
  let mut values : AbsVal := AbsVal.bot
  let mut mapping := false
  let mut invalidSource := false
  for tag in source.tags do
    match tag with
    | .tdict =>
      mapping := true
      for location in source.locs do
        if location.cls.tag == .tdict then
          keys := keys.join (state.heapGet location .dictKeys)
          values := values.join (state.heapGet location .dictValues)
    | .tany =>
      mapping := true
      invalidSource := true
      keys := keys.join anyV
      values := values.join anyV
    | .tunbound | .tuninit | .tmissing =>
      pure ()
    | _ =>
      invalidSource := true
  let cases := translationKeyCases keys
  let mut result : Flow := {}
  if mapping && cases.normal then
    let (translated, outputState) := allocate state p.id .dict []
    let location : Loc := ⟨p.id, .dict, true⟩
    let outputState :=
      (outputState.heapSet location .dictKeys (V [.tint]))
        |>.heapSet location .dictValues values
    result := result.join (Flow.ofNormal translated outputState)
  if invalidSource || cases.typeError then
    result := result.join (← machineRaise p "TypeError" state)
  if mapping && cases.valueError then
    result := result.join (← machineRaise p "ValueError" state)
  pure result

private def executeMaketrans (p : Pos) (arguments : List AbsVal)
    (state : AState) : M (Option Flow) := do
  if arguments.length == 1 then
    return some (← executeMaketransMapping p arguments[0]! state)
  if arguments.length != 2 && arguments.length != 3 then return none
  let x := arguments[0]!
  let y := arguments[1]!
  let z? := arguments[2]?
  let xCases := stringCases x
  let yCases := stringCases y
  let zCases := z?.map stringCases
  let zMayString := zCases.all (·.string)
  let anyTypeError :=
    xCases.nonString || yCases.nonString ||
      zCases.any (·.nonString)
  let mut result : Flow := {}
  if xCases.string && yCases.string && zMayString &&
      lengthsMayAgree x y then
    let (mapping, outputState) := allocate state p.id .dict []
    let location : Loc := ⟨p.id, .dict, true⟩
    let mappedValues :=
      if z?.isSome then V [.tint, .tnone] else V [.tint]
    let outputState :=
      ((outputState.heapSet location .dictKeys (V [.tint])).heapSet location .dictValues mappedValues)
    result := result.join (Flow.ofNormal mapping outputState)
  if xCases.string && yCases.string && zMayString &&
      lengthsMayDiffer x y then
    result := result.join (← machineRaise p "ValueError" state)
  if anyTypeError then
    result := result.join (← machineRaise p "TypeError" state)
  pure (some result)

/-- `close()` injects `GeneratorExit` at the suspension point so the body's
    `finally` blocks run, and then swallows it: the exit itself never escapes,
    which is what makes it an internal signal rather than an outcome.

    What can escape is `RuntimeError`, when the body yields while closing, and
    whatever the body's cleanup raises -- a `finally` that raises raises through
    `close()`. The classes the body can raise are tracked per allocation site, so
    they are replayed here with user provenance: they propagate out of code already
    analyzed under the policy rather than being machine-raised at this call.

    `StopIteration` is excluded because a `return` reached while closing is a
    normal close, and `GeneratorExit` because swallowing it is the point. -/
private def executeGeneratorClose (p : Pos) (receiver : AbsVal)
    (state : AState) : M Flow := do
  let bodyClasses <- genExcOf receiver
  let mut result : Flow := Flow.ofNormal (V [.tnone]) state
  let mut raised : RaisedFlow := {}
  resCaseAt p "call" ".close(..)" "gen" "!RuntimeError"
  raised <- addMachineRaise p "RuntimeError" state raised
  for cls in bodyClasses do
    if cls != "GeneratorExit" && cls != "StopIteration" then
      raised := raised.add
        { cls, value := AbsVal.bot, state, origin := p, from? := .user }
      -- A rule's declared raised-class list cannot name these: which classes a
      -- body's cleanup raises is a property of the analyzed program, not of the
      -- rule. Reported here so the site's row states every outcome its flow
      -- carries.
      resCaseAt p "call" ".close(..)" "gen" s!"!{cls}"
  pure { result with raised := result.raised.join raised }

/-- Execute a known precise transfer. `none` deliberately retains the opaque
    fallback for methods requiring an abstract domain or protocol service not
    available to this module. -/
def execute (p : Pos) (method : OpaqueBuiltinMethod) (receiver : AbsVal)
    (arguments : List AbsVal) (state : AState) : M (Option Flow) :=
  match method with
  | .setDifferenceUpdate =>
    executeDifferenceUpdate p receiver arguments state
  | .setIntersectionUpdate =>
    executeIntersectionUpdate p receiver arguments state
  | .setSymmetricDifferenceUpdate =>
    executeSymmetricDifferenceUpdate p receiver arguments state
  | .strPartition | .strRpartition =>
    executePartition p arguments state
  | .dictPopitem =>
    executePopitem p receiver arguments state
  | .strMaketrans =>
    executeMaketrans p arguments state
  | .genClose =>
    Option.some <$> executeGeneratorClose p receiver state
  | .strEncode | .strFormatMap | .strTranslate
  | .genSend | .genThrow =>
    pure none

end Pylate.RuleDriven.KnownMethods
