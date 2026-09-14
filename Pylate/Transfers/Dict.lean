/-
The the dict and TypedDict method service.

The direct analyzer remains the differential oracle. This module deliberately
owns its key partitioning and field-update logic so agreement is not obtained
by calling the direct transfer.
-/
import Pylate.RuleLang.Keys

namespace Pylate.RuleDriven.Dict

open Pylate


def typedDictKeys (info : ClassInfo) : AbsVal :=
  info.fields.foldl
    (fun result field => result.join (strLitV field.name))
    AbsVal.bot

def typedDictValues (info : ClassInfo) (location : Loc)
    (state : AState) : AbsVal :=
  info.fields.foldl
    (fun result field =>
      result.join
        ((state.heapGet location (.literalKey field.name)).withoutTags [.tmissing]))
    AbsVal.bot

-- One definition, in `Cells/State.lean` beside `heapSet` and `heapJoin`, because
-- choosing between them is what this predicate is for. Four identical copies
-- lived in four files and no test distinguished them.
abbrev isSoleRecentTarget := @strongUpdateTarget

def soleRecent (receiver : AbsVal) (cls : LocCls) : Option Loc :=
  match receiver.locs with
  | [location] =>
    if location.cls == cls && isSoleRecentTarget receiver location then
      some location
    else
      none
  | _ => none

def flowOfResult (result : Flow) : Flow :=
  { normal := result.normal, raised := result.raised }

def checkHashable (p : Pos) (value : AbsVal) : M Unit := do
  let bad := value.tags.filter fun tag =>
    tag == .tlist || tag == .tdict || tag == .tset
  if !bad.isEmpty then
    oblige p "hashability"
      s!"unhashable tags {bad.map Tag.render} at a key or element position"

-- One definition, in `Machine.lean`, taking the operation. This was the third of
-- three copies, and the copies had already diverged on the undeclared-key heap
-- write.
def updateTypedDictField (p : Pos) (receiver : AbsVal) (location : Loc)
    (typeName key : String) (info : ClassInfo) (value : AbsVal)
    (definite : Bool) (state : AState) : M AState :=
  Pylate.updateTypedDictField .update p receiver location typeName key info
    value definite state

def edgeRead (receiver : AbsVal) (cls : LocCls) (edge : CellSelector)
    (state : AState) : AbsVal := Id.run do
  let mut result : AbsVal := AbsVal.bot
  for location in receiver.locs do
    if location.cls == cls ||
        (cls == LocCls.dict && location.cls.tag == .tdict) then
      result := result.join (state.heapGet location edge)
  return result

def edgeReadDict (value : AbsVal) (edge : CellSelector)
    (state : AState) : AbsVal := Id.run do
  let mut result : AbsVal := AbsVal.bot
  for location in value.locs do
    if location.cls.tag == .tdict then
      result := result.join (state.heapGet location edge)
  return result

def joinDictEdge (receiver : AbsVal) (edge : CellSelector) (value : AbsVal)
    (state : AState) : AState := Id.run do
  let mut result := state
  for location in receiver.locs do
    if location.cls == .dict then
      result := result.heapJoin location edge value
  return result

def freshView (p : Pos) (cls : LocCls) (source elements : AbsVal)
    (state : AState) : AbsVal × AState :=
  let (view, nextState) := allocate state p.id cls []
  let location : Loc := ⟨p.id, cls, true⟩
  let initialized :=
    (nextState.heapSet location dictViewSourceCell source).heapSet location .elem elements
  (view, initialized)

/--CLAIM dict-get-default: `get` on a missing key yields the default, or
    `None` with no default, and never raises.
-/
def executeGet (p : Pos) (receiver : AbsVal) (arguments : List AbsVal)
    (state : AState) : M Flow := do
  let context ← get
  let key := arguments.headD AbsVal.bot
  let defaultValue := arguments[1]?.getD (V [.tnone])
  let keys := keyCases key
  let mut value : AbsVal := AbsVal.bot
  let mut exceptions : Exc := {}
  for location in receiver.locs do
    match location.cls with
    | .td typeName =>
      match context.classes.getCls? typeName with
      | some info =>
        for literal in keys.literals do
          match info.fields.find? (·.name == literal) with
          | some _ =>
            let fieldValue := state.heapGet location (.literalKey literal)
            value := value.join (fieldValue.withoutTags [.tmissing])
            if Tag.tmissing ∈ fieldValue.tags then
              value := value.join defaultValue
          | none =>
            value := value.join defaultValue
        if keys.openString || keys.userEquality then
          if keys.userEquality then
            oblige p "special-method"
              s!"key equality/hash against TypedDict {typeName} succeeds without side effects"
          value := value.join (typedDictValues info location state)
            |>.join defaultValue
        if keys.absent then
          value := value.join defaultValue
        if keys.unhashable then
          exceptions ← mraise p exceptions state ["TypeError"]
        if keys.unknown then
          oblige p "dispatch-any" s!"unknown key passed to {typeName}.get"
          value := value.join anyV
          exceptions ← mraise p exceptions state ["TypeError"]
      | none =>
        value := value.join (state.heapGet location .dictValues)
    | .dict =>
      -- The default is reachable only when the key can be missing. A key the
      -- per-key cells prove present makes `none` (or the given default) an
      -- outcome that cannot happen.
      if allKeysPresent state location keys then
        for literal in keys.literals do
          value := value.join (keyValue state location literal)
      else
        value := value.join (state.heapGet location .dictValues) |>.join defaultValue
      if keys.unhashable || keys.unknown then
        exceptions ← mraise p exceptions state ["TypeError"]
    | _ => pure ()
  pure (flowOfResult { normal := some (value.reduce, state), raised := exceptions })

/--CLAIM dict-pop-missing: `pop` on a missing key raises `KeyError` unless a
    default was supplied.
-/
def executePop (p : Pos) (receiver : AbsVal) (arguments : List AbsVal)
    (state : AState) : M Flow := do
  let context ← get
  let key := arguments.headD AbsVal.bot
  let defaultValue? := arguments[1]?
  let keys := keyCases key
  let mut value : AbsVal := AbsVal.bot
  let mut exceptions : Exc := {}
  let mut outputState := state
  for location in receiver.locs do
    match location.cls with
    | .td typeName =>
      match context.classes.getCls? typeName with
      | some info =>
        for literal in keys.literals do
          match info.fields.find? (·.name == literal) with
          | some field =>
            let fieldValue := outputState.heapGet location (.literalKey literal)
            value := value.join (fieldValue.withoutTags [.tmissing])
            if let some detail := shapeObligation .pop typeName field then
              oblige p "shape-break" detail
            else
              let missing := V [.tmissing]
              outputState :=
                if isSoleRecentTarget receiver location then
                  outputState.heapSet location (.literalKey literal) missing
                else
                  outputState.heapJoin location (.literalKey literal) missing
            if Tag.tmissing ∈ fieldValue.tags then
              match defaultValue? with
              | some defaultValue => value := value.join defaultValue
              | none =>
                exceptions ← mraise p exceptions outputState ["KeyError"]
          | none =>
            match defaultValue? with
            | some defaultValue => value := value.join defaultValue
            | none =>
              exceptions ← mraise p exceptions outputState ["KeyError"]
        if keys.openString || keys.userEquality || keys.unknown then
          if let some detail := unresolvedKeyObligation .pop typeName then
            oblige p "shape-break" detail
          value := value.join (typedDictValues info location outputState)
          match defaultValue? with
          | some defaultValue => value := value.join defaultValue
          | none =>
            exceptions ← mraise p exceptions outputState ["KeyError"]
      | none =>
        value := value.join (outputState.heapGet location .dictValues)
    | .dict =>
      -- A key proven present pops without raising, and the popped cell is
      -- tighter than the `val` summary. The removal itself is applied below.
      if allKeysPresent outputState location keys then
        for literal in keys.literals do
          value := value.join (keyValue outputState location literal)
      else
        value := value.join (outputState.heapGet location .dictValues)
        match defaultValue? with
        | some defaultValue => value := value.join defaultValue
        | none =>
          exceptions ← mraise p exceptions outputState ["KeyError"]
    | _ => pure ()
  if keys.absent then
    match defaultValue? with
    | some defaultValue => value := value.join defaultValue
    | none => exceptions ← mraise p exceptions outputState ["KeyError"]
  if keys.unhashable || keys.unknown then
    exceptions ← mraise p exceptions outputState ["TypeError"]
  -- A successful `pop` removes one key, so cardinality is no longer known and
  -- the removed literal may be gone.
  for location in receiver.locs do
    if location.cls == .dict then
      let strong := isSoleRecentTarget receiver location
      for literal in keys.literals do
        let cell := CellSelector.literalKey literal
        outputState :=
          if strong then outputState.heapSet location cell (V [.tmissing])
          else outputState.heapJoin location cell (V [.tmissing])
      outputState :=
        if strong then strongEmptinessUpdate outputState location .top
        else weakEmptinessUpdate outputState location .top
  pure (flowOfResult { normal := some (value.reduce, outputState), raised := exceptions })

/--CLAIM dict-view-types: `keys`, `values`, and `items` yield view objects,
    not lists.
-/
def executeKeysOrValues (p : Pos) (receiver : AbsVal)
    (keys : Bool) (state : AState) : M Flow := do
  let context ← get
  let mut elements : AbsVal := AbsVal.bot
  for location in receiver.locs do
    match location.cls with
    | .td typeName =>
      match context.classes.getCls? typeName with
      | some info =>
        elements := elements.join
          (if keys then typedDictKeys info
           else typedDictValues info location state)
      | none =>
        elements := elements.join
          (state.heapGet location (if keys then .dictKeys else .dictValues))
    | .dict =>
      elements := elements.join
        (state.heapGet location (if keys then .dictKeys else .dictValues))
    | _ => pure ()
  let cls := if keys then LocCls.dictkeys else LocCls.dictvalues
  let (view, outputState) := freshView p cls receiver elements state
  pure (Flow.ofNormal view outputState)

def executeItems (p : Pos) (receiver : AbsVal)
    (state : AState) : M Flow := do
  let context ← get
  let (tupleValue, tupleState) := allocate state p.id .tuple []
  let tupleLocation : Loc := ⟨p.id, .tuple, true⟩
  let mut keys : AbsVal := AbsVal.bot
  let mut values : AbsVal := AbsVal.bot
  for location in receiver.locs do
    match location.cls with
    | .td typeName =>
      match context.classes.getCls? typeName with
      | some info =>
        keys := keys.join (typedDictKeys info)
        values := values.join (typedDictValues info location state)
      | none => pure ()
    | .dict =>
      keys := keys.join (state.heapGet location .dictKeys)
      values := values.join (state.heapGet location .dictValues)
    | _ => pure ()
  let tupleState :=
    ((tupleState.heapSet tupleLocation (.tupleSlot 0) keys).heapSet
      tupleLocation (.tupleSlot 1) values)
      |>.heapSet tupleLocation .elem (keys.join values)
      |>.heapSet tupleLocation dictViewSourceCell receiver
  let (view, outputState) :=
    freshView p .dictitems receiver tupleValue tupleState
  pure (Flow.ofNormal view outputState)

/--CLAIM dict-setdefault-inserts: `setdefault` inserts on a miss and returns
    the value now stored.
-/
def executeSetdefault (p : Pos) (receiver : AbsVal)
    (arguments : List AbsVal) (literalKey : Option String)
    (state : AState) : M Flow := do
  let context ← get
  let key := arguments.headD AbsVal.bot
  let defaultValue := arguments[1]?.getD (V [.tnone])
  checkHashable p key
  let mut outputState := state
  let mut result : AbsVal := AbsVal.bot
  for location in receiver.locs do
    match location.cls, literalKey,
        context.classes.getCls? (match location.cls with
          | .td typeName => typeName
          | _ => "") with
    | .td typeName, some literal, some info =>
      match info.fields.find? (·.name == literal) with
      | some field =>
        -- `setdefault` writes only when the key may be absent, so a definitely
        -- present read-only key is untouched and breaks no shape.
        let mayInsert :=
          Tag.tmissing ∈ (outputState.heapGet location (.literalKey literal)).tags
        -- `mayInsert` is a heap fact and stays here; the field test and the
        -- wording come from the table.
        if mayInsert then
          if let some detail := shapeObligation .setDefault typeName field then
            oblige p "shape-break" detail
        if let some annotation := field.ann then
          if !annEntailedDeep 16 context.classes outputState defaultValue
              annotation then
            oblige p "type-error"
              s!"{typeName}.{literal}: setdefault does not satisfy the declared type"
        let fieldValue := outputState.heapGet location (.literalKey literal)
        let present := fieldValue.withoutTags [.tmissing]
        let inserted := match field.ann with
          | some annotation =>
            assumeAnn context.classes defaultValue annotation
          | none => defaultValue
        let selected :=
          if Tag.tmissing ∈ fieldValue.tags then present.join inserted
          else present
        outputState :=
          outputState.heapStore receiver location (.literalKey literal) selected
        outputState := outputState.heapJoin location .dictValues selected
        result := result.join selected
      | none =>
        if let some detail :=
            undeclaredKeyObligation .setDefault typeName literal then
          oblige p "shape-break" detail
        result := result.join defaultValue
    | .td typeName, none, _ =>
      oblige p "key-membership"
        s!"dynamic setdefault key on TypedDict {typeName}"
      result := result.join
        ((outputState.heapGet location .dictValues).withoutTags [.tmissing])
        |>.join defaultValue
    | .dict, _, _ =>
      outputState := (outputState.heapJoin location .dictKeys key).heapJoin location .dictValues defaultValue
      result := result.join (outputState.heapGet location .dictValues)
    | _, _, _ => pure ()
  pure (Flow.ofNormal result.reduce outputState)

/--CLAIM dict-update-keywords: `update` takes keyword arguments as keys as
    well as a mapping or pair sequence.
-/
def executeUpdate (p : Pos) (receiver : AbsVal)
    (arguments : List AbsVal) (keywords : List (String × AbsVal))
    (state : AState) : M Flow := do
  let context ← get
  let sourceValue := arguments.headD AbsVal.bot
  let inputState := state
  let mut outputState :=
    joinDictEdge receiver .dictKeys (edgeReadDict sourceValue .dictKeys inputState)
      (joinDictEdge receiver .dictValues
        (edgeReadDict sourceValue .dictValues inputState) inputState)
  for location in receiver.locs do
    if location.cls == .dict then
      -- Keyword arguments are keys too. Only the positional source was folded
      -- into the summary edges above, so `d.update(b=2)` on a plain dict lost
      -- `b` outright: absent from the key summary and with no per-key cell,
      -- where `d["b"] = 2` and `d.update({"b": 2})` both record it.
      --
      -- The key summary is what `annEntailedDeep` reads to decide a TypedDict's
      -- key set is closed, so a dropped key there lets a value claim a shape it
      -- does not have. `update` writes every keyword unconditionally, hence a
      -- strong update when this is the sole recent target.
      for (key, value) in keywords do
        outputState := outputState.heapJoin location .dictKeys (strLitV key)
        outputState := outputState.heapJoin location .dictValues value
        let cell := CellSelector.literalKey key
        outputState := outputState.heapStore receiver location cell value
    if let .td typeName := location.cls then
      match context.classes.getCls? typeName with
      | some info =>
        for (key, value) in keywords do
          outputState ← updateTypedDictField p receiver location typeName key
            info value true outputState
        for source in sourceValue.locs do
          match source.cls with
          | .td sourceName =>
            match context.classes.getCls? sourceName with
            | some sourceInfo =>
              for sourceField in sourceInfo.fields do
                let value :=
                  (inputState.heapGet source (.literalKey sourceField.name)).withoutTags [.tmissing]
                if !value.isBot then
                  outputState ← updateTypedDictField p receiver location
                    typeName sourceField.name info value false outputState
            | none => pure ()
          | .dict =>
            let sourceKeys := keyCases (inputState.heapGet source .dictKeys)
            for key in sourceKeys.literals do
              let exact := inputState.heapGet source (.literalKey key)
              let value :=
                if exact.isBot then inputState.heapGet source .dictValues else exact
              outputState ← updateTypedDictField p receiver location typeName
                key info value false outputState
            if sourceKeys.openString || sourceKeys.userEquality ||
                sourceKeys.unknown then
              oblige p "key-membership"
                s!"dynamic mapping update on TypedDict {typeName} uses declared keys"
              let value := inputState.heapGet source .dictValues
              for field in info.fields do
                outputState ← updateTypedDictField p receiver location typeName
                  field.name info value false outputState
            if sourceKeys.absent || sourceKeys.unhashable then
              if let some detail := unresolvedKeyObligation .update typeName then
                oblige p "shape-break" detail
          | _ => pure ()
        if sourceValue.tags.any (· != Tag.tdict) then
          oblige p "dispatch-any"
            s!"non-dictionary update source for TypedDict {typeName} is widened"
          for field in info.fields do
            outputState ← updateTypedDictField p receiver location typeName
              field.name info anyV false outputState
      | none => pure ()
  pure (Flow.ofNormal (V [.tnone]) outputState)

def executeCopy (p : Pos) (receiver : AbsVal)
    (state : AState) : M Flow := do
  let context ← get
  let mut result : AbsVal := AbsVal.bot
  let mut outputState := state
  let mut seen : Fset LocCls := []
  for source in receiver.locs do
    if source.cls.tag == .tdict && !(source.cls ∈ seen) then
      seen := Fset.insert source.cls seen
      match source.cls with
      | .td typeName =>
        let (value, nextState) := allocate outputState p.id (.td typeName) []
        result := result.join value
        outputState := nextState
        let destination : Loc := ⟨p.id, .td typeName, true⟩
        match context.classes.getCls? typeName with
        | some info =>
          for field in info.fields do
            let mut fieldValue : AbsVal := AbsVal.bot
            for candidate in receiver.locs do
              if candidate.cls == LocCls.td typeName then
                fieldValue := fieldValue.join
                  (state.heapGet candidate (.literalKey field.name))
            outputState := outputState.heapSet destination (.literalKey field.name) fieldValue
          outputState :=
            (outputState.heapSet destination .dictKeys (typedDictKeys info))
              |>.heapSet destination .dictValues
                (typedDictValues info destination outputState)
        | none => pure ()
      | .dict =>
        let (value, nextState) := allocate outputState p.id .dict []
        result := result.join value
        let destination : Loc := ⟨p.id, .dict, true⟩
        outputState :=
          (nextState.heapSet destination .dictKeys
            (edgeRead receiver .dict .dictKeys state))
            |>.heapSet destination .dictValues
              (edgeRead receiver .dict .dictValues state)
      | _ => pure ()
  pure (Flow.ofNormal result.reduce outputState)

def executeFromkeys (p : Pos) (arguments : List AbsVal)
    (state : AState) : M Flow :=
  let (value, nextState) := allocate state p.id .dict []
  let location : Loc := ⟨p.id, .dict, true⟩
  let keys := elemOf state (arguments.headD AbsVal.bot)
  let stored := arguments[1]?.getD (V [.tnone])
  let outputState :=
    (nextState.heapSet location .dictKeys keys).heapSet location .dictValues stored
  pure (Flow.ofNormal value outputState)

/-- The literal-key cells a location currently carries. -/
def literalKeyCells (state : AState) (location : Loc) :
    List CellSelector :=
  state.heap.fold (init := []) fun out key _ =>
    match key.2 with
    | .literalKey _ =>
      if key.1 == location then Fset.insert key.2 out else out
    | _ => out

/-- Removing keys must retire the per-key cells and the cardinality claim.
    Leaving either behind lets a later `popitem` conclude the dictionary is
    still nonempty and drop its `KeyError`.

    Plain dictionaries only. A TypedDict's declared keys are its shape, so
    retiring one is a shape break to be reported, not a heap update to be
    modelled; the callers own that decision and this refuses to make it for
    them. -/
def retireKeys (state : AState) (receiver : AbsVal) (location : Loc)
    (emptiness : Emptiness) : AState :=
  if location.cls != .dict then state else
  let strong := isSoleRecentTarget receiver location
  let cleared := (literalKeyCells state location).foldl (fun current cell =>
    if strong then current.heapSet location cell (V [.tmissing])
    else current.heapJoin location cell (V [.tmissing])) state
  if strong then strongEmptinessUpdate cleared location emptiness
  else weakEmptinessUpdate cleared location emptiness

def executeClear (p : Pos) (receiver : AbsVal)
    (state : AState) : M Flow := do
  let context ← get
  let mut outputState := state
  for location in receiver.locs do
    match location.cls with
    | .td typeName =>
      match context.classes.getCls? typeName with
      | some info =>
        if info.fields.any (fun field => field.required || field.readOnly) then
          if let some detail :=
              wholesaleRemovalObligation .clear typeName "" then
            oblige p "shape-break" detail
        else if isSoleRecentTarget receiver location then
          for field in info.fields do
            outputState := outputState.heapSet location (.literalKey field.name)
              (V [.tmissing])
          outputState := outputState.heapSet location .dictValues AbsVal.bot
        else
          for field in info.fields do
            outputState := outputState.heapJoin location (.literalKey field.name)
              (V [.tmissing])
        -- A TypedDict whose keys are all optional may legitimately be emptied,
        -- so its cardinality claim is retired here; one with a required key
        -- kept its cells above and keeps its shape.
        if !info.fields.any (fun field => field.required || field.readOnly) then
          outputState :=
            if isSoleRecentTarget receiver location then
              strongEmptinessUpdate outputState location .empty
            else weakEmptinessUpdate outputState location .empty
      | none => pure ()
    | .dict =>
      if let some only := soleRecent receiver .dict then
        outputState :=
          (outputState.heapSet only .dictKeys AbsVal.bot).heapSet only .dictValues AbsVal.bot
    | _ => pure ()
  -- `clear` empties the dictionary: retire its keys and its cardinality.
  for location in receiver.locs do
    if location.cls.tag == .tdict then
      outputState := retireKeys outputState receiver location .empty
  pure (Flow.ofNormal (V [.tnone]) outputState)

def execute (p : Pos) (method : DictMethod) (receiver : AbsVal)
    (arguments : List AbsVal) (keywords : List (String × AbsVal))
    (literalKey : Option String) (state : AState) : M Flow :=
  match method with
  | .get => executeGet p receiver arguments state
  | .pop => executePop p receiver arguments state
  | .keys => executeKeysOrValues p receiver true state
  | .values => executeKeysOrValues p receiver false state
  | .items => executeItems p receiver state
  | .setdefault =>
    executeSetdefault p receiver arguments literalKey state
  | .update => executeUpdate p receiver arguments keywords state
  | .copy => executeCopy p receiver state
  | .fromkeys => executeFromkeys p arguments state
  | .clear => executeClear p receiver state

end Pylate.RuleDriven.Dict
