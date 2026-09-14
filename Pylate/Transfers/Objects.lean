/-
Transfers for attributes and subscripts.

The receiver, index, and stored value have already been evaluated when these
operations are called.  Static class lookup and heap operations are pure; the
only service supplied by the enclosing interpreter is user FuncDef invocation.
-/
import Pylate.RuleLang.Keys

namespace Pylate.RuleDriven.Objects

open Pylate
open Pylate.RuleDriven

structure Services where
  invokeUser : Pos -> String -> FuncDef -> List AbsVal ->
    List (String × AbsVal) -> AState -> M Flow


-- One definition, in `Cells/State.lean` beside `heapSet` and `heapJoin`, because
-- choosing between them is what this predicate is for. Four identical copies
-- lived in four files and no test distinguished them.
private abbrev completeStrongTarget := @strongUpdateTarget

private def machineRaise (p : Pos) (cls : String) (state : AState) :
    M Flow := do
  let modeled ← mraise p {} state [cls]
  if cls ∈ modeled.tags then
    pure {
      raised := {
        cases := [{
          cls
          value := AbsVal.bot
          state := modeled.st.getD state
          origin := p
        }]
      }
    }
  else
    pure {}

private def addMachineRaise (p : Pos) (result : Flow) (cls : String)
    (state : AState) : M Flow := do
  pure (result.join (← machineRaise p cls state))

private def addMachineRaises (p : Pos) (result : Flow)
    (classes : Fset String) (state : AState) : M Flow := do
  let mut result := result
  for cls in classes do
    result ← addMachineRaise p result cls state
  pure result

private def normal (value : AbsVal) (state : AState) : Flow :=
  Flow.ofNormal value state

private def normalWrite (state : AState) : Flow :=
  Flow.ofNormal (V [.tnone]) state

private def discardWriteResult (flow : Flow) : Flow :=
  { flow with normal := flow.normal.map fun (_, outputState) =>
      (V [.tnone], outputState) }

private def checkHashable (p : Pos) (value : AbsVal) : M Unit := do
  let bad := value.tags.filter fun tag =>
    tag == .tlist || tag == .tdict || tag == .tset
  if !bad.isEmpty then
    oblige p "hashability"
      s!"unhashable tags {bad.map Tag.render} at a key or element position"

private def resolve (className member : String) :
    M (Option (String × FuncDef)) := do
  let context ← get
  pure (resolveMethod context.classes className member)

private def typedDictValues (info : ClassInfo) (location : Loc)
    (state : AState) : AbsVal :=
  info.fields.foldl
    (fun result field =>
      result.join
        ((state.heapGet location (.literalKey field.name)).withoutTags [.tmissing]))
    AbsVal.bot

-- One definition, in `Machine.lean`. This copy had no `definite` parameter,
-- which is to say it always passed `true`: a subscript store happens on every
-- path that reaches it.
private def updateTypedDictField (p : Pos) (receiver : AbsVal)
    (location : Loc) (typeName key : String) (info : ClassInfo)
    (value : AbsVal) (state : AState) : M AState :=
  Pylate.updateTypedDictField .setItem p receiver location typeName key info
    value true state

/-- Narrow the state carried on one exceptional edge to the receiver value that
    produced it.

    A `Completion` already keeps a separate state per exception class, so the
    edges are distinct; what was missing is that the state on a raising edge was
    the ambient one. For `x = A() if c else B()` where only `B` lacks the
    attribute, the handler saw `x : obj:A | obj:B` even though `obj:A` provably
    cannot reach it.

    The transfer knows which tag failed -- it iterates them -- but not which
    variable held the receiver, which is why this takes the receiver's syntax.
    A plain name is narrowed directly; any other expression is left alone, since
    there is no single cell to write the refinement back to. Sound either way:
    not narrowing is the over-approximation.

    Only valid where no user code runs between the read and the raise, which
    holds for these branches: they are the cases with no method to call. -/
private def narrowReceiver (receiverExpr : Option Expr) (narrowed : AbsVal)
    (state : AState) : AState :=
  match receiverExpr with
  | some (.name _ x) =>
    if (state.envGet x).isBot then state else state.envSet x narrowed
  | _ => state

/-- A sequence index must be an integer. CPython raises `TypeError` for
    `xs["a"]`, and the sequence branches below used to ignore the index type
    entirely: they reported a normal element read plus `IndexError` and no
    `TypeError`, so a read that always raises was analysed as returning a value.
    That is unsound in the direction that matters, because the statements after it
    were then reachable and their obligations dischargeable.

    Slices are the other thing CPython accepts here, and the admitted subset
    rejects them, so integer-like is the whole story. `.tany` counts as possibly
    integral, which keeps an unknown index from forcing a spurious `TypeError`. -/
private def indexMayBeIntegral (index : AbsVal) : Bool :=
  index.isBot || index.tags.any fun tag =>
    tag == .tint || tag == .tbool || tag == .tany

/-- Whether the index can be something other than an integer, which is the case
    that raises. -/
private def indexMayBeOther (index : AbsVal) : Bool :=
  index.tags.any fun tag =>
    match tag with
    | .tint | .tbool | .tunbound | .tuninit | .tmissing => false
    | _ => true

-- `builtinProperty` is one row set in `BuiltinOutcomes.lean`.

/-- Read `receiver.name` after receiver evaluation.

    CLAIM attr-instance-then-mro: attribute lookup reads the instance, then the
    MRO in linearization order.
    CLAIM attr-miss-is-attributeerror: a name in neither the instance nor the
    MRO is an `AttributeError`. There is no `__getattr__` hook to consult: a
    class defining one is rejected by `Syntax/Check.lean` rather than modeled
    here, so the miss is the whole answer.
-/
partial def attributeRead (services : Services) (p : Pos)
    (receiver : AbsVal) (name : String) (state : AState)
    (receiverExpr : Option Expr := none) : M Flow := do
  let context ← get
  let mut result : Flow := {}
  for tag in receiver.tags do
    match tag with
    | .tobj className =>
      let taggedReceiver := receiver.restrictTags [tag]
      match ← resolve className s!"@get:{name}" with
      | some (owner, function) =>
        resCase p "getattr" s!".{name}" tag.render
          s!"{owner}.{name} getter"
        let called ← services.invokeUser p s!"{owner}.@get:{name}" function
          [taggedReceiver] [] state
        result := result.join called
      | none =>
        let layout := (context.classes.getCls? className).map (·.layout)
          |>.getD []
        if layout.contains name then
          let mut fieldValue : AbsVal := AbsVal.bot
          for location in taggedReceiver.locs do
            if location.cls == .obj className then
              fieldValue := fieldValue.join (state.heapGet location (.field name))
          if Tag.tuninit ∈ fieldValue.tags then
            if (fieldValue.withoutTags [.tuninit]).isBot then
              oblige p "uninit-field"
                s!"{className}.{name} read before any initialization"
            else
              oblige p "uninit-field"
                s!"{className}.{name} maybe uninitialized at this read"
          resCase p "getattr" s!".{name}" tag.render "field"
          let present := fieldValue.withoutTags [.tuninit]
          if !present.isBot then
            result := result.join (normal present state)
        else
          match ← resolve className name with
          | some (owner, _) =>
            resCase p "getattr" s!".{name}" tag.render s!"{owner}.{name}"
            oblige p "method-escape"
              s!"{className}.{name} read as a value: bound-method escape is outside one-step dispatch"
            result := result.join <|
              normal (V [.tfunc] (funcs := [s!"{owner}.{name}"])) state
          | none =>
            -- A store to a field outside the class layout is not rejected: it
            -- writes the cell and files `attr-missing`. So the cell can be here,
            -- and going straight to AttributeError claimed a *guaranteed* error
            -- on `o.y = 2; v = o.y`, which CPython answers with 2 -- the same
            -- "claimed exception with no normal completion" that the builtin
            -- branch below was already written to avoid, and it makes every
            -- following obligation discharge for free.
            --
            -- Absence is read the way a layout field reads it, through
            -- `tuninit` rather than a missing cell, so a weak store is as
            -- precise here as it is there and no more.
            let mut stored : AbsVal := AbsVal.bot
            for location in taggedReceiver.locs do
              if location.cls == .obj className then
                stored := stored.join (state.heapGet location (.field name))
            let present := stored.withoutTags [.tuninit]
            if !present.isBot then
              resCase p "getattr" s!".{name}" tag.render "field outside layout"
              oblige p "attr-missing"
                s!"read of {className}.{name}: field not in the class layout"
              result := result.join (normal present state)
            else
              resCase p "getattr" s!".{name}" tag.render "!AttributeError"
              result ← addMachineRaise p result "AttributeError"
                (narrowReceiver receiverExpr (receiver.restrictTags [tag]) state)
    | .tany =>
      resCase p "getattr" s!".{name}" "any" "deferred"
      oblige p "dispatch-any" s!"attribute .{name} on an unknown value"
      result := result.join (normal anyV state)
    | .tdictkeys | .tdictitems | .tdictvalues =>
      resCase p "getattr" s!".{name}" tag.render "deferred"
      oblige p "dispatch-any"
        s!"attribute .{name} on a dictionary view is not specialized"
      result := result.join (normal anyV state)
    | .tnone =>
      resCase p "getattr" s!".{name}" "none" "!AttributeError"
      result ← addMachineRaise p result "AttributeError"
        (narrowReceiver receiverExpr (receiver.restrictTags [tag]) state)
    | _ =>
      -- A builtin is not attributeless. It has properties, which are reads with a
      -- value, and methods, which read as bound methods. Falling through to
      -- `AttributeError` for both claimed an exception where CPython returns
      -- something, and a claimed exception with no normal completion makes the
      -- rest of the function unreachable -- so its obligations discharge for free.
      --
      -- Which of those applies is a table row: `byName` means the property and
      -- method tables answer, a deferred row means the surface is not enumerated,
      -- and `never` means the tag genuinely has no attributes.
      let outcome := builtinOutcome tag .attribute
      if outcome.deferred then
        resCase p "getattr" s!".{name}" tag.render "deferred"
        oblige p "dispatch-any"
          s!"attribute .{name} on {tag.render} is not specialized"
        result := result.join (normal anyV state)
      else if outcome.value != .byName then
        resCase p "getattr" s!".{name}" tag.render "!AttributeError"
        result ← addMachineRaise p result "AttributeError"
          (narrowReceiver receiverExpr (receiver.restrictTags [tag]) state)
      else if let some value := builtinProperty tag name then
        resCase p "getattr" s!".{name}" tag.render "property"
        result := result.join (normal value state)
      else if (knownMethods tag).contains name then
        resCase p "getattr" s!".{name}" tag.render s!"{tag.render}.{name}"
        oblige p "method-escape"
          s!"{tag.render}.{name} read as a value: bound-method escape is outside one-step dispatch"
        -- Deliberately `any` rather than a `tfunc` naming the builtin: no
        -- resolver knows a FuncDef by that name, so a `tfunc` would be a
        -- callable target that resolves to nothing. `any` calls back as
        -- deferred dispatch, which is the conservative answer.
        result := result.join (normal anyV state)
      else
        -- Reported unconditionally. The suppression this replaces fired exactly
        -- when the receiver held no object or unknown tag, which is when the
        -- AttributeError is the *only* outcome -- so the row that explains the
        -- raise was dropped in the one case it was load-bearing, and
        -- `unreported-outcome` flagged the gap.
        resCase p "getattr" s!".{name}" tag.render "!AttributeError"
        result ← addMachineRaise p result "AttributeError"
          (narrowReceiver receiverExpr (receiver.restrictTags [tag]) state)
  pure result

/-- One indexed read of a builtin sequence, driven entirely by its table row.

    The five sequence branches this replaces each carried their own copy of the
    same rule: integral index gives the element plus a bounds obligation plus
    `IndexError`, non-integral gives `TypeError`. Five copies meant five chances to
    omit a piece, and `.ttuple` omitted the index-type check entirely -- `t[s]` for
    a string `s` reported `IndexError` and no `TypeError`, where CPython raises
    `TypeError` and never `IndexError`.

    `cellValue` reads the element cell for the row that says `fromCell`; a row with
    fixed tags does not use it. -/
private def sequenceItemRead (p : Pos) (tag : Tag) (index : AbsVal)
    (cellValue : AbsVal) (state : AState) (incoming : Flow)
    (inRange : Bool := false) : M Flow := do
  let outcome := builtinOutcome tag .subscriptRead
  let mut result := incoming
  if !outcome.integralArgument || indexMayBeIntegral index then
    let value := match outcome.value with
      | .tags tags => V tags
      | .fromCell => cellValue
      | _ => AbsVal.bot
    resCase p "getitem" "[..]" tag.render outcome.resultLabel
    if !value.isBot then
      result := result.join (normal value state)
    -- A proven-in-range index owes nothing and cannot raise. This is the only
    -- place the length is consulted; the outcome table is over tags and cannot
    -- see it.
    if let some detail := outcome.bounds then
      if !inRange then
        oblige p "bounds" detail
    if outcome.raises.contains "IndexError" && !inRange then
      result ← addMachineRaise p result "IndexError" state
  if outcome.integralArgument && indexMayBeOther index then
    if outcome.raises.contains "TypeError" then
      resCase p "getitem" "[..]" tag.render "!TypeError"
      result ← addMachineRaise p result "TypeError" state
  pure result

/-- Read `receiver[index]` after receiver and index evaluation.

    CLAIM subscript-getitem-dunder: a subscript on an instance calls
    `__getitem__`, and whatever it raises escapes.
-/
partial def itemRead (services : Services) (p : Pos)
    (receiver index : AbsVal) (_literalKey : Option String)
    (literalIndex : Option Nat) (state : AState) : M Flow := do
  let context ← get
  let mut result : Flow := {}
  for tag in receiver.tags do
    match tag with
    | .ttuple =>
      for location in receiver.locs do
        if location.cls.tag == .ttuple then
          match literalIndex with
          | some position =>
            let slot := state.heapGet location (.tupleSlot position)
            if slot.isBot then
              result ← sequenceItemRead p tag index
                (state.heapGet location .elem) state result
            else
              -- A literal index with a known slot is exact: no bounds question
              -- and no index-type question, because the index is that literal.
              resCase p "getitem" "[..]" "tuple"
                s!"field {(CellSelector.tupleSlot position).render}"
              result := result.join (normal slot state)
          | none =>
            result ← sequenceItemRead p tag index
              (state.heapGet location .elem) state result
              (state.indexDefinitelyInRange (receiver.restrictTags [tag]) index)
    | .tlist =>
      let mut element : AbsVal := AbsVal.bot
      for location in receiver.locs do
        if location.cls.tag == .tlist then
          element := element.join (state.heapGet location .elem)
      result ← sequenceItemRead p tag index element state result
        (state.indexDefinitelyInRange (receiver.restrictTags [tag]) index)
    | .tstr =>
      result ← sequenceItemRead p tag index AbsVal.bot state result
        (state.indexDefinitelyInRange (receiver.restrictTags [tag]) index)
    | .tbytes =>
      -- `b"ab"[0]` is 97: a bytes subscript yields an int. This tag used to fall
      -- into the catch-all, which asserts `TypeError` and no normal completion,
      -- so a real read was analysed as always raising and everything after it
      -- became unreachable -- the worst direction to be wrong in, because
      -- unreachable code discharges its obligations for free.
      result ← sequenceItemRead p tag index AbsVal.bot state result
    | .ttype =>
      -- `list[int]` is a generic alias, not an error. The analysis does not model
      -- alias objects, so this defers rather than asserting a `TypeError` the
      -- interpreter does not raise.
      resCase p "getitem" "[..]" "type" "deferred"
      oblige p "dispatch-any" "subscript of a type object builds a generic alias"
      result := result.join (normal anyV state)
    | .trange =>
      result ← sequenceItemRead p tag index AbsVal.bot state result
    | .tdict =>
      for location in receiver.locs do
        match location.cls with
        | .td typeName =>
          match context.classes.getCls? typeName with
          | some info =>
            let keys := keyCases index
            for key in keys.literals do
              match info.fields.find? (·.name == key) with
              | some _ =>
                resCase p "getitem" "[..]" s!"td:{typeName}"
                  s!"field k:{key}"
                let fieldValue := state.heapGet location (.literalKey key)
                let present := fieldValue.withoutTags [.tmissing]
                if !present.isBot then
                  result := result.join (normal present state)
                if Tag.tmissing ∈ fieldValue.tags then
                  resCase p "getitem" "[..]" s!"td:{typeName}" "!KeyError"
                  result ← addMachineRaise p result "KeyError" state
              | none =>
                resCase p "getitem" "[..]" s!"td:{typeName}" "!KeyError"
                result ← addMachineRaise p result "KeyError" state
            if keys.openString || keys.userEquality then
              if keys.userEquality then
                oblige p "special-method"
                  s!"key equality/hash against TypedDict {typeName} succeeds without side effects"
              resCase p "getitem" "[..]" s!"td:{typeName}" "declared field"
              let values := typedDictValues info location state
              if !values.isBot then
                result := result.join (normal values state)
              resCase p "getitem" "[..]" s!"td:{typeName}" "!KeyError"
              result ← addMachineRaise p result "KeyError" state
            if keys.absent then
              resCase p "getitem" "[..]" s!"td:{typeName}" "!KeyError"
              result ← addMachineRaise p result "KeyError" state
            if keys.unhashable then
              resCase p "getitem" "[..]" s!"td:{typeName}" "!TypeError"
              result ← addMachineRaise p result "TypeError" state
            if keys.unknown then
              resCase p "getitem" "[..]" s!"td:{typeName}" "deferred"
              oblige p "dispatch-any" s!"unknown key on TypedDict {typeName}"
              result := result.join (normal anyV state)
              result ← addMachineRaises p result ["KeyError", "TypeError"] state
          | none =>
            resCase p "getitem" "[..]" s!"td:{typeName}" "deferred"
            result := result.join (normal anyV state)
        | .dict =>
          -- A key the per-key cells prove present cannot raise `KeyError`, and
          -- its cell is tighter than the `val` summary. Absence of a cell means
          -- nothing is known, so it keeps both outcomes.
          let keys := keyCases index
          if allKeysPresent state location keys then
            let mut value : AbsVal := AbsVal.bot
            for key in keys.literals do
              value := value.join (keyValue state location key)
            let shown := match keys.literals with
              | [only] => s!"field k:{only}"
              | _ => "field k:.."
            resCase p "getitem" "[..]" "dict" shown
            result := result.join (normal value state)
          else
            resCase p "getitem" "[..]" "dict" "val"
            oblige p "key-membership" "dictionary key present"
            let value := state.heapGet location .dictValues
            if !value.isBot then
              result := result.join (normal value state)
            resCase p "getitem" "[..]" "dict" "!KeyError"
            result ← addMachineRaise p result "KeyError" state
        | _ => pure ()
    | .tobj className =>
      match ← resolve className "__getitem__" with
      | some (owner, function) =>
        resCase p "getitem" "[..]" tag.render s!"{owner}.__getitem__"
        let called ← services.invokeUser p s!"{owner}.__getitem__" function
          [receiver.restrictTags [tag], index] [] state
        result := result.join called
      | none =>
        resCase p "getitem" "[..]" tag.render "!TypeError"
        result ← addMachineRaise p result "TypeError" state
    | .tany =>
      resCase p "getitem" "[..]" "any" "deferred"
      oblige p "dispatch-any" "subscript on an unknown value"
      result := result.join (normal anyV state)
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      -- The table decides, so a tag with no row cannot be silently asserted to
      -- raise. This arm used to claim TypeError for everything it had not named,
      -- which is how `bytes` and `type` -- both subscriptable -- were reported as
      -- always raising. `RuleValidate` now rejects a table missing a pair, and
      -- `tests/catchall_oracle.py` checks each row against CPython.
      let outcome := builtinOutcome tag .subscriptRead
      match outcome.value with
      | .tags tags =>
        resCase p "getitem" "[..]" tag.render
          ("|".intercalate (tags.map Tag.render))
        result := result.join (normal (V tags) state)
      | .fromCell =>
        -- Reached only if a cell-valued row is added without a branch above to
        -- read the cell. Declared unknown rather than guessed at.
        resCase p "getitem" "[..]" tag.render "deferred"
        oblige p "dispatch-any"
          s!"subscript of {tag.render} reads a cell this transfer does not name"
        result := result.join (normal anyV state)
      | .byName | .unknown =>
        -- `byName` is an attribute answer; a subscript row never carries it, so
        -- reaching it here would mean the table changed shape. Deferred rather
        -- than guessed at either way.
        resCase p "getitem" "[..]" tag.render "deferred"
        oblige p "dispatch-any" s!"subscript on {tag.render} is not specialized"
        result := result.join (normal anyV state)
      | .never => pure ()
      for cls in outcome.raises do
        resCase p "getitem" "[..]" tag.render s!"!{cls}"
        result ← addMachineRaise p result cls state
  pure result

/-- Write `receiver.name = value` after receiver and value evaluation.

    CLAIM attr-write-then-read: an attribute store is visible to the next read,
    and may create the attribute.
-/
partial def attributeWrite (services : Services) (p : Pos)
    (receiver : AbsVal) (name : String) (value : AbsVal)
    (state : AState) : M Flow := do
  let context ← get
  let mut result : Flow := {}
  for tag in receiver.tags do
    match tag with
    | .tobj className =>
      let taggedReceiver := receiver.restrictTags [tag]
      match ← resolve className s!"@set:{name}" with
      | some (owner, function) =>
        resCase p "setattr" s!".{name}=" tag.render
          s!"{owner}.{name} setter"
        let called ← services.invokeUser p s!"{owner}.@set:{name}" function
          [taggedReceiver, value] [] state
        result := result.join (discardWriteResult called)
      | none =>
        if (← resolve className s!"@get:{name}").isSome then
          resCase p "setattr" s!".{name}=" tag.render "!AttributeError"
          result ← addMachineRaise p result "AttributeError" state
        else if (context.classes.getCls? className).any (·.isDataclass) &&
            !context.callStack.contains s!"{className}.__init__" then
          resCase p "setattr" s!".{name}=" tag.render
            "!FrozenInstanceError"
          result ← addMachineRaise p result "FrozenInstanceError" state
        else
          let info? := context.classes.getCls? className
          let layout := (info?.map (·.layout)).getD []
          let slotsComplete := info?.any (·.slotsComplete)
          if !layout.contains name && slotsComplete then
            -- No `__dict__` anywhere on the chain, so CPython has nowhere to put
            -- the field: this store *always* raises. A guaranteed error with no
            -- normal edge, not an obligation to discharge.
            resCase p "setattr" s!".{name}=" tag.render "!AttributeError"
            result ← addMachineRaise p result "AttributeError" state
          else
            resCase p "setattr" s!".{name}=" tag.render "store"
            if !layout.contains name then
              -- CPython permits this on a class that has a `__dict__`, so the
              -- raise is *not* guaranteed -- but the field is outside the
              -- declared layout, which mypy, ty and pyright all report as an
              -- error and which the Laurel composite has no slot for. So both
              -- edges are kept: the store happens, and an `AttributeError` edge
              -- is raised so the site cannot be passed over silently. Declaring
              -- `__slots__` across the MRO turns this into the guaranteed case.
              oblige p "attr-missing"
                s!"store to {className}.{name}: field is outside the declared layout; mypy, ty and pyright all reject it, and the composite has no slot for it"
              result ← addMachineRaise p result "AttributeError" state
            let locations := taggedReceiver.locs.filter
              (·.cls == .obj className)
            let mut outputState := state
            if locations.length == 1 &&
                completeStrongTarget receiver locations.head! then
              outputState := outputState.heapSet locations.head! (.field name) value
              resUpdate p "strong"
            else
              for location in locations do
                outputState := outputState.heapJoin location (.field name) value
              if !locations.isEmpty then
                resUpdate p "weak"
            result := result.join (normalWrite outputState)
    | .tany =>
      resCase p "setattr" s!".{name}=" "any" "deferred"
      oblige p "dispatch-any"
        s!"attribute store .{name} on an unknown value"
      let outputState ← havocReachable p [receiver, value] state
      result := result.join (normalWrite outputState)
      result ← addMachineRaise p result "AttributeError" state
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      resCase p "setattr" s!".{name}=" tag.render "!AttributeError"
      result ← addMachineRaise p result "AttributeError" state
  pure result

/-- Write `receiver[index] = value` after all operands are evaluated.

    CLAIM subscript-setitem-dunder: an item store on an instance calls
    `__setitem__` and can mutate the receiver.
-/
partial def itemWrite (services : Services) (p : Pos)
    (receiver index value : AbsVal) (literalKey : Option String)
    (_literalIndex : Option Nat) (state : AState) : M Flow := do
  let context ← get
  let mut result : Flow := {}
  for tag in receiver.tags do
    match tag with
    | .tlist =>
      let mut outputState := state
      for location in receiver.locs do
        if location.cls == .list then
          outputState := outputState.heapJoin location .elem value
      result := result.join (normalWrite outputState)
      oblige p "bounds" "sequence store index within length"
      result ← addMachineRaise p result "IndexError" state
    | .tdict =>
      checkHashable p index
      let mut outputState := state
      for location in receiver.locs do
        match location.cls with
        | .td typeName =>
          match literalKey, context.classes.getCls? typeName with
          | some key, some info =>
            match info.fields.find? (·.name == key) with
            | some _ =>
              resCase p "setitem" "[..]=" s!"td:{typeName}"
                s!"field k:{key}"
              outputState ← updateTypedDictField p receiver location
                typeName key info value outputState
            | none =>
              oblige p "shape-break"
                ((undeclaredKeyObligation .setItem typeName key).getD "")
              outputState :=
                (outputState.heapJoin location .dictKeys index).heapJoin location .dictValues value
          | _, _ =>
            oblige p "key-membership"
              s!"dynamic key store on TypedDict {typeName}"
            outputState :=
              (outputState.heapJoin location .dictKeys index).heapJoin location .dictValues value
        | .dict =>
          -- The store resolves to a cell, so it is a dispatch row like an
          -- attribute store. It used to be silent: the cell appeared in the heap
          -- and no row named it, which is the same reporting gap the plain-dict
          -- *read* had before its `!KeyError` row was added.
          match literalKey with
          | some key =>
            resCase p "setitem" "[..] =" "dict"
              s!"field {(CellSelector.literalKey key).render}"
          | none => resCase p "setitem" "[..] =" "dict" "val"
          outputState :=
            (outputState.heapJoin location .dictKeys index).heapJoin location
              .dictValues value
          -- A literal key also gets its own cell, so a later read can prove the
          -- key present instead of admitting a KeyError it cannot rule out.
          --
          -- The weak case is where this is easy to get wrong. A store through a
          -- summary location, or through a may-alias set, did not necessarily
          -- happen to *this* object, so the key may still be absent afterwards.
          -- Joining only the value would read back as proof of presence. The
          -- `.tmissing` marker is therefore joined in exactly when the cell held
          -- nothing before: a cell that was already definitely present stays
          -- present, and one that was unknown stays may-be-absent.
          match literalKey with
          | some key =>
            let cell := CellSelector.literalKey key
            -- Not a plain `heapStore`: the weak branch stores a *different*
            -- value. A weak write may not have happened to this object, so the
            -- `.tmissing` marker is joined in when the cell held nothing before,
            -- or the join would read back as proof of presence.
            if strongUpdateTarget receiver location then
              outputState := outputState.heapSet location cell value
            else
              let existing := outputState.heapGet location cell
              let stored := if existing.isBot then value.join (V [.tmissing])
                else value
              outputState := outputState.heapJoin location cell stored
          | none => pure ()
        | _ => pure ()
      result := result.join (normalWrite outputState)
    | .tobj className =>
      match ← resolve className "__setitem__" with
      | some (owner, function) =>
        resCase p "setitem" "[..]=" tag.render s!"{owner}.__setitem__"
        let called ← services.invokeUser p s!"{owner}.__setitem__" function
          [receiver.restrictTags [tag], index, value] [] state
        result := result.join (discardWriteResult called)
      | none =>
        result ← addMachineRaise p result "TypeError" state
    | .tany =>
      oblige p "dispatch-any" "subscript store on an unknown value"
      let outputState ← havocReachable p [receiver, index, value] state
      result := result.join (normalWrite outputState)
      result ← addMachineRaise p result "TypeError" state
    | .tunbound | .tuninit | .tmissing => pure ()
    | _ =>
      result ← addMachineRaise p result "TypeError" state
  pure result

end Pylate.RuleDriven.Objects
