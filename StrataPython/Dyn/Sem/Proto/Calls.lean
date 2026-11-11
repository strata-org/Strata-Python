/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Iter

set_option autoImplicit false

/-!
# Calls

Generic over the record of primitives, the lowering of call arguments: `mkKwargs` and
`argsTupleStep` (`f(*it)`); `f(**m)` is `Mapping.lean`'s, and `print` is `Repr.lean`'s.

The calls themselves are `callN`'s (`Lookup.lean`).  A `TypeError` of `argsTuple` or `dictMerge`
whose message names a function object (CPython's `__main__.g()`) stops with a gap, since the
model doesn't hold a function's `__qualname__`.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- `str(v)` for a value whose `str` runs no protocol: a `str`, an `int`, a `bool`, a `float` or
`None`; `none` for any other value. -/
def plainStr? [PyCalls m V] (v : V) : m (Option String) := do
  match ← PyPure.immView v with
  | some (.str s) => pure (some s.s)
  | some (.bool b) => pure (some (if b then "True" else "False"))
  | some .none => pure (some "None")
  | some (.float f) => pure (some (Format.floatRepr f))
  | some (.int i) => match Format.intRepr i with
    | .ok s => pure (some s)
    | .error f => ofFailure f
  | _ => pure none

/-- The description of the callee `f` in a `TypeError` about its arguments, as CPython's
`_PyObject_FunctionStr` gives it: `print()`, or `module.Q()` for a built-in function or type of
another module.  A function object and any other callee stop with a gap: the message needs their
`__qualname__` or their `str`. -/
def calleeName [PyCalls m V] (f : V) : m String := do
  match ← PyPure.immView f with
  | some (.builtin b) =>
    if b.info.kind == .other then PyPure.gap "a TypeError that names this built-in is not modelled yet"
    let pre := if b.info.module == "builtins" then "" else s!"{b.info.module}."
    pure s!"{pre}{b.info.qualname}()"
  | _ => PyPure.gap "a TypeError that names a function is not modelled yet"

/-- `tuple(it)` for `f(*it)`: CPython's `CALL_FUNCTION_EX`, for a built-in sequence or a dict;
`TypeError` naming `f` for a value that is not iterable. -/
def argsTuple [PyCalls m V] (f it : V) : m V := do
  if let some (.tuple _) ← PyPure.immView it then return it
  userCheck it it
  if (← seqOf it).isSome || (← isDict it) || (← anySet? it).isSome then
    return PyPure.imm (m := m) (.tuple (← (← iterSeq it fun _ => "").items))
  if (← PyPure.immView it).isSome then
    raiseBuiltin "TypeError"
      s!"{← calleeName f} argument after * must be an iterable, not {← typeName it}"
  PyPure.gap "a * argument of this built-in type is not modelled yet"

/-- **`tuple(it)` for `f(*it)`, as CPython's `CALL_FUNCTION_EX`**, one activation of it: a tuple as
it is, an exact built-in container at once; otherwise `TypeError` naming `f` for a value with
neither `__iter__` nor `__getitem__`, else `iter(it)` after its length hint, the items gathered in
a list, its iterator the state. -/
def argsTupleStep [PyWrites m V] [PyNew m V] (f it : V) (st : Option (V × V)) :
    m (LoopStep (V × V) V) := do
  let (lst, iter) ← match st with
    | some x => pure x
    | none =>
      if let some (.tuple _) ← PyPure.immView it then return .done it
      if ← exactBuiltinIterable it then return .done (← argsTuple f it)
      let t ← PyReads.classOf it
      if (← lookupType t "__iter__").isNone && (← lookupType t "__getitem__").isNone then
        raiseBuiltin "TypeError"
          s!"{← calleeName f} argument after * must be an iterable, not {← typeName it}"
      let i ← getIter it
      hintCheck (← lengthHint it 10)
      pure (← PyPure.allocList #[], i)
  match ← forEachItem iterNext iter () fun x _ => do
      PyWrites.listAppend lst x
      pure (.next ()) with
  | .more _ => return .more (lst, iter)
  | .done _ =>
    let some xs ← listOf? lst | PyPure.gap "argsTuple: the list of the items is not a list"
    return .done (PyPure.imm (m := m) (.tuple xs))

/-- A gap unless `builtins.__import__` is the built-in one: CPython's `IMPORT_NAME` calls it
whenever it has been replaced. -/
def importCheck [PyCalls m V] : m Unit := do
  match ← PyReads.builtinGet "__import__" with
  | some v =>
    if !((← PyPure.immView v) matches some (.builtin .«__import__»)) then
      PyPure.gap "an import after builtins.__import__ was replaced is not modelled yet"
  | none => PyPure.gap "an import after builtins.__import__ was deleted is not modelled yet"

/-- `import module`: the `builtins` module; any other module stops with a gap. -/
def importModule [PyCalls m V] (module : String) : m V := do
  importCheck
  if module == "builtins" then
    if let some v ← PyReads.moduleGet "builtins" then return v
  PyPure.gap s!"import of module {module} is not modelled yet"

/-- `from module import name`: an entry of the `builtins` module, or CPython's `ImportError`;
any other module stops with a gap. -/
def importFrom [PyCalls m V] (module name : String) : m V := do
  importCheck
  if module != "builtins" then PyPure.gap s!"import of module {module} is not modelled yet"
  match ← PyReads.builtinGet name with
  | some v => pure v
  | none =>
    -- `IMPORT_FROM` reads an attribute of the module object, and the module type's own
    -- attributes, such as `__dict__`, are all dunder names.
    if name.startsWith "__" && name.endsWith "__" then
      PyPure.gap s!"from builtins import {name} is not modelled yet"
    let msg := s!"cannot import name '{name}' from 'builtins' (unknown location)"
    raiseBuiltin "ImportError" msg
      #[("msg", PyPure.imm (m := m) (.str (.ofString msg))),
        ("name", PyPure.imm (m := m) (.str (.ofString "builtins"))),
        ("path", PyPure.imm (m := m) .none),
        ("name_from", PyPure.imm (m := m) (.str (.ofString name)))]

/-- `module.name` for the `builtins` module, which the translator uses for names that are not in
the source; a missing name, or any other module, stops with a gap. -/
def qualifiedRef [PyCalls m V] (module name : String) : m V := do
  if module != "builtins" then PyPure.gap s!"a reference into module {module} is not modelled yet"
  let some v ← PyReads.builtinGet name | PyPure.gap s!"builtins.{name} is missing"
  pure v

/-- The frames of this piece's own step: `type.__call__` while the `__new__` that it called
(`typeNew`, with the call's class and arguments) or the `__init__` (`typeInit`, with the object
that `__new__` made) is a suspended machine, and an instance's `__call__` (`callLevel`). -/
inductive OpsLoopState (V : Type) where
  | typeNew (cls args kwargs : V)
  | typeInit (obj : V)
  /-- An instance's `__call__`, run one C level deeper (`_PyObject_MakeTpCall`), whose machine
  suspended. -/
  | callLevel

section
variable {S : Type} [PyWrites m V] [PyMachines m V S] [HasLoopPart S (OpsLoopState V)]

/-- A call of `f` that a step machine may suspend: its machine's first step, or else `callN`. -/
def stepCall (f args kwargs : V) : m (CallStep S V) := do
  match ← PyMachines.startStep f args kwargs with
  | some r => pure r
  | none => .done <$> callN dispatchDepth f args kwargs

/-- **The first step of a step machine for the `tp_new` of the built-in type `t`**, bound to
`self`, as a class call starts it (`callTpNew`).  The `.tpNew` value that names it is made here and
handed to `startStep` at once; a piece's machine reads it to choose itself and keeps no callee: this
call is the value's whole life. -/
def startTpNew (self : V) (t : Builtin) (args kwargs : V) : m (Option (CallStep S V)) :=
  PyMachines.startStep (PyPure.imm (m := m) (.bound self t "__new__" .tpNew)) args kwargs

/-- `type.__call__` after `__new__` made `obj`: `__init__` when `obj` is an instance of `cls`,
which may suspend as a `typeInit` frame; then `obj`. -/
def typeInitStep (cls obj args kwargs : V) : m (CallStep S V) := do
  let some objMro ← mroOf (← PyReads.classOf obj) | return .done obj
  let mut isInst := false
  for c in objMro do
    if (← PyPure.identical c cls) == .yes then isInst := true
  if !isInst then return .done obj
  let some init ← lookupType (← PyReads.classOf obj) "__init__" | return .done obj
  let initF ← descrGetN dispatchDepth init (some obj) (← PyReads.classOf obj)
  match ← stepCall initF args kwargs with
  | .suspend fs => return .suspend (HasLoopPart.inj (OpsLoopState.typeInit obj) :: fs)
  | .done r =>
    if !((← PyPure.immView r) matches some .none) then
      raiseBuiltin "TypeError" s!"__init__() should return None, not '{← typeName r}'"
    return .done obj

/-- **A call of the class `cls` that a step machine may suspend**: the steps of `typeCallN`, where
the `__new__` or the `__init__` that it calls may be a machine, which suspends as a `typeNew` or a
`typeInit` frame. A metaclass's own `__call__` and `type`'s own call go through `typeCallN`. -/
def typeCallStep (cls args kwargs : V) : m (CallStep S V) := do
  if (← PyPure.immView cls) matches some (.builtin .type) then
    return .done (← typeCallN dispatchDepth true cls args kwargs)
  if (← metaCall? cls).isSome then
    return .done (← typeCallN dispatchDepth true cls args kwargs)
  PyReads.withDepth 1 do
    let some new ← lookupType cls "__new__" | PyPure.gap s!"a class without __new__"
    metaGetattributeCheck cls
    let some tpNew ← tpNewFor cls new |
      PyPure.gap "a class whose __new__ comes from another built-in base than its tp_new is not modelled yet"
    let args' ← prepend cls args
    let step ← match tpNew with
      -- `type_call` calls the type's `tp_new` directly, without `tp_new_wrapper`'s check.
      | .builtin s u => do
        match ← startTpNew s u args' kwargs with
        | some r => pure r
        | none => .done <$> callTpNew s u args' kwargs
      | .slot => stepCall (← descrGetN dispatchDepth new none cls) args' kwargs
    match step with
    | .suspend fs =>
      return .suspend (HasLoopPart.inj (OpsLoopState.typeNew cls args kwargs) :: fs)
    | .done obj => typeInitStep cls obj args kwargs

/-- **`callResumable f args kwargs saved`**: with no saved frames, a call of `f` as `callN` makes
it, where a built-in step machine that the dispatch reaches (directly, through a class's
`__new__` or `__init__`, a bound method or an instance's `__call__`) runs one step and gives
its frames; with saved frames, the machine that the first one names resumes, with no dispatch.
-/
def callResumable : Nat → V → V → V → List S → m (CallStep S V)
  | _, _, _, _, s :: rest => PyMachines.resume s rest
  | 0, _, _, _, [] => PyPure.gap "a call dispatch nested deeper than the model follows"
  | n + 1, f, args, kwargs, [] => do
    kwargsKeysGap f kwargs
    if let some r ← PyMachines.startStep f args kwargs then return r
    match ← PyPure.immView f with
    | some (.method fn self) => callResumable n fn (← prepend self args) kwargs []
    | some (.builtin b) =>
      if b.info.kind == .type then typeCallStep f args kwargs
      else .done <$> callN dispatchDepth f args kwargs
    | some _ => .done <$> callN dispatchDepth f args kwargs
    | none =>
      match ← PyReads.objView f with
      | some (.cls _) => typeCallStep f args kwargs
      | some .inst =>
        let t ← PyReads.classOf f
        match ← lookupType t "__call__" with
        | some c =>
          -- `slot_tp_call` through `_PyObject_MakeTpCall` counts a C level, as `callN` counts it.
          match ← PyReads.withDepth 1 do
              callResumable n (← descrGetN dispatchDepth c (some f) t) args kwargs [] with
          | .suspend fs => return .suspend (HasLoopPart.inj (OpsLoopState.callLevel (V := V)) :: fs)
          | r => return r
        | none => .done <$> callN dispatchDepth f args kwargs
      | _ => .done <$> callN dispatchDepth f args kwargs

/-- **The resume entry of this piece's frames**, one C level deeper, as the call that suspended ran:
the inner machine resumes with the rest of the frames; a `typeNew` frame then runs `__init__` on the
object that `__new__` made, a `typeInit` frame gives the object, and a `callLevel` frame gives the
inner result. Every frame has an inner one below it: a frame list without one is a model
invariant. -/
def opsResume (fr : OpsLoopState V) (rest : List S) : m (CallStep S V) :=
  PyReads.withDepth 1 do
    let inner ← match rest with
      | s :: rest' => PyMachines.resume s rest'
      | [] => PyPure.modelInvariant "a frame list that doesn't fit the call"
    match fr, inner with
    | _, .suspend fs => return .suspend (HasLoopPart.inj fr :: fs)
    | .typeNew cls args kwargs, .done obj => typeInitStep cls obj args kwargs
    | .typeInit obj, .done r =>
      if !((← PyPure.immView r) matches some .none) then
        raiseBuiltin "TypeError" s!"__init__() should return None, not '{← typeName r}'"
      return .done obj
    | .callLevel, .done r => return .done r


/-- **One activation of `py.call`**: `callResumable` from the frames that the activation before it
saved; the frames of a suspended machine are the state of the next activation. -/
def callStep (f args kwargs : V) (st : Option (List S)) : m (LoopStep (List S) V) := do
  let saved ← match st with
    | none => pure []
    | some [] => PyPure.gap "py.call resumed with no frames"
    | some fs => pure fs
  match ← callResumable dispatchDepth f args kwargs saved with
  | .done v => return .done v
  | .suspend fs => return .more fs

end

end

section
variable {m : Type → Type 1} {V : Type}

/-- `"s"` unless `n` is 1. -/
def pluralS (n : Nat) : String := if n == 1 then "" else "s"

/-- The names `ns`, each quoted, as CPython's `format_missing` lists them: `'a'`, `'a' and 'b'`,
`'a', 'b', and 'c'`. -/
def missingList (ns : Array String) : String :=
  let q := ns.map fun n => s!"'{n}'"
  match q.size with
  | 0 => ""
  | 1 => q[0]!
  | 2 => s!"{q[0]!} and {q[1]!}"
  | k => ", ".intercalate (q.extract 0 (k - 1)).toList ++ s!", and {q[k - 1]!}"

/-- The arguments `args` (a tuple) and `kwargs` (a dict) of a call of the Python
function `qualname` bound to its parameters `names`, as CPython 3.12's `initialize_locals` binds
them, with its `TypeError`s in its order (`py.bindArgs`).  The first `nPosOnly` names are
positional-only, the first `nPos` positional, and `defaults` gives each name's default or
`undef`.  The result is a tuple: one value per name, then the extra positional arguments if
`varPos`, then a new dict of the other keywords, in their order, if `varKw`.  A keyword that is
an object, such as an instance of a subclass of `str`, stops with a gap: its `__eq__` and
`__hash__` could run user code.  So does a keyword that names a positional-only parameter
without `**kw`: CPython's message, which lists every positional-only parameter that a keyword
names, is not modelled yet. -/
def bindArgs [PyReads m V] [PyNew m V] (qualname : String) (args kwargs defaults : V)
    (nPosOnly nPos : Nat) (varPos varKw : Bool) (names : Array String) : m V := do
  let fail {α : Type} (msg : String) : m α := raiseBuiltin "TypeError" s!"{qualname}() {msg}"
  let some (.tuple xs) ← PyPure.immView args | PyPure.modelInvariant "bindArgs: args is not a tuple"
  let some (.tuple dfl) ← PyPure.immView defaults |
    PyPure.modelInvariant "bindArgs: defaults is not a tuple"
  let mut slots : Array (Option V) := Array.replicate names.size none
  let n := min xs.size nPos
  for i in [:n] do
    slots := slots.set! i xs[i]?
  let kws ← PyReads.dictEntries kwargs
  let mut rest : Array (String × V) := #[]
  for (k, v, _) in kws do
    let s ← match ← PyPure.immView k with
      | some (.str s) => pure s.s
      | some _ => fail "keywords must be strings"
      | none => PyPure.gap "a keyword that is not an exact str"
    match (names.extract nPosOnly names.size).findIdx? (· == s) with
    | some j =>
      if slots[nPosOnly + j]!.isSome then fail s!"got multiple values for argument '{s}'"
      slots := slots.set! (nPosOnly + j) (some v)
    | none =>
      if !varKw then
        for (k', _, _) in kws do
          if let some (.str s') ← PyPure.immView k' then
            if (names.extract 0 nPosOnly).contains s'.s then
              PyPure.gap "a keyword that names a positional-only parameter"
        fail s!"got an unexpected keyword argument '{s}'"
      rest := rest.push (s, v)
  let mut defcount := 0
  for i in [:nPos] do
    if let some d := dfl[i]? then
      if !(← PyPure.isUndef d) then defcount := defcount + 1
  let isKwonly (i : Nat) := nPos ≤ i
  if xs.size > nPos && !varPos then
    let kwonlyGiven := ((slots.zipIdx.filter fun (x, i) => isKwonly i && x.isSome)).size
    let given := xs.size
    let (sig, pl) := if defcount > 0 then (s!"from {nPos - defcount} to {nPos}", true)
      else (s!"{nPos}", nPos != 1)
    let kwSig := if kwonlyGiven > 0 then
        s!" positional argument{pluralS given} (and {kwonlyGiven} keyword-only argument{pluralS kwonlyGiven})"
      else ""
    fail s!"takes {sig} positional argument{if pl then "s" else ""} but {given}{kwSig} {if given == 1 && kwonlyGiven == 0 then "was" else "were"} given"
  -- Missing positional parameters, then their defaults.
  let mRequired := nPos - defcount
  let missingPos := (names.zipIdx.filter fun (_, i) => i < mRequired && slots[i]!.isNone).map (·.1)
  if !missingPos.isEmpty then
    fail s!"missing {missingPos.size} required positional argument{pluralS missingPos.size}: {missingList missingPos}"
  -- Defaults of the other parameters, and the missing keyword-only ones.
  let mut missingKw : Array String := #[]
  for h : i in [:names.size] do
    if slots[i]!.isNone then
      match dfl[i]? with
      | some d =>
        if ← PyPure.isUndef d then
          if isKwonly i then missingKw := missingKw.push names[i]
        else slots := slots.set! i (some d)
      | none => pure ()
  if !missingKw.isEmpty then
    fail s!"missing {missingKw.size} required keyword-only argument{pluralS missingKw.size}: {missingList missingKw}"
  let mut out : Array V := #[]
  for x in slots do
    let some v := x | PyPure.modelInvariant "bindArgs: a parameter without a value"
    out := out.push v
  if varPos then out := out.push (PyPure.imm (m := m) (.tuple (xs.extract nPos xs.size)))
  if varKw then
    let d ← PyPure.allocDict
    for (k, v) in rest do
      PyNew.dictSetNew d (PyPure.imm (m := m) (.str (.ofString k))) v none fun _ => pure false
    out := out.push d
  pure (PyPure.imm (m := m) (.tuple out))

end

end

end StrataPython.Dyn.Sem.Proto
