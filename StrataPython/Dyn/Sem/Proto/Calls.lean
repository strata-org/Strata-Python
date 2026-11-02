/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Containers

set_option autoImplicit false

/-!
# Calls

Generic over the record of primitives, CPython 3.12's `print` and the lowering of call arguments:

* `print` writes the `str` of each argument, with `sep` and `end`; `str` of a value other than a
  `str`, `int`, `bool`, `float` or `None` stops with a gap until `str` and `repr` exist;
* the lowering of call arguments: `mkKwargs`, `argsTuple` (`f(*it)`) and `dictMerge` (`f(**m)`).

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

/-- `str(v)`, for the values that `plainStr?` covers; a gap for any other. -/
def plainStr [PyCalls m V] (v : V) : m String := do
  let some s ← plainStr? v | PyPure.gap "str() of this value is not modelled yet"
  pure s

/-- A `sep` or `end` keyword of `print`: a `str`, or `None` for the default `d`. -/
def printText [PyCalls m V] (what : String) (d : String) (v : V) : m String := do
  match ← PyPure.immView v with
  | some (.str s) => pure s.s
  | some .none => pure d
  | _ =>
    -- An instance of a subclass of `str` is accepted by CPython.
    userCheck v v
    raiseBuiltin "TypeError" s!"{what} must be None or a string, not {← typeName v}"

/-- `print(*args, **kwargs)`: the `str` of each argument, joined by `sep`, then `end`, written to
the output; `file` and `flush` stop with a gap.  As CPython's argument parsing does, an unknown
keyword raises before `sep` is checked, and `sep` is checked before `end`. -/
def printCall [PyWrites m V] (args kwargs : V) : m V := do
  let some (.tuple xs) ← PyPure.immView args | PyPure.modelInvariant "print: operand assumption failed"
  let mut sepV := none
  let mut endV := none
  for (k, v, _) in ← PyReads.dictEntries kwargs do
    let some (.str s) ← PyPure.immView k | raiseBuiltin "TypeError" "keywords must be strings"
    if s.s == "sep" then sepV := some v
    else if s.s == "end" then endV := some v
    else if s.s != "file" && s.s != "flush" then
      raiseBuiltin "TypeError" s!"'{s.s}' is an invalid keyword argument for print()"
  for (k, _, _) in ← PyReads.dictEntries kwargs do
    if let some (.str s) ← PyPure.immView k then
      if s.s == "file" || s.s == "flush" then
        PyPure.gap s!"print's keyword argument {s.s} is not modelled yet"
  let sep ← match sepV with | some v => printText "sep" " " v | none => pure " "
  let fin ← match endV with | some v => printText "end" "\n" v | none => pure "\n"
  -- Each argument is written as it is converted, as CPython does, so an error leaves the
  -- earlier ones written.
  for (x, i) in xs.toList.zipIdx do
    if i > 0 then PyWrites.write sep
    PyWrites.write (← plainStr x)
  PyWrites.write fin
  pure (PyPure.imm (m := m) .none)

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

/-- A new dict with the entries of `d`, then those of `other`, for `f(**other)`: CPython's
`DICT_MERGE` into the kwargs dict that the call builds; a key already present raises `TypeError`
naming `f`.  The operand `d` stays as it was. -/
def dictMerge [PyCalls m V] [PyNew m V] (f d other : V) : m V := do
  userCheck other other
  if !(← isDict other) then
    -- A built-in type, function or method may have `keys` (the type `dict` has), so it gaps.
    let plain := match ← PyPure.immView other with
      | some (.builtin _) | some (.descr ..) | some (.bound ..) | some (.method ..) => false
      | some _ => true
      | none => false
    if plain || (← listOf? other).isSome then
      raiseBuiltin "TypeError"
        s!"{← calleeName f} argument after ** must be a mapping, not {← typeName other}"
    PyPure.gap "a ** argument that is not a dict is not modelled yet"
  let merged ← PyReads.dictCopy d
  guardDictWalk other merged
  for (k, v, h) in ← PyReads.dictEntries other do
    if (← PyReads.dictFind merged k (some h) (keyEq k)).isSome then
      -- CPython 3.12 names the key by its `str`, a `str` key or not.
      let some s ← plainStr? k | PyPure.gap "a duplicate ** key whose str runs a protocol"
      raiseBuiltin "TypeError" s!"{← calleeName f} got multiple values for keyword argument '{s}'"
    PyNew.dictSetNew merged k v (some h) (keyEq k)
  pure merged

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
    raiseBuiltin "ImportError" s!"cannot import name '{name}' from 'builtins' (unknown location)"
      #[("name", PyPure.imm (m := m) (.str (.ofString "builtins"))),
        ("name_from", PyPure.imm (m := m) (.str (.ofString name)))]

/-- `module.name` for the `builtins` module, which the translator uses for names that are not in
the source; a missing name, or any other module, stops with a gap. -/
def qualifiedRef [PyCalls m V] (module name : String) : m V := do
  if module != "builtins" then PyPure.gap s!"a reference into module {module} is not modelled yet"
  let some v ← PyReads.builtinGet name | PyPure.gap s!"builtins.{name} is missing"
  pure v

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
