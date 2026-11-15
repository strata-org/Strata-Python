/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Dom
public import StrataPython.Dyn.Sem.Format
public import StrataPython.Dyn.Env

set_option autoImplicit false

/-!
# Checks, identity, globals and dict displays

Generic over the record of primitives:

* the check `requireDefined`, which raises a built-in exception with the translator's message;
* `is`;
* `loadGlobal`, CPython's `LOAD_GLOBAL`: the module's global, then the `builtins` module's;
* `mkDict`, CPython's `BUILD_MAP`, for keys that are not objects.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- Raise a new exception of the built-in class `cls` with the message `msg` and the fields
`fields`. -/
def raiseBuiltin [PyReads m V] {α : Type} (cls msg : String)
    (fields : Array (String × V) := #[]) : m α :=
  match Builtin.ofName? cls with
  | some b => PyReads.raiseNew (PyPure.imm (m := m) (.builtin b))
    #[PyPure.imm (m := m) (.str (.ofString msg))] fields
  | none => PyPure.gap s!"raising the exception class {cls}, which is not built in"

/-- `repr(v)` for `None`, a `bool`, an `int`, a `float` or a `str`, as the checks' messages need. -/
def checkRepr [PyPure m V] (v : V) : m String := do
  match ← PyPure.immView v with
  | some .none => pure "None"
  | some (.bool b) => pure (if b then "True" else "False")
  | some (.int i) => match Format.intRepr i with
    | .ok s => pure s
    | .error _ => PyPure.gap "the repr of an int with too many digits in a check's message"
  | some (.float bits) => pure (Format.floatRepr bits)
  | some (.str s) => pure (Format.strRepr s.s)
  | _ => PyPure.gap "the repr of a value other than None, a bool, an int, a float or a str in a check's message"

/-- `v`, the value of the variable `name`, or a raised `excType(msg)` if `v` is unassigned.  A
`NameError` carries `name` as its `name`, as CPython's `_PyEval_FormatExcCheckArg` sets it; the
other classes (`UnboundLocalError` included) carry none. -/
def requireDefined [PyReads m V] (v : V) (name excType msg : String) : m V := do
  if let some n ← PyPure.undefName? v then
    -- CPython fills a class's `__class__` cell inside `type.__new__`, the model after
    -- `__build_class__` returns; in between, the cell holds the mark `Py.classCreating`.
    if n == Py.classCreating then
      PyPure.gap "the __class__ cell while a class is created is not modelled yet"
    let fields := if excType == "NameError" then #[("name", PyPure.imm (m := m) (.str (.ofString name)))]
      else #[]
    raiseBuiltin excType msg fields
  else pure v

/-- `a is b`. -/
def isOp [PyPure m V] (a b : V) : m Bool := do
  match ← PyPure.identical a b with
  | .yes => pure true
  | .no => pure false
  | .unknown => PyPure.gap "is on two equal immediates depends on CPython's caching"

/-- `a is b` as a `bool`, or `a is not b` when `neg`. -/
def isValue [PyPure m V] (neg : Bool) (a b : V) : m V :=
  (fun r => PyPure.imm (m := m) (.bool (r != neg))) <$> isOp a b

/-- The octets of `s`, one per character, if every character is below 256. -/
def octets (s : String) : Option (Array UInt8) :=
  s.toList.foldl (fun acc c => acc.bind fun a =>
    if c.val < 256 then some (a.push c.val.toUInt8) else none) (some #[])

/-- The `bytes` whose octets are the characters of `s`. -/
def bytesLit [PyPure m V] (s : String) : m V :=
  match octets s with
  | some b => pure (PyPure.imm (m := m) (.bytes b))
  | none => PyPure.modelInvariant "py.bytesLit: operand assumption failed"

/-- `py.isMarker v`: `true` when `v` is pyhard's `loop_invariant` marker. For any other value, the
guard's false branch stands for CPython's call of that value, which the semantics doesn't model, so
the run stops with a gap instead of returning `false`. -/
def isMarker [PyPure m V] (v : V) : m Bool := do
  if (← PyPure.identical v (PyPure.marker (m := m) "loop_invariant")) == .yes then return true
  PyPure.gap "a call of a loop_invariant other than PyHard's is not modelled yet"

/-- The gap of a construct that the translator doesn't translate, named by the `str` `name`. -/
def unsupported [PyPure m V] {α : Type} (name : V) : m α := do
  match ← PyPure.immViewAll name with
  | some (.str s) => PyPure.gap s!"construct not translated: {s.s}"
  | _ => PyPure.modelInvariant "py.unsupported: operand assumption failed"

/-- The item `i` of the tuple `tup`. -/
def tupleGet [PyPure m V] (tup : V) (i : Int) : m V := do
  match ← PyPure.immViewAll tup with
  | some (.tuple xs) => match xs[i.toNat]? with
    | some v => if i ≥ 0 then pure v else PyPure.modelInvariant "tupleGet: operand assumption failed"
    | none => PyPure.modelInvariant "tupleGet: operand assumption failed"
  | _ => PyPure.modelInvariant "tupleGet: operand assumption failed"

/-- The global `name` of `module`, else the entry `name` of the `builtins` module's dict, else a
raised `NameError`. -/
def loadGlobal [PyReads m V] (module name : String) : m V := do
  match ← PyReads.globalGet module name with
  | some v => pure v
  | none =>
    match ← PyReads.builtinGet name with
    | some v => pure v
    | none =>
      let n := PyPure.imm (m := m) (.str (.ofString name))
      raiseBuiltin "NameError" s!"name '{name}' is not defined" #[("name", n)]

/-- Insert the pairs `kvs`, keys and values alternating, into the dict `d`, which the operation
made, in order. -/
def dictInsertAll [PyPure m V] [PyNew m V] (d : V) : List V → m Unit
  | [] => pure ()
  | [_] => PyPure.modelInvariant "mkDict: operand assumption failed"
  | k :: v :: rest => do
    if (← PyPure.immView k).isNone then
      PyPure.gap "a dict key that is an object is not modelled yet"
    -- A key that holds an object gaps in `dictSetNew`: its hash needs the members' `__hash__`.
    PyNew.dictSetNew d k v none fun _ =>
      PyPure.gap "comparing a dict key with user code is not modelled yet"
    dictInsertAll d rest

/-- A dict of the keys and values `kvs`, alternating, in order: CPython's `BUILD_MAP`, for keys
that are not objects. -/
def mkDict [PyPure m V] [PyNew m V] (kvs : Array V) : m V := do
  let d ← PyPure.allocDict
  dictInsertAll d kvs.toList
  pure d

/-- A new read-only view of the dict `d`, a mappingproxy (`types.MappingProxyType(d)`), such as a
dict view's `mapping`. -/
def allocMappingProxy [PyPure m V] (d : V) : m V :=
  PyPure.allocObj (PyPure.imm (m := m) (.builtin .mappingproxy)) (.dictProxy d)

end

end

end StrataPython.Dyn.Sem.Proto
