/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Dom
public import StrataPython.Dyn.Sem.Format

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

/-- `repr(v)` for an `int` or a `str`, as the checks' messages need. -/
def checkRepr [PyPure m V] (v : V) : m String := do
  match ← PyPure.immView v with
  | some (.int i) => match Format.intRepr i with
    | .ok s => pure s
    | .error _ => PyPure.gap "the repr of an int with too many digits in a check's message"
  | some (.str s) => pure (Format.strRepr s.s)
  | _ => PyPure.gap "the repr of a value other than an int or a str in a check's message"

/-- `v`, the value of the variable `name`, or a raised `excType(msg)` if `v` is unassigned.  A
`NameError` carries `name` as its `name`, as CPython's `_PyEval_FormatExcCheckArg` sets it; the
other classes (`UnboundLocalError` included) carry none. -/
def requireDefined [PyReads m V] (v : V) (name excType msg : String) : m V := do
  if ← PyPure.isUndef v then
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

end

end

end StrataPython.Dyn.Sem.Proto
