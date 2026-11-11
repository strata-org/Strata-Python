/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Values

set_option autoImplicit false

/-!
# Values and checks

Literals, tuples and slices, definedness, the checks, `is`, `assertionError`, `unsupported`, and
two rules with hard cases: `loadGlobal` (a cell found in the world, then the `builtins` dict) and
`mkDict` (hashing while it builds).
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.undef] def undef (name : String) : Value := .undef name

@[dyn_sem Py.isDefined] def isDefined (v : Value) : Bool :=
  match v with
  | .undef _ => false
  | _ => true

@[dyn_sem Py.intLit] def intLit (i : Int) : Value := .int i

@[dyn_sem Py.floatLit] def floatLit (f : Float) : Value := .ofFloat f

@[dyn_sem Py.strLit] def strLit (s : String) : Value := .ofString s

@[dyn_sem Py.boolLit] def boolLit (b : Bool) : Value := .bool b

@[dyn_sem Py.noneLit] def noneLit : Value := .none

@[dyn_sem Py.ellipsisLit] def ellipsisLit : Value := .ellipsis

@[dyn_sem Py.assertionError] def assertionError : Value := .builtin .AssertionError

@[dyn_sem Py.mkTuple] def mkTuple (elems : Array Value) : Value := .tuple elems

@[dyn_sem Py.mkSlice] def mkSlice (lo hi step : Value) : Value := .slice lo hi step

@[dyn_sem Py.bytesLit] def bytesLit (s : String) : Sem ε E Value :=
  runTotalFree "py.bytesLit" #[] (Proto.bytesLit (m := PyM σ .pure true) s)

@[dyn_sem Py.requireDefined]
def requireDefined (v : Value) (name excType msg : String) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.requireDefined (m := PyM σ .reads true) v name excType msg)

@[dyn_sem Py.is_] def is_ (a b : Value) : Sem ε E Value :=
  runTotalFree "py.is" #[] (Proto.isValue (m := PyM σ .pure true) false a b)

@[dyn_sem Py.isNot] def isNot (a b : Value) : Sem ε E Value :=
  runTotalFree "py.isNot" #[] (Proto.isValue (m := PyM σ .pure true) true a b)

@[dyn_sem Py.unsupported] def unsupported (name : Value) : Sem ε E Value :=
  runTotalFree "py.unsupported" #[] (Proto.unsupported (m := PyM σ .pure true) name)

@[dyn_sem Py.loadGlobal]
def loadGlobal (module name : String) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.loadGlobal (m := PyM σ .calls true) module name)

@[dyn_sem Py.mkDict] def mkDict (kvs : Array Value) (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (Proto.mkDictHashed (m := PyM σ .calls false) kvs)

end

end StrataPython.Dyn.Sem.Rules
