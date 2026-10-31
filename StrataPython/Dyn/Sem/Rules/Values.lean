/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Concrete
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Values

set_option autoImplicit false

/-!
# Values and checks

Literals, definedness, the checks, `is`, `assertionError`, `unsupported`, and two rules with hard
cases: `loadGlobal` (a cell found in the world, then the `builtins` dict) and `mkDict` (hashing
while it builds).
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

/-- The octets of `s`, one per character, if every character is below 256. -/
def octets (s : String) : Option (Array UInt8) :=
  s.toList.foldl (fun acc c => acc.bind fun a =>
    if c.val < 256 then some (a.push c.val.toUInt8) else none) (some #[])

@[dyn_sem Py.bytesLit] def bytesLit (s : String) : Sem ε E Value :=
  runTotalFree "py.bytesLit" #[] (e := .pure) (σ := σ) <| match octets s with
    | some b => pure (.bytes b)
    | none => PyM.failure "py.bytesLit: operand assumption failed"

@[dyn_sem Py.requireDefined]
def requireDefined (v : Value) (excType msg : String) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.requireDefined (m := PyM σ .reads true) v excType msg)

@[dyn_sem Py.is_] def is_ (a b : Value) : Sem ε E Value :=
  runTotalFree "py.is" #[] ((Value.bool ·) <$> Proto.isOp (m := PyM σ .pure true) a b)

@[dyn_sem Py.isNot] def isNot (a b : Value) : Sem ε E Value :=
  runTotalFree "py.isNot" #[] ((Value.bool ∘ not) <$> Proto.isOp (m := PyM σ .pure true) a b)

@[dyn_sem Py.unsupported] def unsupported (name : Value) : Sem ε E Value :=
  runTotalFree "py.unsupported" #[] (e := .pure) (σ := σ) <| match name with
    | .str s => PyM.gap s!"construct not translated: {s.s}"
    | _ => PyM.failure "py.unsupported: operand assumption failed"

@[dyn_sem Py.loadGlobal]
def loadGlobal (module name : String) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.loadGlobal (m := PyM σ .calls true) module name)

@[dyn_sem Py.mkDict] def mkDict (kvs : Array Value) (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (Proto.mkDict (m := PyM σ .calls false) kvs)

end

end StrataPython.Dyn.Sem.Rules
