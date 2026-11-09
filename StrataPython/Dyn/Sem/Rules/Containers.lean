/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Containers
public import StrataPython.Dyn.Sem.Proto.Iter

set_option autoImplicit false

/-!
# Containers

Item access, slices, unpacking, `in`, and the lists, tuples, dicts and sets that the emitting
code builds, on built-in values and through user dunders (`Proto/Containers.lean`).
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.in_] def in_ (lhs rhs : Value) (err : Target E [Value]) (st : Option Value)
    (again : Again E Value) : Sem ε E Value :=
  runLoopFree err again st #[] (Proto.inStep (m := PyM σ .calls true) false lhs rhs)

@[dyn_sem Py.notIn] def notIn (lhs rhs : Value) (err : Target E [Value]) (st : Option Value)
    (again : Again E Value) : Sem ε E Value :=
  runLoopFree err again st #[] (Proto.inStep (m := PyM σ .calls true) true lhs rhs)

@[dyn_sem Py.mkList] def mkList (elems : Array Value) : Sem ε E Value :=
  runTotalFree "py.mkList" #[] (PyPure.allocList (m := PyM σ .pure true) elems)

@[dyn_sem Py.getItem] def getItem (obj key : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.getItem (m := PyM σ .calls true) obj key)

@[dyn_sem Py.getSlice] def getSlice (obj lo hi step : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.getItem (m := PyM σ .calls true) obj (.slice lo hi step))

@[dyn_sem Py.getOptionalItem] def getOptionalItem (obj key fallback : Value)
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.getOptionalItem (m := PyM σ .calls true) obj key fallback)

@[dyn_sem Py.dictSet] def dictSet (dict key value : Value) (err : Target E [Value]) :
    Sem ε E Unit :=
  runRuleFree err #[] do
    let h ← Proto.hash (m := PyM σ .writes true) key
    PyWrites.dictSet dict key value (some h) (Proto.keyEq key)

@[dyn_sem Py.setItem] def setItem (obj key val : Value) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (Proto.setItem (m := PyM σ .writes true) obj key val)

@[dyn_sem Py.delItem] def delItem (obj key : Value) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (Proto.delItem (m := PyM σ .writes true) obj key)

@[dyn_sem Py.unpackSeq] def unpackSeq (val : Value) (n : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.unpackSeqAll (m := PyM σ .writes true) val n.toNat)

@[dyn_sem Py.unpackEx] def unpackEx (val : Value) (before after : Int) (err : Target E [Value])
    (st : Option (Proto.UnpackState Value)) (again : Again E (Proto.UnpackState Value)) :
    Sem ε E Value :=
  runLoopFree err again st #[]
    (Proto.unpackExStep (m := PyM σ .writes true) val before.toNat after.toNat)

@[dyn_sem Py.listToTuple] def listToTuple (list : Value) : Sem ε E Value :=
  runTotalFree "py.listToTuple" #[] (e := .reads) (σ := σ) do
    let some xs ← Proto.listOf? list | PyM.failure "listToTuple: operand assumption failed"
    pure (.tuple xs)

@[dyn_sem Py.tupleGet] def tupleGet (tup : Value) (i : Int) : Sem ε E Value :=
  runTotalFree "py.tupleGet" #[] (e := .pure) (σ := σ) <| match tup with
    | .tuple xs => match xs[i.toNat]? with
      | some v => if i ≥ 0 then pure v else PyM.failure "tupleGet: operand assumption failed"
      | none => PyM.failure "tupleGet: operand assumption failed"
    | _ => PyM.failure "tupleGet: operand assumption failed"

@[dyn_sem Py.mkSet] def mkSet (elems : Array Value) (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (Proto.mkSet (m := PyM σ .calls false) elems)

@[dyn_sem Py.constSet] def constSet (elems : Array Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (Proto.constSet (m := PyM σ .calls false) elems)

@[dyn_sem Py.setAdd] def setAdd (set value : Value) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (Proto.setAddItem (m := PyM σ .writes true) set value)

@[dyn_sem Py.setUpdate] def setUpdate (set iterable : Value) (err : Target E [Value])
    (st : Option Value) (again : Again E Value) : Sem ε E Unit :=
  runLoopFree err again st #[] (Proto.setUpdateStep (m := PyM σ .writes true) set iterable)

@[dyn_sem Py.listAppend] def listAppend (list value : Value) : Sem ε E Unit :=
  runTotalFree "py.listAppend" #[] (PyWrites.listAppend (m := PyM σ .writes true) list value)

@[dyn_sem Py.listExtend] def listExtend (list iterable : Value) (err : Target E [Value])
    (st : Option Value) (again : Again E Value) : Sem ε E Unit :=
  runLoopFree err again st #[] (Proto.listExtendStep (m := PyM σ .writes true) list iterable)

end

end StrataPython.Dyn.Sem.Rules
