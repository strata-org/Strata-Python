/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Attrs

set_option autoImplicit false

/-!
# Calls and modules

Calls of function objects and of `print`, the lowering of call arguments, references into the
`builtins` module, the imports of `builtins` (`Proto/Calls.lean`), and the dict operations of a
translated function's argument prologue.
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.call] def call (func args kwargs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.callN (m := PyM σ .writes true) Proto.dispatchDepth func args kwargs)

@[dyn_sem Py.qualifiedRef] def qualifiedRef (moduleName name : String) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.qualifiedRef (m := PyM σ .calls true) moduleName name)

@[dyn_sem Py.importModule] def importModule (module : String) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.importModule (m := PyM σ .calls true) module)

@[dyn_sem Py.importFrom] def importFrom (module name : String) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.importFrom (m := PyM σ .calls true) module name)

@[dyn_sem Py.bindArgs]
def bindArgs (args kwargs defaults : Value) (qualname : String) (nPosOnly nPos : Int)
    (varPos varKw : Bool) (names : Array String) (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (Proto.bindArgs (m := PyM σ .reads false) qualname args kwargs defaults
    nPosOnly.toNat nPos.toNat varPos varKw names)

@[dyn_sem Py.mkKwargs] def mkKwargs (kvs : Array Value) : Sem ε E Value :=
  runTotal "py.mkKwargs" #[] (Proto.mkDict (m := PyM σ .pure false) kvs)

@[dyn_sem Py.argsTuple] def argsTuple (callee iterable : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.argsTuple (m := PyM σ .calls true) callee iterable)

@[dyn_sem Py.dictMerge] def dictMerge (callee dict other : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (Proto.dictMerge (m := PyM σ .calls false) callee dict other)

end

end StrataPython.Dyn.Sem.Rules
