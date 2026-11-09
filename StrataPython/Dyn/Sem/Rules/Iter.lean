/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Iter

set_option autoImplicit false

/-!
# Iteration

`iter(obj)` and the next item of an iterator, through `Proto/Iter.lean`.
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.getIter] def getIter (obj : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.getIter (m := PyM σ .writes true) obj)

@[dyn_sem Py.next] def next (iter : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    match ← Proto.iterStep (m := PyM σ .writes true) iter with
    | some v => pure v
    | none => Proto.raiseStop : PyM σ .writes true Value)

end

end StrataPython.Dyn.Sem.Rules
