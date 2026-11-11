/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Contracts.Ops

set_option autoImplicit false

/-!
# The rules of the contract operations

A contract of a Python function uses these operations; the translator of Python code doesn't
emit them.  Each rule runs its combinator of `Ops.lean` at its operation's declared effect.
-/

namespace StrataPython.Dyn.Sem.Contracts

open Strata.Dyn.Exec StrataPython.Dyn.Sem

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.argOf] def argOfRule (args kwargs : Value) (pos : Int) (name : String)
    (default : Value) : Sem ε E Value :=
  runTotalFree "py.argOf" #[] (argOf (m := PyM σ .reads true) args kwargs pos name default)

@[dyn_sem Py.extraKwargs] def extraKwargsRule (kwargs : Value) (names : Array String) :
    Sem ε E Value :=
  runTotalFree "py.extraKwargs" #[] (extraKwargs (m := PyM σ .reads true) kwargs names)

@[dyn_sem Py.bindsTo] def bindsToRule (args kwargs : Value) (nPos : Int) (varKw : Bool)
    (names : Array String) : Sem ε E Bool :=
  runTotalFree "py.bindsTo" #[] (bindsTo (m := PyM σ .reads true) args kwargs nPos varKw names)

@[dyn_sem Py.stdClass] def stdClassRule (module name : String) : Sem ε E Value :=
  runTotalFree "py.stdClass" #[] (stdClass (m := PyM σ .pure true) module name)

@[dyn_sem Py.isInstance] def isInstanceRule (v cls : Value) (err : Target E [Value]) :
    Sem ε E Bool :=
  runRuleFree err #[] (isInstance (m := PyM σ .calls true) v cls)

@[dyn_sem Py.typeIsSubclass] def typeIsSubclassRule (v cls : Value) (err : Target E [Value]) :
    Sem ε E Bool :=
  runRuleFree err #[] (typeIsSubclass (m := PyM σ .reads true) v cls)

@[dyn_sem Py.len] def lenRule (v : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (len (m := PyM σ .calls true) v)

@[dyn_sem Py.reSearch] def reSearchRule (pattern : String) (s : Value) (err : Target E [Value]) :
    Sem ε E Bool :=
  runRuleFree err #[] (reSearch (m := PyM σ .reads true) pattern s)

@[dyn_sem Py.strIsOneOf] def strIsOneOfRule (v : Value) (lits : Array String) : Sem ε E Bool :=
  runTotalFree "py.strIsOneOf" #[] (strIsOneOf (m := PyM σ .pure true) v lits)

@[dyn_sem Py.intIsOneOf] def intIsOneOfRule (v : Value) (lits : Array Int) : Sem ε E Bool :=
  runTotalFree "py.intIsOneOf" #[] (intIsOneOf (m := PyM σ .pure true) v lits)

@[dyn_sem Py.isImmutableScalar] def isImmutableScalarRule (v : Value) : Sem ε E Bool :=
  runTotalFree "py.isImmutableScalar" #[] (isImmutableScalar (m := PyM σ .pure true) v)

@[dyn_sem Py.dictKeysWithin] def dictKeysWithinRule (d : Value) (keys : Array String) :
    Sem ε E Bool :=
  runTotalFree "py.dictKeysWithin" #[] (dictKeysWithin (m := PyM σ .reads true) d keys)

end

end StrataPython.Dyn.Sem.Contracts
