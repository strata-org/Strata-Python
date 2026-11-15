/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Modules.Common

set_option autoImplicit false

/-!
# The model of `pyhard`

`Python/pyhard/pyhard.py` defines the loop-invariant markers `loop_invariant` and `OLD`
(`docs/PythonToDyn.md` §6.11). The model's module holds `__name__` and the two markers, as
marker values. CPython's `vars(pyhard)` holds no other name except dunders, and a read of any
other dunder stops with a gap, as for every made module. The import charges no
frames: outside code imports `pyhard` before the program starts (§12.9), so CPython's import finds
the module in `sys.modules` and runs no Python frame.
-/

namespace StrataPython.Dyn.Sem.Modules

open Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- **`import pyhard`**: the module whose `loop_invariant` and `OLD` are the markers, made at its
first import. A write to one of its attributes stops with a gap, as for every made module. -/
def importPyhard [PyWrites m V] [PyNew m V] (_self _args _kwargs : V) : m V := do
  let attrs : Array (String × V) := #[("__name__", strValue (m := m) "pyhard"),
    ("loop_invariant", PyPure.marker (m := m) "loop_invariant"),
    ("OLD", PyPure.marker (m := m) "OLD")]
  let mod ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .module)) (.module "pyhard" #[] true attrs)
  PyReads.moduleAdd "pyhard" mod
  pure mod

end

/-- **The rules of `pyhard`**: its import. It has no bodies: a call of a marker stops with a gap. -/
def pyhardImpls : Impls where
  method
    | .module, n => if n == importHook "pyhard" then some fun {_} {_} [_] [_] => importPyhard else none
    | _, _ => none

end

end StrataPython.Dyn.Sem.Modules
