/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Concrete
public import StrataPython.Dyn.Sem.PyTypes

set_option autoImplicit false

/-!
# Global cells

`globalCell` gives the cell of a module's global: the cell in the module table, or a new cell
holding `undef`, which it records there.  A module's first global also makes the module object.
It is the one rule whose result is a cell, so it is written directly in `Sem`, with its own
proofs.
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

/-- The module object of `module`. -/
def moduleObj (module : String) : Obj σ :=
  ⟨.builtin .module, none, #[], .module ⟨module, #[], false⟩⟩

@[dyn_sem Py.globalCell] def globalCell (module name : String) : Sem ε E (Ref σ Value) := do
  let m ← getThe (Modules σ)
  match m.cell? module name with
  | some r => pure r
  | none =>
    let r : Ref σ Value ← newRef (Value.undef name)
    let isNew := (m.map[module]?).isNone
    let n ← modifyGetThe (ObjStore σ) fun st =>
      (st.size, if isNew then (st.alloc (moduleObj module)).1 else st)
    modifyThe (Modules σ) fun m => m.withCell module name n r
    pure r

end

end StrataPython.Dyn.Sem.Rules
