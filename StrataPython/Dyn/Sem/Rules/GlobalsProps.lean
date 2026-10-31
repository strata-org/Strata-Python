/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Rules.Globals

set_option autoImplicit false

/-!
# `globalCell` gives the same cell for the same arguments

`globalCell_found`: in a world whose module table holds the cell, `globalCell` returns it.
`globalCell_records`: otherwise it makes a new cell and records it, and then the table holds it
(`Modules.cell?_withCell_self`).
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

/-- **`globalCell` gives the same cell for the same arguments**: in a world whose module table
holds a cell for `name` of `module`, it reads the world and returns that cell; a first call
records the new cell it returns (`Modules.cell?_withCell_self`). -/
theorem globalCell_found (module name : String) (w : ε.W) (r : Ref σ Value)
    (h : (HasPart.get w : Modules σ).cell? module name = some r) :
    ∃ k, (globalCell (E := E) module name : Sem ε E (Ref σ Value)) = .update k ∧
      k w = (w, .ret r) := by
  refine ⟨_, rfl, ?_⟩
  dsimp only [Sem.bindAfter, Sem.bind]
  rw [h]
  rfl

/-- The other half of **the same cell for the same arguments**: in a world whose module table
holds no cell for `name` of `module`, `globalCell` makes a new cell holding `undef`, records it
in the module table, and returns it; by `Modules.cell?_withCell_self`, the table then holds that
cell for `name` of `module`. -/
theorem globalCell_records (module name : String) (w : ε.W)
    (h : (HasPart.get w : Modules σ).cell? module name = none) :
    ∃ k, (globalCell (E := E) module name : Sem ε E (Ref σ Value)) = .update k ∧ (k w).1 = w ∧
      (k w).2 = (do
        let r : Ref σ Value ← newRef (Value.undef name)
        let isNew := ((HasPart.get w : Modules σ).map[module]?).isNone
        let n ← modifyGetThe (ObjStore σ) fun st =>
          (st.size, if isNew then (st.alloc (moduleObj module)).1 else st)
        modifyThe (Modules σ) fun m => m.withCell module name n r
        pure r) := by
  refine ⟨_, rfl, rfl, ?_⟩
  dsimp only [Sem.bindAfter, Sem.bind]
  rw [h]

end

end StrataPython.Dyn.Sem.Rules
