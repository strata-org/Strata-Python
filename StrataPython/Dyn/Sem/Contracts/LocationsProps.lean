/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Contracts.Locations

set_option autoImplicit false

/-!
# The location operations stop with a gap

Each rule of `Locations.lean` stops with the gap `locGap op`, on every input and in every state:
`attrLoc_eq`, `itemLoc_eq`, `objLoc_eq`, `reachLoc_eq` and `instanceState_eq`.  So these
operations stop visibly, never with a failure, which a verifier would read as a path that can't
happen.
-/

namespace StrataPython.Dyn.Sem.Contracts

open Strata.Dyn.Exec StrataPython.Dyn.Sem

public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

/-- `py.attrLoc obj name` stops with the gap that says frames have no meaning at run time, for every
object and name. -/
theorem attrLoc_eq (obj : Value) (name : String) :
    attrLoc (σ := σ) (ε := ε) (E := E) obj name = semanticGap (locGap "py.attrLoc") := rfl

/-- `py.itemLoc obj key` stops with the gap that says frames have no meaning at run time, for every
object and key. -/
theorem itemLoc_eq (obj : Value) (key : String) :
    itemLoc (σ := σ) (ε := ε) (E := E) obj key = semanticGap (locGap "py.itemLoc") := rfl

/-- `py.objLoc obj` stops with the gap that says frames have no meaning at run time, for every
object. -/
theorem objLoc_eq (obj : Value) :
    objLoc (σ := σ) (ε := ε) (E := E) obj = semanticGap (locGap "py.objLoc") := rfl

/-- `py.reachLoc obj` stops with the gap that says frames have no meaning at run time, for every
object. -/
theorem reachLoc_eq (obj : Value) :
    reachLoc (σ := σ) (ε := ε) (E := E) obj = semanticGap (locGap "py.reachLoc") := rfl

/-- `py.instanceState` stops with the gap that says frames have no meaning at run time. -/
theorem instanceState_eq :
    instanceState (σ := σ) (ε := ε) (E := E) = semanticGap (locGap "py.instanceState") := rfl

end

end StrataPython.Dyn.Sem.Contracts
