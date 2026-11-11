/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes

set_option autoImplicit false

/-!
# The locations of frames

A frame names the locations that a call may read or write, and its regions compute them at the
call.  Frames have no meaning at run time yet, so `base.Loc` is a type with no values
(`Exec.NoLoc`), and each operation that makes a set of locations stops with a gap.
`LocationsProps.lean` proves that each one does, on every input.
-/

namespace StrataPython.Dyn.Sem.Contracts

open Strata.Dyn.Exec StrataPython.Dyn.Sem

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

/-- The message of the gap that the location operation `op` stops with. -/
def locGap (op : String) : String := s!"{op}: frames have no meaning at run time"

/-- The location operation `op`, generic in its monad: it stops with its gap. -/
def locationGap {m : Type → Type 1} {V : Type} [PyPure m V] (op : String) : m NoLoc :=
  PyPure.gap (locGap op)

@[dyn_sem Py.attrLoc] def attrLoc (_obj : Value) (_name : String) : Sem ε E NoLoc :=
  runTotalFree "py.attrLoc" #[] (locationGap (m := PyM σ .reads true) "py.attrLoc")

@[dyn_sem Py.itemLoc] def itemLoc (_obj : Value) (_key : String) : Sem ε E NoLoc :=
  runTotalFree "py.itemLoc" #[] (locationGap (m := PyM σ .pure true) "py.itemLoc")

@[dyn_sem Py.objLoc] def objLoc (_obj : Value) : Sem ε E NoLoc :=
  runTotalFree "py.objLoc" #[] (locationGap (m := PyM σ .reads true) "py.objLoc")

@[dyn_sem Py.reachLoc] def reachLoc (_obj : Value) : Sem ε E NoLoc :=
  runTotalFree "py.reachLoc" #[] (locationGap (m := PyM σ .reads true) "py.reachLoc")

@[dyn_sem Py.instanceState] def instanceState : Sem ε E NoLoc :=
  runTotalFree "py.instanceState" #[]
    (locationGap (m := PyM σ .reads true) "py.instanceState")

end

end StrataPython.Dyn.Sem.Contracts
