/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.CertTest
public import StrataDyn.Exec.CertModelProps

set_option autoImplicit false

/-!
# A cell request at another tag, at the test environment's accounts

A read of a cell at another tag than the one it holds is rejected by the machine's spec
(`Accounts.sat_retyped_cell`), as a rule that reads through a retyped ref would make it.
-/

namespace Strata.Dyn.ExecTest.CertModelPropsTest

open Strata.Dyn.Exec Strata.Dyn.ExecTest.CertTest

@[expose] public section

/-- A typing in which cell `0` holds `Int`s. -/
def intAt0 : Typing := { cell := fun l => if l = 0 then some (.app 4 []) else none }

-- A read of cell `0` at `Bool`, where it holds `Int`s, is rejected by the machine's spec.
example : ¬ (accounts.spec [] [] (St := Empty) fun _ _ => True).Sat (fun _ _ => True) intAt0
    (.vis (.get (.app 3 []) 0) fun _ => (.ret () : Tree ExSem.model.at.interp Run
      ExSem.model.at.W [] [] Empty Unit)) :=
  Accounts.sat_retyped_cell accounts _ _ (S := intAt0) (l := 0) (t₁ := .app 4 []) rfl (by decide)
    (.inl rfl) _

end

end Strata.Dyn.ExecTest.CertModelPropsTest
