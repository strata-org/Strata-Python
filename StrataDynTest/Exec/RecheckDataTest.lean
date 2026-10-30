/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.RecheckDataGen

set_option autoImplicit false

/-! # The table checks each datatype's rule again, at its own type rules -/

namespace Strata.Dyn.ExecTest

attribute [dyn_type HData.Num] Nat

/--
error: the type rule HData.Box.Val for hdata.Box does not fit this table's type rules: field n of hdata.box: HData.Box.Val.box has Int, but ⟦hdata.Num⟧ is Nat
---
error: the type rule HData.RCell.Val for hdata.RCell does not fit this table's type rules: field r of hdata.rcell: HData.RCell.Val.rcell has Exec.Ref
  σ Int, but ⟦base.Ref hdata.Num⟧ is Exec.Ref σ Nat
-/
#guard_msgs in
#dyn_sem_table HDataSem for HData

end Strata.Dyn.ExecTest
