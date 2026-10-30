/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.RecheckRule

set_option autoImplicit false

/-! # The table checks each rule again, at its own type rules -/

namespace Strata.Dyn.ExecTest

attribute [dyn_type Hid.Num] Nat
attribute [dyn_type Hid.Flag] Bool

/--
error: the rule RecheckRule.posI for hid.pos does not fit this table's type rules: operand x of hid.pos: expected Nat, but RecheckRule.posI takes Int
-/
#guard_msgs in
#dyn_sem_table HidSem for Hid

end Strata.Dyn.ExecTest
