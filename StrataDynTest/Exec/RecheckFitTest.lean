/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.RecheckRule
public import StrataDynTest.Exec.RecheckInt

set_option autoImplicit false

/-!
# A table that sees the rule's type rules

The twin of `RecheckTest`: this module imports `RecheckInt` too, so the table's `hid.Num` is
the `Int` that `RecheckRule.posI` was checked at, and the table passes.
-/

namespace Strata.Dyn.ExecTest

#guard_msgs in
#dyn_sem_table HidSem for Hid

end Strata.Dyn.ExecTest
