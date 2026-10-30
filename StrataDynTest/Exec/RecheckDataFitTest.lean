/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.RecheckDataGen
public import StrataDynTest.Exec.RecheckDataInt

set_option autoImplicit false

/-!
# A table that sees the datatypes' type rules

The twin of `RecheckDataTest`: this module imports `RecheckDataInt` too, so the table's
`hdata.Num` is the `Int` that the datatypes' fields were generated at, and the table passes.
-/

namespace Strata.Dyn.ExecTest

#guard_msgs in
#dyn_sem_table HDataSem for HData

end Strata.Dyn.ExecTest
