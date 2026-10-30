/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.RecheckEnv
import StrataDynTest.Exec.RecheckInt

set_option autoImplicit false

/-! # A rule for `hid.pos`, registered where `hid.Num` is `Int` -/

namespace Strata.Dyn.ExecTest.RecheckRule

/-- Whether `x` is positive. -/
@[dyn_sem Hid.pos, expose] public def posI (x : Int) : Bool := decide (0 < x)

end Strata.Dyn.ExecTest.RecheckRule
