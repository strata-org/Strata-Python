/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.DupShared

/-! # `DupShared`'s declarations, registered -/

namespace Strata.Dyn.ExecTest

attribute [dyn_type Dup.Num] Int
attribute [dyn_sem Dup.inc] DupShared.incS

end Strata.Dyn.ExecTest
