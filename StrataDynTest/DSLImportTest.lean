/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataDyn.DSL
import StrataDyn.Env.WF

set_option autoImplicit false

/-! # An `environment` in a module that does not import the handle module

The command reports the missing import instead of failing on the code it would generate. -/

namespace Strata.Dyn.DSLImportTest

/-- error: an environment needs `public import StrataDyn.Env.Handle` -/
#guard_msgs in
environment Lone where
  type T

end Strata.Dyn.DSLImportTest
