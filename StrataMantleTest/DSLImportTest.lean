/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataMantle.DSL
import StrataMantle.Env.WF

set_option autoImplicit false

/-! # An `environment` in a module that does not import the refinement module

The command reports the missing import instead of failing on the code it would generate. -/

namespace Strata.Mantle.DSLImportTest

/-- error: an environment needs `public import StrataMantle.Env.Refine` -/
#guard_msgs in
environment Lone where
  type T

end Strata.Mantle.DSLImportTest
