/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
-- The command alone: `StrataDyn.DSL` imports the handle module through the typed builder.
import StrataDyn.DSL.Core
import StrataDyn.Env.WF

set_option autoImplicit false

/-! # An `environment` in a module that does not import the handle module

The command reports the missing import instead of failing on the code it would generate.  In a
module that imports `StrataDyn.DSL`, which imports the handle module, a block is accepted
(`DSLTest`). -/

namespace Strata.Dyn.DSLImportTest

/-- error: an environment needs `public import StrataDyn.Env.Handle` -/
#guard_msgs in
environment Lone where
  type T

end Strata.Dyn.DSLImportTest
