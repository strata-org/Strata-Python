/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Env.Handle
import StrataDyn.Env.WF
import StrataDyn.DSL
public import StrataDyn.Exec

set_option autoImplicit false

/-!
# A type rule that only a rule's module sees

`RecheckRule` registers a rule for `hid.pos` where `hid.Num` is `Int`, by a private import of
`RecheckInt`.  `RecheckTest` imports `RecheckRule` but not `RecheckInt`, and makes `hid.Num` a
`Nat`.  `hid.Flag` is `Bool` in both, so the rule's wrapper would compile, through a coercion
from `Nat` to `Int`, if the table did not check the rule again.  `RecheckFitTest` imports
both, and its table passes.
-/

namespace Strata.Dyn.ExecTest

/-- A language whose rule was checked against a type rule that its table may not see. -/
public environment Hid where
  namespace hid
  type Num
  type Flag
  insn pos (x : Num) : Flag
  end hid

end Strata.Dyn.ExecTest
