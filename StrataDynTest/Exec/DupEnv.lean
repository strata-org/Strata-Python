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
# An environment that two sibling modules give rules

`DupA` and `DupB` each register a type rule for `dup.Num` and a rule for `dup.inc`, and neither
imports the other.  `DupTest` imports both, and `DupOneTest` only `DupA`.
-/

namespace Strata.Dyn.ExecTest

/-- An environment whose rules come from sibling modules. -/
public environment Dup where
  namespace dup
  type Num
  insn inc (x : Num) : Num
  insn neg (x : Num) : Num
  end dup

end Strata.Dyn.ExecTest
