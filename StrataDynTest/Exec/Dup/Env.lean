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
# Rules from two modules

`Dup` gets its rules from other modules: `RulesA` and `RulesB` each give `dup.Num` and
`dup.inc` a rule of their own, and `Clash` imports both.  The two meanings of `dup.Num` are
declared here, so that an error names this module, not the ones that register them.
-/

namespace Strata.Dyn.ExecTest.Dup

/-- A language whose rules other modules give. -/
public environment Dup where
  namespace dup
  type Num
  insn inc (x : Num) : Num
  end dup

/-- A number, as an integer. -/
public structure NumI where
  n : Int

/-- A number, as a natural number. -/
public structure NumN where
  n : Nat

end Strata.Dyn.ExecTest.Dup
