/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Dup.RulesA
import StrataDyn.Env.WF
import StrataDyn.DSL

set_option autoImplicit false

/-!
# A datatype with two type rules

`GenGenerated` generates `gen.Box`'s Lean type, and `GenWritten` gives it a hand-written one.
`GenBoth` imports both.  Only the type has two rules: `dup.inc` has one.
-/

namespace Strata.Dyn.ExecTest.Dup

/-- A child of `Dup` with a datatype. -/
public environment Gen extends Dup where
  namespace gen
  open dup
  data Box where
    | box (n : Num)
  end gen

end Strata.Dyn.ExecTest.Dup
