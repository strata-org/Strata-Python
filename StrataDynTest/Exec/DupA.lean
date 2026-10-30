/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.DupEnv

set_option autoImplicit false

/-!
# Rules for `Dup`, from one of two sibling modules

This module and `DupB` each register a type rule for `dup.Num` and a rule for
`dup.inc`.
-/

namespace Strata.Dyn.ExecTest.DupA

open Strata.Dyn.Exec

/-- `dup.Num`'s Lean type, from this module. -/
public abbrev NumA := Int

attribute [dyn_type Dup.Num] NumA

/-- `dup.inc`'s rule, from this module. -/
@[expose, dyn_sem Dup.inc] public def incA (x : Int) : Int := x + 1

end Strata.Dyn.ExecTest.DupA
