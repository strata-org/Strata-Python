/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.DupEnv

set_option autoImplicit false

/-!
# One declaration, registered by two modules

`DupSharedX` and `DupSharedY` do not import each other, and each registers the same
declarations: `Int` for `dup.Num`, and `incS` for `dup.inc`.  `DupSharedTest` imports both,
and sees one rule for each.  `DupTest` is its twin, whose two modules register different
declarations.
-/

namespace Strata.Dyn.ExecTest.DupShared

/-- Add one. -/
@[expose] public def incS (x : Int) : Int := x + 1

end Strata.Dyn.ExecTest.DupShared
