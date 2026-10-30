/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.DupA
-- `#guard` runs the table's wrapper, and `DupA`'s rule, as compiled code.
meta import StrataDynTest.Exec.DupA

set_option autoImplicit false

/-!
# One imported registration per key

The twin of `DupTest`: this module imports only `DupA`, so each key of `Dup` has one rule, and
the commands that `DupTest` pins as errors pass.
-/

namespace Strata.Dyn.ExecTest.DupOne

open Strata.Dyn.Exec

#guard_msgs in
@[dyn_sem Dup.neg] def neg (x : Int) : Int := -x

/--
info: type dup.Num ↦ DupA.NumA
op dup.inc ↦ DupA.incA (pure)
op dup.neg ↦ neg (pure)
0 missing, and 0 in ancestors
-/
#guard_msgs in
#dyn_coverage Dup

#guard_msgs in
#dyn_coverage Dup (complete)

#guard_msgs in
#dyn_types Dup

#guard_msgs in
#dyn_sem_table DupSem for Dup

-- The table runs `DupA`'s rule.
#guard id (α := Int) (DupSem.rule.dup.inc Run (41 : Int)) == 42

end Strata.Dyn.ExecTest.DupOne
