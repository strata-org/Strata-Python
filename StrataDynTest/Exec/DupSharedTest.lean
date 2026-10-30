/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.DupSharedX
public import StrataDynTest.Exec.DupSharedY

set_option autoImplicit false

/-! # Two registrations of one declaration are one rule -/

namespace Strata.Dyn.ExecTest.DupSharedBoth

open Strata.Dyn.Exec

#guard_msgs in
@[dyn_sem Dup.neg] def neg (x : Int) : Int := -x

/--
info: type dup.Num ↦ Int
op dup.inc ↦ DupShared.incS (pure)
op dup.neg ↦ neg (pure)
0 missing, and 0 in ancestors
-/
#guard_msgs in
#dyn_coverage Dup

#guard_msgs in
#dyn_types Dup

#guard_msgs in
#dyn_sem_table DupSem for Dup

end Strata.Dyn.ExecTest.DupSharedBoth
