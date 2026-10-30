/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.DupA
public import StrataDynTest.Exec.DupB

set_option autoImplicit false

/-!
# Two imported registrations for one key

`DupA` and `DupB` each register `dup.Num` and `dup.inc`.  This module imports both, so the
commands that read `Dup`'s rules report both pairs.  `DupOneTest` imports only `DupA`, and the
same commands pass.
-/

namespace Strata.Dyn.ExecTest.DupBoth

open Strata.Dyn.Exec

/--
error: two imported modules give dup.Num a type rule: DupA.NumA (in StrataDynTest.Exec.DupA) and DupB.NumB (in StrataDynTest.Exec.DupB)
two imported modules give dup.inc a rule: DupA.incA (in StrataDynTest.Exec.DupA) and DupB.incB (in StrataDynTest.Exec.DupB)
-/
#guard_msgs in
#dyn_coverage Dup

/--
error: two imported modules give dup.Num a type rule: DupA.NumA (in StrataDynTest.Exec.DupA) and DupB.NumB (in StrataDynTest.Exec.DupB)
two imported modules give dup.inc a rule: DupA.incA (in StrataDynTest.Exec.DupA) and DupB.incB (in StrataDynTest.Exec.DupB)
-/
#guard_msgs in
#dyn_coverage Dup (complete)

/--
error: two imported modules give dup.Num a type rule: DupA.NumA (in StrataDynTest.Exec.DupA) and DupB.NumB (in StrataDynTest.Exec.DupB)
two imported modules give dup.inc a rule: DupA.incA (in StrataDynTest.Exec.DupA) and DupB.incB (in StrataDynTest.Exec.DupB)
-/
#guard_msgs in
#dyn_sem_table DupSem for Dup

/--
error: two imported modules give dup.Num a type rule: DupA.NumA (in StrataDynTest.Exec.DupA) and DupB.NumB (in StrataDynTest.Exec.DupB)
two imported modules give dup.inc a rule: DupA.incA (in StrataDynTest.Exec.DupA) and DupB.incB (in StrataDynTest.Exec.DupB)
-/
#guard_msgs in
#dyn_types Dup

/--
error: two imported modules give dup.Num a type rule: DupA.NumA (in StrataDynTest.Exec.DupA) and DupB.NumB (in StrataDynTest.Exec.DupB)
two imported modules give dup.inc a rule: DupA.incA (in StrataDynTest.Exec.DupA) and DupB.incB (in StrataDynTest.Exec.DupB)
-/
#guard_msgs in
@[dyn_sem Dup.neg] def neg (x : Int) : Int := -x

end Strata.Dyn.ExecTest.DupBoth
