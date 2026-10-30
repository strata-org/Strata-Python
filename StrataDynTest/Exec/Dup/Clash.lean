/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Dup.RulesA
public import StrataDynTest.Exec.Dup.RulesB
import StrataDyn.Env.WF
import StrataDyn.DSL

set_option autoImplicit false

/-!
# Two rules for one type or instruction of an ancestor

`RulesA` and `RulesB` each give `dup.Num` and `dup.inc` a rule.  `DupChild` extends `Dup`, so
registering a rule for one of its own instructions, and its coverage, are errors that name both
of `Dup`'s pairs.  For `dup.Num`, the error names the module that declares each type, `Env`,
not the module that registers it: this pins today's message, which should name the
registering module.
-/

namespace Strata.Dyn.ExecTest.Dup

/-- A child of `Dup`. -/
environment DupChild extends Dup where
  namespace child
  open dup
  insn dec (x : Num) : Num
  end child

/--
error: two imported modules give dup.Num a type rule: NumI (in StrataDynTest.Exec.Dup.Env) and NumN (in StrataDynTest.Exec.Dup.Env)
two imported modules give dup.inc a rule: A.incA (in StrataDynTest.Exec.Dup.RulesA) and B.incB (in StrataDynTest.Exec.Dup.RulesB)
-/
#guard_msgs in
@[dyn_sem DupChild.dec] def decI (x : NumI) : NumI := ⟨x.n - 1⟩

/--
error: two imported modules give dup.Num a type rule: NumI (in StrataDynTest.Exec.Dup.Env) and NumN (in StrataDynTest.Exec.Dup.Env)
two imported modules give dup.inc a rule: A.incA (in StrataDynTest.Exec.Dup.RulesA) and B.incB (in StrataDynTest.Exec.Dup.RulesB)
-/
#guard_msgs in
#dyn_coverage DupChild

end Strata.Dyn.ExecTest.Dup
