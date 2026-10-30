/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Dup.GenGenerated
public import StrataDynTest.Exec.Dup.GenWritten

/-! # The generated and the hand-written type rule clash. -/

namespace Strata.Dyn.ExecTest.Dup

/--
error: two imported modules give gen.Box a type rule: Gen.Box.Val (in StrataDynTest.Exec.Dup.GenGenerated) and Written.Box (in StrataDynTest.Exec.Dup.GenWritten)
-/
#guard_msgs in
#dyn_coverage Gen

/--
error: two imported modules give gen.Box a type rule: Gen.Box.Val (in StrataDynTest.Exec.Dup.GenGenerated) and Written.Box (in StrataDynTest.Exec.Dup.GenWritten)
-/
#guard_msgs in
#dyn_sem_table GenSem for Gen

end Strata.Dyn.ExecTest.Dup
