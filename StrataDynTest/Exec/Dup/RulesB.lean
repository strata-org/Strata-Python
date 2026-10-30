/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Dup.Env

set_option autoImplicit false

/-! # Another meaning for `Dup`: numbers are natural numbers. -/

namespace Strata.Dyn.ExecTest.Dup.B

attribute [dyn_type Dup.Num] NumN

/-- Add a hundred. -/
@[dyn_sem Dup.inc, expose] public def incB (x : NumN) : NumN := ⟨x.n + 100⟩

end Strata.Dyn.ExecTest.Dup.B
