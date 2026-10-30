/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Dup.Env

set_option autoImplicit false

/-! # One meaning for `Dup`: numbers are integers. -/

namespace Strata.Dyn.ExecTest.Dup.A

attribute [dyn_type Dup.Num] NumI

/-- Add one. -/
@[dyn_sem Dup.inc, expose] public def incA (x : NumI) : NumI := ⟨x.n + 1⟩

end Strata.Dyn.ExecTest.Dup.A
