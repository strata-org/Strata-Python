/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Dup.GenEnv

set_option autoImplicit false

/-! # A hand-written Lean type for `gen.Box`. -/

namespace Strata.Dyn.ExecTest.Dup.Written

/-- A box. -/
@[dyn_type Gen.Box] public inductive Box where
  | box (n : NumI)

end Strata.Dyn.ExecTest.Dup.Written
