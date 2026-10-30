/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.RecheckHiddenDefs

set_option autoImplicit false

/-! # A public swap lemma, which `RecheckHiddenUse` imports only privately -/

namespace Strata.Dyn.ExecTest.HiddenLemma

/-- `revI` is `myRevI`: public, but in a module that its user imports only privately. -/
public theorem revI_eq_myRevI : @revI = @myRevI := by funext xs; rfl

end Strata.Dyn.ExecTest.HiddenLemma
