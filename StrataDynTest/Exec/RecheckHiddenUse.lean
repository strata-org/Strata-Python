/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.RecheckHiddenDefs
import StrataDynTest.Exec.RecheckHiddenLemma

set_option autoImplicit false

/-! # A swap whose lemma comes from a module imported only privately

A module that imports this one sees `swappedI`'s definition, but neither the lemma, nor the
module it comes from, nor `swappedI`'s compiled code. -/

namespace Strata.Dyn.ExecTest.HiddenUse

open Strata.Dyn.ExecTest.HiddenLemma

section
attribute [local csimp] revI_eq_myRevI
/-- `xs` reversed, compiled here with the swap of `revI` for `myRevI`, so it runs `lieRevI`; a
caller doesn't inline it. -/
@[expose, noinline] public def swappedI (xs : Array Int) : Array Int := revI xs
end

end Strata.Dyn.ExecTest.HiddenUse
