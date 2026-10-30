/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-! # Functions whose swap lemma is in `RecheckHiddenLemma`, and an `@[init]` definition -/

namespace Strata.Dyn.ExecTest.HiddenLemma

/-- The compiled code of `myRevI`: it drops everything. -/
@[expose] public def lieRevI (_xs : Array Int) : Array Int := #[]
/-- `xs` reversed, run as `lieRevI`. -/
@[implemented_by lieRevI, expose] public def myRevI (xs : Array Int) : Array Int := xs.reverse
/-- `xs` reversed. -/
@[expose] public def revI (xs : Array Int) : Array Int := xs.reverse

/-- The initializer of `initFive`: at run time, its value is `7`. -/
public def initSeven : IO Int := pure 7
/-- `5` in the logic; at run time, what `initSeven` computes.  A `module` file that imports this
one doesn't see the `@[init]`. -/
@[init initSeven, expose] public def initFive : Int := 5

end Strata.Dyn.ExecTest.HiddenLemma
