/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env
import StrataMantle.Env.WF
import StrataMantle.DSL
-- Imported privately on purpose: a public child of `Demo` cannot be declared here.
import StrataMantleTest.DSLTest

set_option autoImplicit false

/-!
# The `environment` command: a parent imported privately

A public environment needs its parent in the public scope.  Under a plain `import` of the
parent's module, the elaborator says so at the `extends` clause, before emitting anything.
A private child is fine.
-/

namespace Strata.Mantle.DSLPrivTest

open Strata.Mantle.DSLTest

/--
error: `Demo` is imported privately; use `public import StrataMantleTest.DSLTest`
-/
#guard_msgs in
public environment PubChild extends Demo where
  type A

/-- A private child of a privately imported parent. -/
environment PrivChild extends Demo where
  namespace priv
  open demo
  type A
  insn f (x : Value) : A

example : Demo.env ⊑ PrivChild.env := inferInstance

end Strata.Mantle.DSLPrivTest
