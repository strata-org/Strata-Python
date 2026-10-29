/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Env.Handle
import StrataDyn.Env.WF
import StrataDyn.DSL
-- Imported privately on purpose: a public child of `Demo` cannot be declared here.
import StrataDynTest.DSLTest

set_option autoImplicit false

/-!
# The `environment` command: a parent imported privately

A public environment needs its parent in the public scope.  Under a plain `import` of the
parent's module, the elaborator says so at the `extends` clause, before emitting anything.
A private child is fine.
-/

namespace Strata.Dyn.DSLPrivTest

open Strata.Dyn.DSLTest

/--
error: `Demo` is imported privately; use `public import StrataDynTest.DSLTest`
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

end Strata.Dyn.DSLPrivTest
