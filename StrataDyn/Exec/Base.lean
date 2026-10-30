/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Base
public import StrataDyn.Exec
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The base environment's rules

What every environment that extends `Base` inherits, so that its table covers the base.  The
module that generates the table imports this one.

It registers:

* the base's types at their Lean types: `base.Unit` as `Unit`, `Bool`, `Int`, `Float64` as
  `Float`, `String`, `Sequence` as `Array` and `Except` as `Except`.  `Unit` and `Except` are
  datatypes, so their constructors are checked against Lean's;
* rules for the terminators of control flow: `base.jump` takes its one successor,
  `base.branch` the first if its condition holds and the second otherwise, and
  `base.unreachable` stops with `Fault.failure`.

The rest of the base needs no rule.  The engine interprets `base.Ref` and `base.Fn`; the
machine implements `base.refNew`, `refGet`, `refSet` and `callCode`; and the constructors and
case instructions of `Unit` and `Except` are derived.  A transfer to a body's exit leaves the
body, so `Terminator.ret` is a `base.jump` there.
-/

namespace Strata.Dyn

attribute [dyn_type Base.Unit] Unit
attribute [dyn_type Base.Bool] Bool
attribute [dyn_type Base.Int] Int
attribute [dyn_type Base.Float64] Float
attribute [dyn_type Base.String] String
attribute [dyn_type Base.Sequence] Array
attribute [dyn_type Base.Except] Except

namespace Exec.BaseRules

@[expose] public section

variable {ε : Eff} {E : Type}

@[dyn_sem Base.jump] def jump (k : Target E []) : Sem ε E Empty := Exec.jump k ()

@[dyn_sem Base.branch] def branch (cond : Bool) (t f : Target E []) : Sem ε E Empty :=
  if cond then Exec.jump t () else Exec.jump f ()

@[dyn_sem Base.unreachable] def unreachable : Sem ε E Empty :=
  semanticFailure "base.unreachable"

end

end Exec.BaseRules

#dyn_coverage Base (complete)

end Strata.Dyn
