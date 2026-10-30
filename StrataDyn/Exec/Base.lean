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
  `Float`, `String`, `Sequence` as `Array`, `Except` as `Except` and `Loc` as `Exec.NoLoc`, which
  has no values.  `Unit` and `Except` are datatypes, so their constructors are checked against
  Lean's;
* rules for the terminators of control flow: `base.jump` takes its one successor,
  `base.branch` the first if its condition holds and the second otherwise, and
  `base.unreachable` stops with `Fault.failure`;
* rules for the contracts' instructions, which stop with `Fault.gap`: `base.old`, because a run
  does not keep the state at the call, and `base.cellLoc`, because frames have no meaning at run
  time.

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

/-- `base.Loc` at run time, a type with no values: no run makes a set of locations, since frames
have no run-time meaning yet. -/
public inductive Exec.NoLoc : Type
  deriving DecidableEq, Repr, Ord

attribute [dyn_type Base.Loc] Exec.NoLoc

namespace Exec.BaseRules

@[expose] public section

variable {ε : Eff} {E : Type}

@[dyn_sem Base.jump] def jump (k : Target E []) : Sem ε E Empty := Exec.jump k ()

@[dyn_sem Base.branch] def branch (cond : Bool) (t f : Target E []) : Sem ε E Empty :=
  if cond then Exec.jump t () else Exec.jump f ()

@[dyn_sem Base.unreachable] def unreachable : Sem ε E Empty :=
  semanticFailure "base.unreachable"

@[dyn_sem Base.old] def old {e a : Type} (_body : Region ε [] (Except e a)) (_err : Target E [e]) :
    Sem ε E a :=
  semanticGap "base.old: the state at the call is not kept at run time"

@[dyn_sem Base.cellLoc] def cellLoc {σ : Type} [Store σ] {a : Type} (_cell : Ref σ a) :
    Sem ε E NoLoc :=
  semanticGap "base.cellLoc: frames have no meaning at run time"

end

end Exec.BaseRules

#dyn_coverage Base (complete)

end Strata.Dyn
