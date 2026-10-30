/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR

set_option autoImplicit false

/-!
# Typed values

The IR names values by `ValId`.  Here a value has a typed view, whose Lean type carries the
function's environment `env` and the value's Dyn type, a type expression of `env`.  The typed
emitters (`StrataDyn.Build.Typed`) take and give these, so Lean checks a call against the
instruction's signature.  The type is a phantom: nothing ties it to the function but the code
that made the value, and `Build.run` checks the function.

* `Val env t`, a value of type `t`; `Val.ofId` and `Val.cast` give one whatever type they are
  told.
* `Vals env ts`, a value per type of `ts`, written `vals[x, y]` where `Strata.Dyn` is open.

The typed blocks and targets are in `StrataDyn.Build.Typed`, beside the builder operations
that make them.
-/

namespace Strata.Dyn

public section

/-- A value of the function being emitted, over `env`, whose Dyn type is `t`.  `t` is a
phantom: nothing ties it to the value's recorded type but the emitter that made it. -/
structure Val (env : Env Unit) (t : TypeExpr env) where
  id : ValId

namespace Val

variable {env : Env Unit}

/-- The value `id`, at type `t`.  Lean does not check `t`: the escape for a value whose type is
computed when the builder runs. -/
@[inline] def ofId (t : TypeExpr env) (id : ValId) : Val env t := ⟨id⟩

/-- `v`, at type `t`.  Lean does not check `t`. -/
@[inline] def cast {s : TypeExpr env} (t : TypeExpr env) (v : Val env s) : Val env t := ⟨v.id⟩

end Val

/-- A value per type of `ts`, in order: a spread operand, or a block's parameters. -/
inductive Vals (env : Env Unit) : List (TypeExpr env) → Type where
  | nil : Vals env []
  | cons {t : TypeExpr env} {ts : List (TypeExpr env)} (v : Val env t) (vs : Vals env ts) :
      Vals env (t :: ts)

namespace Vals

variable {env : Env Unit}

/-- The values' ids, appended to `acc`. -/
def idsTo {ts : List (TypeExpr env)} (acc : Array ValId) : Vals env ts → Array ValId
  | .nil => acc
  | .cons v vs => vs.idsTo (acc.push v.id)

/-- The values' ids. -/
@[inline] def ids {ts : List (TypeExpr env)} (vs : Vals env ts) : Array ValId := vs.idsTo #[]

end Vals

/-- `vals[x, y]`: the values `x` and `y`, as a `Vals`. -/
scoped syntax (name := valsLit) "vals[" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(vals[$xs,*]) => do
    let mut t ← `(Strata.Dyn.Vals.nil)
    for x in xs.getElems.reverse do
      t ← `(Strata.Dyn.Vals.cons $x $t)
    return t

end

end Strata.Dyn
