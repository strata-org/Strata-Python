/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env
-- Private: building an `Env` value needs its representation at code-generation time.
import StrataMantle.Env.WF
import StrataMantle.DSL

set_option autoImplicit false

/-!
# The base environment

The declarations every language environment extends: `Unit`, the scalar types a constant can
have, a sequence, a mutable cell, a code pointer, `Except`, and the terminal operations of
control flow.  `Unit` and `Except` are datatypes; the rest of the types are primitive.

`Base` is an `environment` block, so a language environment declares it as its parent with
`extends Base`.  In every `e` with `Base.env ⊑ e`:

* `Base.T.ref : TypeRef e n` and `Base.T.ty`, its application to arguments;
* `Base.o.sig : InsnSig e` and `Base.o : InsnRef e Base.o.sig`, for `refNew`, `refGet` and
  `refSet`;
* `Base.Except.ok` and `Base.Except.error`, `Except`'s constructors, as instructions in the
  same way: `Base.Except.ok.sig` is `[e a] (value : a) : Except e a`;
* `Base.Except.case`, the terminal operation that eliminates an `Except`:
  `[e a] (scrutinee : Except e a) (^ok (value : a)) (^error (err : e))`;
* `Base.Unit.unit`, `Unit`'s constructor, and `Base.Unit.case`, which eliminates a `Unit`:
  `(scrutinee : Unit) (^unit)`.  A literal `()` is still the constant `Const.unit`;
* `Base.jump`, `Base.branch` and `Base.unreachable`, the terminal operations of control flow.
  `Terminator.jump`, `.branch`, `.unreachable` and `.ret` apply them.

`base` and `bn` name `Base.env` and its namespace.
-/

namespace Strata.Mantle

/-- The declarations every language environment extends. -/
public environment Base where
  namespace base
  /-- `base.Unit`, the type of `()`. -/
  data Unit where
    | /-- `base.unit`, the unit value. -/ unit
  /-- `base.Bool`. -/
  type Bool
  /-- `base.Int`, the unbounded integers. -/
  type Int
  /-- `base.Float64`. -/
  type Float64
  /-- `base.String`. -/
  type String
  /-- `base.Sequence a`, a sequence of `a`. -/
  type Sequence (+a)
  /-- `base.Ref a`, a mutable cell holding an `a`.  A datatype may recurse through one. -/
  type Ref (+a)

  /-- `base.Except e a`: a value, or the error that replaced it.  `base.Except.case`'s
  successors are in this order, `ok` first; a datatype may recurse through either
  parameter. -/
  data Except (+e) (+a) where
    | /-- `base.ok`, a success. -/ ok (value : a)
    | /-- `base.error`, a failure. -/ error (err : e)

  /-- `base.refNew`, a new cell holding `value`. -/
  insn refNew [a] (value : a) : Ref a
  /-- `base.refGet`, the contents of `cell`. -/
  insn refGet [a] (cell : Ref a) : a
  /-- `base.refSet`, which replaces the contents of `cell` with `value`. -/
  insn refSet [a] (cell : Ref a) (value : a) : Unit

  /-- `base.jump`: A jump to a block `k`.  A jump to a body's exit returns from it. -/
  terminal insn jump (^k)
  /-- `base.branch`: continue at `t` if `cond` holds. -/
  terminal insn branch (cond : Bool) (^t ^f)
  /-- `base.unreachable`: control never gets here. -/
  terminal insn unreachable

  /-- `base.Code`, a code pointer: what `Const.func` denotes and a closure holds.
  The base fixes no calling convention.

  To be revisited: a code pointer should carry its argument and result types, which needs
  function types in `TypeExpr`. -/
  type Code
  end base

public section

/-- The base environment, `Base.env`. -/
abbrev base : Env Unit := Base.env

/-- `base.<s>`, the namespace the base declarations live under. -/
abbrev bn (s : String) : Name := .str (.str .base "base") s

end

end Strata.Mantle
