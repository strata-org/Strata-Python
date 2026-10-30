/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Env.Handle
-- Private: building an `Env` value needs its representation at code-generation time.
import StrataDyn.Env.WF
-- The command alone: the typed builder, which `StrataDyn.DSL` adds, is built over `Base`.
import StrataDyn.DSL.Core

set_option autoImplicit false

/-!
# The base environment

The declarations every language environment extends: `Unit`, the scalar types a constant can
have, a sequence, a mutable cell, a typed code pointer and a call through it, `Except`, `old`,
which an `ensures` clause applies to read the state at the call, `Loc`, a set of locations that a
frame names, with `cellLoc`, the location of a cell's contents, and the terminal operations of
control flow.  `Unit` and `Except` are datatypes; the rest of the types are primitive.

`Base` is an `environment` block, so a language environment declares it as its parent with
`extends Base`.  In every `e` with `Base.env ≼ e`:

* `Base.T.ref : TypeRef e n`, and the handle `Base.T`, its type expression, applied to its
  arguments if it has parameters;
* `Base.o.sig : InsnSig e` and `Base.o : InsnRef e Base.o.sig`, for `refNew`, `refGet`,
  `refSet`, `old`, `cellLoc` and `callCode`;
* `Base.Except.ok` and `Base.Except.error`, `Except`'s constructors, as instructions in the
  same way: `Base.Except.ok.sig` is `[e a] (value : a) : Except e a`;
* `Base.Except.case`, the terminal operation that eliminates an `Except`:
  `[e a] (scrutinee : Except e a) (^ok (value : a)) (^error (err : e))`;
* `Base.Unit.unit`, `Unit`'s constructor, and `Base.Unit.case`, which eliminates a `Unit`:
  `(scrutinee : Unit) (^unit)`.  A literal `()` is still the constant `Const.unit`;
* `Base.jump`, `Base.branch` and `Base.unreachable`, the terminal operations of control flow.
  `Terminator.jump`, `.branch`, `.unreachable` and `.ret` apply them.

Each instruction declares its effect.  `refNew`, which allocates, `cellLoc`, and `jump`, `branch`
and `unreachable` are `pure`; `refGet` and `old` are `reads`; `refSet` and `callCode` are
`writes`.
`Unit`'s and `Except`'s constructors and case instructions are `pure`, as every datatype's are.

`base` and `bn` name `Base.env` and its namespace.
-/

namespace Strata.Dyn

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
  pure insn refNew [a] (value : a) : Ref a
  /-- `base.refGet`, the contents of `cell`. -/
  reads insn refGet [a] (cell : Ref a) : a
  /-- `base.refSet`, which replaces the contents of `cell` with `value`. -/
  writes insn refSet [a] (cell : Ref a) (value : a) : Unit
  /-- `base.old`, which runs `body` in the state at the call of the function whose `ensures`
  clause applies it: the value of an `ok`, or a transfer to `err` with the error of an
  `error`.  Only an `ensures` clause may apply it. -/
  reads insn old [e a] (&body : Except e a) (^err (exc : e)) : a

  /-- `base.Loc`, a set of mutable locations of the program state, which a frame names.  A
  language adds operations that give its own locations. -/
  type Loc
  /-- `base.cellLoc`, the contents of `cell`: a set of one location.  It denotes the location by
  the cell's identity, and reads no state. -/
  pure insn cellLoc [a] (cell : Ref a) : Loc

  /-- `base.jump`: A jump to a block `k`.  A jump to a body's exit returns from it. -/
  pure terminal insn jump (^k)
  /-- `base.branch`: continue at `t` if `cond` holds. -/
  pure terminal insn branch (cond : Bool) (^t ^f)
  /-- `base.unreachable`: control never gets here. In a contract region, such as a clause, a
  frame region, an initializer or an invariant, reaching it means that the region is not well
  defined, so a consumer must not read it as `assume(false)`. -/
  pure terminal insn unreachable

  /-- `base.Fn as r`, a typed code pointer: to a function that takes arguments of the types
  `as`, in order, and returns an `r`.  A function reference has its target's `Fn` type,
  `Func.codeType`.  A datatype may recurse through `r`. -/
  type Fn (as : list) (+r)
  /-- `base.callCode`, a call of the function `f` points to: one argument per element of
  `as`, of that element's type.  The callee may change state. -/
  writes insn callCode [(as : list) r] (f : Fn as r) (*args : as) : r
  end base

public section

/-- The base environment, `Base.env`. -/
abbrev base : Env Unit := Base.env

/-- `base.<s>`, the namespace the base declarations live under. -/
abbrev bn (s : String) : Name := .str (.str .base "base") s

end

end Strata.Dyn
