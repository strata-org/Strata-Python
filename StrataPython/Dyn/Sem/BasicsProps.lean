/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Basics
public import StrataPython.Dyn.Sem.ValueProps

set_option autoImplicit false

/-!
# Properties of identity

Key theorem: `Value.identical_self_ne_no`, that `is` never answers "no" for a defined value and
itself.  `sameOrEq` relies on it to skip `is` for two tuples: it never gives false for two
equal members, so two tuples that `==` finds not equal are structurally different.

The definitions are in `Basics.lean`: `Value.identical`, `Value.isConstant` and
`Value.immKind`.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- `v is v` is never "no" for a value `v` other than an unassigned name: an object has its own
id, a constant equals itself, and any other immediate equals itself, which makes the answer
unknown.  No comparison sees an unassigned name: every read of a name checks it first, and the
tuple of defaults that a function's prologue builds, which holds `undef` for a parameter without a
default, goes only to `bindArgs`. -/
public theorem Value.identical_self_ne_no (v : Value) (h : ∀ n, v ≠ .undef n) :
    Value.identical v v ≠ .no := by
  cases v <;> simp_all [Value.identical, Value.isConstant, Value.immKind]
