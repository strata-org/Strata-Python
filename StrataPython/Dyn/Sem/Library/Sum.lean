/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Arith

set_option autoImplicit false

/-!
# The numeric core of `sum`

CPython 3.12's `sum(iterable, start)` (`builtin_sum_impl` in `Python/bltinmodule.c`) adds the
items in one of three phases:
* the int phase keeps the total of exact ints and bools as a C integer, while each item and the
  total fit in 64 bits;
* the float phase keeps the total of exact floats with a compensation term (Neumaier's improved
  Kahan–Babuška summation), and adds any int that fits in 64 bits (a bool or an instance of a
  subclass included) without compensation;
* the generic phase adds each item with `+`.

An item that its phase doesn't take ends the phase: CPython adds it to the total with `+`. After
the int phase, the sum goes on in the float phase if the total is then an exact float, and in the
generic phase otherwise. After the float phase, it always goes on in the generic phase. So an item
can change how the items after it are added: `sum([0.1] * 10)` is `1.0`, but
`sum([2 ** 63, -2 ** 63] + [0.1] * 10)` is `0.9999999999999999`, since the big int ends the int
phase with an int total.

This file defines the loop's state and one step of each phase, as pure functions, generic in
the type `α` of the caller's objects. The caller gets the items, adds an item with `+` when
`step` says so, and calls `afterAdd` with the result. The generic phase holds its total object;
the int and float phases hold their totals as numbers.
-/

namespace StrataPython.Dyn.Sem.Library.Sum

open StrataPython.Dyn.Sem.Arith
open StrataPython.Dyn.Sem.Format (Failure ssizeMax roundToBits)

@[expose] public section

/-- The state of `sum`'s loop. -/
inductive State (α : Type) where
  /-- The int phase, with the total so far, which fits in a C `long`. -/
  | int (total : Int)
  /-- The float phase, with the bits of the total so far and of the compensation. -/
  | float (total compensation : UInt64)
  /-- The generic phase, with the total object. -/
  | generic (total : α)
  deriving Repr, BEq, DecidableEq

/-- An item, as the phases tell items apart. -/
inductive Item where
  /-- An instance of `int` (a `bool` or a subclass included) with its int value, read without
  calling any method; `exact` if its type is `int` or `bool`. -/
  | int (value : Int) (exact : Bool)
  /-- An object whose type is `float`, by its bits. -/
  | float (bits : UInt64)
  /-- Any other object, an instance of a subclass of `float` included. -/
  | other
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The types whose instances `sum` rejects as a start. -/
inductive Rejected where
  | str
  | bytes
  | bytearray
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The start of `sum`, as its phases tell it apart. -/
inductive Start (α : Type) where
  /-- No `start`: the int phase from `0`. -/
  | none
  /-- An object `obj` whose type is `int` (not a `bool` and not a subclass), with its value. -/
  | int (value : Int) (obj : α)
  /-- An object whose type is `float`, by its bits. -/
  | float (bits : UInt64)
  /-- An instance of `str`, `bytes` or `bytearray`, or of a subclass of one of them. -/
  | rejected (t : Rejected)
  /-- Any other object, which becomes the total of the generic phase. -/
  | other (obj : α)
  deriving Repr, BEq, DecidableEq

/-- Whether `n` fits in a C `long`, as `PyLong_AsLongAndOverflow` checks it. -/
def fitsLong (n : Int) : Bool := ssizeMin ≤ n && n ≤ ssizeMax

/-- The first state of the loop, or CPython's `TypeError` for a `str`, `bytes` or `bytearray`
start. An int start that doesn't fit in a C `long` skips the int phase. The caller calls `iter`
on the iterable first, as CPython does. -/
def init {α : Type} : Start α → Except Failure (State α)
  | .none => .ok (.int 0)
  | .int v obj => .ok (if fitsLong v then .int v else .generic obj)
  | .float bits => .ok (.float bits zero)
  | .rejected .str => .error (.raise "TypeError" "sum() can't sum strings [use ''.join(seq) instead]")
  | .rejected .bytes =>
    .error (.raise "TypeError" "sum() can't sum bytes [use b''.join(seq) instead]")
  | .rejected .bytearray =>
    .error (.raise "TypeError" "sum() can't sum bytearray [use b''.join(seq) instead]")
  | .other obj => .ok (.generic obj)

/-- C's `fabs(x) >= fabs(y)` for the floats with the bits `x` and `y`: false when one of them is
a NaN. Without their sign bits, two floats that are not NaNs compare as their bits do. -/
def absGe (x y : UInt64) : Bool := !isNaN x && !isNaN y && fabs x ≥ fabs y

/-- The total of the float phase: the compensation is added only if it is non-zero and finite, so
that a negative zero keeps its sign and an infinite total doesn't become a NaN. -/
def floatTotal (total compensation : UInt64) : UInt64 :=
  if !isZero compensation && !isNaN compensation && !isInf compensation then
    fadd total compensation
  else total

/-- The total that the caller adds an item to, or that the loop ends with: an `int` or a
`float`, for which the caller makes a new object, or the total object of the generic phase. -/
inductive Total (α : Type) where
  | int (i : Int)
  | float (bits : UInt64)
  | obj (v : α)
  deriving Repr, BEq, DecidableEq

/-- What the loop does with an item. -/
inductive Step (α : Type) where
  /-- The phase takes the item; the loop goes on in this state. -/
  | next (s : State α)
  /-- The caller computes `total + item` with `+`, and calls `afterAdd` with the result. -/
  | add (total : Total α)
  deriving Repr, BEq, DecidableEq

/-- One item of the loop in the state `s`. -/
def step {α : Type} : State α → Item → Step α
  | .int total, .int b true =>
    if fitsLong b && fitsLong (total + b) then .next (.int (total + b)) else .add (.int total)
  | .int total, _ => .add (.int total)
  | .float total c, .float x =>
    let t := fadd total x
    let c := if absGe total x then fadd c (fadd (fsub total t) x)
      else fadd c (fadd (fsub x t) total)
    .next (.float t c)
  | .float total c, .int v _ =>
    -- C's `(double)value`: the nearest float, ties to even; a 64-bit value can't overflow.
    if fitsLong v then .next (.float (fadd total (roundToBits (v < 0) v.natAbs 0)) c)
    else .add (.float (floatTotal total c))
  | .float total c, .other => .add (.float (floatTotal total c))
  | .generic total, _ => .add (.obj total)

/-- The state after an add in the state `s` gave the object `r`; `bits` are `r`'s bits if its type
is `float`, and `none` otherwise. -/
def afterAdd {α : Type} (s : State α) (r : α) (bits : Option UInt64) : State α :=
  match s, bits with
  | .int _, some bits => .float bits zero
  | _, _ => .generic r

/-- The result at the end of the items. -/
def finish {α : Type} : State α → Total α
  | .int total => .int total
  | .float total c => .float (floatTotal total c)
  | .generic total => .obj total

end

end StrataPython.Dyn.Sem.Library.Sum
