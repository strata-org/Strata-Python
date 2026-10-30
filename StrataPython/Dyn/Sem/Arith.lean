/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Format

set_option autoImplicit false

/-!
# Arithmetic on ints, bools and floats

CPython 3.12's arithmetic operators, comparisons and conversions on `int`, `bool` and `float`
(`Objects/longobject.c`, `Objects/boolobject.c` and `Objects/floatobject.c`), and the indices of
a slice (`Objects/sliceobject.c`).  Each function gives CPython's result, or the exception that
CPython raises, or says that the case is not modelled.

A float is given by its IEEE 754 bits.  `+`, `-`, `*` and `/` of floats that are not NaNs are
Lean's `Float` operations, which round to nearest, ties to even, as C's do.  `**` of floats
handles CPython's special cases first, as `float_pow` does, and then calls the C library's `pow`
through `Float.pow`, as CPython does; so its result is the platform's (the tests pin glibc 2.34's
on x86-64).  The rest is exact
arithmetic on the parts of the floats: `fmod`, `floor`, the comparisons, the conversions, and int
true division, which CPython rounds correctly.

A NaN result has the bits of `ieeeOp`: an operation keeps the payload of a NaN operand, and an
invalid operation gives a NaN with the sign bit set, as x86-64 does.  CPython itself doesn't fix
these bits: ARM gives an invalid operation's NaN without the sign bit, `nan1 + nan2` gives the
first NaN once the interpreter specializes the addition, and the compiled `nan * -1` flips the
sign.  So no rule may depend on a NaN's sign or payload.  `repr`, `str`, `format` and `hash`
ignore them, and the built-ins that expose them (`math.copysign`, `struct.pack`, …) stop with a gap
on a NaN.

These results are not modelled:
* an int result that may have more than `2 ^ 32` bits, from `**` or `<<`, for which CPython raises
  `MemoryError` if the machine doesn't have the memory;
* `~` on a bool, whose `DeprecationWarning` CPython records in the module's `__warningregistry__`;
* the `OverflowError` of a float power, which has two arguments (an errno and a message);
* a negative float to a power that is not an integer, for which CPython computes a complex number,
  or raises `OverflowError` ("complex exponentiation") when that overflows.
-/

namespace StrataPython.Dyn.Sem.Arith

open StrataPython.Dyn.Sem.Format

@[expose] public section

/-- A `ZeroDivisionError` with the message `msg`. -/
def zeroDivision (msg : String) : Failure := .raise "ZeroDivisionError" msg

/-- An `OverflowError` with the message `msg`. -/
def overflow (msg : String) : Failure := .raise "OverflowError" msg

/-! ## Binary64 values by their bits -/

/-- The sign bit of a binary64 value. -/
def signBit : UInt64 := 0x8000000000000000

/-- The bits of `0.0`. -/
def zero : UInt64 := 0

/-- The bits of `1.0`. -/
def one : UInt64 := 0x3FF0000000000000

/-- The bits of `-1.0`. -/
def negOne : UInt64 := 0xBFF0000000000000

/-- The bits of `2.0`. -/
def two : UInt64 := 0x4000000000000000

/-- The bits of `0.5`. -/
def half : UInt64 := 0x3FE0000000000000

/-- Whether `x` is the bits of a NaN. -/
def isNaN (x : UInt64) : Bool := x &&& ~~~signBit > 0x7FF0000000000000

/-- Whether `x` is the bits of an infinity. -/
def isInf (x : UInt64) : Bool := x &&& ~~~signBit == 0x7FF0000000000000

/-- Whether `x` is the bits of `0.0` or `-0.0`. -/
def isZero (x : UInt64) : Bool := x &&& ~~~signBit == 0

/-- C's `x < 0` for the float with the bits `x`: false for a zero and a NaN. -/
def isNeg (x : UInt64) : Bool := x &&& signBit != 0 && !isNaN x && !isZero x

/-- C's `x > 0` for the float with the bits `x`: false for a zero and a NaN. -/
def isPos (x : UInt64) : Bool := x &&& signBit == 0 && !isNaN x && !isZero x

/-- C's `-x`: `x` with its sign bit flipped, a NaN too. -/
def fneg (x : UInt64) : UInt64 := x ^^^ signBit

/-- C's `fabs(x)`: `x` with its sign bit cleared. -/
def fabs (x : UInt64) : UInt64 := x &&& ~~~signBit

/-- C's `copysign(x, y)`: `x` with the sign bit of `y`. -/
def copysign (x y : UInt64) : UInt64 := fabs x ||| (y &&& signBit)

/-- The bit that makes a NaN quiet. -/
def quietBit : UInt64 := 0x0008000000000000

/-- The NaN of an invalid operation without a NaN operand, such as `inf - inf`, on x86-64: its
sign bit is set.  (ARM's has it clear.) -/
def defaultNaN : UInt64 := 0xFFF8000000000000

/-- The result of the binary64 operation `op` on `x` and `y`, as x86-64 computes it.  A NaN
operand gives itself, quieted; with two NaN operands, `x` if `firstWins` and `y` otherwise.  Then
`op` computes the result, rounded to nearest, ties to even, and an invalid operation gives
`defaultNaN`.  No NaN goes into or comes out of `Float`, so the kernel's model of `Float`, which has
a single NaN, and the compiled code give the same bits. -/
def ieeeOp (op : Float → Float → Float) (firstWins : Bool) (x y : UInt64) : UInt64 :=
  if isNaN x && (firstWins || !isNaN y) then x ||| quietBit
  else if isNaN y then y ||| quietBit
  else
    let r := (op (Float.ofBits x) (Float.ofBits y)).toBits
    if isNaN r then defaultNaN else r

/-- `x + y` in binary64, as CPython's `float_add` computes it on x86-64: of two NaN operands, the
second one wins.  (CPython's interpreter gives the first one once it specializes the addition of
two floats, so the NaN of `nan1 + nan2` can change while a program runs.) -/
def fadd (x y : UInt64) : UInt64 := ieeeOp (· + ·) false x y

/-- `x - y` in binary64; of two NaN operands, the first one wins. -/
def fsub (x y : UInt64) : UInt64 := ieeeOp (· - ·) true x y

/-- `x * y` in binary64; of two NaN operands, the first one wins. -/
def fmul (x y : UInt64) : UInt64 := ieeeOp (· * ·) true x y

/-- `x / y` in binary64; of two NaN operands, the first one wins. -/
def fdiv (x y : UInt64) : UInt64 := ieeeOp (· / ·) true x y

/-! ## Exact values and comparisons -/

/-- A number as an exact value. -/
inductive Exact where
  /-- A NaN. -/
  | nan
  /-- An infinity, negative if `neg`. -/
  | inf (neg : Bool)
  /-- The finite value `m * 2 ^ e`. -/
  | finite (m : Int) (e : Int)

/-- The exact value of the float with the bits `x`. -/
def Exact.ofBits (x : UInt64) : Exact :=
  match parts x with
  | .nan => .nan
  | .inf neg => .inf neg
  | .finite neg m e => .finite (if neg then -(m : Int) else m) e

/-- How the exact value `a` compares with `b`: `none` when one of them is a NaN.  Two infinities
of the same sign are equal. -/
def Exact.compare : Exact → Exact → Option Ordering
  | .nan, _ => none
  | _, .nan => none
  | .inf a, .inf b => some (if a == b then .eq else if a then .lt else .gt)
  | .inf neg, .finite _ _ => some (if neg then .lt else .gt)
  | .finite _ _, .inf neg => some (if neg then .gt else .lt)
  | .finite m e, .finite n f =>
    let k := min e f
    some (Ord.compare (m * 2 ^ (e - k).toNat) (n * 2 ^ (f - k).toNat))

/-- C's `x < y` for the floats with the bits `x` and `y`: false when one of them is a NaN. -/
def flt (x y : UInt64) : Bool := (Exact.ofBits x).compare (Exact.ofBits y) == some .lt

/-! ## C library functions that are exact -/

/-- The NaN of an invalid `fmod(x, y)`, as the C library makes it: `x * y / (x * y)`.  It keeps
the payload of a NaN operand. -/
def invalidNaN (x y : UInt64) : UInt64 := fdiv (fmul x y) (fmul x y)

/-- C's `fmod(x, y)` for the floats with the bits `x` and `y`: `x - n * y`, where `n` is `x / y`
rounded toward zero.  The result is exact and has the sign of `x`.  It is `x` for a finite `x` and
an infinite `y`, and a NaN for an infinite `x`, a zero `y` or a NaN operand. -/
def fmod (x y : UInt64) : UInt64 :=
  match parts x, parts y with
  | .finite xneg xm xe, .finite _ ym ye =>
    if ym == 0 then invalidNaN x y
    else
      let e := min xe ye
      roundToBits xneg ((xm * 2 ^ (xe - e).toNat) % (ym * 2 ^ (ye - e).toNat)) e
  | .finite .., .inf _ => x
  | _, _ => invalidNaN x y

/-- C's `floor(x)` for the float with the bits `x`: the largest integer not above `x`, which is
exact.  An infinity, a NaN, a zero and an integer stay as they are. -/
def floor (x : UInt64) : UInt64 :=
  match parts x with
  | .finite neg m e =>
    if 0 ≤ e then x
    else
      -- `q` is `|x|` rounded toward zero.
      let q := m / 2 ^ e.natAbs
      if !neg then roundToBits false q 0
      else if q * 2 ^ e.natAbs == m then x
      else roundToBits true (q + 1) 0
  | _ => x

/-- Whether the float with the bits `x` is finite and an integer. -/
def isInteger (x : UInt64) : Bool :=
  match parts x with
  | .finite _ m e => 0 ≤ e || m % 2 ^ e.natAbs == 0
  | _ => false

/-- CPython's `DOUBLE_IS_ODD_INTEGER(x)`, `fmod(fabs(x), 2.0) == 1.0`: whether the float with the
bits `x` is an odd integer. -/
def isOddInteger (x : UInt64) : Bool := fmod (fabs x) two == one

/-! ## Ints -/

/-- CPython's `PY_SSIZE_T_MIN` on a 64-bit build. -/
def ssizeMin : Int := -(ssizeMax : Int) - 1

/-- The most bits of an int result of `**` or `<<` that this port builds. -/
def maxBits : Nat := 2 ^ 32

/-- The result of a `**` or a `<<` whose int would have more than `maxBits` bits. -/
def tooLarge : Failure := .notModelled "an int with more than 2 ^ 32 bits"

/-- CPython's `MAX_LONG_DIGITS`: the most 30-bit digits of an int, beyond which `_PyLong_New`
raises `OverflowError`.  The header of an int is 24 bytes and a digit 4. -/
def maxLongDigits : Nat := (ssizeMax - 24) / 4

/-- The number of 30-bit digits of `n`, which CPython keeps for an int of magnitude `n`. -/
def digitCount (n : Nat) : Nat := if n == 0 then 0 else n.log2 / 30 + 1

/-- The binary64 value nearest `p / q` (for a positive `q`), ties to even, negative if `neg`; an
infinity if it rounds to `2 ^ 1024` or more.  A huge or a tiny quotient is decided from the bit
lengths first, as CPython does, so that no large power is computed. -/
def roundQuotient (neg : Bool) (p q : Nat) : UInt64 :=
  let sign : UInt64 := if neg then signBit else zero
  if p.log2 > q.log2 + 1025 then sign ||| 0x7FF0000000000000
  else if p == 0 || p.log2 + 1076 < q.log2 then sign
  else
  -- `k` makes the quotient `r` of `p * 2 ^ k` by `q` at least `2 ^ 54`, so that its last two bits
  -- are below the last bit that the result keeps.  The remainder becomes a sticky bit below them.
  let k := q.log2 + 55 - p.log2
  let n := p * 2 ^ k
  let r := n / q
  roundToBits neg (2 * r + (if n % q == 0 then 0 else 1)) (-(k : Int) - 1)

/-- `a / b` for ints (`long_true_divide`): the binary64 value nearest the exact quotient, ties to
even, with the sign of `a * b`, so `0 / -1` is `-0.0`. -/
def intTrueDiv (a b : Int) : Except Failure UInt64 :=
  if b == 0 then .error (zeroDivision "division by zero")
  else
    let bits := roundQuotient (decide (a < 0) != decide (b < 0)) a.natAbs b.natAbs
    if isInf bits then .error (overflow "integer division result too large for a float")
    else .ok bits

/-- `a // b` for ints: the floor of `a / b`. -/
def intFloorDiv (a b : Int) : Except Failure Int :=
  if b == 0 then .error (zeroDivision "integer division or modulo by zero") else .ok (a.fdiv b)

/-- `a % b` for ints: `a - b * (a // b)`, with the sign of `b`. -/
def intMod (a b : Int) : Except Failure Int :=
  if b == 0 then .error (zeroDivision "integer modulo by zero") else .ok (a.fmod b)

/-- `divmod(a, b)` for ints: `(a // b, a % b)`. -/
def intDivmod (a b : Int) : Except Failure (Int × Int) :=
  if b == 0 then .error (zeroDivision "integer division or modulo by zero")
  else .ok (a.fdiv b, a.fmod b)

/-- `a << b` for ints (`long_lshift`): `a * 2 ^ b`.  A negative `b` is a `ValueError`, even when
`a` is `0`.  For a nonzero `a`, CPython first counts the 30-bit digits of the result, from `b` as
`divmod_shift` splits it; a huge `b` is clipped there.  When the count is over `maxLongDigits`,
CPython raises `OverflowError`.  A result with more than `maxBits` bits is not modelled. -/
def intLshift (a b : Int) : Except Failure Int :=
  if b < 0 then .error (valueError "negative shift count")
  else if a == 0 then .ok 0
  else
    let n := b.toNat
    let (wordShift, remShift) :=
      if n / 30 < ssizeMax / 4 then (n / 30, n % 30) else (ssizeMax / 4, 0)
    let newSize := digitCount a.natAbs + wordShift + (if remShift == 0 then 0 else 1)
    if newSize > maxLongDigits then .error (overflow "too many digits in integer")
    else if a.natAbs.log2 + 1 + n > maxBits then .error tooLarge
    else .ok (a <<< n)

/-- `a >> b` for ints: the floor of `a / 2 ^ b`, so `0` or `-1` for a huge `b`.  A negative `b` is a
`ValueError`. -/
def intRshift (a b : Int) : Except Failure Int :=
  if b < 0 then .error (valueError "negative shift count") else .ok (a >>> b.toNat)

/-- `a & b` for ints, as two's complement with infinitely many sign bits.  A negative int
`-[n+1]` is `~n`. -/
def intAnd : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .ofNat m, .negSucc n => .ofNat (m ^^^ (m &&& n))
  | .negSucc m, .ofNat n => .ofNat (n ^^^ (n &&& m))
  | .negSucc m, .negSucc n => .negSucc (m ||| n)

/-- `a | b` for ints, as two's complement with infinitely many sign bits. -/
def intOr : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ||| n)
  | .ofNat m, .negSucc n => .negSucc (n ^^^ (n &&& m))
  | .negSucc m, .ofNat n => .negSucc (m ^^^ (m &&& n))
  | .negSucc m, .negSucc n => .negSucc (m &&& n)

/-- `a ^ b` for ints, as two's complement with infinitely many sign bits. -/
def intXor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ^^^ n)
  | .ofNat m, .negSucc n => .negSucc (m ^^^ n)
  | .negSucc m, .ofNat n => .negSucc (m ^^^ n)
  | .negSucc m, .negSucc n => .ofNat (m ^^^ n)

/-! ## Floats -/

/-- `v / w` for floats (`float_div`). -/
def floatTrueDiv (v w : UInt64) : Except Failure UInt64 :=
  if isZero w then .error (zeroDivision "float division by zero") else .ok (fdiv v w)

/-- `v % w` for floats (`float_rem`): `fmod(v, w)`, plus `w` when the signs of `fmod(v, w)` and
`w` differ.  A zero remainder takes the sign of `w`. -/
def floatMod (v w : UInt64) : Except Failure UInt64 :=
  if isZero w then .error (zeroDivision "float modulo")
  else
    let m := fmod v w
    if isZero m then .ok (copysign zero w)
    else if isNeg w != isNeg m then .ok (fadd m w)
    else .ok m

/-- CPython's `_float_div_mod` for a nonzero `w`: `(v // w, v % w)`.  The quotient is
`(v - fmod(v, w)) / w`, minus one when `fmod(v, w)` is not zero and its sign differs from the sign
of `w`, then snapped to the nearest integer; a zero quotient takes the sign of `v / w`. -/
def floatDivMod (v w : UInt64) : UInt64 × UInt64 :=
  let m := fmod v w
  let d := fdiv (fsub v m) w
  let (m, d) :=
    if isZero m then (copysign zero w, d)
    else if isNeg w != isNeg m then (fadd m w, fsub d one)
    else (m, d)
  let q :=
    if isZero d then copysign zero (fdiv v w)
    else
      let f := floor d
      if flt half (fsub d f) then fadd f one else f
  (q, m)

/-- `v // w` for floats (`float_floor_div`). -/
def floatFloorDiv (v w : UInt64) : Except Failure UInt64 :=
  if isZero w then .error (zeroDivision "float floor division by zero")
  else .ok (floatDivMod v w).1

/-- `divmod(v, w)` for floats (`float_divmod`). -/
def floatDivmod (v w : UInt64) : Except Failure (UInt64 × UInt64) :=
  if isZero w then .error (zeroDivision "float divmod()") else .ok (floatDivMod v w)

/-- `v ** w` for floats (`float_pow`).  CPython's special cases come first, in this order:
* `v ** 0` is `1.0`, even for a NaN `v`;
* a NaN stays, but `1.0 ** nan` is `1.0`;
* `w = inf` gives `0.0`, `1.0` or `inf`, by whether `|v|` is below `1`, `1` or above it, and
  `w = -inf` gives `inf`, `1.0` or `0.0`;
* an infinite `v` gives `inf` for a positive `w` and `0.0` for a negative one, with the sign of
  `v` for an odd integer `w`;
* a zero `v` gives `0.0`, with the sign of `v` for an odd integer `w`, and a negative `w` is a
  `ZeroDivisionError`;
* a negative `v` with an integer `w` gives `|v| ** w`, negated for an odd `w`.  With any other `w`,
  CPython computes a complex number, which is not modelled.

Then the C library's `pow` computes the power of a positive `v` other than `1.0`.  An infinite
result is CPython's `OverflowError` for `ERANGE`. -/
def floatPow (v w : UInt64) : Except Failure UInt64 :=
  if isZero w then .ok one
  else if isNaN v then .ok v
  else if isNaN w then .ok (if v == one then one else w)
  else if isInf w then
    let av := fabs v
    if av == one then .ok one
    else if isPos w == flt one av then .ok (fabs w)
    else .ok zero
  else if isInf v then
    if isPos w then .ok (if isOddInteger w then v else fabs v)
    else .ok (if isOddInteger w then copysign zero v else zero)
  else if isZero v then
    if isNeg w then .error (zeroDivision "0.0 cannot be raised to a negative power")
    else .ok (if isOddInteger w then v else zero)
  else if isNeg v && !isInteger w then .error (.notModelled "a complex power")
  else
    let negate := isNeg v && isOddInteger w
    let av := fabs v
    if av == one then .ok (if negate then negOne else one)
    else
      let r := (Float.pow (Float.ofBits av) (Float.ofBits w)).toBits
      -- CPython raises `OverflowError(34, 'Numerical result out of range')`, an exception with
      -- two arguments, which a `Failure` can't carry.
      if isInf r then .error (.notModelled "the OverflowError of a float power, which has an errno")
      else .ok (if negate then fneg r else r)

/-! ## Numbers -/

/-- A number: a `bool`, an `int` or a `float`. -/
inductive Num where
  /-- A `bool`. -/
  | bool (b : Bool)
  /-- An `int`. -/
  | int (i : Int)
  /-- A `float`, by its IEEE 754 bits. -/
  | float (bits : UInt64)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The value of a `bool` or an `int` as an int; `none` for a `float`. -/
def Num.toInt? : Num → Option Int
  | .bool b => some (if b then 1 else 0)
  | .int i => some i
  | .float _ => none

/-- `float(x)` for the number `x`: a float as it is, and an int or a bool converted as
`PyLong_AsDouble` does, with its `OverflowError`. -/
def Num.toFloat : Num → Except Failure UInt64
  | .bool b => .ok (if b then one else zero)
  | .int i => intToFloat i
  | .float bits => .ok bits

/-- The exact value of the number `x`. -/
def Num.exact : Num → Exact
  | .bool b => .finite (if b then 1 else 0) 0
  | .int i => .finite i 0
  | .float bits => Exact.ofBits bits

/-- `int(x)` for the float with the bits `x` (`PyLong_FromDouble`): `x` rounded toward zero. -/
def floatToInt (x : UInt64) : Except Failure Int :=
  match parts x with
  | .nan => .error (valueError "cannot convert float NaN to integer")
  | .inf _ => .error (overflow "cannot convert float infinity to integer")
  | .finite neg m e =>
    let n : Nat := if 0 ≤ e then m * 2 ^ e.toNat else m / 2 ^ e.natAbs
    .ok (if neg then -(n : Int) else n)

/-! ## Operators -/

/-- `a ** e` for ints, with `e` not negative.  A power whose result may have more than `maxBits`
bits is not modelled: one with `(log2 |a| + 1) * e > maxBits`. -/
def intPowNat (a : Int) (e : Nat) : Except Failure Int :=
  if a.natAbs ≤ 1 then
    -- `0`, `1` and `-1` have small powers, whatever the exponent.
    .ok (if e == 0 then 1 else if e % 2 == 0 then a * a else a)
  else if (a.natAbs.log2 + 1) * e > maxBits then .error tooLarge
  else .ok (a ^ e)

/-- `a ** b` for ints (`long_pow`): an int for a `b` that is not negative, otherwise `float(a) **
float(b)` as a float, with the `OverflowError` of either conversion. -/
def intPow (a b : Int) : Except Failure Num :=
  if b < 0 then do .float <$> floatPow (← intToFloat a) (← intToFloat b)
  else .int <$> intPowNat a b.toNat

/-- The binary operators on numbers. -/
inductive BinOp where
  /-- `+` -/
  | add
  /-- `-` -/
  | sub
  /-- `*` -/
  | mul
  /-- `/` -/
  | trueDiv
  /-- `//` -/
  | floorDiv
  /-- `%` -/
  | mod
  /-- `**` -/
  | pow
  /-- `<<` -/
  | lshift
  /-- `>>` -/
  | rshift
  /-- `&` -/
  | and
  /-- `|` -/
  | or
  /-- `^` -/
  | xor
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `a op b` for the ints `a` and `b` (the slots of `int`). -/
def intBinary (op : BinOp) (a b : Int) : Except Failure Num :=
  match op with
  | .add => .ok (.int (a + b))
  | .sub => .ok (.int (a - b))
  | .mul => .ok (.int (a * b))
  | .trueDiv => .float <$> intTrueDiv a b
  | .floorDiv => .int <$> intFloorDiv a b
  | .mod => .int <$> intMod a b
  | .pow => intPow a b
  | .lshift => .int <$> intLshift a b
  | .rshift => .int <$> intRshift a b
  | .and => .ok (.int (intAnd a b))
  | .or => .ok (.int (intOr a b))
  | .xor => .ok (.int (intXor a b))

/-- The slot of `float` for `op` (`float_add` and the others), if `float` has one: it has none for
`<<`, `>>`, `&`, `|` and `^`. -/
def floatBinary : BinOp → Option (UInt64 → UInt64 → Except Failure UInt64)
  | .add => some fun v w => .ok (fadd v w)
  | .sub => some fun v w => .ok (fsub v w)
  | .mul => some fun v w => .ok (fmul v w)
  | .trueDiv => some floatTrueDiv
  | .floorDiv => some floatFloorDiv
  | .mod => some floatMod
  | .pow => some floatPow
  | _ => none

/-- `a op b` for the numbers `a` and `b`, as the slots of `int`, `bool` and `float` give it:
* `&`, `|` and `^` of two bools give a bool;
* two ints or bools give what `int` gives;
* with a float operand, both operands convert to floats, the first one first, and `float` gives
  the result.

The result is `none` when no slot implements `op` for the operands: for a float operand of `<<`,
`>>`, `&`, `|` or `^`.  CPython then raises `TypeError` ("unsupported operand type(s)"), without
converting anything. -/
def binary (op : BinOp) (a b : Num) : Option (Except Failure Num) :=
  match op, a, b with
  | .and, .bool x, .bool y => some (.ok (.bool (x && y)))
  | .or, .bool x, .bool y => some (.ok (.bool (x || y)))
  | .xor, .bool x, .bool y => some (.ok (.bool (x != y)))
  | _, _, _ =>
    match a.toInt?, b.toInt? with
    | some x, some y => some (intBinary op x y)
    | _, _ => (floatBinary op).map fun f => do .float <$> f (← a.toFloat) (← b.toFloat)

/-- `divmod(a, b)` for the numbers `a` and `b`: two ints for two ints or bools, otherwise two
floats, after converting both operands to floats. -/
def divmod (a b : Num) : Except Failure (Num × Num) :=
  match a.toInt?, b.toInt? with
  | some x, some y => (fun (q, r) => (Num.int q, Num.int r)) <$> intDivmod x y
  | _, _ => do
    let (q, r) ← floatDivmod (← a.toFloat) (← b.toFloat)
    pure (.float q, .float r)

/-- The unary operators on numbers, and `abs`. -/
inductive UnaryOp where
  /-- `-` -/
  | neg
  /-- `+` -/
  | pos
  /-- `~` -/
  | invert
  /-- `abs()` -/
  | abs
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `op i` for the int `i`; `~i` is `-(i + 1)`. -/
def intUnary (op : UnaryOp) (i : Int) : Int :=
  match op with
  | .neg => -i
  | .pos => i
  | .invert => ~~~i
  | .abs => i.natAbs

/-- `op a` for the number `a`.  A bool acts as its int and gives an int: `-True` is `-1`.  `~` on
a bool is not modelled: CPython 3.12 gives `-2` for `~True`, but also issues a
`DeprecationWarning`, which records the warning in the module's `__warningregistry__` even when
the warning is ignored.  `-` flips the sign bit of a float, a NaN's too, and `abs` clears it.
`none` for `~` on a float, for which CPython raises `TypeError`. -/
def unary (op : UnaryOp) (a : Num) : Option (Except Failure Num) :=
  match a with
  | .float x =>
    match op with
    | .neg => some (.ok (.float (fneg x)))
    | .pos => some (.ok (.float x))
    | .abs => some (.ok (.float (fabs x)))
    | .invert => none
  | .bool b =>
    if op == .invert then some (.error (.notModelled "~ on a bool, which warns"))
    else some (.ok (.int (intUnary op (if b then 1 else 0))))
  | .int i => some (.ok (.int (intUnary op i)))

/-! ## Comparisons -/

/-- The comparison operators. -/
inductive CmpOp where
  /-- `==` -/
  | eq
  /-- `!=` -/
  | ne
  /-- `<` -/
  | lt
  /-- `<=` -/
  | le
  /-- `>` -/
  | gt
  /-- `>=` -/
  | ge
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether the comparison `op` holds for the outcome `o` of comparing two numbers: with a NaN
(`none`), only `!=` holds. -/
def CmpOp.holds (op : CmpOp) (o : Option Ordering) : Bool :=
  match op with
  | .eq => o == some .eq
  | .ne => o != some .eq
  | .lt => o == some .lt
  | .le => o == some .lt || o == some .eq
  | .gt => o == some .gt
  | .ge => o == some .gt || o == some .eq

/-- `a op b` for the numbers `a` and `b` (`long_richcompare` and `float_richcompare`): exact,
even between a huge int and a float.  A NaN is unequal to everything, itself included, and
unordered; the infinities are beyond every int; `-0.0` equals `0`. -/
def compare (op : CmpOp) (a b : Num) : Bool := op.holds (a.exact.compare b.exact)

/-! ## Slice indices -/

/-- The indices of a slice of a sequence, as CPython uses them. -/
structure SliceIndices where
  /-- The first index. -/
  start : Int
  /-- The index where the slice stops. -/
  stop : Int
  /-- The step. -/
  step : Int
  /-- The number of items in the slice. -/
  length : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The int `x` as `PyNumber_AsSsize_t(x, NULL)` gives it: clamped to `[PY_SSIZE_T_MIN,
PY_SSIZE_T_MAX]`. -/
def clampSsize (x : Int) : Int := max ssizeMin (min x ssizeMax)

/-- The indices of the slice `start:stop:step` of a sequence of `length` items (`PySlice_Unpack`,
then `PySlice_AdjustIndices`).  `none` stands for a missing bound, and `length` is at most
`PY_SSIZE_T_MAX`.
* Each bound is clamped to a C `Py_ssize_t`.
* A zero step is a `ValueError`, whatever the other bounds are.  A step of `PY_SSIZE_T_MIN`
  becomes `-PY_SSIZE_T_MAX`.
* A missing start is the first item for a positive step and the last one for a negative step; a
  missing stop is past the other end.
* A negative index counts from the end.
* An index is then clamped to the sequence.  Below it, it becomes `-1` for a negative step and `0`
  otherwise; above it, `length - 1` for a negative step and `length` otherwise.

The bounds come already converted to ints.  CPython converts the step first and raises on a zero
step before it converts the start and the stop, so `[1, 2, 3][None:'a':0]` raises `ValueError`, not
`TypeError`; a caller that converts the bounds must check the step in the same place. -/
def sliceIndices (start stop step : Option Int) (length : Nat) : Except Failure SliceIndices := do
  let step ← match step with
    | none => pure 1
    | some s =>
      let s := clampSsize s
      if s == 0 then throw (valueError "slice step cannot be zero")
      pure (max s (-(ssizeMax : Int)))
  let start := match start with
    | none => if step < 0 then (ssizeMax : Int) else 0
    | some i => clampSsize i
  let stop := match stop with
    | none => if step < 0 then ssizeMin else (ssizeMax : Int)
    | some i => clampSsize i
  let len : Int := length
  let adjust (i : Int) : Int :=
    if i < 0 then (if i + len < 0 then (if step < 0 then -1 else 0) else i + len)
    else if i ≥ len then (if step < 0 then len - 1 else len)
    else i
  let start := adjust start
  let stop := adjust stop
  let count : Int :=
    if step < 0 then (if stop < start then (start - stop - 1) / (-step) + 1 else 0)
    else (if start < stop then (stop - start - 1) / step + 1 else 0)
  pure { start, stop, step, length := count.toNat }

end

end StrataPython.Dyn.Sem.Arith
