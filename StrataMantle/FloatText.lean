/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# Binary64 floats as decimals

The printer and the reader agree on this pair:

* `FloatText.ofDecimal neg m e`: the binary64 value nearest `±m * 10 ^ e`, ties to even,
  overflowing to an infinity and underflowing through the subnormals to a zero;
* `FloatText.shortest f`: the decimal with the fewest significant digits that
  `ofDecimal` reads back as `f`, the nearest one if several have that many, as Python's
  `repr` chooses.  `none` for the non-finite values.

All arithmetic is on `Nat`, so the conversions are exact.
-/

namespace Strata.Mantle.FloatText

public section

/-- A finite decimal: `±mantissa * 10 ^ exponent`. -/
structure Decimal where
  neg : Bool
  mantissa : Nat
  exponent : Int
deriving Repr, BEq

/-- The number of decimal digits of `n`, at least one, if it has at most `fuel + 1`. -/
def digitsAux : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, n => if n < 10 then 1 else digitsAux fuel (n / 10) + 1

/-- The number of decimal digits of `n`, at least one. -/
def digits (n : Nat) : Nat := digitsAux n n

/-- `num / den` rounded to the nearest natural number, ties to even. -/
def roundDiv (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den || (2 * r == den && q % 2 == 1) then q + 1 else q

/-- The bits of the binary64 value nearest `m * 10 ^ e`, ties to even, sign clear. -/
def magnitudeBits (m : Nat) (e : Int) : Nat :=
  -- Bounds on the number of digits of `m`, from its bit length, so that a long mantissa
  -- costs no division per digit.
  let maxDigits : Int := m.log2 / 3 + 1
  let minDigits : Int := m.log2 * 3 / 10
  if m == 0 || maxDigits + e < -330 then 0
  else if minDigits + e > 310 then 0x7FF0000000000000
  else
    -- The value is `n / d`.
    let (n, d) : Nat × Nat := if 0 ≤ e then (m * 10 ^ e.toNat, 1) else (m, 10 ^ e.natAbs)
    -- `n / d / 2 ^ k` truncates to `[2 ^ 52, 2 ^ 53)` at the right `k`; this one is at most
    -- one too high.
    let quot (k : Int) : Nat :=
      if 0 ≤ k then n / (d * 2 ^ k.toNat) else n * 2 ^ k.natAbs / d
    let k₀ : Int := (n.log2 : Int) - d.log2 - 52
    let k := if quot k₀ < 2 ^ 52 then k₀ - 1 else k₀
    -- Below the normal range the step is fixed: a subnormal.
    let k := max k (-1074)
    let q := if 0 ≤ k then roundDiv n (d * 2 ^ k.toNat) else roundDiv (n * 2 ^ k.natAbs) d
    -- Rounding up may carry into the next binade.
    let (q, k) := if q == 2 ^ 53 then (2 ^ 52, k + 1) else (q, k)
    if q < 2 ^ 52 then q
    else
      let biased := k + 1075
      if biased ≥ 2047 then 0x7FF0000000000000
      else biased.toNat * 2 ^ 52 + (q - 2 ^ 52)

/-- The binary64 value nearest `±m * 10 ^ e`, ties to even. -/
def ofDecimal (d : Decimal) : Float :=
  let bits := magnitudeBits d.mantissa d.exponent
  Float.ofBits (if d.neg then bits + 2 ^ 63 else bits).toUInt64

/-- `n` with its trailing zeros moved into the exponent `e`. -/
def trimZeros (n : Nat) (e : Int) : Nat × Int :=
  -- A mantissa of at most 18 digits has at most 17 trailing zeros.
  (List.range 18).foldl (init := (n, e)) fun (n, e) _ =>
    if n != 0 && n % 10 == 0 then (n / 10, e + 1) else (n, e)

/-- The decimal with the fewest significant digits that reads back as `f`, the nearest if
several have that many; `none` if `f` is not finite.  Its mantissa has no trailing zeros. -/
def shortest (f : Float) : Option Decimal :=
  let bits := f.toBits.toNat
  let neg := bits >>> 63 == 1
  let biased := (bits >>> 52) % 2048
  let frac := bits % 2 ^ 52
  if biased == 2047 then none
  else if biased == 0 && frac == 0 then some ⟨neg, 0, 0⟩
  else
    -- The magnitude is `m * 2 ^ x`, that is `n / d`.
    let (m, x) : Nat × Int :=
      if biased == 0 then (frac, -1074) else (frac + 2 ^ 52, (biased : Int) - 1075)
    let (n, d) : Nat × Nat := if 0 ≤ x then (m * 2 ^ x.toNat, 1) else (m, 2 ^ x.natAbs)
    -- `p`, the decimal exponent of the leading digit: `10 ^ p ≤ n / d < 10 ^ (p + 1)`.
    let atLeast (p : Int) : Bool :=
      if 0 ≤ p then n ≥ d * 10 ^ p.toNat else n * 10 ^ p.natAbs ≥ d
    let p₀ : Int := (digits n : Int) - digits d
    let p := if atLeast p₀ then p₀ else p₀ - 1
    let p := if atLeast p then p else p - 1
    -- The `k`-digit candidates: the value rounded to `k` significant digits, then its
    -- other neighbour, which may be the only one that reads back next to a power of two.
    let candidates (k : Nat) : List (Nat × Int) :=
      let s : Int := (k : Int) - 1 - p
      let (num, den) := if 0 ≤ s then (n * 10 ^ s.toNat, d) else (n, d * 10 ^ s.natAbs)
      let q := roundDiv num den
      let other := if q == num / den then q + 1 else num / den
      [(q, -s), (other, -s)]
    let reads (c : Nat × Int) : Bool := magnitudeBits c.1 c.2 == bits % 2 ^ 63
    -- Seventeen significant digits always suffice.
    let (q, e) := ((List.range 17).flatMap (candidates ∘ (· + 1))).find? reads
      |>.getD ((candidates 17).headD (0, 0))
    let (q, e) := trimZeros q e
    some ⟨neg, q, e⟩

end

end Strata.Mantle.FloatText
