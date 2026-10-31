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

For long decimal strings, `FloatText.ofDigits neg ds e` gives `ofDecimal` of the number with the
decimal digits `ds` times `10 ^ e`, at a cost linear in the length of `ds`.

All arithmetic is on `Nat`, so the conversions are exact.
-/

namespace Strata.Dyn.FloatText

-- Exposed, so that `#dyn_sem_table`'s check of the axioms that a rule reaches can see these
-- definitions.
@[expose] public section

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

/-! ## Long decimal strings -/

/-- The value of the digits `ds` in base `base`, most significant first, computed by halves, so
that a long string costs a few multiplications of large numbers, not one per digit. -/
def digitsValue (base : Nat) (ds : Array Nat) : Nat := go 0 ds.size
where
  go (lo hi : Nat) : Nat :=
    if _h : hi - lo ≤ 16 then
      (List.range (hi - lo)).foldl (fun acc i => acc * base + ds.getD (lo + i) 0) 0
    else
      let mid := lo + (hi - lo) / 2
      go lo mid * base ^ (hi - mid) + go mid hi
  termination_by hi - lo
  decreasing_by all_goals omega

/-- How many significant digits `ofDigits` reads exactly. A midpoint between two adjacent
binary64 values has at most 768 significant digits (`(2 ^ 54 - 1) * 5 ^ 1075` has 768). Let `T` be
the first 800 significant digits of a number, and `u` the unit of its 800th digit. Only a midpoint
strictly between `T` and `T + u` could change the rounding, and such a midpoint has its leading
digit where `T` has it, so its at most 768 significant digits end above the 800th, and it is a
multiple of `u`. So no midpoint lies strictly between `T` and `T + u`, and the number rounds as `T` if its other digits are all zero,
and otherwise as `T` followed by a digit 1. This argument is not proved: no theorem states that
`ofDigits` gives the nearest binary64 value. -/
def keptDigits : Nat := 800

/-- The binary64 value nearest `±n * 10 ^ e`, ties to even, where `n` has the decimal digits `ds`
(most significant first, leading zeros allowed). It drops the digits after the first
`keptDigits` significant ones, adds one digit 1 if any dropped digit is not zero, and calls
`ofDecimal`. The cost is linear in the length of `ds`, plus that of `ofDecimal` on at most 801
digits. -/
def ofDigits (neg : Bool) (ds : List Nat) (e : Int) : Float :=
  let sig := ds.dropWhile (· == 0)
  let kept := sig.take keptDigits
  let extra := sig.length - kept.length
  let sticky := (sig.drop keptDigits).any (· != 0)
  let mantissa := digitsValue 10 (kept ++ if sticky then [1] else []).toArray
  ofDecimal ⟨neg, mantissa, e + extra - (if sticky then 1 else 0)⟩

end

end Strata.Dyn.FloatText
