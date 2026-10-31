/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.FloatText
meta import StrataDyn.FloatText

set_option autoImplicit false

/-! # Long decimal strings

`FloatText.ofDigits` and `FloatText.digitsValue` on a few inputs, with the bits that CPython 3.12
gives for the same decimal (`float(…)`). -/

namespace Strata.Dyn.FloatTextTest

open Strata.Dyn.FloatText

/-- The digits of `n`, most significant first. -/
private def digitsOf (n : Nat) : List Nat := (Nat.toDigits 10 n).map (·.toNat - '0'.toNat)

-- Leading zeros don't count as significant digits: 1000 zeros, then a 1, is 1.
#guard (ofDigits false (List.replicate 1000 0 ++ [1]) 0).toBits == 0x3FF0000000000000
-- Only zeros: zero, and minus zero with the sign.
#guard (ofDigits false [0, 0, 0] 5).toBits == 0
#guard (ofDigits true [0] 0).toBits == 0x8000000000000000
-- 2 ^ 53 + 1 is the midpoint between 2 ^ 53 and 2 ^ 53 + 2, and rounds to even.
#guard (ofDigits false (digitsOf 9007199254740993) 0).toBits == 0x4340000000000000
-- A 1 at the 917th significant digit puts the number above the midpoint.
#guard (ofDigits false (digitsOf 9007199254740993 ++ List.replicate 900 0 ++ [1]) (-901)).toBits
  == 0x4340000000000001
-- The same digits, with the 1 replaced by a 0, stay at the midpoint.
#guard (ofDigits false (digitsOf 9007199254740993 ++ List.replicate 901 0) (-901)).toBits
  == 0x4340000000000000

-- More than 16 digits take the halving path.
#guard digitsValue 2 (Array.replicate 20 1) == 1048575
#guard digitsValue 16 (Array.replicate 20 15) == 1208925819614629174706175
#guard digitsValue 10 #[] == 0

end Strata.Dyn.FloatTextTest
