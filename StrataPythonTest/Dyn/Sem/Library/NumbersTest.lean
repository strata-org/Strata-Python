/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Numbers
public import StrataPythonTest.Dyn.Sem.Library.NumberCases
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Library.Numbers
meta import StrataPythonTest.Dyn.Sem.Library.NumberCases

set_option autoImplicit false

/-!
# `int(s, base)` and `float(s)` of a `str`

`NumberCases` holds CPython 3.12's results on test strings; the readers must give the same: the
same int or float bits, or a `ValueError` with the same message.
-/

namespace StrataPython.Dyn.Sem.Library.NumbersTest

open StrataPython.Dyn.Sem
open StrataPython.Dyn.Sem.Library.Numbers

/-- Whether a result is the case's: the same value, or a `ValueError` with the same message. -/
private def same {α : Type} [BEq α] : Except Format.Failure α → Except String α → Bool
  | .ok v, .ok w => v == w
  | .error (.raise "ValueError" msg), .error m => msg == m
  | _, _ => false

private def intMismatches : List (String × Nat) :=
  NumberCases.intCases.toList.filterMap fun (s, base, r) =>
    if same (intFromStr s base) r then none else some (s, base)

private def floatMismatches : List String :=
  NumberCases.floatCases.toList.filterMap fun (s, r) =>
    if same (floatFromStr s) r then none else some s

#guard NumberCases.intCases.size == 357
#guard NumberCases.floatCases.size == 598
#guard intMismatches == []
#guard floatMismatches == []

/-! ## The limit on digits

`_Py_dg_strtod` rejects a number with more than `10 ^ 9` significant digits, or as many digits
after the point; a smaller limit shows the rule without a string of a gigabyte. -/

#guard (readDecimal "123".toList (limit := 2)).isNone
#guard readDecimal "000.12".toList (limit := 2) == some (0x3FBEB851EB851EB8, [])
#guard (readDecimal "0.000".toList (limit := 2)).isNone

end StrataPython.Dyn.Sem.Library.NumbersTest
