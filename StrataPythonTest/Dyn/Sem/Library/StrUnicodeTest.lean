/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Unicode
public import StrataPythonTest.Dyn.Sem.Library.StrCases
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Library.Unicode
meta import StrataPythonTest.Dyn.Sem.Library.StrCases

set_option autoImplicit false

/-!
# The case methods and class tests of `str`

`StrCases.cases` holds CPython 3.12's results on test strings; the functions must give the same.
-/

namespace StrataPython.Dyn.Sem.Library.StrUnicodeTest

open StrataPython.Dyn.Sem.Library.Unicode

/-- The functions' results on `s`, in the order of `StrCases.Case`. -/
private def results (s : String) : List String × List Bool :=
  ([upper s, lower s, casefold s, swapcase s, capitalize s, title s],
   [allNonEmpty isAlpha s, allNonEmpty isDecimal s, allNonEmpty isDigit s,
    allNonEmpty isNumeric s, allNonEmpty isAlnum s, allNonEmpty isSpace s, isUpperStr s,
    isLowerStr s, isTitleStr s, isIdentifierStr s, isPrintableStr s, isAsciiStr s])

/-- The strings where a function differs from CPython. -/
private def mismatches : List String :=
  StrCases.cases.toList.filterMap fun c =>
    if results c.s == (c.cases, c.tests) then none else some c.s

#guard StrCases.cases.size == 467
#guard mismatches == []

/-! ## Single characters -/

#guard toUpper 'ß' == ['S', 'S']
#guard toTitle 'ǆ' == ['ǅ']
#guard caseFold 'ß' == ['s', 's']
#guard isCased 'ʰ' && isCaseIgnorable 'ʰ'
#guard isCaseIgnorable '\'' && !isCased '\''
#guard isLineBreak '\u2028' && !isLineBreak ' '

end StrataPython.Dyn.Sem.Library.StrUnicodeTest
