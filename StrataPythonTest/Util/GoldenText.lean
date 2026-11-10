/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! # Shared text helpers for the golden suites

Small string utilities used by both the interpret goldens
(`StrataPythonTest.InterpretGolden.Matching`) and the analyze goldens
(`StrataPythonTest.AnalyzeGolden.Matching`), and by their write sides. Defined once
here so the two suites cannot drift on how they trim or substring-match output. -/

namespace StrataPython.GoldenText

/-- `s` contains `sub` as a substring. -/
public def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Drop trailing carriage returns and newlines, as command substitution
    (`pattern=$(cat …)`) does to a file's contents. -/
public def rstripNewlines (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r')).reverse

end StrataPython.GoldenText
