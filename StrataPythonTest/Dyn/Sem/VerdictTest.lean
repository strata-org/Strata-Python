/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPythonTest.Util.SemDiff
meta import StrataPython.Dyn.Sem.Invariant

/-! # The verdict of one program against CPython

`SemDiff.judge` on small traces, one per verdict and per failure.
-/

namespace StrataPython.SemDiff.VerdictTest

open StrataPython.SemDiff Strata.Dyn.Exec.Diff

/-- The verdict's text, or the failure's first line. -/
meta def verdictText (r : Except String Verdict) : String :=
  match r with
  | .ok v => (Entry.mk "p" v).render
  | .error m => s!"fails: {(m.splitOn "\n").head!}"

/-- A trace whose output is `out`. -/
meta def tr (out rest : String) : String := traceOf out rest

/-- CPython's trace: the output `a`, then `b`, each on its line. -/
meta def cpy : String := tr "a\nb\n" "--- outcome\nok\n--- globals\nx = 1\n"

/-- info: p | agree -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace cpy) cpy none))

-- A gap after the same output, or after a beginning of it.
/-- info: p | gap | g -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace (tr "a\n" "--- gap g\n")) cpy none))

/-- info: p | gap | g -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace (tr "a\nb" "--- gap g\n")) cpy none))

-- A model-invariant gap (`PyM.failure`) as a run's first gap fails the test, whatever the verdict
-- file says: it is a bug in the model, never an allowed gap.
/-- info: fails: p: the run breaks a model invariant: model invariant: x -/
#guard_msgs in
#eval IO.println (verdictText
  (judge "p" (.trace (tr "a\n" ("--- gap " ++ StrataPython.Dyn.Sem.modelInvariantPrefix ++ "x\n")))
    cpy (some ⟨"r", none⟩)))

-- A trace without its output section fails the test, even for a program with a known difference.
/-- info: fails: p: the run's trace has no output section -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace "--- outcome\nok\n") cpy (some ⟨"r", none⟩)))

-- A fault other than a gap fails the test too, even for a program with a known difference.
/-- info: fails: p: the run ends with a fault: --- fault Strata.Dyn.Exec.Fault.badCell 3 -/
#guard_msgs in
#eval IO.println (verdictText
  (judge "p" (.trace (tr "a\n" "--- fault Strata.Dyn.Exec.Fault.badCell 3\n")) cpy (some ⟨"r", none⟩)))

-- A wrong output before the gap fails, and so does a wrong last line: `a` with its newline is no
-- beginning of `ab`.
/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace (tr "z\n" "--- gap g\n")) cpy none))

/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\n" "--- gap g\n")) (tr "ab\n" "--- outcome\nok\n") none))

-- A gap in place of the globals, after the same output and outcome; a different outcome before
-- it fails, and so does a shorter output.
/-- info: p | gap | g -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\nb\n" "--- outcome\nok\n--- gap g\n")) cpy none))

/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\nb\n" "--- outcome\nraised E: x\n--- gap g\n")) cpy none))

/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\n" "--- outcome\nok\n--- gap g\n")) cpy none))

-- A gap in place of the outcome comes after the outcome's header, so the output must be whole.
/-- info: p | gap | g -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\nb\n" "--- outcome\n--- gap g\n")) cpy none))

/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\n" "--- outcome\n--- gap g\n")) cpy none))

-- A gap in the outcome after its exception's type: CPython's outcome must raise that type.
/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\nb\n" "--- outcome\nraised E\n--- gap g\n")) cpy none))

/-- info: p | gap | g -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\nb\n" "--- outcome\nraised E\n--- gap g\n")) (tr "a\nb\n" "--- outcome\nraised E: x\n--- globals\n") none))

/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\nb\n" "--- outcome\nraised E\n--- gap g\n")) (tr "a\nb\n" "--- outcome\nraised EE: x\n--- globals\n") none))

-- A global named `raised` is not the outcome's type line: the run agrees up to its gap.
/-- info: p | gap | g -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\n" "--- outcome\nok\n--- globals\nraised = 3\n--- gap g\n")) (tr "a\n" "--- outcome\nok\n--- globals\nraised = 3\nx = 1\n") none))

-- A line of the output that looks like a gap is output, not a gap.
/-- info: fails: p: the traces differ -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\n--- gap g\n" "--- outcome\nok\n--- globals\nx = 2\n")) (tr "a\n--- gap g\n" "--- outcome\nok\n--- globals\nx = 1\n") none))

/-- info: fails: p: the traces differ -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "a\nb\n" "--- outcome\nok\n--- globals\nx = 2\n")) cpy none))

-- A documented difference holds for the run's pinned trace, and for no other trace.
meta def known2 : String := tr "a\nb\n" "--- outcome\nok\n--- globals\nx = 2\n"

/-- info: p | known | r -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace known2) cpy (some ⟨"r", some known2⟩)))

/-- info: fails: p: the run's trace differs from its pinned trace -/
#guard_msgs in
#eval IO.println (verdictText
  (judge "p" (.trace (tr "a\nb\n" "--- outcome\nok\n--- globals\nx = 3\n")) cpy (some ⟨"r", some known2⟩)))

-- Without a pinned trace (while the golden is written), any differing trace is the difference.
/-- info: p | known | r -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace known2) cpy (some ⟨"r", none⟩)))

/-- info: fails: p: the run is out of fuel -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace (tr "a\n" "--- out of fuel\n")) cpy none))

-- CPython's two runs differ: the run must stop with a gap, and agree with both runs before it.
meta def two : String :=
  s!"--- PYTHONHASHSEED=0\n{tr "<0x?>\n" ""}--- PYTHONHASHSEED=1\n{tr "<0x?>\n" ""}"

/-- info: p | gap | g -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace (tr "" "--- gap g\n")) two none))

/-- info: fails: p: CPython's two runs differ, but the run doesn't stop with a gap -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace (tr "<0x?>\n" "")) two none))

-- A gap after an output that neither run printed fails.
/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace (tr "z\n" "--- gap g\n")) two none))

-- Two runs whose outputs differ in order, as a set of `str`s does under two hash seeds: a gap after
-- the order of one run fails, and a gap before the point where the two outputs differ is a gap.
meta def twoOrders : String :=
  s!"--- PYTHONHASHSEED=0\n{tr "['a', 'b']\n" ""}--- PYTHONHASHSEED=1\n{tr "['b', 'a']\n" ""}"

/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "['a', 'b']\n" "--- gap g\n")) twoOrders none))

/-- info: p | gap | g -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace (tr "['" "--- gap g\n")) twoOrders none))

-- Two runs with the same output and a global that differs by seed: a gap after the global of one
-- run fails, and a gap before the global is a gap.
meta def twoGlobals : String :=
  s!"--- PYTHONHASHSEED=0\n{tr "a\n" "--- outcome\nok\n--- globals\nh = 1\n"}--- PYTHONHASHSEED=1\n\
    {tr "a\n" "--- outcome\nok\n--- globals\nh = 2\n"}"

/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in
#eval IO.println (verdictText
  (judge "p" (.trace (tr "a\n" "--- outcome\nok\n--- globals\nh = 1\n--- gap g\n")) twoGlobals none))

/-- info: p | gap | g -/
#guard_msgs in
#eval IO.println (verdictText
  (judge "p" (.trace (tr "a\n" "--- outcome\nok\n--- globals\n--- gap g\n")) twoGlobals none))

-- A gap in the globals section, after the globals before it: they must be CPython's.
/-- info: p | gap | g -/
#guard_msgs in
#eval IO.println (verdictText
  (judge "p" (.trace (tr "a\nb\n" "--- outcome\nok\n--- globals\nx = 1\n--- gap g\n")) cpy none))

/-- info: fails: p: the run differs from CPython's before its gap -/
#guard_msgs in
#eval IO.println (verdictText
  (judge "p" (.trace (tr "a\nb\n" "--- outcome\nok\n--- globals\nx = 2\n--- gap g\n")) cpy none))

-- An output line that reads `--- out of fuel` is output.
/-- info: p | agree -/
#guard_msgs in
#eval IO.println (verdictText (judge "p" (.trace (tr "--- out of fuel\n" "--- outcome\nok\n"))
  (tr "--- out of fuel\n" "--- outcome\nok\n") none))

/-- info: p | syntax -/
#guard_msgs in #eval IO.println (verdictText (judge "p" .syntax syntaxTrace none))

/-- info: fails: p: the translator reports a syntax error, but CPython compiles it -/
#guard_msgs in #eval IO.println (verdictText (judge "p" .syntax cpy none))

/-- info: fails: p: CPython reports a syntax error, but the program runs -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace (tr "" "--- gap g\n")) syntaxTrace none))

/-- info: p | gap | the translator does not support async def, match -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.unsupported ["async def", "match"]) cpy none))

/-- info: fails: p: CPython reports a syntax error, but the translator only rejects async def -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.unsupported ["async def"]) syntaxTrace none))

-- What the translator's diagnostics say when `pydyn run` rejects a program.
/-- The result of `readRejection`, as text. -/
meta def rejectionText (stdout : String) : String :=
  match readRejection stdout with
  | .ok .syntax => "syntax"
  | .ok (.unsupported cs) => s!"unsupported {cs}"
  | .ok (.trace _) => "trace"
  | .error e => s!"fails: {e}"

/-- info: unsupported [async def, match] -/
#guard_msgs in
#eval IO.println (rejectionText "-- unsupported: async def is not supported at 1:0-1:9\n\
  -- unsupported: match is not supported at 2:0-2:5\n-- unsupported: async def is not supported at 3:0-3:9\n")

/-- info: syntax -/
#guard_msgs in
#eval IO.println (rejectionText "-- unsupported: match is not supported at 2:0-2:5\n\
  -- syntax error: 'return' outside function at 1:0-1:6\n")

-- An internal error of the translator, a line that is no diagnostic, and no diagnostic at all
-- fail the test.
/-- info: fails: the translator reports an internal error: -- internal error: x at ? -/
#guard_msgs in
#eval IO.println (rejectionText "-- unsupported: match is not supported at 2:0-2:5\n\
  -- internal error: x at ?\n")

/-- info: fails: the translator prints a line that is no diagnostic: oops -/
#guard_msgs in #eval IO.println (rejectionText "-- unsupported: match is not supported at 2:0-2:5\noops\n")

/-- info: fails: the translator rejects the program with no diagnostic -/
#guard_msgs in #eval IO.println (rejectionText "\n")

-- Masking keeps the header's length right.
/-- info: --- stdout 8
<x 0x?>

--- outcome
ok
-/
#guard_msgs in #eval IO.println (maskTrace (tr "<x 0x7f3>\n" "--- outcome\nok"))

/-- info: <x at 0x?> 0x 10 -/
#guard_msgs in #eval IO.println (maskAddresses "<x at 0x7f3a9c> 0x 10")

-- `joinRuns` gives CPython's trace unmasked when its two runs agree. When they differ, it gives
-- both traces, masked, each after its line `--- PYTHONHASHSEED=N`.
#guard joinRuns (tr "0xff\n" "--- outcome\nok\n") (tr "0xff\n" "--- outcome\nok\n") ==
  tr "0xff\n" "--- outcome\nok\n"
#guard joinRuns (tr "<x 0x7f3>\n" "--- outcome\nok\n") (tr "<x 0x7f4>\n" "--- outcome\nok\n") ==
  "--- PYTHONHASHSEED=0\n" ++ tr "<x 0x?>\n" "--- outcome\nok\n" ++ "--- PYTHONHASHSEED=1\n" ++
    tr "<x 0x?>\n" "--- outcome\nok\n"

-- A program whose CPython run doesn't end in time: a run out of fuel, or one that stops with a
-- gap, is a gap; a model-invariant gap and a run that ends with a result fail.
/-- info: p | gap | CPython's run does not end in time, so the outputs are not compared -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace (tr "a\n" "--- out of fuel\n")) endlessTrace none))

/-- info: fails: p: the run breaks a model invariant: model invariant: x -/
#guard_msgs in
#eval IO.println (verdictText
  (judge "p" (.trace (tr "a\n" ("--- gap " ++ StrataPython.Dyn.Sem.modelInvariantPrefix ++ "x\n")))
    endlessTrace none))

/-- info: fails: p: the run ends, but CPython's doesn't -/
#guard_msgs in #eval IO.println (verdictText (judge "p" (.trace cpy) endlessTrace none))

end StrataPython.SemDiff.VerdictTest
