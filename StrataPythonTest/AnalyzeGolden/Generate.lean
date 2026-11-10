/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- `withPython` (the interpreter locator that honours `SKIP_PYTHON_TESTS`) is
-- re-exported to the generated children: each child `#eval`s `runAnalyzeCase`,
-- whose body calls it, so the symbol must reach them transitively.
public meta import StrataPythonTest.Util.Python
-- The compile+analyze pipeline and the label normalizer are shared with
-- `Scripts.pyAnalyzeUpdate` so the read and write sides cannot drift. They are used
-- at meta time here and re-exported to the generated children, hence both forms.
public meta import StrataPythonTest.AnalyzeGolden.Matching
public import StrataPythonTest.AnalyzeGolden.Matching
-- The `--metrics` test parses each JSONL record.
public meta import Lean.Data.Json
import Strata.Util.Tests

open StrataPython.GoldenText

/-! ## Golden analyze tests for both front ends (dynamically generated)

Runs the compiled analyzers (`pyAnalyzeLaurel` for V1, `pyAnalyzeV2` for V2) on every
`StrataPythonTest/tests/test_*.py` that has a golden and diffs the normalized output
against it byte for byte. This file is the *generator*: it declares one
`#eval runAnalyzeCase "<stem>"` per corpus file, plus the `--metrics` check, and
writes one child module per entry under `StrataPythonTestExtra/AnalyzeGolden/Gen/`,
which `testMain` runs as its own `lean` process. The children run concurrently, so
the corpus is spread across cores; each case compiles and analyzes in a private
scratch directory (see `StrataPythonTest.AnalyzeGolden.Matching`), so they share no
files.

`#test_for_each_file` reads the corpus directory at build time so the set of
children tracks `tests/`, and `#run_tests_as_modules` checks the committed children
against what this file would emit; on drift it regenerates them and fails the build
until they are committed. Re-baselining the goldens, reporting the V1/V2 divergence
and running the `tests/pending/` cases are not test-time concerns; the
`pyAnalyzeUpdate` executable does those.

Each front end has its own full set of goldens: V1 in
`StrataPythonTest/expected_laurel_v1/` and V2 in `StrataPythonTest/expected_laurel/`
(see `expected_laurel/README.md` for why the sets sit at those paths). The presence
of `<expected_dir>/<stem>.expected` is what puts a case in that front end's suite; a
corpus file with neither golden passes without running. When
`<expected_dir>/<stem>.user_errors.expected` exists, the `user_errors.txt` the
analyzer writes must match it exactly; when it does not, the run must write none.

Requires Python with `strata_python.gen` (the build exports `PYTHON`), the SMT
solvers cvc5 and z3 on PATH, and the two analyzer binaries, which
`StrataPythonFrontEndTestMain` lists in its `needs` so `lake test` builds them once.
Generation itself (the commands at the foot of this file) runs at build time and
needs none of these; only the children `testMain` later spawns do. -/

namespace StrataPython.AnalyzeGolden

meta section

/-- A unified diff of `expected` against `actual`, for a failure message. -/
private def showDiff (dir : System.FilePath) (expected actual : String) : IO String := do
  IO.FS.writeFile (dir / "diff-expected") expected
  IO.FS.writeFile (dir / "diff-actual") actual
  let o ← IO.Process.output {
    cmd := "diff", args := #["-u", (dir / "diff-expected").toString, (dir / "diff-actual").toString]
  }
  return o.stdout

/-- Check one front end's run of a compiled case against its goldens and return the
    failures (empty when it matches). -/
private def checkOnePass (root scratch : System.FilePath) (stem : String) (v2 : Bool)
    (caseArgs : Array String) : IO (Array String) := do
  let feName := if v2 then "V2" else "V1"
  let expectedDir := root / "StrataPythonTest" / expectedDirName v2
  let r ← analyzeCompiled root scratch "tests" stem v2 caseArgs
  let mut errs := #[]
  let expected ← IO.FS.readFile (expectedDir / (stem ++ ".expected"))
  let actual := normalizeOutput r.stdout
  if actual != expected then
    errs := errs.push <|
      s!"{stem} [{feName}]: analysis output does not match {expectedDirName v2}/{stem}.expected\n"
      ++ (← showDiff scratch expected actual)
  let ueFile := expectedDir / (stem ++ ".user_errors.expected")
  match (← ueFile.pathExists), r.userErrors with
  | true, none =>
    errs := errs.push s!"{stem} [{feName}]: user_errors.txt not generated"
  | true, some got =>
    let want ← IO.FS.readFile ueFile
    if got != want then
      errs := errs.push <|
        s!"{stem} [{feName}]: user_errors.txt does not match \
           {expectedDirName v2}/{stem}.user_errors.expected\n"
        ++ (← showDiff scratch want got)
  | false, some got =>
    errs := errs.push
      s!"{stem} [{feName}]: user_errors.txt written but no \
         {stem}.user_errors.expected exists:\n{got}"
  | false, none => pure ()
  return errs

/-- Run every front end that has a golden for `stem` and throw on any mismatch, so the
    child `lean` process exits non-zero and `testMain` reports it. The case compiles to
    Ion once and both analyzers run on that Ion. `withPython` supplies the interpreter
    and honours `SKIP_PYTHON_TESTS`. -/
public def runAnalyzeCase (stem : String) : IO Unit :=
  withPython fun pythonCmd => do
    let root ← IO.currentDir
    let mut fronts := #[]
    for v2 in [false, true] do
      if ← (root / "StrataPythonTest" / expectedDirName v2 / (stem ++ ".expected")).pathExists then
        fronts := fronts.push v2
    if fronts.isEmpty then return
    let caseArgs := strataArgs
      (← IO.FS.readFile (root / "StrataPythonTest" / "tests" / (stem ++ ".py")))
    let r ← withCompiledCase pythonCmd.toString root "tests" stem fun scratch => do
      let mut errs := #[]
      for v2 in fronts do
        errs := errs ++ (← checkOnePass root scratch stem v2 caseArgs)
      return errs
    match r with
    | .error out => throw <| .userError s!"{stem}: py_to_strata failed\n{out}"
    | .ok errs =>
      unless errs.isEmpty do
        throw <| .userError (String.intercalate "\n" errs.toList)

/-- The first corpus stem, in sorted order, with a golden for the front end. -/
private def firstGoldenStem (root : System.FilePath) (v2 : Bool) : IO (Option String) := do
  let mut stems := #[]
  for de in ← (root / "StrataPythonTest" / "tests").readDir do
    let fn := de.fileName
    if fn.startsWith "test_" && fn.endsWith ".py" then
      let stem := String.ofList (fn.toList.take (fn.length - ".py".length))
      if ← (root / "StrataPythonTest" / expectedDirName v2 / (stem ++ ".expected")).pathExists then
        stems := stems.push stem
  return (stems.qsort (· < ·))[0]?

/-- Run one front end with `--metrics` on one golden case and check the JSONL it
    writes: non-empty, every non-empty line a JSON object with a `type` key, and an
    `outcome` record present. -/
private def checkMetrics (pythonCmd root : System.FilePath) (v2 : Bool) : IO Unit := do
  let feName := if v2 then "V2" else "V1"
  let some stem ← firstGoldenStem root v2
    | throw <| .userError s!"--metrics [{feName}]: no corpus case has a golden"
  let r ← withCompiledCase pythonCmd.toString root "tests" stem fun scratch => do
    let metricsFile := scratch / "metrics.jsonl"
    discard <| analyzeCompiled root scratch "tests" stem v2 #["--metrics", metricsFile.toString]
    if ← metricsFile.pathExists then IO.FS.readFile metricsFile else pure ""
  let content ← match r with
    | .ok c => pure c
    | .error out => throw <| .userError s!"--metrics [{feName}]: py_to_strata failed \
        for {stem}\n{out}"
  if content.isEmpty then
    throw <| .userError s!"--metrics [{feName}]: metrics file is empty for {stem}"
  let bad := (content.splitOn "\n").filter fun ln =>
    !ln.isEmpty && !(match Lean.Json.parse ln with
      | .ok j => (j.getObjVal? "type").toOption.isSome
      | .error _ => false)
  unless hasSub content "\"outcome\"" do
    throw <| .userError s!"--metrics [{feName}]: missing outcome record for {stem}"
  unless bad.isEmpty do
    throw <| .userError <|
      s!"--metrics [{feName}]: {bad.length} invalid line(s) for {stem}:\n"
      ++ String.intercalate "\n" bad

/-- The `--metrics` check under both front ends. `#test_for_each` names the child by
    its argument, which this ignores. -/
public def runMetricsCase (_name : String) : IO Unit :=
  withPython fun pythonCmd => do
    let root ← IO.currentDir
    checkMetrics pythonCmd root (v2 := false)
    checkMetrics pythonCmd root (v2 := true)

end -- meta section

end StrataPython.AnalyzeGolden

open StrataPython.AnalyzeGolden

-- The `--metrics` JSONL check, as one more child.
#test_for_each runMetricsCase ["metrics_jsonl"]

-- Declare one `#eval runAnalyzeCase "<stem>"` per `tests/test_*.py`, then check (and
-- on drift regenerate) the child modules. The directory is read at build time, so
-- the generated set tracks the corpus.
#test_for_each_file "StrataPythonTest/tests" "test_" ".py" runAnalyzeCase
#run_tests_as_modules "StrataPythonTestExtra/AnalyzeGolden/Gen"
