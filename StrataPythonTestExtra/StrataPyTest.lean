/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import Strata.Cli.CoreCommands
meta import StrataPython.Cli
meta import StrataPythonTest.AnalyzeGolden.Matching
meta import StrataPythonTest.InterpretGolden.Matching
meta import StrataPythonTest.Util.Python

open StrataPython (withPython)
open StrataPython.Cli (pythonFrontend)
open StrataPython.AnalyzeGolden (analyzeCompiled strataArgs withCompiledCase)
open StrataPython.InterpretGolden (compileAndRun)

/-! ## The commands `pythonFrontend` offers

`strataPy` and `stratainternal` register `pythonFrontend` with Strata's command
builders. Pin its groups and the names of its Python commands, so adding, dropping or
renaming a Python command fails here until the list changes. -/

meta def expectedPythonCommands : List String :=
  ["pyAnalyzeLaurel", "pyResolveOverloads", "pySpecs", "pySpecToLaurel",
   "pyAnalyzeLaurelToGoto", "pyAnalyzeToGoto", "pyTranslateLaurel", "pyInterpret"]

meta def strataPyGroups : List CommandGroup :=
  Strata.Cli.buildCommandGroups [] {} [pythonFrontend]

#guard (strataPyGroups.map (·.name)) == ["Core", "Python"]
#guard ((strataPyGroups.find? (·.name == "Python")).map (·.commands.map (·.name))) ==
  some expectedPythonCommands
-- `buildCommandMap` keys the commands by name, so a name two commands share leaves the
-- map smaller than the list.
#guard (Strata.Cli.buildCommandMap [] {} [pythonFrontend]).size ==
  (Strata.Cli.buildCommandList [] {} [pythonFrontend]).length

/-! ## `strataPy` dispatches to `pyInterpret` and `pyAnalyzeLaurel`

Runs corpus cases through `strataPy <command>` and through the command's own
executable, under the V1 and the V2 front end, and checks that both give the same exit
code and the same output. Under V2 the standalone analyzer is `pyAnalyzeV2`, so the
check also covers `strataPy pyAnalyzeLaurel --v2` behaving like it. The other Python
commands are pinned by name only (above). -/

/-- The standalone executables name the program `strata` in the usage hint
    (`Run strata --help for additional help.`), and `strataPy` names itself.
    Rename the program in that line only, so the rest of both outputs compares exactly. -/
meta def asStrataPyHint (output : String) : String :=
  let renameLine (line : String) : String :=
    if line.startsWith "Run strata " && line.endsWith " for additional help." then
      "Run strataPy " ++ String.ofList (line.toList.drop "Run strata ".length)
    else line
  "\n".intercalate ((output.splitOn "\n").map renameLine)

/-- Fail with both outputs when `strataPy`'s run differs from the standalone run. -/
meta def expectSameRun (label viaStrataPy standalone : String) : IO Unit :=
  unless viaStrataPy == asStrataPyHint standalone do
    throw <| .userError
      s!"{label}: strataPy and the standalone executable differ\n\
         --- strataPy:\n{viaStrataPy}\n--- standalone:\n{standalone}"

meta def frontEndName (v2 : Bool) : String := if v2 then "V2" else "V1"

/-- Interpreter cases: one passes, one fails an assertion, and the front end rejects
    one (`class decorators are not supported`), which prints the usage hint. -/
meta def interpretCases : List String :=
  ["test_any_arithmetic", "test_soundness_global_annotation_only",
   "test_class_decorator_rejection"]

meta def checkInterpret (python : String) (stem : String) (v2 : Bool) : IO Unit := do
  let label := s!"pyInterpret {stem} ({frontEndName v2})"
  let root ← IO.currentDir
  let standalone ← match ← compileAndRun python root stem v2 with
    | .ok r => pure r
    | .error msg => throw <| .userError s!"{label}: {msg}"
  let viaStrataPy ← match ← compileAndRun python root stem v2
      (exe := some ("strataPy", #["pyInterpret"])) with
    | .ok r => pure r
    | .error msg => throw <| .userError s!"{label}: {msg}"
  expectSameRun label s!"exit {viaStrataPy.1}\n{viaStrataPy.2}"
    s!"exit {standalone.1}\n{standalone.2}"

/-- Analyzer cases: one passes, one reports failures (with its own `# strata-args:`),
    and one is a user error that writes `user_errors.txt` under V1. -/
meta def analyzeCases : List String :=
  ["test_ifexpr", "test_bug_finding_unreachable", "test_user_error_metadata"]

/-- Everything a caller of `pyAnalyzeLaurel` reads: the exit code, stdout, stderr and
    `user_errors.txt`. -/
meta def renderAnalyze (r : StrataPython.AnalyzeGolden.AnalyzeResult) : String :=
  s!"exit {r.exitCode}\n--- stdout:\n{r.stdout}\n--- stderr:\n{r.stderr}\n\
     --- user_errors.txt:\n{r.userErrors.getD "(not written)"}"

/-- Compile the case once and run both analyzers on the same Ion. `analyzeCompiled`
    removes `user_errors.txt` before each run, so the second run starts clean. -/
meta def checkAnalyze (python : String) (stem : String) (v2 : Bool) : IO Unit := do
  let label := s!"pyAnalyzeLaurel {stem} ({frontEndName v2})"
  let root ← IO.currentDir
  let caseArgs := strataArgs
    (← IO.FS.readFile (root / "StrataPythonTest" / "tests" / (stem ++ ".py")))
  let compiled ← withCompiledCase python root "tests" stem fun scratch => do
    let standalone ← analyzeCompiled root scratch "tests" stem v2 caseArgs
    let viaStrataPy ← analyzeCompiled root scratch "tests" stem v2 caseArgs
      (exe := some ("strataPy", #["pyAnalyzeLaurel"]))
    return (standalone, viaStrataPy)
  let .ok (standalone, viaStrataPy) := compiled
    | throw <| .userError s!"{label}: the Python front end could not lower the case"
  expectSameRun label (renderAnalyze viaStrataPy) (renderAnalyze standalone)

#eval withPython fun pythonCmd => do
  for v2 in [false, true] do
    for stem in interpretCases do
      checkInterpret pythonCmd.toString stem v2
    for stem in analyzeCases do
      checkAnalyze pythonCmd.toString stem v2
