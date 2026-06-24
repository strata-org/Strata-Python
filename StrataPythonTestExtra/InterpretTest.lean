/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python -- shake: keep
meta import StrataPython
meta import StrataPython.PySpecPipeline
meta import StrataPython.PyFactory
public meta import Strata.Languages.Core.StatementEval
public meta import Strata.Languages.Core.ProgramEval

/-! ## pyInterpret golden tests

Ports `StrataPythonTest/run_py_interpret.sh` to a Lean test. For each
`tests/test_*.py` the test spawns `strata_python.gen py_to_strata` to compile
the source to Ion, then runs the interpreter pipeline in-process — the same
path `Cli.lean`'s `pyInterpret` command drives (Python → Laurel → Core →
execute `__main__`) — and checks the outcome against `expected_interpret/`:

- No `.expected`/`.skip` file → the program must run to completion.
- A `.expected` file → the program must fail, and the failure text must
  contain the file's pattern. All committed patterns are escaped literals
  (every metacharacter is backslash-escaped), so "matches" reduces to
  substring containment after unescaping `\X → X`; no regex engine is needed.
- A `.skip` file → skip (the contents are the reason).

This is a runtime test (needs Python with `strata_python.gen`), run from
`StrataPythonTestExtra/` via `lake test`. Unlike the shell version it runs the
interpreter in-process rather than via `lake exe pyInterpret`.
-/

open Strata
open StrataPython (withPython)

namespace StrataPython.InterpretTest

meta section

def testsDir : System.FilePath := "StrataPythonTest/tests"
def expectedDir : System.FilePath := "StrataPythonTest/expected_interpret"

/-- Default interpreter fuel, matching `run_py_interpret.sh`. -/
def defaultFuel : Nat := 100000

/-- Compile a Python source file to a `.python.st.ion` Ion file in `outDir`.
    Returns `none` on a parse failure (the shell script's "SKIP (parse)"). -/
def compilePython (pythonCmd dialectFile pyFile outDir : System.FilePath)
    : IO (Option System.FilePath) := do
  let some stem := pyFile.fileStem
    | return none
  let ionPath := outDir / s!"{stem}.python.st.ion"
  let child ← IO.Process.spawn {
    cmd := pythonCmd.toString
    args := #["-m", "strata_python.gen", "py_to_strata",
              "--dialect", dialectFile.toString,
              pyFile.toString, ionPath.toString]
    inheritEnv := true
    stdin := .null, stdout := .null, stderr := .null
  }
  let exitCode ← child.wait
  if exitCode ≠ 0 then return none
  return some ionPath

/-- Interpret a compiled Python Ion program, mirroring `Cli.lean`'s
    `pyInterpretCommand`. Returns `.ok ()` when `__main__` runs to completion,
    or `.error msg` with the formatted failure text otherwise (the same text
    the CLI prints, which the `.expected` patterns match against). -/
def interpret (ionFile : System.FilePath) : IO (Except String Unit) := do
  let quietCtx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
  let coreOpt ←
    match ← (StrataPython.pythonAndSpecToLaurel ionFile.toString (specDir := ".")).run quietCtx
        |>.toBaseIO with
    | .ok laurel =>
      match ← StrataPython.translateCombinedLaurel laurel with
      | (some core, _diags) => pure (Except.ok core)
      | (none, diags) => pure (Except.error s!"Laurel to Core translation failed: {diags}")
    | .error () =>
      let msgs ← quietCtx.getMessages
      pure (Except.error (match msgs.back? with | some m => m.message | none => "Pipeline aborted"))
  match coreOpt with
  | .error msg => return .error msg
  | .ok core =>
    match Core.typeCheck Core.VerifyOptions.quiet core (moreFns := StrataPython.ReFactory) with
    | .error e => return .error s!"Core type checking failed: {e.message}"
    | .ok core =>
      match core.run with
      | .error diag => return .error s!"Error: {diag}"
      | .ok E =>
        let mainProc := Core.Program.Procedure.find? core ⟨"__main__", ()⟩
        let outputNames := match mainProc with
          | some p => p.header.outputs.keys.map (·.name)
          | none => []
        let (lhs, exprEnv) := Core.Env.genVars outputNames E.exprEnv
        let E := { E with exprEnv }
        let E := Core.Statement.Command.runCall lhs "__main__" [] defaultFuel E
        match E.error with
        | none => return .ok ()
        | some e => return .error (toString (Std.format e))

/-- Unescape a committed `.expected` pattern (`\X → X`) so a literal substring
    check is equivalent to the original POSIX-regex match. -/
def unescapePattern (s : String) : String :=
  let rec go (cs : List Char) (acc : String) : String :=
    match cs with
    | [] => acc
    | '\\' :: c :: rest => go rest (acc.push c)
    | c :: rest => go rest (acc.push c)
  go s.toList ""

structure Outcome where
  passed : Nat := 0
  skipped : Nat := 0
  errors : Nat := 0

def collectTestFiles : IO (Array System.FilePath) := do
  let mut out := #[]
  for entry in ← testsDir.readDir do
    let p := entry.path
    if p.extension == some "py" then
      if let some stem := p.fileStem then
        if stem.startsWith "test_" then
          out := out.push p
  return out.qsort (·.toString < ·.toString)

def main : IO Unit := do
  withPython fun pythonCmd => do
    IO.FS.withTempDir fun tmpDir => do
      let dialectFile := tmpDir / "Python.dialect.st.ion"
      IO.FS.writeBinFile dialectFile Python.toIon

      let files ← collectTestFiles
      let mut o : Outcome := {}
      for pyFile in files do
        let some baseName := pyFile.fileStem
          | continue
        let expectedFile := expectedDir / s!"{baseName}.expected"
        let skipFile := expectedDir / s!"{baseName}.skip"

        if ← skipFile.pathExists then
          let reason := (← IO.FS.readFile skipFile).trimAscii.toString
          IO.println s!"SKIP: {baseName} — {reason}"
          o := { o with skipped := o.skipped + 1 }
          continue

        match ← compilePython pythonCmd dialectFile pyFile tmpDir with
        | none =>
          IO.println s!"SKIP (parse): {baseName}"
          o := { o with skipped := o.skipped + 1 }
        | some ionFile =>
          let result ← interpret ionFile
          if ← expectedFile.pathExists then
            -- Expected failure: result must be an error containing the pattern.
            let pattern := unescapePattern (← IO.FS.readFile expectedFile).trimAscii.toString
            match result with
            | .ok () =>
              IO.println s!"ERR:  {baseName} (expected failure matching /{pattern}/ but test passed)"
              o := { o with errors := o.errors + 1 }
            | .error output =>
              if (output.splitOn pattern).length > 1 then
                IO.println s!"OK:   {baseName} (expected failure)"
                o := { o with passed := o.passed + 1 }
              else
                IO.println s!"ERR:  {baseName} (output does not match expected pattern /{pattern}/)"
                IO.println s!"  got: {output}"
                o := { o with errors := o.errors + 1 }
          else
            -- No expected file: the program must run to completion.
            match result with
            | .ok () =>
              IO.println s!"OK:   {baseName}"
              o := { o with passed := o.passed + 1 }
            | .error output =>
              IO.println s!"ERR:  {baseName} (expected pass but failed) — {output}"
              o := { o with errors := o.errors + 1 }

      IO.println s!"\nResults: {o.passed} passed, {o.skipped} skipped, {o.errors} errors"
      if o.errors > 0 then
        throw <| .userError s!"{o.errors} pyInterpret test failure(s)."

end

end StrataPython.InterpretTest

#eval StrataPython.InterpretTest.main
