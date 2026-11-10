/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPythonTest.Util.GoldenText

/-! # Shared compile, analyze and normalize helpers for the analyze goldens

The read side (`StrataPythonTest.AnalyzeGolden.Generate`, which each generated child
runs) and the write side (`Scripts.pyAnalyzeUpdate`, which regenerates the
`.expected` files) must produce the same text for a case: the write side stores the
normalized analyzer output as the golden and the read side diffs fresh output against
it byte for byte. So the pipeline that produces that text (compiling the case to Ion,
running the analyzer, normalizing assertion labels) is defined once here and both
sides import it.

Each case runs in its own scratch directory laid out like `StrataPythonTest/`: the
source is copied to `<scratch>/tests/<stem>.py`, compiled beside it, and the analyzer
runs with `<scratch>` as its working directory on `tests/<stem>.python.st.ion`. The
analyzer derives the source path from the Ion path it is given and writes
`user_errors.txt` into its working directory, so this layout reproduces the
`test_<stem>.py(line, col)` and `tests/test_<stem>.py` renderings the goldens hold,
while concurrent cases share no files. -/

namespace StrataPython.AnalyzeGolden

-- `hasSub` and `rstripNewlines` are shared with the interpret goldens; opened here so
-- the suite and its write side keep referring to them unqualified.
open StrataPython.GoldenText

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `cs` is exactly `_` followed by one or more digits. -/
private def isCounter : List Char → Bool
  | '_' :: d :: ds => isDigit d && ds.all isDigit
  | _ => false

/-- If `cs` starts with `(` digits `)`, the characters after the `)`. -/
private def afterNumericParen : List Char → Option (List Char)
  | '(' :: rest =>
    let digits := rest.takeWhile isDigit
    match rest.drop digits.length with
    | ')' :: after => if digits.isEmpty then none else some after
    | _ => none
  | _ => none

/-- The match of `(.*? - )([^ ]*)\(([0-9]+)\)(.*)` whose prefix ends at `p` (just past a
    ` - `): the label name and the text after its `)`. `[^ ]*` is greedy, so the name
    is the longest space-free run starting at `p` that a `(digits)` follows. -/
private def labelAt (cs : List Char) (p : Nat) : Option (List Char × List Char) :=
  let tail := cs.drop p
  let run := tail.takeWhile (· != ' ')
  (List.range (run.length + 1)).reverse.findSome? fun q =>
    (afterNumericParen (tail.drop q)).map fun after => (tail.take q, after)

/-- Normalize one line of analyzer output. When an obligation has no property summary
    the analyzer prints its raw label, which embeds internal IDs (`main_assert(471)_32`)
    that shift whenever the pipeline's numbering changes. A line matching
    `^(.*? - )([^ ]*)\(([0-9]+)\)(.*)$` whose text after the `)` is empty or a bare
    `_<digits>` counter has the label replaced by `name(…)`; every other line, including
    labels with a meaningful suffix such as `assert_assert(71)_calls_Any_get_0`, is
    unchanged. The lazy prefix makes the first ` - ` that admits a match win. -/
public def normalizeLine (line : String) : String := Id.run do
  let cs := line.toList
  let n := cs.length
  for i in List.range n do
    if (cs.drop i).take 3 == [' ', '-', ' '] then
      let p := i + 3
      if let some (name, after) := labelAt cs p then
        if after.isEmpty || isCounter after then
          return String.ofList (cs.take p ++ name) ++ "(…)"
        else
          return line
  return line

/-- Normalize a whole analyzer output into golden form: normalize each line, then end
    the text with exactly one newline. -/
public def normalizeOutput (output : String) : String :=
  let lines := (output.splitOn "\n").map normalizeLine
  rstripNewlines (String.intercalate "\n" lines) ++ "\n"

/-- Split on runs of spaces and tabs, dropping empty words, as the shell splits an
    unquoted expansion. -/
private def words (s : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  for c in s.toList do
    if c == ' ' || c == '\t' then
      unless cur.isEmpty do out := out.push cur
      cur := ""
    else
      cur := cur.push c
  unless cur.isEmpty do out := out.push cur
  return out

/-- The arguments a case asks for on a `# strata-args:` line (the first such line in
    the file), split into words. -/
public def strataArgs (source : String) : Array String :=
  let tag := "# strata-args:"
  match (source.splitOn "\n").find? (·.startsWith tag) with
  | some ln => words (String.ofList (ln.toList.drop tag.length))
  | none => #[]

/-- The result of one analyzer run on a compiled case. -/
public structure AnalyzeResult where
  exitCode : UInt32
  stdout : String
  stderr : String
  /-- The contents of the `user_errors.txt` the run wrote, if it wrote one. -/
  userErrors : Option String

/-- The analyzer binary for a front end, as built under `.lake/build/bin`. -/
public def analyzerPath (root : System.FilePath) (v2 : Bool) : System.FilePath :=
  root / ".lake" / "build" / "bin" / (if v2 then "pyAnalyzeV2" else "pyAnalyzeLaurel")

/-- Throw a clear error if a case's corpus `.py` is absent. A missing source means a
    committed child names a test that is gone, not a parse failure; without this the
    bare `readBinFile`/`readFile` below fails with an opaque "no such file" that does
    not say which case or what to do. -/
public def ensureCaseExists (root : System.FilePath) (subdir stem : String) : IO Unit := do
  let pyPath := root / "StrataPythonTest" / subdir / (stem ++ ".py")
  unless ← pyPath.pathExists do
    throw <| IO.userError
      s!"analyze golden corpus file missing: {pyPath}; the child module for \"{stem}\" \
         references a test that is gone — regenerate the children (build once locally) \
         and commit the result"

/-- Copy `StrataPythonTest/<subdir>/<stem>.py` into a fresh scratch directory and
    compile it to Ion beside the copy, then run `k` with the scratch directory. When
    the Python front end cannot lower the file, returns its combined output as the
    error instead. A corpus file that is absent entirely throws (a stale committed
    child, not a lowering failure). The dialect path is relative to
    `Python/strata-python`, so the compiler runs there with absolute file paths. -/
public def withCompiledCase {α : Type} (python : String) (root : System.FilePath)
    (subdir stem : String) (k : System.FilePath → IO α) : IO (Except String α) := do
  ensureCaseExists root subdir stem
  IO.FS.withTempDir fun scratch => do
    let caseDir := scratch / subdir
    IO.FS.createDirAll caseDir
    let pyCopy := caseDir / (stem ++ ".py")
    IO.FS.writeBinFile pyCopy
      (← IO.FS.readBinFile (root / "StrataPythonTest" / subdir / (stem ++ ".py")))
    let compile ← IO.Process.output {
      cmd := python
      args := #["-m", "strata_python.gen", "py_to_strata",
                "--dialect", "dialects/Python.dialect.st.ion",
                pyCopy.toString, (caseDir / (stem ++ ".python.st.ion")).toString]
      cwd := some (root / "Python" / "strata-python").toString
      inheritEnv := true
    }
    if compile.exitCode != 0 then
      return .error (compile.stdout ++ compile.stderr)
    return .ok (← k scratch)

/-- Run one front end's analyzer on a case already compiled by `withCompiledCase`,
    from the scratch directory, on `<subdir>/<stem>.python.st.ion`. `timeoutSecs` wraps
    the run in `timeout`. Any `user_errors.txt` is captured and removed, so the next
    run in the same scratch directory starts clean. -/
public def analyzeCompiled (root scratch : System.FilePath) (subdir stem : String)
    (v2 : Bool) (extraArgs : Array String) (timeoutSecs : Option String := none)
    : IO AnalyzeResult := do
  let userErrorsFile := scratch / "user_errors.txt"
  if ← userErrorsFile.pathExists then IO.FS.removeFile userErrorsFile
  let analyzer := (analyzerPath root v2).toString
  let ionRel := s!"{subdir}/{stem}.python.st.ion"
  let (cmd, args) := match timeoutSecs with
    | some t => ("timeout", #[t, analyzer] ++ extraArgs ++ #[ionRel])
    | none => (analyzer, extraArgs ++ #[ionRel])
  let out ← IO.Process.output {
    cmd, args
    cwd := some scratch.toString
    inheritEnv := true
  }
  let userErrors ←
    if ← userErrorsFile.pathExists then do
      let s ← IO.FS.readFile userErrorsFile
      IO.FS.removeFile userErrorsFile
      pure (some s)
    else pure none
  return { exitCode := out.exitCode, stdout := out.stdout, stderr := out.stderr, userErrors }

/-- Compile `StrataPythonTest/<subdir>/<stem>.py` to Ion in a private scratch directory
    and run one front end's analyzer on it (`v2` selects `pyAnalyzeV2` over
    `pyAnalyzeLaurel`), with the case's `# strata-args:` followed by `extraArgs`.
    Returns the compiler's output as the error when the file cannot be lowered. -/
public def compileAndAnalyze (python : String) (root : System.FilePath) (stem : String)
    (v2 : Bool) (extraArgs : Array String := #[]) (subdir : String := "tests")
    (timeoutSecs : Option String := none) : IO (Except String AnalyzeResult) := do
  ensureCaseExists root subdir stem
  let caseArgs := strataArgs
    (← IO.FS.readFile (root / "StrataPythonTest" / subdir / (stem ++ ".py")))
  withCompiledCase python root subdir stem fun scratch =>
    analyzeCompiled root scratch subdir stem v2 (caseArgs ++ extraArgs) timeoutSecs

/-- The golden directory of a front end, under `StrataPythonTest/`. -/
public def expectedDirName (v2 : Bool) : String :=
  if v2 then "expected_laurel" else "expected_laurel_v1"

end StrataPython.AnalyzeGolden
