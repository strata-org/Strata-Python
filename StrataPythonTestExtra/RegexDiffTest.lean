/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python -- shake: keep
meta import StrataPython.Regex.ReToCore
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects
public meta import Strata.Languages.Core.Verifier
public meta import Strata.Languages.Core

/-! ## Regex differential test: Strata SMT backend vs Python `re`

Runs Regex differential testing for Strata SMT backend vs Pyrthon The test corpus —
`(regex, string, mode)` triples — lives in `StrataPythonTest/Regex/corpus.tsv`,
one tab-separated triple per line.

For each case the test:
1. Runs the regex through Strata's SMT backend in-process.
2. Gets the Python `re` result from the `regex_oracle.py` helper, spawned once
   over the whole corpus.
3. Classifies the pair as agree / bug / known_gap / investigate and fails the
   test on any bug or investigate, matching the Python driver.

-/

open Strata
open StrataPython (MatchMode pythonRegexToCore)
open StrataDDM.Elab (LoadedDialects elabProgram)

namespace StrataPython.RegexDiffTest

meta section

def corpusFile : System.FilePath := "StrataPythonTest/Regex/corpus.tsv"
def oracleScript : System.FilePath := "StrataPythonTest/Regex/regex_oracle.py"

def parseMode (s : String) : Option MatchMode :=
  match s with
  | "match"     => some .match
  | "fullmatch" => some .fullmatch
  | "search"    => some .search
  | _           => none

/-- Strata-side result. -/
inductive StrataResult where
  | match
  | noMatch
  | parseError (kind : String)  -- "patternError" or "unimplemented"
  | smtError   (msg  : String)

def StrataResult.toStr : StrataResult → String
  | .match           => "match"
  | .noMatch         => "noMatch"
  | .parseError kind => s!"parseError:{kind}"
  | .smtError   msg  => s!"smtError:{msg}"

/-- Escape a string for embedding as a double-quoted Core string literal. -/
def escapeForCore (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '\\' => "\\\\"
    | '"'  => "\\\""
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | _    => toString c) ""

/-- Build a Core program asserting `str.in.re(testStr, regexExpr)`. -/
def mkProgText (testStr regexStr : String) : String :=
  "program Core;\n" ++
  "procedure main() {\n" ++
  s!"  assert [match_check]: (str.in.re(\"{escapeForCore testStr}\", {regexStr}));\n" ++
  "};"

/--
Check whether `testStr` matches `pyRegex` (in `mode`) via Strata's SMT
backend
-/
def checkMatch (pyRegex testStr : String) (mode : MatchMode) : IO StrataResult := do
  let (regexExpr, parseErr) := pythonRegexToCore pyRegex mode
  match parseErr with
  | some (.patternError ..)  => return .parseError "patternError"
  | some (.unimplemented ..) => return .parseError "unimplemented"
  | none =>
    let regexStr := toString (Core.formatExprs [regexExpr])
    let progText := mkProgText testStr regexStr
    let inputCtx := Lean.Parser.mkInputContext progText "<diff_test>"
    let dctx := LoadedDialects.builtin.addDialect! Core
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match elabProgram dctx leanEnv inputCtx with
    | .error errors =>
      let msgs ← errors.toList.mapM (·.toString)
      return .smtError s!"elab: {String.intercalate "; " msgs}"
    | .ok pgm =>
      let vcResults ← Strata.Core.verify pgm inputCtx none .quiet
      match vcResults[0]? with
      | none    => return .smtError "no VCs generated"
      | some vc =>
        if vc.isSuccess then return .match
        else if vc.isFailure then return .noMatch
        else return match vc.outcome with
          | .error err => .smtError s!"impl: {err}"
          | _ => .smtError "unknown"

/-- Verdict for a (python, strata) result pair. Mirrors `classify` in
    `diff_test.py`. -/
inductive Verdict where
  | agree
  | bug
  | knownGap
  | investigate

/-- Classify a Python `re` result string against a Strata result. `pyResult`
    is one of `match`, `noMatch`, or `error:<msg>` (from `regex_oracle.py`). -/
def classify (pyResult : String) (st : StrataResult) : Verdict :=
  let pyMatch   := pyResult == "match"
  let pyNoMatch := pyResult == "noMatch"
  let pyError   := pyResult.startsWith "error:"
  match st with
  -- Agreement
  | .match    => if pyMatch then .agree else if pyNoMatch then .bug
                 else /- pyError -/ .bug   -- Strata accepted an invalid regex
  | .noMatch  => if pyNoMatch then .agree else if pyMatch then .bug
                 else /- pyError -/ .bug   -- Strata accepted an invalid regex
  | .parseError "unimplemented" =>
                 if pyError then .agree
                 else /- pyMatch || pyNoMatch -/ .knownGap
  | .parseError _ /- patternError -/ =>
                 if pyError then .agree
                 else /- Strata rejected a valid regex -/ .bug
  | .smtError _ => .investigate

/-- One classified corpus entry, kept for reporting. -/
structure Entry where
  idx    : Nat
  regex  : String
  str    : String
  mode   : String
  py     : String
  st     : String
  verdict : Verdict

/-- Read the corpus as `(regex, string, mode)` triples. -/
def readCorpus : IO (Array (String × String × String)) := do
  let contents ← IO.FS.readFile corpusFile
  let mut out := #[]
  for line in contents.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    -- Skip blank lines and full-line comments (first non-whitespace char is `#`).
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    match line.splitOn "\t" with
    | [r, s, m] => out := out.push (r, s, m)
    | _ => throw <| .userError s!"Malformed corpus line: {line}"
  return out

/-- Run all corpus cases through the Python `re` oracle in one subprocess,
    returning a map from `(regex, string, mode)` to the result string. -/
def runOracle (pythonCmd : System.FilePath)
    (cases : Array (String × String × String)) : IO (Std.HashMap (String × String × String) String) := do
  let stdinData := String.intercalate "\n" (cases.toList.map (fun (r, s, m) => s!"{r}\t{s}\t{m}")) ++ "\n"
  let child ← IO.Process.spawn {
    cmd := pythonCmd.toString
    args := #[oracleScript.toString]
    stdin := .piped, stdout := .piped, stderr := .piped
  }
  let (stdinH, child) ← child.takeStdin
  stdinH.putStr stdinData
  stdinH.flush
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode ≠ 0 then
    throw <| .userError s!"regex_oracle.py failed (exit {exitCode}): {stderr}"
  let mut m : Std.HashMap (String × String × String) String := {}
  for line in stdout.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | [r, s, mode, res] => m := m.insert (r, s, mode) res
    | _ => pure ()
  return m

def main : IO Unit := do
  withPython fun pythonCmd => do
    let cases ← readCorpus
    IO.println s!"Running {cases.size} regex differential cases..."
    let oracle ← runOracle pythonCmd cases

    let mut entries : Array Entry := #[]
    let mut idx := 0
    for (regex, str, mode) in cases do
      idx := idx + 1
      let some mm := parseMode mode
        | throw <| .userError s!"Unknown mode in corpus: {mode}"
      let st ← checkMatch regex str mm
      let py := oracle.getD (regex, str, mode) "error:missing_oracle_output"
      entries := entries.push {
        idx, regex, str, mode, py, st := st.toStr, verdict := classify py st }

    let count (v : Verdict → Bool) := entries.filter (fun e => v e.verdict) |>.size
    let agree := count (· matches .agree)
    let bugs := entries.filter (fun e => e.verdict matches .bug)
    let gaps := count (· matches .knownGap)
    let investigations := entries.filter (fun e => e.verdict matches .investigate)

    IO.println s!"  agree: {agree}   bugs: {bugs.size}   known gaps: {gaps}   investigate: {investigations.size}"

    let report (e : Entry) : String :=
      s!"  [#{e.idx}] regex={e.regex} string={e.str} mode={e.mode}\n    Python: {e.py}\n    Strata: {e.st}"
    unless bugs.isEmpty do
      IO.println s!"\nBUGS ({bugs.size}) — Strata and Python disagree on a valid regex:"
      for e in bugs do IO.println (report e)
    unless investigations.isEmpty do
      IO.println s!"\nINVESTIGATE ({investigations.size}):"
      for e in investigations do IO.println (report e)

    if !bugs.isEmpty || !investigations.isEmpty then
      throw <| .userError s!"{bugs.size} bug(s), {investigations.size} investigate — regex differential test failed."
    IO.println "All cases either agree or are known gaps."

end

end StrataPython.RegexDiffTest

#eval StrataPython.RegexDiffTest.main
