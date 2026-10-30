/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.Dyn.PySpec.Load
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataPython.Dyn.Env
meta import StrataDyn.Env.WF
meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Dyn.TestUtil

/-! # PySpec models as IR modules

Translates every model set listed in `StrataPythonTest/Dyn/pyspec_models.txt` with
`PySpec.translateModels` (`docs/PythonToDyn.md` §12). The list has one line per set:

```
StrataPythonTestExtra/Specs/dispatch_test | servicelib | ok
StrataPythonTestExtra/Specs/dispatch_test | servicelib.Counter | ensures
```

The columns are PySpec's search path, the model module, and `ok` or the rule IDs of the set's
rejections, sorted and joined by commas. A translated set's modules must each equal
`StrataPythonTest/Dyn/pyspec_models/<module>.expected.dyn`, and read back in `Py.env`,
which checks them, to the same text. A rejected set's rejections, with their messages, must
equal `<module>.expected.rejections` there. Set `PYSPEC_DYN_UPDATE=1` to rewrite the goldens.
The test needs Python, as `withPython` finds it.
-/

namespace StrataPython.PySpecDynTest

open StrataPython.Dyn.PySpec
open StrataPython (withPython)
open StrataPython.Dyn.TestUtil (firstDiff)

private meta def listFile : System.FilePath := "StrataPythonTest" / "Dyn" / "pyspec_models.txt"
private meta def goldenDir : System.FilePath := "StrataPythonTest" / "Dyn" / "pyspec_models"

/-- One line of the list: the search path, the module, and its expected outcome. -/
private structure Entry where
  searchPath : String
  module : String
  expected : String

/-- The lines of the list, without blank lines and comments. -/
private meta def entries : IO (Array Entry) := do
  let mut out := #[]
  for line in (← IO.FS.readFile listFile).splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "|" |>.map (·.trimAscii.toString) with
    | [sp, m, e] => out := out.push { searchPath := sp, module := m, expected := e }
    | _ => throw <| IO.userError s!"bad line in {listFile}: {line}"
  return out

/-- Run one set; return its failures, as lines. -/
private meta def runEntry (pythonCmd : String) (update : Bool) (e : Entry) : IO (Array String) := do
  let some mod := StrataPython.ModuleName.ofString? e.module
    | return #[s!"{e.module}: not a module name"]
  let (file, _) ← IO.ofExcept (← (mod.findInPath e.searchPath).toBaseIO)
  let (set, _) ← loadModels pythonCmd e.searchPath file e.module
  match translateModels set, e.expected with
  | .error rs, expected =>
    let got := ",".intercalate ((rs.map (·.rule)).toList.eraseDups.mergeSort (· ≤ ·))
    if got != expected then
      return #[s!"{e.module}: expected {expected}, got {got}: {rs.map (·.message)}"]
    let text := String.join (rs.toList.map fun r => s!"[{r.rule}] {r.module}: {r.message}\n")
    let golden := goldenDir / s!"{e.module}.expected.rejections"
    if update then IO.FS.writeFile golden text; return #[]
    if !(← golden.pathExists) then
      return #[s!"{e.module}: no golden {golden}; run with PYSPEC_DYN_UPDATE=1"]
    match firstDiff text (← IO.FS.readFile golden) with
    | some d => return #[s!"{e.module}: rejections differ from {golden} at {d}"]
    | none => return #[]
  | .ok _, expected@(_) =>
    if expected != "ok" then return #[s!"{e.module}: expected {expected}, but it translated"]
    let .ok mods := translateModels set | return #[]
    let mut fails := #[]
    for m in mods do
      let name := Strata.Dyn.Build.nameText m.raw.name
      let text := m.format
      let golden := goldenDir / s!"{name}.expected.dyn"
      match ← Strata.Dyn.Module.read StrataPython.Dyn.Py.env text name with
      | .error d => fails := fails.push s!"{name}: does not read back: {d}"
      | .ok back =>
        if back.format != text then fails := fails.push s!"{name}: reads back differently"
      if update then IO.FS.writeFile golden text
      else if !(← golden.pathExists) then
        fails := fails.push s!"{name}: no golden {golden}; run with PYSPEC_DYN_UPDATE=1"
      else if let some d := firstDiff text (← IO.FS.readFile golden) then
        fails := fails.push s!"{name}: differs from {golden} at {d}"
    return fails

/-- Run every set of the list. -/
private meta def runAll : IO Unit := withPython fun pythonCmd => do
  let update := (← IO.getEnv "PYSPEC_DYN_UPDATE").isSome
  IO.FS.createDirAll goldenDir
  let mut fails := #[]
  for e in ← entries do
    fails := fails ++ (← runEntry (toString pythonCmd) update e)
  unless fails.isEmpty do
    throw <| IO.userError ("\n".intercalate fails.toList)

#guard_msgs in
#eval runAll

/-- PySpec's warnings reach the IR path: an `@admit` that PySpec leaves out is reported. -/
private meta def admitWarnings : IO Unit := withPython fun pythonCmd => do
  let dir : System.FilePath := "StrataPythonTestExtra/Specs/dyn_cases"
  let (_, warnings) ← loadModels (toString pythonCmd) dir (dir / "unfaithful_admit.py") "unfaithful_admit"
  unless (warnings.filter (·.contains "@admit dropped")).size == 1 do
    throw <| IO.userError s!"expected one @admit warning, got {warnings}"

#guard_msgs in
#eval admitWarnings

/-- A model's field records carry `trustedType` and never `type`; a translated class's field
records never carry `trustedType`, so a trusted type never shares a key with an annotation. -/
private meta def fieldKeys : IO Unit := do
  let isFields (l : String) := l.contains "#[py.fields = [" || l.contains "#[py.initFields = ["
  let mut models := 0
  for f in ← goldenDir.readDir do
    if !f.fileName.endsWith ".expected.dyn" then continue
    for l in (← IO.FS.readFile f.path).splitOn "\n" do
      if isFields l && (l.contains "{name = ") then
        unless l.contains "trustedType = " && !(l.contains ", type = ") do
          throw <| IO.userError s!"{f.fileName}: a model field record without trustedType: {l}"
        models := models + 1
  unless models > 0 do throw <| IO.userError "no model field record found"
  let translated : System.FilePath := "StrataPythonTest/Dyn/dyn_tests"
  for f in ← translated.readDir do
    if !f.fileName.endsWith ".expected.dyn" then continue
    if (← IO.FS.readFile f.path).contains "trustedType" then
      throw <| IO.userError s!"{f.fileName}: a translated class's record has trustedType"

#guard_msgs in
#eval fieldKeys

end StrataPython.PySpecDynTest
