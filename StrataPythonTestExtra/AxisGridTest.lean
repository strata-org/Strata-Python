/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.AxisSource
meta import StrataPython.Dyn.Sem.Assembly
meta import StrataDyn.DDM

/-! # The axis grid against CPython

Runs every program of the axis grid (`StrataPythonTest/Dyn/axes/grid.py`: one operation with one
kind of input on one axis, e.g. `len` of an instance of a `list` subclass that overrides
`__iter__`) with CPython 3.12 and with the Python semantics, and judges each pair with
`SemDiff.judge`. The verdicts are pinned in `StrataPythonTest/Dyn/axes/grid_expected.txt`, and our
run of each `known` case in `grid_known/`. The test fails:

* on a generator bug (`AxisSource.generatorBug?`): a case whose CPython run doesn't run its
  operation, or doesn't end the way the case expects, tests nothing; in update mode also a case
  whose CPython trace doesn't change when its operation is replaced by `r = None`
  (`AxisSource.observes`);
* on any difference that is not a gap after agreeing with CPython, and on any change of verdict;
* on a change of `grid_digest.txt`. The digest stands for this property: CPython's traces under
  the hash seeds 0 to 7 were compared on exactly these programs, and were equal. The build runs
  CPython under seed 0 only. The digest check makes sure that no program changes without an
  update, and the update compares the eight traces again. An update that fails writes nothing.

The coverage check (`AxisSource.coverage`) then takes what the cases that agree with CPython
reach: observed, the built-in functions and methods that CPython calls in their operations
(`StrataPythonTest/Dyn/axes/cpython_calls.py`) and the instructions that their operations'
translations have (and those of the program around every operation, once any case agrees); and
declared, the dunder entries that the catalog maps their operations to and the attributes of
`typing` and `dataclasses` that they read. It fails on a name of the model's tables (every
instruction of `Py.env`, every built-in function and method that `Assembly.impls` implements, every
attribute that the model binds in `typing` and `dataclasses`, and the natives of those modules'
classes, `moduleNatives`) that nothing covers and that
`StrataPythonTest/Dyn/axes/not_covered.txt` doesn't list with a reason, and on a stale entry
there. The summary lists the names that only declared entries cover.

`grid_summary.txt` shows the verdicts by group and axis; it is compared like the verdicts, so that
it stays current. The test needs CPython 3.12, which it finds or fails without (`SKIP_PYTHON_TESTS`
skips it, as it does every Python test). Set `SEM_UPDATE=1` to compare the eight traces of every
program and rewrite the verdicts, the known runs, the summary and the digest.
-/

namespace StrataPython.AxisGridTest

open Strata.Dyn.Exec
open Strata.Dyn.Exec.Diff (Entry Verdict)
open StrataPython.AxisSource

private meta def here : System.FilePath := "StrataPythonTest" / "Dyn" / "axes"
private meta def outDir : System.FilePath := ".lake" / "build" / "differential" / "axes"
private meta def knownDir : System.FilePath := here / "grid_known"
private meta def knownSuffix : String := ".known.trace"

open StrataPython.Dyn.Sem in
open StrataPython.Dyn.Sem.Modules in
/-- The natives of the classes of `typing`, `dataclasses`, `collections` and `types` that the model
defines, by their keys (`<module>.<class>.<name>`): every `native`, `cached` and `staticNative`
entry of the class specs, the methods that `@dataclass` generates (`dataclasses.__eq__`, …), and
those of a named tuple class (`collections.namedtuple._make`, …). The specs are listed here: the
model keeps no list of them. -/
private meta def moduleNatives : List String :=
  let specs := [finalSpec, notIterableSpec, specialFormSpec, baseGenericAliasSpec,
    genericAliasSpec, specialGenericAliasSpec, tupleTypeSpec, unionGenericAliasSpec, forwardRefSpec,
    anyMetaSpec, anySpec, typedDictMetaSpec, typedDictSpec, namedTupleMetaSpec, namedTupleSpec,
    tupleGetterSpec, frozenErrorSpec, missingTypeSpec, hasFactorySpec, fieldBaseSpec, paramsSpec,
    fieldSpec, gaSpec, unionSpec]
  let keys := specs.flatMap fun spec => spec.entries.toList.filterMap fun
    | .native _ key _ | .cached _ key | .staticNative _ key => some key
    | _ => none
  let generated := ["__init__", "__repr__", "__eq__", "__lt__", "__le__", "__gt__", "__ge__",
    "__hash__", "__setattr__", "__delattr__"].map (s!"dataclasses.{·}")
  let namedtuple := ["__new__", "_make", "_replace", "__repr__", "_asdict", "__getnewargs__"].map
    (s!"collections.namedtuple.{·}")
  -- The natives that no spec holds: the decorator that `@dataclass(...)` returns, and the
  -- function that `TypedDict(...)` calls.
  let others := ["dataclasses.dataclass.<locals>.wrap", "typing.TypedDict.<lambda>"]
  keys ++ generated ++ namedtuple ++ others

open StrataPython.Dyn.Sem in
open Strata.Dyn in
open StrataPython.Dyn in
/-- The names that the grid must cover: the instructions of `Py.env`, the built-in functions and
the methods of the built-in types that `Assembly.impls` implements, as `<type>.<name>`, the
attributes that the model binds in `typing` and `dataclasses`, as `<module>.<name>`, and the
natives of those modules' classes (`moduleNatives`). -/
private meta def requiredNames : Array String :=
  let insns := Py.names.filterMap fun n =>
    match Py.env.get? n with
    | some (.insn ..) => some (ToDDM.nameText n)
    | _ => none
  let fns := Builtin.allConstants.toList.filterMap fun b =>
    if (Assembly.impls.function b).isSome then some b.info.name else none
  let methods := Builtin.allConstants.toList.flatMap fun t =>
    ((Builtin.ownNames t).toList.map (·.1)).filterMap fun n =>
      if (Assembly.impls.method t n).isSome then some s!"{t.info.name}.{n}" else none
  let modules := Modules.typingAttrNames.map (s!"typing.{·}") ++
    Modules.dataclassesAttrNames.map (s!"dataclasses.{·}")
  (insns ++ fns ++ methods ++ modules ++ moduleNatives).toArray

/-- The names that CPython calls by name in the case `c`'s operation (`cpython_calls.py`). -/
private meta def calledIn (pythonCmd : System.FilePath) (c : Case) : IO (List String) := do
  let r ← IO.Process.output {
    cmd := pythonCmd.toString
    args := #[(here / "cpython_calls.py").toString, (outDir / s!"{c.id}.py").toString]
    env := #[("PYTHONHASHSEED", some "0"), ("LC_ALL", some "C.UTF-8"),
      ("PYTHONIOENCODING", some "utf-8")] }
  unless r.exitCode == 0 do
    throw <| .userError s!"{c.id}: cpython_calls.py failed:\n{r.stderr}"
  return (r.stdout.splitOn "\n").filter (!·.isEmpty)

/-- The translation of `f` by `pydyn dyn`, or none if the translator rejects it. -/
private meta def dynOf (f : System.FilePath) : IO (Option String) := do
  let r ← IO.Process.output { cmd := SemDiff.pydynPath.toString, args := #["dyn", f.toString] }
  return if r.exitCode == 0 then some r.stdout else none

/-- The instructions that the operation of the template `t` adds to its translation, against
`base`, the instructions of `templates/null.py` (`r = None`); none if the translator rejects it. -/
private meta def insnsOf (base : List String) (t : String) : IO (List String) := do
  let some withOp ← dynOf (outDir / "templates" / s!"{t}.py") | return []
  return (insnNames withOp).filter (!base.contains ·)

/-- The verdict of the case `c` and, for a `known` case in update mode, our run to pin; or why the
test fails on it. `reasons` maps each case pinned as `known` to its reason. -/
private meta def runCase (pythonCmd : System.FilePath) (update : Bool)
    (reasons : Std.HashMap String String) (c : Case) :
    IO (Except String (Entry × Option String × List String × Bool)) := do
  let file := outDir / s!"{c.id}.py"
  let traces ← if update then seeds.toArray.mapM (cpythonTraceSeed pythonCmd file)
    else pure #[← cpythonTraceSeed pythonCmd file 0]
  unless seedsAgree traces do
    return .error s!"{c.id}: generator bug: CPython's trace depends on the hash seed or the machine"
  let theirs := traces[0]!
  if update then
    let null ← cpythonTraceSeed pythonCmd (outDir / s!"{c.id}.null.py") 0
    unless observes c theirs null do
      return .error s!"{c.id}: generator bug: CPython's trace is the same without the operation"
  let ours ← SemDiff.runOurs file
  if let some bug := generatorBug? c theirs ours then return .error bug
  let called ← calledIn pythonCmd c
  -- Whether CPython's run gave a result in the operation (not an exception), for coverage.
  let result := match SemDiff.splitOutput theirs with
    | some (out, _) => (caseOutcome c.id out matches .ok .result)
    | none => false
  let reason := reasons.get? c.id
  let pin := knownDir / s!"{c.id}{knownSuffix}"
  let known ← match reason with
    | none => pure none
    | some r =>
      if update then pure (some ⟨r, none⟩)
      else if ← pin.pathExists then pure (some ⟨r, some (← IO.FS.readFile pin)⟩)
      else return .error s!"{c.id}: missing {pin}; run with SEM_UPDATE=1"
  match SemDiff.judge c.id ours theirs known, ours with
  | .error e, _ => return .error e
  | .ok v@(.known _), .trace t =>
    return .ok (⟨c.id, v⟩, if update then some t else none, called, result)
  | .ok v, _ => return .ok (⟨c.id, v⟩, none, called, result)

/-- Compare `text` with the file `path`, or write it in update mode. -/
private meta def checkFile (path : System.FilePath) (text : String) (update : Bool) :
    IO (Option String) := do
  if update then
    IO.FS.writeFile path text
    return none
  let old ← if ← path.pathExists then IO.FS.readFile path else pure ""
  return if old == text then none else
    some s!"{path} differs from this run; run with SEM_UPDATE=1 after checking the change"

#eval show IO Unit from do
  if let some skip ← IO.getEnv "SKIP_PYTHON_TESTS" then
    if !skip.isEmpty then return
  unless ← SemDiff.pydynPath.pathExists do
    throw <| .userError s!"{SemDiff.pydynPath} is missing: build it with `lake build pydyn`"
  let start ← IO.monoMsNow
  let pythonCmd ← StrataPython.findPython3 (minVersion := 12) (maxVersion := 12)
  let update := (← IO.getEnv "SEM_UPDATE").isSome
  let script := here / "grid.py"
  let lines ← TraceSource.programsOf pythonCmd script #[outDir.toString]
  let cases ← IO.ofExcept (parseCases ("\n".intercalate lines.toList))
  let pinned ← TraceSource.readPinned (here / "grid_expected.txt")
  let reasons : Std.HashMap String String := pinned.foldl (init := {}) fun m e =>
    match e.verdict with | .known r => m.insert e.path r | _ => m
  let mut failures : Array String := #[]
  let digest := String.intercalate "" (← TraceSource.programsOf pythonCmd script
    #["--digest", outDir.toString]).toList ++ "\n"
  IO.FS.createDirAll knownDir
  let results ← TraceSource.mapBounded 8 cases (runCase pythonCmd update reasons)
  let mut now : Array Entry := #[]
  let mut pins : Array (String × String) := #[]
  let mut calls : Std.HashMap String (List String × Bool) := {}
  for r in results do
    match r with
    | .ok (e, pin, called, result) =>
      now := now.push e
      calls := calls.insert e.path (called, result)
      if let some t := pin then pins := pins.push (e.path, t)
    | .error msg => failures := failures.push msg
  -- The coverage check, from the runs.
  let templates := (cases.map (·.template)).toList.eraseDups.toArray
  let some nullDyn ← dynOf (outDir / "templates" / "null.py")
    | throw <| .userError "the translator rejects templates/null.py"
  let insns ← TraceSource.mapBounded 8 templates (insnsOf (insnNames nullDyn))
  let insnsByTemplate : Std.HashMap String (List String) :=
    (templates.zip insns).foldl (fun m (t, i) => m.insert t i) {}
  let verdictOf : Std.HashMap String Verdict := now.foldl (fun m e => m.insert e.path e.verdict) {}
  let evidence := cases.map fun c =>
    let (called, result) := calls.getD c.id ([], false)
    ({ case := c, counted := counts (verdictOf.get? c.id), result, called,
       insns := insnsByTemplate.getD c.template [] } : Evidence)
  -- The instructions of the program around every operation count once any case agrees.
  let scaffoldFile := outDir / "templates" / "scaffold.py"
  let sc ← IO.Process.output
    { cmd := SemDiff.pydynPath.toString, args := #["dyn", scaffoldFile.toString] }
  unless sc.exitCode == 0 do
    throw <| .userError s!"the translator rejects templates/scaffold.py:\n{sc.stdout}"
  let scaffoldCase : Case := { id := "scaffold", group := "", axis := "scaffold", expect := .result }
  let evidence := evidence.push
    { case := scaffoldCase, counted := evidence.any (·.counted), result := true, called := [],
      insns := insnNames sc.stdout, cells := false }
  let notCovered ← IO.ofExcept (parseNotCovered (← IO.FS.readFile (here / "not_covered.txt")))
  let cov := coverage requiredNames evidence notCovered
  if failures.isEmpty then
    failures := failures ++ cov.failures
  unless update do
    for f in ← knownDir.readDir do
      let n := (f.fileName.dropEnd knownSuffix.length).toString
      unless reasons.contains n do
        failures := failures.push s!"{f.path}: pinned run for no known case"
  -- An update writes its files only when every case passed, so that the digest's property holds.
  if failures.isEmpty then
    if let some f ← checkFile (here / "grid_digest.txt") digest update then
      failures := failures.push f
    for ch in ← Diff.checkOrUpdate (here / "grid_expected.txt") now update do
      failures := failures.push ch.render
    -- The names that only the catalog's declared entries cover, each with the cases that declare
    -- it, so that a declaration that no run backs is visible here.
    let entryOnly := s!"covered only by the catalog's entries | {cov.byEntriesOnly.size} names\n" ++
      String.join (cov.byEntriesOnly.toList.map fun (n, ids) =>
        s!"  {n} | declared by {declaredBy ids}\n")
    if let some f ← checkFile (here / "grid_summary.txt") (summary cases now ++ entryOnly) update then
      failures := failures.push f
    if update then
      for f in ← knownDir.readDir do IO.FS.removeFile f.path
      for (id, t) in pins do IO.FS.writeFile (knownDir / s!"{id}{knownSuffix}") t
  -- The wall time, so that a build log shows what the grid costs.
  let secs := ((← IO.monoMsNow) - start) / 1000
  TraceSource.report s!"AxisGridTest ({secs} s)" now cases.size failures

end StrataPython.AxisGridTest
