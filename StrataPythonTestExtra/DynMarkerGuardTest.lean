/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Ion
meta import StrataPython.ReadPython
meta import StrataPython.Dyn.Translate
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataPython.Dyn.Sem.Run
meta import StrataPythonTest.Util.Python

/-! # The marker guard on the machine

Before a loop with invariants, the translation reads `loop_invariant` for each marker statement, and
the run stops with a gap unless it is the marker `pyhard.loop_invariant` (`docs/PythonToDyn.md`
§6.11). No program that the translator accepts changes the name in a way that the Python semantics
runs, so this test edits the printed translation of `li_while` (a loop in a function) and
`li_module_level` (a loop at module level), reads it back and runs it:

* `none`: after the import's write of `loop_invariant`, a second write stores `None`. CPython's
  call then raises `TypeError`; the run stops with the guard's gap, so the dropped call is never
  taken as PyHard's. This also shows that the guard reads the current global, not the import's
  result.
* `OLD`: the import reads `OLD`, a marker but the wrong one: the guard's gap.
* `between` (li_while, which has two marker statements): `None` is written after the first
  statement's guard holds: the second statement's guard reads the name again and stops with the
  gap.
* `unbound`: the second write unbinds the name. The guard's read raises `NameError`, as CPython's
  call does.

Each case pins the trace's lines between the program's output and its globals. -/

namespace StrataPython.DynMarkerGuardTest

open StrataPython (withPython)
open Strata.Dyn StrataPython.Dyn

private meta def testDir : System.FilePath := "StrataPythonTest" / "Dyn" / "dyn_tests"

/-- The printed translation of `name` as module `__main__`. -/
private meta def translated (python : System.FilePath) (name : String) : IO String := do
  let pyFile := testDir / s!"{name}.py"
  let stmts ← IO.FS.withTempFile fun _ dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    match ← (StrataPython.pythonToStrata dialectFile pyFile python.toString).toBaseIO with
    | .ok s => pure s
    | .error m => throw <| .userError s!"{pyFile}: {m}"
  let r := StrataPython.Dyn.PyTranslate.translate "__main__" stmts
  unless r.ok do throw <| .userError s!"{pyFile}: the translator rejects it"
  return r.module.format {}

/-- The import's write of `loop_invariant` at module level. -/
private meta def importWrite : String :=
  "base.refSet[py.Value](%loop_invariant.cell.0, %loop_invariant.0)\n"

/-- `text` with `new` written to `loop_invariant`'s global cell right after the import's write. -/
private meta def rewrite (text new : String) : Except String String := do
  let parts := text.splitOn importWrite
  unless parts.length == 2 do throw "not exactly one import write of loop_invariant"
  let indent := "      "
  return parts[0]! ++ importWrite ++ indent ++ s!"%testVal.0 : py.Value = {new}\n" ++ indent ++
    "%testSet.0 : base.Unit = base.refSet[py.Value](%loop_invariant.cell.0, %testVal.0)\n" ++
    parts[1]!

/-- `text` with `None` written to the global `loop_invariant` at the start of the first guard's
true branch, `guarded.0`, so that only the second guard sees it; `none` without a second guard. -/
private meta def betweenGuards (text : String) : Option String :=
  let label := "    guarded.0():\n"
  if (text.splitOn "py.isMarker(").length < 3 then none else
  match text.splitOn label with
  | [pre, post] => some (pre ++ label ++
      "      %testCell.0 : base.Ref(py.Value) = py.globalCell(\"__main__\", \"loop_invariant\")\n" ++
      "      %testVal.1 : py.Value = py.noneLit()\n" ++
      "      %testSet.1 : base.Unit = base.refSet[py.Value](%testCell.0, %testVal.1)\n" ++ post)
  | _ => none

/-- The edits of the test: a name and the edited text. -/
private meta def cases (text : String) : Except String (List (String × String)) := do
  let importLi := "py.importFrom(\"pyhard\", \"loop_invariant\")"
  unless (text.splitOn importLi).length == 2 do throw "not exactly one import of loop_invariant"
  return [("none", ← rewrite text "py.noneLit()"),
    ("OLD", text.replace importLi "py.importFrom(\"pyhard\", \"OLD\")"),
    ("unbound", ← rewrite text "py.undef(\"loop_invariant\")")] ++
    (match betweenGuards text with | some t => [("between", t)] | none => [])

/-- The lines of `trace` after the program's output and before `--- globals`. -/
private meta def outcomeOf (trace : String) : List String :=
  let lines := trace.splitOn "\n"
  let afterOut := (lines.dropWhile (!·.startsWith "--- stdout ")).drop 1
  let afterOut := afterOut.dropWhile fun l =>
    !(l.startsWith "--- outcome" || l.startsWith "--- fault" || l.startsWith "--- gap")
  afterOut.takeWhile (!·.startsWith "--- globals")
    |>.filter (!·.isEmpty)

/-- What each case of each program must give. -/
private meta def expected : List (String × String × List String) :=
  let gap := ["--- gap a call of a loop_invariant other than PyHard's is not modelled yet"]
  let nameError := ["--- outcome", "raised NameError: name 'loop_invariant' is not defined"]
  [("li_while", "none", gap), ("li_while", "OLD", gap), ("li_while", "unbound", nameError),
   ("li_while", "between", gap),
   ("li_module_level", "none", gap), ("li_module_level", "OLD", gap),
   ("li_module_level", "unbound", nameError)]

#eval withPython fun python => do
  let mut failures : Array String := #[]
  let mut ran := 0
  for name in ["li_while", "li_module_level"] do
    let text ← translated python name
    for (c, edited) in ← IO.ofExcept (cases text) do
      let m ← match ← Module.read Py.env edited s!"{name}-{c}.dyn" with
        | .ok m => pure m
        | .error e => throw <| IO.userError s!"{name} {c}: the edited module doesn't read: {e}"
      let got := outcomeOf (StrataPython.Dyn.Sem.runModuleThen m
        (.str (.str .base "__main__") "<module>") "__main__" [])
      ran := ran + 1
      let want := (expected.find? fun (n, k, _) => n == name && k == c).map (·.2.2)
      unless want == some got do
        failures := failures.push s!"{name} {c}: got {got}, expected {want}"
  unless ran == expected.length do
    failures := failures.push s!"ran {ran} cases, but {expected.length} are expected"
  IO.println s!"DynMarkerGuardTest: {ran} cases"
  unless failures.isEmpty do
    for f in failures do IO.println f
    throw <| IO.userError s!"DynMarkerGuardTest: {failures.size} failure(s)"

end StrataPython.DynMarkerGuardTest
