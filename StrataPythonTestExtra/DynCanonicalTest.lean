/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.Dyn.Env
meta import StrataPython.Dyn.Canonical
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.Env.WF
meta import StrataPythonTest.Dyn.TestUtil

/-! # The canonical form of the example programs

Reads the translator golden of each example program `g01` to `g06`, each of which exercises some
properties of the canonical form, puts it in Python's canonical form with `PyCanonical.runModule`,
checks the result again with `PyCanonical.checkModule`, and compares the module printed with its
golden `NAME.expected.canonical`.  With
`CANON_UPDATE=1`, it writes the goldens instead.  No Python is needed. -/

namespace StrataPython.DynCanonicalTest

open Strata.Dyn
open StrataPython.Dyn
open StrataPython.Dyn.TestUtil (firstDiff)

/-- The directory holding the goldens. -/
private meta def testDir : System.FilePath := "StrataPythonTest" / "Dyn" / "dyn_tests"

/-- The example programs: the `.py` files whose name starts with `g` and a digit, sorted by
name. -/
private meta def programs : IO (List String) := do
  let names := (← testDir.readDir).filterMap fun e =>
    let n := e.fileName
    if n.endsWith ".py" && n.startsWith "g" && ((n.toList[1]?).any Char.isDigit) then
      e.path.fileStem else none
  return names.toList.mergeSort (· ≤ ·)

/-- The canonical form of `name`'s translator golden, printed, or why there is none. -/
private meta def canonical (name : String) : IO (Except String String) := do
  let path := testDir / s!"{name}.expected.dyn"
  match ← Module.read Py.env (← IO.FS.readFile path) path.toString with
  | .error e => return .error s!"{path}: does not read back:\n{e}"
  | .ok m =>
    match PyCanonical.runModule m with
    | .error fs => return .error s!"{path}: not put in canonical form: {fs.map toString}"
    | .ok cm =>
      match PyCanonical.checkModule cm.canonical.module with
      | .error fs => return .error s!"{path}: its canonical form fails the check: {fs.map toString}"
      | .ok cm' => return .ok (toString cm'.canonical.module)

#eval show IO Unit from do
  let update := (← IO.getEnv "CANON_UPDATE") == some "1"
  let programs ← programs
  let mut failures := #[]
  for name in programs do
    let golden := testDir / s!"{name}.expected.canonical"
    match ← canonical name with
    | .error e => failures := failures.push e
    | .ok text =>
      if update then IO.FS.writeFile golden text
      else if !(← golden.pathExists) then failures := failures.push s!"{golden}: missing"
      else if let some d := firstDiff text (← IO.FS.readFile golden) then
        failures := failures.push s!"{golden}: differs at {d}"
  -- `PyCanonical.checkModule` rejects g05's translator output, which the pass changes, and leaves
  -- it as it is: it never runs the pass.
  let path := testDir / "g05_tail_not_in_loop.expected.dyn"
  match ← Module.read Py.env (← IO.FS.readFile path) path.toString with
  | .error e => failures := failures.push s!"{path}: does not read back:\n{e}"
  | .ok m =>
    match PyCanonical.checkModule m with
    | .ok _ => failures := failures.push s!"{path}: passes the check before the pass"
    | .error fs =>
      let msgs := fs.toList.map toString
      unless msgs == ["g05_tail_not_in_loop.e: not canonical"] do
        failures := failures.push s!"{path}: rejected with {msgs}"
  -- In g05, the outer loop's latch is `then.0`, the block of `i += 1; continue`, which the pass
  -- leaves as it is.
  let path := testDir / "g05_tail_not_in_loop.expected.canonical"
  match ← Module.read Py.env (← IO.FS.readFile path) path.toString with
  | .error e => failures := failures.push s!"{path}: does not read back:\n{e}"
  | .ok m =>
    let roles := m.raw.funcs.toList.flatMap fun f =>
      (Body.loopRoles f.blocks.toList
          (((PyCanonical.records? f.info).getD []).map (·.head)).contains).map
        fun r => (ToDDM.nameText r.head.name, ToDDM.nameText r.preheader.name,
          r.latch.map (ToDDM.nameText ·.name))
    unless roles == [("head.0", "start.0", some "then.0"), ("head.1", "join.0", some "body.1")] do
      failures := failures.push s!"{path}: loop roles {roles}"
  -- In m_for, `first`'s loop always returns, so no back edge enters its head, but its record
  -- gives it its roles: its preheader, the start block, and no latch.
  let path := testDir / "m_for.expected.dyn"
  match ← Module.read Py.env (← IO.FS.readFile path) path.toString with
  | .error e => failures := failures.push s!"{path}: does not read back:\n{e}"
  | .ok m =>
    match PyCanonical.runModule m with
    | .error fs => failures := failures.push s!"{path}: not put in canonical form: {fs.map toString}"
    | .ok cm =>
      let roles := cm.canonical.module.raw.funcs.toList.flatMap fun f =>
        if ToDDM.nameText f.name != "m_for.first" then [] else
        (Body.loopRoles f.blocks.toList
            (((PyCanonical.records? f.info).getD []).map (·.head)).contains).map
          fun r => (ToDDM.nameText r.head.name, ToDDM.nameText r.preheader.name,
            r.latch.map (ToDDM.nameText ·.name))
      unless roles == [("head.0", "start.0", none)] do
        failures := failures.push s!"{path}: loop roles of first {roles}"
  -- In g06, `total`'s entry block binds the arguments with `py.bindArgs`, whose failure goes to
  -- `propagate.0` and on to `post.0`: a run whose binding fails reaches the end of `post.0`
  -- without passing `start.0`, where the precondition is assumed (F1).
  let path := testDir / "g06_function_contract.expected.canonical"
  match ← Module.read Py.env (← IO.FS.readFile path) path.toString with
  | .error e => failures := failures.push s!"{path}: does not read back:\n{e}"
  | .ok m =>
    let l (s : String) : Label := ⟨.num (.str .base s) 0⟩
    match m.raw.funcs.toList.find? (ToDDM.nameText ·.name == "g06_function_contract.total") with
    | none => failures := failures.push s!"{path}: no function total"
    | some f =>
      let bs := f.blocks.toList
      let postEnd : Option Point := (Body.blockAt? bs (l "post")).map Body.endOf
      unless postEnd.any (Body.reachAvoidB bs ⟨l "start", 0⟩ ·) do
        failures := failures.push s!"{path}: no run of total reaches the end of post.0 without \
          passing start.0"
  IO.println s!"DynCanonicalTest: {programs.length - failures.size}/{programs.length} \
    in canonical form as their goldens"
  if !failures.isEmpty then
    for f in failures do IO.println f
    throw <| IO.userError s!"DynCanonicalTest: {failures.size} failure(s)"

end StrataPython.DynCanonicalTest
