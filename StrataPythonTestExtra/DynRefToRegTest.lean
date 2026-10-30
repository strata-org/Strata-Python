/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPython.Dyn.Env
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.Env.WF
meta import StrataDyn.RefToReg
meta import StrataDynTest.RefToRegSim
meta import StrataPythonTest.Dyn.TestUtil

/-! # Ref-to-reg on the translator goldens

Reads every `NAME.expected.dyn` in `StrataPythonTest/Dyn/dyn_tests/` against `Py.env`,
promotes its cells with `refToReg`, and checks:

* the pass succeeds, and its output is `NAME.expected.ssa.dyn`, byte for byte;
* the output reads back, and reprints the same;
* promoting the output again changes nothing;
* the number of promoted cells, the candidates left as cells, and the spoiled promotions that
  are not caught (see below), as `ref_to_reg.summary` lists them;
* the functions that reach their frame's locals and promote a cell are those of
  `expectedUnsound`;
* every `.ssa.dyn` golden belongs to a translator golden;
* every edge of the check's walk agrees with its target's start map on the cells the target
  doesn't carry, and no start map holds its block's own parameter for an inherited cell
  (`RefToRegSim.edgesAgree`);
* each function and its promoted form run the same along random paths and along one path per
  edge of the top-level blocks, and a spoiled promotion is caught (`RefToRegSim`).

No Python is needed.  Set `DYN_UPDATE=1` to rewrite the `.ssa.dyn` goldens and the
summary. -/

namespace StrataPython.DynRefToRegTest

open Strata.Dyn
open StrataPython.Dyn
open StrataPython.Dyn.TestUtil (firstDiff)

/-- The directory holding the goldens. -/
private meta def testDir : System.FilePath := "StrataPythonTest" / "Dyn" / "dyn_tests"

/-- The suffix of a translator golden. -/
private meta def goldenSuffix : String := ".expected.dyn"

/-- The suffix of a ref-to-reg golden. -/
private meta def ssaSuffix : String := ".expected.ssa.dyn"

/-- The summary of the run, `ref_to_reg.summary`. -/
private meta def summaryPath : System.FilePath := testDir / "ref_to_reg.summary"

/-- The names through which a Python function reaches its frame's locals without being given
their cells: builtins it calls, and attributes of frame objects. -/
private meta def frameNames : List String :=
  ["locals", "vars", "dir", "eval", "exec", "breakpoint", "set_trace", "_getframe",
   "_current_frames", "currentframe", "settrace", "setprofile", "f_locals", "f_back", "tb_frame",
   "gi_frame", "cr_frame", "ag_frame"]

/-- Whether the function `name` of the printed module `text` names one of `frameNames`.  The
printer writes a name such as `m.<lambda>` between bars. -/
private meta def reachesFrame (text name : String) : Bool :=
  (text.splitOn "\n  func @").any fun part =>
    (part.startsWith (name ++ "(") || part.startsWith ("|" ++ name ++ "|(")) &&
      frameNames.any fun n => (part.splitOn s!"\"{n}\"").length > 1

/-- The functions, `file: function`, whose promotion is wrong: they reach their frame's locals
through a call that is given no cells (`vars()`, `locals()`), so the pass's rule that an
operation reaches only the cells it is given doesn't hold (`docs/Dyn.md`, §3).  A planned
admission pass is to reject them before ref-to-reg runs. -/
private meta def expectedUnsound : List String := [
  "p18_builtins.expected.dyn: p18_builtins.f",
  "rr03_frame_lambda.expected.dyn: rr03_frame_lambda.<lambda>"]

/-- What one golden gives: the number of promoted cells, the candidates left, the number of
functions with a removed read, the functions whose spoiled promotion is not caught, and the
functions that reach their frame's locals and promote a cell; or what is wrong.  Each function
and its promoted form run side by side (`RefToRegSim.sameRuns`), and must not differ.  Then the
promotion is spoiled: the first removed read (in the order of ids) is replaced by another
value, and the runs must differ. -/
private meta def check (update : Bool) (path : System.FilePath) :
    IO (Except String (Nat × List String × Nat × List String × List String)) := do
  let golden ← IO.FS.readFile path
  match ← Module.read Py.env golden path.toString with
  | .error e => return .error s!"{path}: does not read:\n{e}"
  | .ok m =>
    let mut promoted := 0
    let mut left := []
    let mut spoilable := 0
    let mut uncaught := []
    let mut promoting := []
    for f in m.raw.funcs do
      let fnName := s!"{path.fileName.getD ""}: {ToDDM.nameText f.name}"
      match RefToReg.planOf f with
      | .error e => return .error s!"{path}: {ToDDM.nameText f.name}: {e}"
      | .ok P =>
        let .ok S := do P.starts (← RefToReg.trees f) f
          | return .error s!"{path}: {ToDDM.nameText f.name}: the plan has no start maps"
        let f' := P.apply S.maps f
        if let some d := RefToRegSim.edgesAgree P S f then
          return .error s!"{path}: {ToDDM.nameText f.name}: {d}"
        if let some d := RefToRegSim.sameRuns P f f' 7 50 400 then
          return .error s!"{path}: {ToDDM.nameText f.name}: the promoted form differs: {d}"
        -- The removed read with the least id.
        let first := P.sigma.fold (init := none) fun acc r u =>
          match acc with
          | some (r₀, _) => if r.id < r₀.id then some (r, u) else acc
          | none => some (r, u)
        if let some (r, u) := first then
          let other : ValId := ⟨if u.id == 0 then 1 else 0⟩
          let spoilt := { P with sigma := P.sigma.insert r other }
          spoilable := spoilable + 1
          -- A spoiled plan whose start maps fail is caught too.
          if let .ok f₂ := spoilt.applyFor f then
            if (RefToRegSim.sameRuns P f f₂ 7 50 400).isNone then
              uncaught := uncaught ++ [fnName]
        promoted := promoted + P.promoted.size
        if P.promoted.size > 0 && reachesFrame golden (ToDDM.nameText f.name) then
          promoting := promoting ++ [fnName]
        left := left ++ (P.left f).map fun c =>
          s!"{fnName}: {ToDDM.nameText (f.names[c.id]?.getD .base)}"
    match refToReg m with
    | .error es =>
      return .error s!"{path}: {es.toList.map fun (n, e) => s!"{ToDDM.nameText n}: {e}"}"
    | .ok m₁ =>
      let out := toString m₁ ++ "\n"
      let ssa := path.toString.dropEnd goldenSuffix.length |>.toString |>.append ssaSuffix
      if update then IO.FS.writeFile ssa out
      else
        unless ← System.FilePath.pathExists ssa do
          return .error s!"{ssa}: missing; run with DYN_UPDATE=1"
        let expected ← IO.FS.readFile ssa
        if let some d := firstDiff out expected then
          return .error s!"{ssa}: differs at {d}"
      match ← Module.read Py.env out ssa with
      | .error e => return .error s!"{ssa}: does not read back:\n{e}"
      | .ok m₂ =>
        if let some d := firstDiff (toString m₂ ++ "\n") out then
          return .error s!"{ssa}: reprints differently at {d}"
        match refToReg m₁ with
        | .error _ => return .error s!"{ssa}: promoting it again fails"
        | .ok m₃ =>
          if let some d := firstDiff (toString m₃ ++ "\n") out then
            return .error s!"{ssa}: promoting it again changes it at {d}"
          return .ok (promoted, left, spoilable, uncaught, promoting)

#eval show IO Unit from do
  let update := (← IO.getEnv "DYN_UPDATE").isSome
  let goldens := (← testDir.readDir).filter (·.fileName.endsWith goldenSuffix)
  let goldens := goldens.qsort (·.fileName < ·.fileName)
  let mut failures := #[]
  -- Every ref-to-reg golden belongs to a translator golden.
  for f in ← testDir.readDir do
    if f.fileName.endsWith ssaSuffix then
      let stem := (f.fileName.dropEnd ssaSuffix.length).toString
      unless goldens.any (·.fileName == stem ++ goldenSuffix) do
        if update then IO.FS.removeFile f.path
        else failures := failures.push s!"{f.path}: belongs to no translator golden"
  let mut promoted := 0
  let mut left := []
  let mut spoilable := 0
  let mut uncaught := []
  let mut promoting := []
  for g in goldens do
    match ← check update g.path with
    | .error msg => failures := failures.push msg
    | .ok (n, l, sp, u, pr) =>
      promoted := promoted + n; left := left ++ l; spoilable := spoilable + sp
      uncaught := uncaught ++ u; promoting := promoting ++ pr
  IO.println s!"DynRefToRegTest: {goldens.size - failures.size}/{goldens.size} promoted, \
    {promoted} cells"
  -- A spoiled promotion replaces a function's first removed read (in the order of ids) by
  -- another value; one that is not caught is on a path that no run reaches.
  let summary := s!"promoted cells: {promoted}\n\
    functions with a removed read: {spoilable}\n\
    candidates left as cells:\n{String.join (left.map (s!"  {·}\n"))}\
    spoiled promotions not caught:\n{String.join (uncaught.map (s!"  {·}\n"))}"
  if update then IO.FS.writeFile summaryPath summary
  else if failures.isEmpty then
    let expected ← IO.FS.readFile summaryPath
    if let some d := firstDiff summary expected then
      failures := failures.push s!"{summaryPath}: differs at {d}; run with DYN_UPDATE=1"
  if promoting != expectedUnsound then
    failures := failures.push s!"the functions that reach their frame's locals and promote a \
      cell are:\n{"\n".intercalate promoting}"
  if !failures.isEmpty then
    for f in failures do IO.println f
    throw <| IO.userError s!"DynRefToRegTest: {failures.size} failure(s)"

end StrataPython.DynRefToRegTest
