/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.Dyn.PySpec.Load
meta import StrataDyn.DDM
meta import StrataPythonTest.Util.Python

/-! # The translation from PySpec against the hand-written models

`StrataPythonTest/Dyn/contract_models/` holds models written by hand by the rules of
`docs/PythonToDyn.md` §12, seven of them for PySpec fixtures (§12.12). For each of those
seven, this test translates the fixture with `PySpec.translateModels` and compares each extern
of the hand-written model with ours: its `requires` messages, its `free ensures` messages, and
the location operation of each frame region. The names of values and blocks, and the shape of
the code inside a clause, may differ. Every difference is pinned below. The test needs Python,
as `withPython` finds it.
-/

namespace StrataPython.ContractAgreementTest

open StrataPython.Dyn.PySpec
open StrataPython (withPython)

/-- What a contract of an extern says, as text. -/
private structure Summary where
  requires : Array String := #[]
  ensures : Array String := #[]
  /-- The location operation of each frame region, or `none` for an extern without a frame. -/
  writes : Option (Array String) := none
deriving BEq, Repr

/-- The quoted message of a clause line, such as `requires "m" {`. -/
private meta def quoted (line : String) : String :=
  match line.splitOn "\"" with
  | _ :: m :: _ => m
  | _ => line

/-- Each extern of the printed module `text`, by its name within the module, with what its
contract says. -/
private meta def externs (text : String) : Array (String × Summary) := Id.run do
  let mut out : Array (String × Summary) := #[]
  let mut cur : Option (String × Summary) := none
  let mut pre := ""
  for line in text.splitOn "\n" do
    if line.startsWith "module " then
      pre := ((line.drop "module ".length).toString.splitOn " ").head! ++ "."
    if line.startsWith "  extern func @" || line.startsWith "  func " || line == "}" then
      if let some c := cur then out := out.push c
      cur := none
      if line.startsWith "  extern func @" then
        let name := ((line.drop "  extern func @".length).toString.splitOn "(").head!
        cur := some ((name.drop pre.length).toString, {})
      continue
    let some (n, s) := cur | continue
    let t := line.trimAscii.toString
    if t.startsWith "requires \"" then cur := some (n, { s with requires := s.requires.push (quoted t) })
    else if t.startsWith "free ensures \"" then
      cur := some (n, { s with ensures := s.ensures.push (quoted t) })
    else if t.startsWith "writes(" then cur := some (n, { s with writes := some #[] })
    else if t.startsWith "%l." && (t.splitOn " : base.Loc = ").length == 2 then
      let op := (((t.splitOn " : base.Loc = ")[1]!).splitOn "(").head!
      cur := some (n, { s with writes := (s.writes.getD #[]).push op })
  if let some c := cur then out := out.push c
  return out

/-- The lines of a hand-written model without its comment lines. -/
private meta def stripComments (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").filter (!·.trimAscii.toString.startsWith "--"))

/-- The differences between the hand-written model `file` and our translation of `module`
under `searchPath`. -/
private meta def compare (pythonCmd : String) (file searchPath module : String) :
    IO (Array String) := do
  let hand := externs (stripComments (← IO.FS.readFile
    (System.FilePath.mk "StrataPythonTest" / "Dyn" / "contract_models" / file)))
  let some mod := StrataPython.ModuleName.ofString? module | return #[s!"{module}: not a name"]
  let (path, _) ← IO.ofExcept (← (mod.findInPath searchPath).toBaseIO)
  let (set, _) ← loadModels pythonCmd searchPath path module
  match translateModels set with
  | .error rs => return #[s!"ours rejects the set: {(rs.map (·.rule)).toList.eraseDups}"]
  | .ok mods =>
    let some m := mods.find? (Strata.Dyn.Build.nameText ·.raw.name == module)
      | return #[s!"ours has no module {module}"]
    let ours := externs m.format
    let mut out := #[]
    for (n, h) in hand do
      match ours.find? (·.1 == n) with
      | none => out := out.push s!"{n}: only in the hand-written model"
      | some (_, o) =>
        if h.requires != o.requires then
          out := out.push s!"{n}: requires: hand {h.requires}, ours {o.requires}"
        if h.ensures != o.ensures then
          out := out.push s!"{n}: ensures: hand {h.ensures}, ours {o.ensures}"
        if h.writes != o.writes then
          out := out.push s!"{n}: writes: hand {h.writes}, ours {o.writes}"
    for (n, _) in ours do
      unless hand.any (·.1 == n) do out := out.push s!"{n}: only in ours"
    return out

/-- The seven hand-written models of PySpec fixtures. -/
private meta def pairs : List (String × String × String) :=
  [("admitted.dyn", "StrataPythonTestExtra/Specs/dispatch_test", "servicelib.Admitted"),
   ("dispatch.dyn", "StrataPythonTestExtra/Specs/dispatch_test", "servicelib"),
   ("ghost_old.dyn", "StrataPythonTestExtra/Specs/dispatch_test", "servicelib.GhostOld"),
   ("storage.dyn", "StrataPythonTestExtra/Specs/dispatch_test", "servicelib.Storage"),
   ("init_contract.dyn", "StrataPythonTestExtra/Specs", "native_cases.init_contract"),
   ("invariant.dyn", "StrataPythonTestExtra/Specs",
    "native_cases.class_invariant_with_method_contract"),
   ("modifies_self.dyn", "StrataPythonTestExtra/Specs", "native_cases.modifies_self")]

private meta def runAll : IO Unit := withPython fun pythonCmd => do
  for (file, sp, module) in pairs do
    let diffs ← compare (toString pythonCmd) file sp module
    if diffs.isEmpty then IO.println s!"{file}: agrees"
    else for d in diffs do IO.println s!"{file}: {d}"

-- In `init_contract`, `assert n <= 3` comes after an assignment that PySpec skips, so PySpec
-- records it as dropped and the translation rejects the model; the hand-written model keeps it.
-- Rejecting is stricter, so it is sound.
/--
info: admitted.dyn: agrees
dispatch.dyn: agrees
ghost_old.dyn: agrees
storage.dyn: agrees
init_contract.dyn: ours rejects the set: [dropped-clause]
invariant.dyn: agrees
modifies_self.dyn: agrees
-/
#guard_msgs in
#eval runAll

end StrataPython.ContractAgreementTest
