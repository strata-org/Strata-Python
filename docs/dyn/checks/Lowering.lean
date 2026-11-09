/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Examples.While.Run
public import StrataDyn.DDM
import StrataDyn.Env.WF
meta import StrataDyn.Examples.While.Run
meta import StrataDyn.DDM
meta import StrataDyn.Env.WF
meta import StrataDDM.Elab
meta import Lean.Data.Json

/-!
The guide's printed modules and outcomes, made by While's lowering and runs.  The two programs
of `data/`, `mean.while` and `mean-region.while`, are parsed with the While dialect, as `#while`
parses the text it encloses, lowered with `lower`, and printed folded and in full; each print
must equal its file of `data/` byte for byte.  Each run that `data/outcomes.json` lists, the interpreter
panel's expected outcomes, must give its result and printed output.  `checks/run.sh` elaborates
this file from the package root, so the paths below are relative to it.  A missing file, a parse
error, a lowering error, a print that differs or an outcome that differs is an error.
-/

namespace Strata.Dyn.Guide

open Strata.Dyn.While Strata.Dyn.Exec

/-- The directory of the guide's data, from the package root. -/
meta def dataDir : System.FilePath := "docs" / "dyn" / "data"

/-- The contents of the data file `name`, or an error if it is missing. -/
meta def readData (name : String) : IO String := do
  let path := dataDir / name
  unless ← path.pathExists do
    throw <| IO.userError s!"{path} is missing: run this check from the package root"
  IO.FS.readFile path

/-- The While dialect, loaded for parsing, as the reader loads Dyn's. -/
meta def whileDialects : Except String StrataDDM.Elab.LoadedDialects := do
  let ds := Ast.While_map.toList.toArray
  return { dialects := Ast.While_map,
           dialectParsers := ← StrataDDM.Elab.DialectParsers.ofDialects ds,
           syntaxElabMap := ← StrataDDM.Elab.SyntaxElabMap.ofDialects ds }

/-- The While program in the data file `name`, parsed as `#while` parses its text. -/
meta def parseData (name : String) : IO Ast.Program := do
  let text ← readData name
  let loaded ← IO.ofExcept whileDialects
  if h : "While" ∈ loaded.dialects then
    let input := Lean.Parser.mkInputContext text (dataDir / name).toString
    match StrataDDM.Elab.elabProgramRest loaded (← Lean.mkEmptyEnvironment 0) input "While" h 0
        input.endPos with
    | .error msgs =>
      let msgs ← msgs.mapM fun m => do return s!"{m.pos.line}:{m.pos.column}: {← m.data.toString}"
      throw <| IO.userError s!"{name} does not parse:\n{"\n".intercalate msgs.toList}"
    | .ok pgm =>
      pgm.commands.mapM fun op => IO.ofExcept <| (Ast.Command.ofAst op).mapError (s!"{name}: " ++ ·)
  else
    throw <| IO.userError "the While dialect is not loaded"

/-- The first line where `got` and `want` differ, both shown, or `none` if they are equal. -/
meta def firstDiff (got want : String) : Option String :=
  if got == want then none else
  let gs := got.splitOn "\n"
  let ws := want.splitOn "\n"
  let i := ((gs.zip ws).findIdx? fun (g, w) => g != w).getD (min gs.length ws.length)
  some s!"line {i + 1}:\n  lowering prints: {(gs[i]?).getD "(end of text)"}\n  \
    file holds:      {(ws[i]?).getD "(end of text)"}"

/-- Lower the program in `source`, and compare its folded and full prints with the files
`folded` and `full`.  The errors, one per print that differs. -/
meta def checkLowering (source folded full : String) : IO (Array String) := do
  let m ← IO.ofExcept <| (lower (← parseData source)).mapError (s!"{source} does not lower: " ++ ·)
  let mut errs := #[]
  for (file, got) in [(folded, m.format), (full, m.raw.format .full)] do
    if let some d := firstDiff got (← readData file) then
      errs := errs.push s!"{file} is not what lowering {source} prints, at {d}"
  return errs

/-- How a run of `source`'s function `entry` on `args` ends, as the interpreter panel shows it:
its result, read as an `Except Int Int`, and its printed output. -/
meta def runData (source entry : String) (args : Array Int) : IO (String × String) := do
  let m ← IO.ofExcept <| (lower (← parseData source)).mapError (s!"{source} does not lower: " ++ ·)
  let o := runModule WhileSem.model m (.str .base entry) (args.map (WhileSem.model.arg ·)) 100000
  let r := match o.read? (Except Int Int) with
    | some (.ok v) => s!"ok {v}"
    | some (.error e) => s!"error {e}"
    | none => "not an Except Int Int"
  return (r, s!"{o.snapshot.world.out.items}")

/-- Run each entry of `outcomes.json` on the program of `mean.while`, and compare its result and
output with the entry's.  The errors, one per entry that differs. -/
meta def checkOutcomes : IO (Array String) := do
  let json ← IO.ofExcept (Lean.Json.parse (← readData "outcomes.json"))
  let entries ← IO.ofExcept (json.getArr?)
  let mut errs := #[]
  for j in entries do
    let entry ← IO.ofExcept (j.getObjValAs? String "entry")
    let args ← IO.ofExcept (j.getObjValAs? (Array Int) "args")
    let expected ← IO.ofExcept (j.getObjValAs? String "expected")
    let printed ← IO.ofExcept (j.getObjValAs? String "printed")
    let (r, out) ← runData "mean.while" entry args
    unless r == expected && out == printed do
      errs := errs.push s!"outcomes.json: {entry} {args} gives {r}, printed {out}, but the \
        file says {expected}, printed {printed}"
  return errs

#eval show IO Unit from do
  let errs := (← checkLowering "mean.while" "mean.folded.dyn" "mean.full.dyn") ++
    (← checkLowering "mean-region.while" "mean-region.folded.dyn" "mean-region.full.dyn") ++
    (← checkOutcomes)
  unless errs.isEmpty do throw <| IO.userError ("\n".intercalate errs.toList)

end Strata.Dyn.Guide
