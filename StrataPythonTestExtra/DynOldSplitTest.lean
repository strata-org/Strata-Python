/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPython
meta import StrataPython.Dyn.Markers
meta import StrataPythonTest.Util.ExprText
meta import StrataPython.ReadPython
meta import StrataDDM.Util.IO
meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Dyn.TestUtil

/-! # The old parts of loop invariants

Runs `PyMarkers.splitOld` on each expression of `StrataPythonTest/Dyn/old_split_cases.py` (one
`e = …` per line) and compares the results with `old_split_cases.expected`: each case's source,
then the expression with its old parts written `OLD(…)`. Set `OLDSPLIT_UPDATE=1` to rewrite the
file. -/

namespace StrataPython.DynOldSplitTest

open StrataPython
open StrataPython (withPython)
open StrataPython.Dyn.TestUtil (compilePython)

private meta def cases : System.FilePath := "StrataPythonTest" / "Dyn" / "old_split_cases.py"

private meta def golden : System.FilePath := "StrataPythonTest" / "Dyn" / "old_split_cases.expected"

#eval withPython fun pythonCmd => IO.FS.withTempDir fun tmpDir => do
  let src ← IO.FS.readFile cases
  let ionPath ← compilePython pythonCmd cases tmpDir
  let bytes ← StrataDDM.Util.readBinInputSource ionPath.toString
  let .ok stmts := StrataPython.readPythonStrataBytes ionPath.toString bytes
    | throw <| IO.userError "DynOldSplitTest: can't read the cases"
  let mut out := ""
  for s in stmts do
    match s with
    | .Assign _ _ v _ =>
      out := out ++ s!"{String.Pos.Raw.extract src v.ann.start v.ann.stop}\n    => {StrataPython.Dyn.ExprText.exprText src (StrataPython.Dyn.PyMarkers.splitOld v)}\n"
    | _ => pure ()
  if (← IO.getEnv "OLDSPLIT_UPDATE").isSome then
    IO.FS.writeFile golden out
  else if out != (← IO.FS.readFile golden) then
    throw <| IO.userError s!"DynOldSplitTest: the old parts differ from {golden}:\n{out}"
  IO.println s!"DynOldSplitTest: {(out.splitOn "\n    => ").length - 1} cases"

end StrataPython.DynOldSplitTest
