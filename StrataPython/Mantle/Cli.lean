/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Cli.Framework
import StrataDDM.Ion
import StrataPython.ReadPython
import StrataPython.Mantle.Translate
import StrataMantle.DDM
import StrataMantle.Env.WF

/-! # The `mantle` command

`mantle FILE` translates a Python program with `PyTranslate.translate` and prints its
diagnostics, then its module.

* `FILE.py` is parsed with `python -m strata_python.gen`.  `PYTHON` selects the interpreter
  (default `python3`; the target is Python 3.12), from which `strata_python.gen` must be
  importable.  The module is named `FILE`.
* Any other file is read as a Python Ion file (`FILE.python.st.ion`).  Diagnostics carry line
  and column positions when `FILE.py` sits beside it, and byte offsets otherwise.

Exit status: 0 if the translation succeeded and the module is well formed, 1 if there are
diagnostics or ill-formed functions, 2 if `FILE` cannot be parsed or read.  A wrong argument
count is a usage error of the CLI framework, status 1. -/

public section

namespace StrataPython.Mantle.Cli

open StrataPython.Mantle.PyTranslate (translate formatDiagnostic illFormed nameText)

/-- The suffixes of a Python Ion file, longest first. -/
private def ionSuffixes : List String := [".python.st.ion", ".py.ion", ".st.ion", ".ion"]

/-- `path` without its Python Ion suffix. -/
private def ionStem (path : String) : String :=
  match ionSuffixes.find? (path.endsWith ·) with
  | some sfx => (path.dropEnd sfx.length).toString
  | none => path

/-- The statements of `path` and the source they came from, if it can be read. -/
private def load (path : String) :
    IO (Except String (Array (stmt StrataDDM.SourceRange) × Option String)) := do
  if path.endsWith ".py" then
    let pythonCmd := (← IO.getEnv "PYTHON").getD "python3"
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
      match ← (StrataPython.pythonToStrata dialectFile path pythonCmd).toBaseIO with
      | .ok s => return .ok (s, some (← IO.FS.readFile path))
      | .error m => return .error m
  else
    match ← (StrataPython.readPythonStrata path).toBaseIO with
    | .error m => return .error m
    | .ok s =>
      let src ← try pure (some (← IO.FS.readFile (ionStem path ++ ".py"))) catch _ => pure none
      return .ok (s, src)

/-- Translate and print `path`, returning the exit status. -/
def run (path : String) : IO UInt32 := do
  let moduleName :=
    if path.endsWith ".py" then (System.FilePath.mk path).fileStem.getD "main"
    else (System.FilePath.mk (ionStem path)).fileName.getD "main"
  let (stmts, src) ← match ← load path with
    | .ok r => pure r
    | .error m => IO.eprintln s!"pymantle mantle: {m}"; return 2
  let fileMap := src.map Lean.FileMap.ofString
  let r := translate moduleName stmts
  for d in r.diagnostics do IO.println (formatDiagnostic fileMap d)
  IO.println (toString r.module)
  let bad := illFormed r.module
  for f in bad do IO.eprintln s!"pymantle mantle: {nameText f} is not well formed"
  return if r.ok && bad.isEmpty then 0 else 1

/-- The `mantle` subcommand. -/
def mantleCommand : _root_.Command where
  name := "mantle"
  args := [ "file" ]
  help := "Translate a Python program (a .py file, or a Python Ion file) to Mantle and print \
    its diagnostics and module. Exit status: 0 if it translated and is well formed, 1 if \
    there are diagnostics or ill-formed functions, 2 on a parse error. PYTHON selects the \
    interpreter that parses a .py file (default python3)."
  callback := fun v _ => do
    let code ← run v[0]
    unless code == 0 do IO.Process.exit code.toUInt8

end StrataPython.Mantle.Cli

end -- public section
