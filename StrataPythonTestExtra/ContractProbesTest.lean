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
meta import StrataPythonTest.Util.SemDiff

/-! # The contract operations against CPython

Each probe `StrataPythonTest/Dyn/contract_rules/probes/NAME.py` is a Python program in UTF-8, or
in the encoding that its coding line declares, then three comment lines:

```
# probe: base.Bool = py.typeIsSubclass($x, $C) ^err
# python: contract_rules_ref.typeIsSubclass_ref(x, C)
# expect: agree
```

The test translates the program as module `__main__`, adds a function `__probe__` that applies
the `probe:` instruction to the operands that `$` marks outside its string literals (a global
`g`, or its attribute `g.a`), and runs the module body, then `__probe__`,
with the Python semantics (`runModuleThen`).  `^err` is the target that receives the operation's
exception; a `base.Bool` result becomes a Python `bool`.  CPython 3.12 runs the program, then
evaluates the `python:` line (`probe_trace.py`), with `PYTHONHASHSEED` 0 and 1.  `SemDiff.judge`
compares the two traces, with no documented difference, and gives the verdict that `expect:`
names: `agree`, or `gap <message>`.  The run's own trace is pinned in `NAME.expected`; set
`PROBE_UPDATE=1` to rewrite it.  The lines `# probe:` and `# expect:` must be ASCII.  The test
skips when the Python it finds is not 3.12.
-/

namespace StrataPython.ContractProbesTest

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn
open StrataPython (withPython getPython3Version)

/-- The probes' folder. -/
meta def probesDir : System.FilePath := "StrataPythonTest" / "Dyn" / "contract_rules" / "probes"

/-- CPython's side of a probe. -/
meta def probeScript : System.FilePath :=
  "StrataPythonTest" / "Dyn" / "contract_rules" / "probe_trace.py"

/-- The texts after `key` on the lines of `source` that start with it. -/
meta def keyLines (key source : String) : List String :=
  (source.splitOn "\n").filterMap fun l => (l.dropPrefix? key).map (·.toString)

/-- The text `v` of the line `key`, trimmed, if it is ASCII. -/
meta def asciiLine (name key v : String) : Except String String :=
  if v.toList.all (fun (c : Char) => c.toNat < 128) then .ok v.trimAscii.toString
  else .error s!"{name}: the line '{key}' must be ASCII"

/-- The text after `key` on the one line of `source` that starts with it, which must be ASCII. -/
meta def field (name key : String) (source : String) : Except String String :=
  match keyLines key source with
  | [v] => asciiLine name key v
  | _ => .error s!"{name}: needs exactly one line '{key}'"

#guard (field "p" "# probe: " "x = 1\n# probe: base.Bool = py.len($x)\r\n").toOption ==
  some "base.Bool = py.len($x)"
#guard field "p" "# probe: " "x = 1\n# probe: py.len(\"\u00c3\u00a9\")\n" matches
  .error "p: the line '# probe: ' must be ASCII"
#guard field "p" "# probe: " "x = 1\n" matches .error "p: needs exactly one line '# probe: '"
#guard field "p" "# probe: " "# probe: a\n# probe: b\n" matches
  .error "p: needs exactly one line '# probe: '"

/-- Whether `c` may be part of an operand's name. -/
meta def isNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.'

/-- `text` with its marks replaced outside string literals: each operand that `$` marks (a global
`g`, or an attribute `g.a` of one) by `%g.i`, and `^err` by the target `^err.0()`.  It gives the
operands, `i` being an operand's index, and whether `^err` appears. -/
meta def substMarks (text : String) : Except String (String × Array String × Bool) := do
  let mut out := ""
  let mut names : Array String := #[]
  let mut usesErr := false
  let mut cs := text.toList
  let mut inStr := false
  while !cs.isEmpty do
    match cs with
    | '\\' :: c :: rest =>
      out := out.push '\\' |>.push c
      cs := rest
    | '"' :: rest =>
      inStr := !inStr
      out := out.push '"'
      cs := rest
    | '$' :: rest =>
      if inStr then
        out := out.push '$'
        cs := rest
      else
        let n := String.ofList (rest.takeWhile isNameChar)
        if n.isEmpty then throw s!"the probe '{text}' has a '$' with no name after it"
        let i := (names.idxOf? n).getD names.size
        unless names.contains n do names := names.push n
        out := out ++ s!"%g.{i}"
        cs := rest.dropWhile isNameChar
    | '^' :: 'e' :: 'r' :: 'r' :: rest =>
      if inStr then
        out := out ++ "^err"
      else
        out := out ++ "^err.0()"
        usesErr := true
      cs := rest
    | c :: rest =>
      out := out.push c
      cs := rest
    | [] => pure ()
  return (out, names, usesErr)

/-- The instructions that load the operand `o` into `%g.i`: the global, then its attribute. -/
meta def loadOperand (o : String) (i : Nat) : String :=
  match o.splitOn "." with
  | [g, a] => s!"      %cell.{i} : base.Ref(py.Value) = py.globalCell(\"__main__\", \"{g}\")\n\
      %obj.{i} : py.Value = base.refGet[py.Value](%cell.{i})\n\
      %g.{i} : py.Value = py.attr(%obj.{i}, \"{a}\") ^err.0()\n"
  | _ => s!"      %cell.{i} : base.Ref(py.Value) = py.globalCell(\"__main__\", \"{o}\")\n\
      %g.{i} : py.Value = base.refGet[py.Value](%cell.{i})\n"

/-- The function `__probe__` of the instruction `insn`, `<type> = <operation>`, as IR text. -/
meta def probeFunc (insn : String) : Except String String := do
  let (ty, rhs) ← match insn.splitOn " = " with
    | [t, r] => pure (t.trimAscii.toString, r.trimAscii.toString)
    | _ => throw s!"the probe '{insn}' is not '<type> = <operation>'"
  let (rhs, ops, errTarget) ← substMarks rhs
  let names := ops.toList
  let loads := names.zipIdx.map fun (n, i) => loadOperand n i
  -- An attribute's load raises along `^err` too.
  let usesErr := errTarget || names.any (·.contains '.')
  let errBlock := if usesErr then
      "    err.0(%e.0 : py.Value):\n\
       %x.0 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%e.0)\n\
       ret(%x.0)\n"
    else ""
  let body ← match ty with
    | "py.Value" => pure s!"      %r.0 : py.Value = {rhs}\n\
        %ok.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%r.0)\n\
        ret(%ok.0)\n"
    | "base.Bool" => pure s!"      %r.0 : base.Bool = {rhs}\n\
        branch(%r.0) ^yes.0() ^no.0()\n\
    yes.0():\n\
      %t.0 : py.Value = py.boolLit(true)\n\
      %ok.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%t.0)\n\
      ret(%ok.0)\n\
    no.0():\n\
      %f.0 : py.Value = py.boolLit(false)\n\
      %ok.1 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%f.0)\n\
      ret(%ok.1)\n"
    | _ => throw s!"the probe's type {ty} is neither py.Value nor base.Bool"
  return s!"  func @__main__.__probe__() -> base.Except(py.Value, py.Value) \{\n\
    entry.0():\n{String.join loads}{body}{errBlock}  }\n"

/-- The run's trace of the probe `pyFile`, whose instruction is `insn`. -/
meta def runOurs (pythonCmd pyFile : System.FilePath) (insn : String) : IO SemDiff.Ours := do
  let stmts ← IO.FS.withTempFile fun _ dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    match ← (StrataPython.pythonToStrata dialectFile pyFile pythonCmd.toString).toBaseIO with
    | .ok s => pure s
    | .error m => throw <| .userError s!"{pyFile}: {m}"
  let r := StrataPython.Dyn.PyTranslate.translate "__main__" stmts
  unless r.ok do
    throw <| .userError s!"{pyFile}: the translator rejects the probe's program"
  let func ← IO.ofExcept (probeFunc insn)
  let text := (r.module.format {}).trimAsciiEnd.toString
  let some pre := text.dropSuffix? "}" | throw <| .userError s!"{pyFile}: a module text without '}'"
  match ← Module.read Py.env (pre.toString ++ func ++ "}\n") "probe.dyn" with
  | .error e => throw <| .userError s!"{pyFile}: the module with __probe__ doesn't read: {e}"
  | .ok m => return .trace (StrataPython.Dyn.Sem.runModuleThen m
      (.str (.str .base "__main__") "<module>") "__main__"
      [.str (.str .base "__main__") "__probe__"])

/-- CPython's text for the probe `pyFile`: its trace, or both traces if its runs with
`PYTHONHASHSEED` 0 and 1 differ. -/
meta def cpythonTrace (pythonCmd pyFile : System.FilePath) : IO String := do
  let traceWith (seed : String) : IO String := do
    let r ← IO.Process.output {
      cmd := "timeout"
      args := #[toString SemDiff.cpythonSeconds, pythonCmd.toString, probeScript.toString,
        pyFile.toString]
      env := #[("PYTHONHASHSEED", some seed)] }
    unless r.exitCode == 0 do
      throw <| .userError s!"{pyFile}: probe_trace.py failed ({r.exitCode}):\n{r.stderr}"
    return r.stdout
  return SemDiff.joinRuns (← traceWith "0") (← traceWith "1")

/-- Whether the verdict `v` is the one that `expect` names. -/
meta def expected (expect : String) (v : Diff.Verdict) : Bool :=
  match v, expect.dropPrefix? "gap " with
  | .agree, _ => expect == "agree"
  | .gap msg, some m => msg == m.toString
  | _, _ => false

/-- The failure of the probe `name`, if any. -/
meta def runProbe (pythonCmd : System.FilePath) (update : Bool) (name : String) :
    IO (Option String) := do
  let pyFile := probesDir / s!"{name}.py"
  -- The bytes as Latin-1 characters: the program may be in any encoding, and the lines that
  -- `field` reads are ASCII.
  let source := String.ofList ((← IO.FS.readBinFile pyFile).toList.map (Char.ofUInt8 ·))
  let (insn, expect) ← match field name "# probe: " source, field name "# expect: " source with
    | .ok i, .ok e => pure (i, e)
    | .error e, _ | _, .error e => return some e
  let ours ← runOurs pythonCmd pyFile insn
  let pin := probesDir / s!"{name}.expected"
  if let .trace t := ours then
    if update then IO.FS.writeFile pin t
    else if !(← pin.pathExists) then return some s!"{name}: missing {pin}; run with PROBE_UPDATE=1"
    else if (← IO.FS.readFile pin) != t then
      return some s!"{name}: the run's trace differs from {pin}:\n{t}"
  match SemDiff.judge name ours (← cpythonTrace pythonCmd pyFile) none with
  | .error e => return some e
  | .ok v =>
    if expected expect v then return none
    return some s!"{name}: the verdict is {repr v}, but the probe expects {expect}"

#eval withPython fun pythonCmd => do
  if (← getPython3Version pythonCmd.toString) != some 12 then
    IO.println s!"ContractProbesTest: skipped: {pythonCmd} is not CPython 3.12"
    return
  let update := (← IO.getEnv "PROBE_UPDATE").isSome
  let mut names : Array String := #[]
  for f in ← probesDir.readDir do
    if f.path.extension == some "py" then names := names.push (f.path.fileStem.getD "")
  names := names.qsort (· < ·)
  let tasks ← names.mapM fun n => IO.asTask (runProbe pythonCmd update n)
  let mut failures : Array String := #[]
  for (n, t) in names.zip tasks do
    match ← IO.wait t with
    | .ok none => pure ()
    | .ok (some msg) => failures := failures.push msg
    | .error err => failures := failures.push s!"{n}: {err}"
  for f in failures do IO.println f
  unless failures.isEmpty do
    throw <| .userError s!"ContractProbesTest: {failures.size} of {names.size} probes fail"
  IO.println s!"ContractProbesTest: {names.size} probes agree with CPython or stop as expected"

end StrataPython.ContractProbesTest
