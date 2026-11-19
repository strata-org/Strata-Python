/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython
meta import StrataPython.Dyn.Translate
meta import StrataPython.Dyn.Canonical
meta import StrataPython.ReadPython
meta import StrataDDM.Util.IO
meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Dyn.TestUtil

/-! # A loop's tail stays out of the loop in the translator's canonical output

Translates functions whose outer loop has a tail, the code in the loop's body that cannot come
back to its head: an inner loop and a `return`; a `try`/`finally` and a `return`; a `with` and a
`return` in a `while` loop, and the same in a `for` loop; and the `try`/`finally` tail again,
after a function whose `continue` goes through a `finally`.  Each module is put in canonical
form with `PyCanonical.runModule`.  The outer loop is the recorded loop whose head block carries
the source line of the outer loop statement.  The test pins the source lines of the instructions
in that loop's natural loop (`Body.loopOf`): the loop statement and the code that comes back to
the head, and none of the tail's lines.  It names no block and reads no golden.  It needs
Python, as `withPython` finds it. -/

namespace StrataPython.DynTailTest

open Strata.Dyn
open StrataPython.Dyn
open StrataPython.Dyn.TestUtil (compilePython)

/-- A program and what the test expects of it: the line of the outer loop statement, the lines
of the instructions in the outer loop, and the lines of the tail. -/
private structure Case where
  name : String
  program : String
  headLine : Nat
  loopLines : List Nat
  tailLines : List Nat

/-- The five programs.  In each, the outer loop statement and the code that comes back to it
(lines 3 to 6, or 10 to 13 in the last) are the outer loop (the `continue` emits no
instruction), and the lines after it in the loop's body are its tail. -/
private meta def cases : List Case := [
  { name := "inner_loop", headLine := 3, loopLines := [3, 4, 5], tailLines := [7, 8, 9],
    program :=
      "def e(v):\n" ++
      "    i = 0\n" ++
      "    while g(i):\n" ++
      "        if h(i):\n" ++
      "            i += 1\n" ++
      "            continue\n" ++
      "        while k():\n" ++
      "            m()\n" ++
      "        return v\n" ++
      "    return -1\n" },
  { name := "try_finally", headLine := 3, loopLines := [3, 4, 5], tailLines := [7, 8, 9, 10, 11],
    program :=
      "def e(v):\n" ++
      "    i = 0\n" ++
      "    while g(i):\n" ++
      "        if h(i):\n" ++
      "            i += 1\n" ++
      "            continue\n" ++
      "        try:\n" ++
      "            m()\n" ++
      "        finally:\n" ++
      "            n()\n" ++
      "        return v\n" ++
      "    return -1\n" },
  { name := "with_while", headLine := 3, loopLines := [3, 4, 5], tailLines := [7, 8, 9],
    program :=
      "def e(v):\n" ++
      "    i = 0\n" ++
      "    while g(i):\n" ++
      "        if h(i):\n" ++
      "            i += 1\n" ++
      "            continue\n" ++
      "        with c():\n" ++
      "            m()\n" ++
      "        return v\n" ++
      "    return -1\n" },
  { name := "with_for", headLine := 3, loopLines := [3, 4, 5], tailLines := [7, 8, 9],
    program :=
      "def e(xs, v):\n" ++
      "    i = 0\n" ++
      "    for x in xs:\n" ++
      "        if h(x):\n" ++
      "            i += 1\n" ++
      "            continue\n" ++
      "        with c():\n" ++
      "            m()\n" ++
      "        return v\n" ++
      "    return -1\n" },
  { name := "after_continue", headLine := 10, loopLines := [10, 11, 12],
    tailLines := [14, 15, 16, 17, 18],
    program :=
      "def a(xs):\n" ++
      "    for x in xs:\n" ++
      "        try:\n" ++
      "            continue\n" ++
      "        finally:\n" ++
      "            n()\n" ++
      "\n" ++
      "def e(v):\n" ++
      "    i = 0\n" ++
      "    while g(i):\n" ++
      "        if h(i):\n" ++
      "            i += 1\n" ++
      "            continue\n" ++
      "        try:\n" ++
      "            m()\n" ++
      "        finally:\n" ++
      "            n()\n" ++
      "        return v\n" ++
      "    return -1\n" }]

/-- An instruction's annotation. -/
private meta def Instruction.info' : Instruction Py.env Info → Info
  | .const info .. => info
  | .apply info .. => info

/-- `ps` for a message: each label with its line. -/
private meta def showLines (ps : List (Label × Nat)) : String :=
  ", ".intercalate (ps.map fun (l, n) => s!"{ToDDM.nameText l.name}:{n}")

/-- The label of each block of `bs` with the source line of each of its instructions. -/
private meta def linesOf (fm : Lean.FileMap) (bs : List (Block Py.env Info)) :
    List (Label × Nat) :=
  bs.flatMap fun b => b.instrs.toList.filterMap fun i =>
    let r := (Instruction.info' i).range
    if r.isNone then none else some (b.label, (fm.toPosition r.start).line)

/-- What is wrong with `c`'s translation, if anything. -/
private meta def check (pythonCmd tmpDir : System.FilePath) (c : Case) : IO (Array String) := do
  let pyFile := tmpDir / s!"{c.name}.py"
  IO.FS.writeFile pyFile c.program
  let ionPath ← compilePython pythonCmd pyFile tmpDir
  let bytes ← StrataDDM.Util.readBinInputSource ionPath.toString
  let stmts ← match StrataPython.readPythonStrataBytes ionPath.toString bytes with
    | .ok stmts => pure stmts
    | .error msg => return #[s!"{c.name}: the Ion file does not read: {msg}"]
  let r := PyTranslate.translate c.name stmts
  unless r.ok do return #[s!"{c.name}: the program does not translate"]
  let cm ← match PyCanonical.runModule r.module with
    | .ok cm => pure cm
    | .error fs => return #[s!"{c.name}: not canonical: {fs.map toString}"]
  let some f := cm.module.raw.funcs.find? (ToDDM.nameText ·.name == s!"{c.name}.e")
    | return #[s!"{c.name}: no function {c.name}.e"]
  let bs := f.blocks.toList
  let fm := Lean.FileMap.ofString c.program
  let lines := linesOf fm bs
  let mut failures : Array String := #[]
  -- The tail has instructions, so that leaving them out of the loop is a real check.
  if (lines.filter fun (_, n) => c.tailLines.contains n).isEmpty then
    failures := failures.push s!"{c.name}: no instruction on the tail's lines: {showLines lines}"
  let heads := ((PyCanonical.records? f.info).getD []).map (·.head)
  let lineOf (h : Label) : Option Nat := (bs.find? (·.label == h)).bind fun b =>
    if b.info.range.isNone then none else some (fm.toPosition b.info.range.start).line
  match heads.filter (lineOf · == some c.headLine) with
  | [h] =>
    let L := Body.loopOf bs h
    let inLoop := ((lines.filter fun (l, _) => L.contains l).map (·.2)).eraseDups.mergeSort (· ≤ ·)
    unless inLoop == c.loopLines do
      failures := failures.push s!"{c.name}: the outer loop holds instructions of lines {inLoop}, \
        not {c.loopLines}"
  | hs => failures := failures.push s!"{c.name}: {hs.length} recorded heads on line \
      {c.headLine}, not one"
  return failures

#eval withPython fun pythonCmd => IO.FS.withTempDir fun tmpDir => do
  let mut failures : Array String := #[]
  for c in cases do
    failures := failures ++ (← check pythonCmd tmpDir c)
  if !failures.isEmpty then
    for m in failures do IO.println s!"DynTailTest: {m}"
    throw <| IO.userError s!"DynTailTest: {failures.size} failure(s)"
  IO.println s!"DynTailTest: in all {cases.length} programs, the outer loop holds exactly the \
    lines it should, and none of its tail"

end StrataPython.DynTailTest
