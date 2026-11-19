/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Table
public import StrataPython.Dyn.Sem.Run
public import StrataDyn.DDMRead
public import StrataDyn.Exec.Run
import StrataPython.Dyn.Translate
import StrataPythonTest.Util.ExprText
import StrataPython.ReadPython
import StrataDDM.Ion
import StrataDyn.DSL
import StrataDyn.Env.WF

/-! # `invRun`: run each compared loop invariant of a program on the machine

`invRun FILE.py` translates `FILE.py` as module `__main__`, and prints:

* the line `--- compared RANKS`: the ranks of the invariants it compares, comma-separated;
* one line `--- status RANK compared` or `--- status RANK skipped: REASON` per invariant;
* one line `--- part RANK TEXT` per part read at entry of a compared invariant, in source order:
  the parts that the translator's `splitOld` gives, for `invariant_trace.py` to check;
* the trace of the run: `--- stdout <n>`, the program's output with one line
  `--- invariant RANK True|False` per evaluation of a compared invariant at its loop's head, then
  the outcome (`--- outcome`, `ok` or the exception's lines), or a gap or fault line.

An invariant's rank is its index among the module's invariants ordered by the byte offset of the
start of its `P`, the same rank that `StrataPythonTest/Dyn/invariant_trace.py` gives it on
CPython. An invariant is compared when every operation of its region has a rule in the Python
semantics and each of its old regions names, from outside it, only the function's parameters.

The module is printed, each compared `base.loopInvariant` becomes the test-only
`pytest.checkInvariant` with its rank, each skipped one is deleted, and the text is read back in
`InvTest.env`, whose rule for `pytest.checkInvariant` runs the region and writes the line. A run
doesn't keep the state at a call, so each `base.old` of a compared invariant moves to the start of
its function's entry block, where the state is the one at the call, as a `pytest.oldAtEntry`, and
becomes a `pytest.oldUse` of its result. invRun fails when a compared invariant has another number
of old regions than of parts, so that a lowering that drops a `base.old` fails the test. Not a
production tool: production linking never runs an invariant's region. -/

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn StrataPython.Dyn.Sem
open StrataPython (expr stmt)
open StrataDDM (SourceRange)

namespace InvRun

/-- Python's environment, with three test-only operations. -/
public environment InvTest extends Py where
  namespace pytest
  open base
  /-- Run `body`, an invariant's region, and write `--- invariant KEY True|False`. -/
  insn checkInvariant (key : String) (&body : Bool) : Unit
  /-- Run `body`, a `base.old` region moved to the start of its function's entry block, where
  the state is the one at the call, and give its result. -/
  insn oldAtEntry (&body : Except py.Value py.Value) : Except py.Value py.Value
  /-- Inside the invariant, in place of the moved `base.old`: the value of an `ok`, or a transfer
  to `err` with the error of an `error`, as `base.old` does. -/
  insn oldUse (r : Except py.Value py.Value) (^err (exc : py.Value)) : py.Value
  end pytest

#dyn_types InvTest

section
variable {ε : Eff} {E : Type}

/-- Run the invariant's region and write its result as one line of the program's output. -/
@[dyn_sem InvTest.checkInvariant, expose] public def checkInvariant {σ : Type} [Store σ]
    [Decode σ] [PyLang σ ε] (key : String) (body : Region ε [] Bool) : Sem ε E Unit := do
  let b ← runRegion body ()
  modifyThe Output fun o =>
    ⟨o.pieces.push s!"--- invariant {key} {if b then "True" else "False"}\n"⟩

/-- Run the moved old region. -/
@[dyn_sem InvTest.oldAtEntry, expose] public def oldAtEntry {σ : Type} [Store σ] [Decode σ]
    [PyLang σ ε] (body : Region ε [] (Except Value Value)) : Sem ε E (Except Value Value) :=
  runRegion body ()

/-- The moved old region's value, or a transfer to `err`. -/
@[dyn_sem InvTest.oldUse, expose] public def oldUse (r : Except Value Value)
    (err : Target E [Value]) : Sem ε E Value :=
  match r with
  | .ok v => pure v
  | .error e => Exec.jump err e
end

public section
-- The compiler specializes every piece's step machines into `py.call`'s implementation, which
-- takes more than the default budget.
set_option maxHeartbeats 1000000 in
#dyn_sem_table InvSem for InvTest (world := Sem.World)
end

/-- The source range of `P` of each `base.loopInvariant` of `m`, in the order the module prints
them: functions, blocks and instructions in order. -/
def invariantRanges (m : Module Py.env Info) : Array SourceRange := Id.run do
  let mut out := #[]
  for f in m.raw.funcs do
    for b in f.blocks do
      for i in b.instrs do
        match i with
        | .apply info _ r .. =>
          if nameStr r.name == "base.loopInvariant" then out := out.push info.range
        | _ => pure ()
  return out

/-- The rank of each invariant, in print order: its index when ordered by `starts`. -/
def ranksOf (starts : Array Nat) : Array Nat :=
  let sorted := starts.qsort (· < ·)
  starts.map fun s => (sorted.findIdx? (· == s)).getD 0

/-- The names of the operations that the lines of a region apply. -/
def opsIn (lines : List String) : List String :=
  lines.flatMap fun l =>
    match l.splitOn " = " with
    | _ :: rhs :: _ =>
      let op := (rhs.takeWhile fun c => c.isAlphanum || c == '.' || c == '_').toString
      if op.contains '.' then [op] else []
    | _ => []

/-- Why an invariant whose region applies `ops` isn't compared, if it isn't: an operation with no
rule in the Python semantics. -/
def skipReason (ops : List String) : Option String :=
  match ops.find? fun op => (InvSem.model.index.find? (nameOfStr op)).isNone with
  | some op => some s!"no rule for {op}"
  | none => none
where
  nameOfStr (s : String) : Name :=
    (s.splitOn ".").foldl (fun n p => .str n p) .base

/-- Whether `c` can continue a value's name after its `%`. -/
def nameChar (c : Char) : Bool := c.isAlphanum || c == '.' || c == '_'

/-- The value names (`%x`) that `line` mentions, with repeats. -/
def namesIn (line : String) : List String := Id.run do
  let mut out := []
  for piece in (line.splitOn "%").drop 1 do
    let n := (piece.takeWhile nameChar).toString
    -- A name's last character is no `.`: `%x.0.` ends a sentence.
    let n := (n.dropEndWhile (· == '.')).toString
    if !n.isEmpty then out := ("%" ++ n) :: out
  return out.reverse

/-- The value names that `lines` define: each instruction's result and each block's parameters. -/
def definedIn (lines : List String) : List String :=
  lines.flatMap fun l =>
    let t := l.trimAsciiStart.toString
    if t.startsWith "%" then (namesIn ((t.splitOn " : ").headD "")).take 1
    else if t.endsWith "):" then namesIn t
    else []

/-- The indentation of `l`. -/
def indentOf (l : String) : Nat := (l.takeWhile (· == ' ')).toString.length

/-- The index of the line after `i` that closes the region that `lines[i]` opens: the closing
brace at `lines[i]`'s indentation. -/
def closeOf (lines : Array String) (i : Nat) : Nat := Id.run do
  let indent := "".pushn ' ' (indentOf lines[i]!)
  let mut j := i + 1
  while j < lines.size && lines[j]! != indent ++ "}" do j := j + 1
  return j

/-- Move each `base.old` of the invariant region `region` to the start of its function's entry
block, as a `pytest.oldAtEntry`, with `base.old` becoming `pytest.oldUse` of its result: the
region in its new form, the lines to put at the start of the entry block, numbered from `next`,
and the number of old regions moved; or why it can't. An old region may name, from outside it,
only the function's parameters `params`: anything else, such as a quantifier's variable, has no
value at entry. -/
def moveOlds (region : Array String) (params : List String) (next : Nat) :
    Except String (Array String × Array String × Nat × Nat) := do
  let mut out : Array String := #[]
  let mut hoisted : Array String := #[]
  let mut n := next
  let mut moved := 0
  let mut i := 0
  while i < region.size do
    let l := region[i]!
    match l.splitOn " = base.old[" with
    | [pre, post] =>
      let j := closeOf region i
      let body := region.extract (i + 1) j
      let free := (body.toList.flatMap namesIn).eraseDups.filter fun x =>
        !(definedIn body.toList).contains x && !params.contains x
      if let x :: _ := free then throw s!"an OLD whose region reads {x}, a value of its invariant"
      let shift := indentOf l - 6
      let entryVal := s!"%oldAtEntry.{n}"
      n := n + 1
      moved := moved + 1
      let lines := body.map fun b => (b.drop (min shift (indentOf b))).toString
      let targs := ((post.splitOn "] ").drop 1).headD ""
      let types := (post.splitOn "] ").headD ""
      hoisted := hoisted ++
        #[s!"      {entryVal} : base.Except({types}) = pytest.oldAtEntry \{"] ++ lines ++ #["      }"]
      out := out.push s!"{pre} = pytest.oldUse({entryVal}) {(targs.dropEnd 2).toString}"
      i := j + 1
    | _ =>
      out := out.push l
      i := i + 1
  return (out, hoisted, n, moved)

/-- The printed module with each compared invariant made a `pytest.checkInvariant`, its old
regions moved to its function's entry block (`moveOlds`), and each skipped one deleted; and each
invariant's rank and status. -/
def rewrite (text : String) (ranks : Array Nat) :
    String × Array (Nat × Option String × Nat) := Id.run do
  let lines := (text.splitOn "\n").toArray
  let mut out : Array String := #[]
  let mut status : Array (Nat × Option String × Nat) := #[]
  let mut i := 0
  let mut k := 0
  let mut n := 0
  -- The current function's parameters, the index in `out` of its entry block's label, and the
  -- lines to put after it.
  let mut params : List String := []
  let mut entry : Option Nat := none
  let mut hoisted : Array String := #[]
  while i < lines.size do
    let l := lines[i]!
    if l.startsWith "  func @" then
      params := namesIn ((l.splitOn " -> ").headD "")
      entry := none
      hoisted := #[]
      out := out.push l
      i := i + 1
    else if l == "  }" then
      if let some e := entry then
        out := out.extract 0 (e + 1) ++ hoisted ++ out.extract (e + 1) out.size
      entry := none
      hoisted := #[]
      out := out.push l
      i := i + 1
    else if l.endsWith "= base.loopInvariant {" then
      let j := closeOf lines i
      let region := lines.extract (i + 1) j
      let rank := ranks[k]!
      k := k + 1
      match skipReason (opsIn region.toList) with
      | some why => status := status.push (rank, some why, 0)
      | none =>
        match moveOlds region params n with
        | .error why => status := status.push (rank, some why, 0)
        | .ok (region, h, n', moved) =>
          n := n'
          hoisted := hoisted ++ h
          status := status.push (rank, none, moved)
          out := out.push (l.replace "= base.loopInvariant {" s!"= pytest.checkInvariant(\"{rank}\") \{")
          out := out ++ region
          out := out.push lines[j]!
      i := j + 1
    else
      if entry.isNone && l.startsWith "    " && !l.startsWith "     " && l.endsWith ":" then
        entry := some out.size
      out := out.push l
      i := i + 1
  return ("\n".intercalate out.toList, if k == ranks.size then status else #[])

/-- The parts read at entry of `e`, as `splitOld` wraps them, in source order. -/
partial def oldParts (e : expr SourceRange) : List (expr SourceRange) :=
  match e with
  | .Call _ (.Name _ ⟨_, "OLD"⟩ _) ⟨_, #[a]⟩ _ => [a]
  | e => (PyMarkers.oldChildren e).flatMap oldParts

/-- The trace of a run: its output, and its outcome, gap or fault. -/
def traceOf (o : Outcome InvSem.model) : String :=
  let out := String.join o.snapshot.world.out.pieces.toList
  let stdout := s!"--- stdout {out.length}\n{out}"
  let rest : List String := match o.result with
    | .fault f => [faultLine f]
    | .ok _ => match o.read? (Except Value Value) with
      | some (.ok _) => ["--- outcome", "ok"]
      | some (.error e) => match excLines o.snapshot.world.store 100 e with
        | .ok ls => "--- outcome" :: ls
        -- The exception's type comes before the gap, so that the gap can't hide a wrong outcome.
        | .error msg => "--- outcome" :: (excTypeLine o.snapshot.world.store e).toList ++
            [s!"--- gap {msg}"]
      | none => ["--- fault a result that is not an Except"]
  "\n".intercalate (stdout :: rest) ++ "\n"

/-- Translate, rewrite, run and print, returning the exit status. -/
def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: invRun FILE.py"; return 2
  if let some msg := PyMarkers.mainFileProblem? path then IO.eprintln s!"invRun: {msg}"; return 1
  let pythonCmd := (← IO.getEnv "PYTHON").getD "python3"
  let stmts ← parse pythonCmd path
  let r := PyTranslate.translate "__main__" stmts
  unless r.ok do IO.eprintln "invRun: the translator rejects the program"; return 1
  let ranges := invariantRanges r.module
  let starts := ranges.map (·.start.byteIdx)
  if starts.toList.eraseDups.length != starts.size then
    IO.eprintln "invRun: two invariants share the start of P"; return 3
  let ranks := ranksOf starts
  let (text, status) := rewrite (r.module.format {}) ranks
  if status.size != starts.size then
    IO.eprintln "invRun: the rewrite found another number of invariants than the module has"
    return 3
  let compared := status.filterMap fun (k, w, _) => if w.isNone then some k else none
  IO.println s!"--- compared {",".intercalate ((compared.qsort (· < ·)).toList.map toString)}"
  for (k, w, _) in status.qsort (fun a b => a.1 < b.1) do
    IO.println s!"--- status {k} {match w with | none => "compared" | some why => s!"skipped: {why}"}"
  -- The parts read at entry of each compared invariant, as the translator's `splitOld` gives
  -- them: each `P` is read again from its source text, as `e = (P)`.
  let src ← IO.FS.readFile path
  let comparedIdx := (List.range ranks.size).filter fun i => compared.contains ranks[i]!
  let psrc := String.join (comparedIdx.map fun i =>
    s!"e = (\n{String.Pos.Raw.extract src ranges[i]!.start ranges[i]!.stop}\n)\n")
  let pstmts ← IO.FS.withTempDir fun dir => do
    let f := dir / "parts.py"
    IO.FS.writeFile f psrc
    parse pythonCmd f.toString
  unless pstmts.size == comparedIdx.length do
    IO.eprintln "invRun: the invariants read again aren't one statement each"; return 3
  for (i, s) in comparedIdx.zip pstmts.toList do
    let .Assign _ _ v _ := s
      | IO.eprintln "invRun: an invariant read again isn't an assignment"; return 3
    let parts := oldParts (PyMarkers.splitOld v)
    for p in parts do
      IO.println s!"--- part {ranks[i]!} {ExprText.exprText psrc p}"
    -- Each part has its old region: a lowering that dropped a `base.old` fails here.
    let moved := (status[i]!).2.2
    unless parts.length == moved do
      IO.eprintln s!"invRun: invariant {ranks[i]!} has {parts.length} parts but {moved} old regions"
      return 3
  let m ← match ← Module.read InvTest.env text path with
    | .ok m => pure m
    | .error e => IO.eprintln s!"invRun: {e}"; return 3
  if m.format {} != text then
    IO.eprintln "invRun: the module read back doesn't print as the text that was read"
    return 3
  match prepare InvSem.model m (.str (.str .base "__main__") "<module>") with
  | .error f => IO.print (traceOf' f); return 0
  | .ok ⟨_, hw, i⟩ =>
    IO.print (traceOf (runPrepared hw i #[] 1000000000 (fun _ => 0)))
    return 0
where
  traceOf' (f : Fault) : String := s!"--- stdout 0\n\n{faultLine f}\n"
  /-- The statements of the Python file `path`. -/
  parse (pythonCmd path : String) : IO (Array (stmt SourceRange)) :=
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
      match ← (StrataPython.pythonToStrata dialectFile path pythonCmd).toBaseIO with
      | .ok s => pure s
      | .error m => throw (IO.userError m)

end InvRun

public def main (args : List String) : IO UInt32 := InvRun.main args
