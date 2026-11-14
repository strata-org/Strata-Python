/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPythonTest.Util.AxisSource

/-! # The checks of the generated differential sources

How a case ended is read between its markers, user calls left out; a case that doesn't run its
operation, or ends otherwise than it expects, is a generator bug; eight traces agree only if all
are equal; and the summary counts the verdicts by group and axis. -/

namespace StrataPython.AxisSourceTest

open Strata.Dyn.Exec.Diff (Entry Verdict)
open StrataPython.AxisSource

/-- Results compared by their contents. -/
private meta instance {α : Type} [BEq α] : BEq (Except String α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private meta instance : BEq Expect := ⟨fun a b => decide (a = b)⟩
private meta instance : BEq Outcome := ⟨fun a b => decide (a = b)⟩

#guard Expect.parse "result" == .ok .result
#guard Expect.parse "raises:TypeError" == .ok (.raises "TypeError")
#guard Expect.parse "rejects:a % format" == .ok (.rejects "a % format")
#guard Expect.parse "any" == .ok .any
#guard Expect.parse "maybe" == .error "unknown expectation: maybe"

#guard (parseCases ("a | operators | A1 | result | t1 | - | int.__add__\n\n" ++
    "b | methods | A1 | raises:TypeError | t2 | str.split,len | -\n")).map
    (·.map fun c => (c.id, c.group, c.axis, c.template, c.calls, c.entries)) ==
  .ok #[("a", "operators", "A1", "t1", [], ["int.__add__"]),
        ("b", "methods", "A1", "t2", ["str.split", "len"], [])]
#guard (parseCases "a | operators\n").map (·.size) == .error "malformed case line: a | operators"

/-- The output of a case `c` with the lines `body` between its markers. -/
private meta def out (body : List String) : String :=
  "\n".intercalate (["ev prelude", "@op c"] ++ body ++ ["@done c", ""])

#guard caseOutcome "c" (out ["= int 3"]) == .ok .result
#guard caseOutcome "c" (out ["ev C.__len__", "= int 3", "is True", "self list [1]", "ev C.__del__"]) ==
  .ok .result
#guard caseOutcome "c" "@done c\n@op c\n= int 1\n" == .error "the @done line comes before the @op line"
#guard caseOutcome "c" (out ["! TypeError: no | cause - | context - | suppress False"]) ==
  .ok (.raises "TypeError")
#guard caseOutcome "c" "@done c\n" == .error "the operation never ran (no @op line)"
#guard caseOutcome "c" "@op c\n= int 1\n" == .error "the case didn't finish (no @done line)"
#guard caseOutcome "c" (out ["ev C.__len__"]) == .error "the case printed no result and no exception"
#guard caseOutcome "c" (out ["hello"]) ==
  .error "the case's last line is neither a result nor an exception: hello"
-- Another case's markers don't count.
#guard caseOutcome "d" (out ["= int 3"]) == .error "the operation never ran (no @op line)"

/-- A trace whose output is `o` and whose outcome is `ok`. -/
private meta def okTrace (o : String) : String :=
  SemDiff.traceOf o "--- outcome\nok\n--- globals\n"

private meta def case (e : Expect) : Case := { id := "c", group := "g", axis := "A1", expect := e }

#guard generatorBug? (case .result) (okTrace (out ["= int 3"])) (.trace "") == none
#guard generatorBug? (case .any) (okTrace (out ["! KeyError: 1 | x"])) (.trace "") == none
#guard generatorBug? (case (.raises "TypeError")) (okTrace (out ["! TypeError: x"])) (.trace "") ==
  none
#guard generatorBug? (case .result) (okTrace (out ["! TypeError: x"])) (.trace "") ==
  some "c: generator bug: CPython's case ends with raises TypeError, the case expects a result"
#guard generatorBug? (case (.raises "TypeError")) (okTrace (out ["= int 3"])) (.trace "") ==
  some "c: generator bug: CPython's case ends with a result, the case expects raises TypeError"
#guard generatorBug? (case (.raises "ValueError")) (okTrace (out ["! TypeError: x"])) (.trace "") ==
  some "c: generator bug: CPython raises TypeError, the case expects ValueError"
-- A prelude that raises before the operation (e.g. `class S(range)`) is a generator bug, even
-- when the two runs agree.
#guard generatorBug? (case .any) (okTrace "! TypeError: x\n@done c\n") (.trace "") ==
  some "c: generator bug: the operation never ran (no @op line)"
#guard generatorBug? (case .result)
    (SemDiff.traceOf (out ["= int 3"]) "--- outcome\nraised ValueError: v\n--- globals\n")
    (.trace "") == some "c: generator bug: CPython's run doesn't end with `ok`"
#guard generatorBug? (case .result) "no header\n" (.trace "") ==
  some "c: generator bug: CPython's trace has no output section"
#guard generatorBug? (case .result) SemDiff.syntaxTrace (.trace "") ==
  some "c: generator bug: CPython doesn't compile the program"
#guard generatorBug? (case .result) SemDiff.endlessTrace (.trace "") ==
  some "c: generator bug: CPython's run doesn't end in time"
#guard generatorBug? (case .result) (okTrace (out ["= int 3"])) .syntax ==
  some "c: generator bug: the translator reports a syntax error"
#guard generatorBug? (case .result) (okTrace (out ["= int 3"])) (.unsupported ["generator"]) ==
  some "c: generator bug: the translator rejects generator"
#guard generatorBug? (case (.rejects "generator")) (okTrace (out ["= int 3"]))
    (.unsupported ["generator"]) == none
#guard generatorBug? (case (.rejects "generator")) (okTrace (out ["= int 3"]))
    (.unsupported ["lambda"]) == some "c: generator bug: the translator rejects lambda, not generator"
#guard generatorBug? (case (.rejects "generator")) (okTrace (out ["= int 3"])) (.trace "") ==
  some "c: generator bug: the translator doesn't reject generator"

-- A case observes its operation only if CPython's trace changes without it.
#guard observes (case .result) (okTrace (out ["= int 3"])) (okTrace (out ["= NoneType None"]))
#guard !observes (case .result) (okTrace (out ["= NoneType None"]))
  (okTrace (out ["= NoneType None"]))
#guard observes (case (.rejects "generator")) "same" "same"

#guard seedsAgree #["a", "a", "a"]
#guard !seedsAgree #["a", "a", "b"]
#guard seeds.length == 8

#guard summary #[{ id := "x", group := "ops", axis := "A1", expect := .result },
    { id := "y", group := "ops", axis := "A1", expect := .result },
    { id := "z", group := "lookup", axis := "A3", expect := .result }]
    #[⟨"x", .agree⟩, ⟨"y", .gap "m"⟩, ⟨"z", .known "k"⟩] ==
  "lookup | A3 | 0 agree | 0 gap | 1 known\nops | A1 | 1 agree | 1 gap | 0 known\n\
   total | 3 cases | 1 agree | 1 gap | 1 known\n"

-- The instructions of a printed module: bound results and statements, each name once.
#guard insnNames "func @f() {\n  entry.0():\n    %a : py.Value = py.intLit(1)\n    %b : py.Value = py.add(%a, %a) ^p()\n    %c : py.Value = py.intLit(2)\n    ret(%c)\n" ==
  ["py.intLit", "py.add"]
#guard insnNames "  entry.0():\n    branch(%c, a.0(), b.0())\n  a.0():\n    jump b.0()\n  unreachable.0():\n    unreachable\n    py.Completion.case(%x)\n" ==
  ["base.branch", "base.jump", "base.unreachable", "py.Completion.case"]

#guard (parseNotCovered "# comment\nset.__len__ | a gap\nint.__add__ @ A3 | why\n").map
    (·.map fun e => (e.name, e.axis, e.reason)) ==
  .ok #[("set.__len__", none, "a gap"), ("int.__add__", some "A3", "why")]
#guard (parseNotCovered "x\n").map (·.size) == .error "malformed not-covered entry: x"

/-- A case of the axis `axis` that calls `calls` by name and reaches `entries`. -/
private meta def cov (id axis : String) (calls entries : List String) : Case :=
  { id, group := "g", axis, expect := .result, calls, entries }

/-- The evidence of a case that agrees (`counted`), whose CPython run gives a result (`result`),
and that shows the calls `called` and the instructions `insns`. -/
private meta def ev (c : Case) (counted : Bool) (called insns : List String) (result := true) :
    Evidence := { case := c, counted, result, called, insns }

private meta def fails (r : Coverage) : Array String := r.failures

-- Only an agreeing case counts: a known case is a wrong result.
#guard counts (some .agree)
#guard !counts (some (.known "a bug"))
#guard !counts (some (.gap "m"))
#guard !counts none

-- Covered by a call, an entry and an instruction: nothing fails, and the entry-only name is
-- reported apart.
#guard coverage #["len", "list.__len__", "py.add"]
    #[ev (cov "a" "A1" ["len"] ["list.__len__"]) true ["len"] ["py.add"]] #[] ==
  ⟨#[], #[("list.__len__", #["a"])]⟩
-- A case that agrees but doesn't make the call it declares.
#guard fails (coverage #["len"] #[ev (cov "a" "A1" ["len"] []) true [] []] #[]) ==
  #["a: the case calls len by name, but CPython's run doesn't show it",
    "len: no case that agrees with CPython reaches it, and not_covered.txt doesn't list it",
    "len @ A1: no case of the axis that agrees with CPython reaches it, and not_covered.txt doesn't list the cell"]
-- A case that gaps covers nothing; the uncovered name passes only if `not_covered.txt` lists it.
#guard fails (coverage #["len"] #[ev (cov "a" "A1" ["len"] []) false ["len"] []] #[]) ==
  #["len: no case that agrees with CPython reaches it, and not_covered.txt doesn't list it",
    "len @ A1: no case of the axis that agrees with CPython reaches it, and not_covered.txt doesn't list the cell"]
#guard fails (coverage #["len"] #[ev (cov "a" "A1" ["len"] []) false ["len"] []]
    #[⟨"len", none, "gap"⟩]) == #[]
-- A case whose CPython run raises covers its cell, not the name.
#guard fails (coverage #["len"] #[ev (cov "a" "A8" ["len"] []) true ["len"] [] (result := false)]
    #[]) ==
  #["len: no case that agrees with CPython reaches it, and not_covered.txt doesn't list it"]
-- A name of the tables that no case reaches is reported, also with no case declaring it.
#guard fails (coverage #["len", "hex"] #[ev (cov "a" "A1" ["len"] []) true ["len"] []] #[]) ==
  #["hex: no case that agrees with CPython reaches it, and not_covered.txt doesn't list it"]
-- A declared cell of another axis needs its own agreeing case.
#guard fails (coverage #["len"]
    #[ev (cov "a" "A1" ["len"] []) true ["len"] [], ev (cov "b" "A3" ["len"] []) false [] []]
    #[]) ==
  #["len @ A3: no case of the axis that agrees with CPython reaches it, and not_covered.txt doesn't list the cell"]
#guard fails (coverage #["len"]
    #[ev (cov "a" "A1" ["len"] []) true ["len"] [], ev (cov "b" "A3" ["len"] []) false [] []]
    #[⟨"len", some "A3", "gap"⟩]) == #[]
-- A name that the model doesn't implement needs no cell: its cases gap by design.
#guard fails (coverage #["len"]
    #[ev (cov "a" "A1" ["len"] []) true ["len"] [], ev (cov "b" "direct" ["str.isprintable"] []) false [] []]
    #[]) == #[]
-- Evidence with `cells := false` covers the name but no cell.
#guard fails (coverage #["len"]
    #[{ case := cov "s" "A1" ["len"] [], counted := true, result := true, called := ["len"],
        insns := [], cells := false }] #[]) ==
  #["len @ A1: no case of the axis that agrees with CPython reaches it, and not_covered.txt doesn't list the cell"]
-- A declared entry of a case whose CPython run raises covers its cell, not the name.
#guard fails (coverage #["list.__len__"]
    #[ev (cov "a" "A1" [] ["list.__len__"]) true [] [] (result := false)] #[]) ==
  #["list.__len__: no case that agrees with CPython reaches it, and not_covered.txt doesn't list it"]
-- A case whose CPython run raises isn't asked to show the calls it declares.
#guard fails (coverage #["len"]
    #[ev (cov "a" "A8" ["len"] []) true [] [] (result := false), ev (cov "b" "A1" ["len"] []) true ["len"] []]
    #[⟨"len", some "A8", "raises"⟩]) == #[]
-- An instruction that can never run in an agreeing case doesn't count, though the translation has it.
#guard fails (coverage #["base.unreachable"] #[ev (cov "a" "A1" [] []) true [] ["base.unreachable"]] #[]) ==
  #["base.unreachable: no case that agrees with CPython reaches it, and not_covered.txt doesn't list it"]
-- The program around every operation covers names, never cells.
#guard fails (coverage #["py.strLit"]
    #[{ case := cov "s" "scaffold" [] [], counted := true, result := true, called := [],
        insns := ["py.strLit"], cells := false }] #[]) == #[]
-- An entry that no table has, and stale entries of `not_covered.txt`: covered, not in the tables,
-- or a cell that no case declares.
#guard fails (coverage #["len"] #[ev (cov "a" "A1" ["len"] ["no.such"]) true ["len"] []]
    #[⟨"len", none, "x"⟩, ⟨"len", some "A1", "y"⟩, ⟨"gone", none, "z"⟩, ⟨"len", some "A5", "w"⟩]) ==
  #["a: the catalog says the case reaches no.such, which no table of the model has",
    "not_covered.txt: len is covered; remove its entry",
    "not_covered.txt: len @ A1 is covered; remove its entry",
    "not_covered.txt: gone is no name of the model's tables",
    "not_covered.txt: no case declares len @ A5 for a name of the model's tables"]

-- A name that only declared entries cover is listed with the cases that declare it, in order, and
-- a stale entry of `not_covered.txt` for it says so: no run of ours shows it.
private meta def declaredOnly : Array Evidence :=
  #[ev (cov "a" "A1" [] ["list.__len__"]) true [] [], ev (cov "b" "A1" [] ["list.__len__"]) true [] [],
    ev (cov "c" "A1" ["len"] []) true ["len"] []]
#guard (coverage #["len", "list.__len__"] declaredOnly #[]).byEntriesOnly ==
  #[("list.__len__", #["a", "b"])]
#guard fails (coverage #["len", "list.__len__"] declaredOnly
    #[⟨"list.__len__", none, "x"⟩, ⟨"list.__len__", some "A1", "y"⟩, ⟨"len", some "A1", "z"⟩]) ==
  #["not_covered.txt: list.__len__ is covered only by the declared entries of a and 1 more; remove its entry",
    "not_covered.txt: list.__len__ @ A1 is covered only by the declared entries of a and 1 more; remove its entry",
    "not_covered.txt: len @ A1 is covered; remove its entry"]
-- A name that a run shows is not in the list, even when a case also declares it.
#guard (coverage #["len"] #[ev (cov "a" "A1" ["len"] ["len"]) true ["len"] []] #[]).byEntriesOnly == #[]
#guard declaredBy #["a"] == "a"
#guard declaredBy #["a", "b", "c"] == "a and 2 more"
#guard declaredBy #[] == "no case"

end StrataPython.AxisSourceTest
