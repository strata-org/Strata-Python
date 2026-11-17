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

private meta instance {α : Type} [BEq α] : BEq (Except FuzzFail α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => decide (a = b)
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
-- The coverage facts: sorted names and cells, the cases of each entry in the cases' order, only
-- the observed cells that a case declares, and the entries of every counted case.
private meta def factsEvs : Array Evidence :=
  #[ev (cov "b" "A2" ["len"] ["list.__len__"]) true ["len", "iter"] ["py.add"],
    ev (cov "a" "A1" [] ["list.__len__"]) true [] [],
    ev (cov "c" "A1" ["hex"] []) false ["hex"] []]
#guard (coverageFacts factsEvs).1 ==
  { observed := #["iter", "len", "py.add"], byEntries := #[("list.__len__", #["b", "a"])],
    observedCells := #[("len", "A2")],
    entryCells := #[(("list.__len__", "A1"), #["a"]), (("list.__len__", "A2"), #["b"])],
    declared := #[("hex", "A1"), ("len", "A2"), ("list.__len__", "A1"), ("list.__len__", "A2")],
    caseEntries := #[("b", "list.__len__"), ("a", "list.__len__")] }
-- The failures that only the runs show stay out of the facts.
#guard (coverageFacts #[ev (cov "a" "A1" ["len"] []) true [] []]).2 ==
  #["a: the case calls len by name, but CPython's run doesn't show it"]
-- The facts read back as they were printed, and the judgment of what was read back equals the
-- coverage check's result.
#guard parseCoverageFacts (printCoverageFacts (coverageFacts factsEvs).1) == .ok (coverageFacts factsEvs).1
#guard parseCoverageFacts (printCoverageFacts (coverageFacts declaredOnly).1) ==
  .ok (coverageFacts declaredOnly).1
#guard (parseCoverageFacts (printCoverageFacts (coverageFacts factsEvs).1)).map
    (judgeCoverage #["len", "hex"] · #[⟨"len", none, "x"⟩]) ==
  .ok (coverage #["len", "hex"] factsEvs #[⟨"len", none, "x"⟩])
#guard printCoverageFacts (coverageFacts declaredOnly).1 ==
  "observed | len\nentries | list.__len__ | a b\ncell | len @ A1\nentry-cell | list.__len__ @ A1 | a b\n\
  declared | len @ A1\ndeclared | list.__len__ @ A1\ncase-entry | a | list.__len__\n\
  case-entry | b | list.__len__\n"
#guard parseCoverageFacts "observed | len\nbogus | x\n" ==
  .error "malformed line in the coverage facts: bogus | x"
#guard parseCoverageFacts "cell | len\n" == .error "malformed cell in the coverage facts: cell | len"
-- A case id with a space doesn't read back as it was written, so the check fails instead of
-- judging other facts.
#guard (coverageText #["list.__len__"] #[ev (cov "a b" "A1" [] ["list.__len__"]) true [] []] #[]).1 ==
  ⟨#["the coverage facts don't read back as written"], #[]⟩
#guard (coverageText #["len"] factsEvs #[]).2 == printCoverageFacts (coverageFacts factsEvs).1
-- A digest file holds a stamp as one of its lines.
#guard checkStamp "T" "d.txt" "abc\nsources 1f\n" "sources 1f" == none
#guard checkStamp "T" "d.txt" "abc\nsources 1f\n" "sources 2f" ==
  some "d.txt: the sources changed since T's last update; run T with SEM_UPDATE=1"
#guard declaredBy #["a"] == "a"
#guard declaredBy #["a", "b", "c"] == "a and 2 more"
#guard declaredBy #[] == "no case"

-- Fuzz programs.
#guard (parseFuzz "fuzz_1_0 | plain | c:C0,v:v0,o0 | -\nfuzz_1_1 | seed | o0,seed | c:C1\n").map
    (·.map fun p => (p.id, p.seedBucket, p.steps, p.failing)) ==
  .ok #[("fuzz_1_0", false, ["c:C0", "v:v0", "o0"], []), ("fuzz_1_1", true, ["o0", "seed"], ["c:C1"])]
#guard (parseFuzz "x | other | o0 | -\n").map (·.size) == .error "unknown bucket: x | other | o0 | -"
#guard (parseFuzz "x | plain\n").map (·.size) == .error "malformed fuzz line: x | plain"
#guard (parseFuzz "x | seed | o0 | -\n").map (·.size) ==
  .error "the bucket disagrees with the last step: x | seed | o0 | -"

private meta def prog (steps : List String) (failing : List String := []) : FuzzProgram :=
  ⟨"f", steps, failing⟩
private meta def steps (body : List String) : String := "\n".intercalate body ++ "\n"

#guard fuzzBug? (prog ["c:C0", "o0"])
    (okTrace (steps ["@op c:C0", "= NoneType None", "@done c:C0", "@op o0", "! TypeError: x", "@done o0"]))
    (.trace "") == none
#guard fuzzBug? (prog ["c:C0", "o0"]) (okTrace (steps ["@op c:C0", "= NoneType None", "@done c:C0"]))
    (.trace "") == some "f: generator bug: step o0 didn't run (no @op or @done line)"
-- A class whose creation raises is a generator bug unless the tree says it is meant to raise.
#guard fuzzBug? (prog ["c:C0"]) (okTrace (steps ["@op c:C0", "! TypeError: x", "@done c:C0"]))
    (.trace "") ==
  some "f: generator bug: the creation of c:C0 raises, or doesn't, against the program's tree"
#guard fuzzBug? (prog ["c:C0"] ["c:C0"]) (okTrace (steps ["@op c:C0", "! TypeError: x", "@done c:C0"]))
    (.trace "") == none
#guard fuzzBug? (prog ["c:C0"] ["c:C0"]) (okTrace (steps ["@op c:C0", "= NoneType None", "@done c:C0"]))
    (.trace "") ==
  some "f: generator bug: the creation of c:C0 raises, or doesn't, against the program's tree"
-- A class whose base failed skips, whatever its tree says.
#guard fuzzBug? (prog ["c:C1"] ["c:C1"]) (okTrace (steps ["@op c:C1", "skip c:C1", "@done c:C1"]))
    (.trace "") == none
-- A step that uses a name that no step defined is a generator bug.
#guard fuzzBug? (prog ["o0"]) (okTrace (steps ["@op o0", "! NameError: name 'v2' is not defined", "@done o0"]))
    (.trace "") == some "f: generator bug: a step uses a name that no step defined"
#guard fuzzBug? (prog ["o0"]) SemDiff.endlessTrace (.trace "") ==
  some "f: generator bug: CPython's run doesn't end in time"
#guard fuzzBug? (prog ["o0"]) SemDiff.syntaxTrace (.trace "") ==
  some "f: generator bug: CPython doesn't compile the program"
#guard fuzzBug? (prog ["o0"]) "no header\n" (.trace "") ==
  some "f: generator bug: CPython's trace has no output section"
#guard fuzzBug? (prog ["o0"])
    (SemDiff.traceOf (steps ["@op o0", "= int 1", "@done o0"]) "--- outcome\nraised X: y\n--- globals\n")
    (.trace "") == some "f: generator bug: CPython's run doesn't end with `ok`"
#guard fuzzBug? (prog ["o0"]) (okTrace (steps ["@op o0", "= int 1", "@done o0"])) .syntax ==
  some "f: generator bug: the translator reports a syntax error"
#guard fuzzBug? (prog ["o0"]) (okTrace (steps ["@op o0", "= int 1", "@done o0"])) (.unsupported ["x"]) ==
  some "f: generator bug: the translator rejects x"

/-- CPython's trace of a seed-dependent program whose last step prints `order`. -/
private meta def seedTrace (order : String) : String :=
  okTrace (steps ["@op o0", "= int 1", "@done o0", "@op seed", s!"= list {order}", "@done seed"])

private meta def traces : Array String := #[seedTrace "['a', 'b']", seedTrace "['b', 'a']"] ++
  (List.replicate 6 (seedTrace "['a', 'b']")).toArray

/-- Our run that prints `out` and then stops with a gap. -/
private meta def gapRun (out : String) : SemDiff.Ours :=
  .trace (SemDiff.traceOf out "--- gap the order of a set\n")

-- A run that gaps before the seed-dependent step agrees with every trace up to its gap.
#guard judgeSeedDependent "f" (gapRun (steps ["@op o0", "= int 1", "@done o0", "@op seed"])) traces ==
  .ok (.gap "the order of a set")
-- A run that prints seed 0's order, then gaps, agrees with only some traces: it fails.
#guard (judgeSeedDependent "f"
    (gapRun (steps ["@op o0", "= int 1", "@done o0", "@op seed", "= list ['a', 'b']", "@done seed"]))
    traces).isOk == false
#guard match judgeSeedDependent "f"
    (gapRun (steps ["@op o0", "= int 1", "@done o0", "@op seed", "= list ['a', 'b']", "@done seed"]))
    traces with
  | .error e => e.startsWith "f: the run differs before its gap from CPython's run under PYTHONHASHSEED=1"
  | .ok _ => false
-- A gap whose message is a model invariant still fails through the judge.
#guard judgeSeedDependent "f"
    (.trace (SemDiff.traceOf (steps ["@op o0", "= int 1", "@done o0"]) s!"--- gap {StrataPython.Dyn.Sem.modelInvariantPrefix}x\n"))
    traces == .error s!"f: the run breaks a model invariant: {StrataPython.Dyn.Sem.modelInvariantPrefix}x"
-- A run that gives a result where CPython's runs differ fails.
#guard match judgeSeedDependent "f" (.trace (seedTrace "['a', 'b']")) traces with
  | .error e => e.startsWith "f: the run gives a result where CPython's runs depend on the hash seed"
  | .ok _ => false
-- Eight equal traces: the seed-dependent step showed nothing seed-dependent.
#guard judgeSeedDependent "f" (gapRun "") (Array.replicate 8 (seedTrace "['a', 'b']")) ==
  .error "f: generator bug: its seed-dependent step shows the same order under every seed"

-- A known program whose run differs before its gap: `known` when the run is its pinned trace.
private meta def wrongGap : SemDiff.Ours := gapRun (steps ["@op o0", "= int 2", "@done o0", "@op seed"])
private meta def wrongGapTrace : String := SemDiff.traceOf (steps ["@op o0", "= int 2", "@done o0", "@op seed"])
  "--- gap the order of a set\n"
#guard knownGap? "f" false wrongGap traces ⟨"D6", none⟩ == some (.ok (.known "D6"))
#guard knownGap? "f" false wrongGap traces ⟨"D6", some wrongGapTrace⟩ == some (.ok (.known "D6"))
#guard knownGap? "f" false wrongGap traces ⟨"D6", some "other"⟩ ==
  some (.error "f: the run's trace differs from its pinned trace")
-- A run that agrees before its gap is the judge's to decide.
#guard knownGap? "f" false (gapRun (steps ["@op o0", "= int 1", "@done o0", "@op seed"])) traces ⟨"D6", none⟩ == none
-- A gap that is a model invariant, a fault, a run out of fuel or a result: still the judge's.
#guard knownGap? "f" false (.trace (SemDiff.traceOf (steps ["@op o0", "= int 2"])
  s!"--- gap {StrataPython.Dyn.Sem.modelInvariantPrefix}x\n")) traces ⟨"D6", none⟩ == none
#guard knownGap? "f" false (.trace (SemDiff.traceOf (steps ["@op o0", "= int 2"]) "--- out of fuel\n--- gap g\n"))
  traces ⟨"D6", none⟩ == none
#guard knownGap? "f" false (.trace (seedTrace "['b', 'a']")) traces ⟨"D6", none⟩ == none
#guard knownGap? "f" false .syntax traces ⟨"D6", none⟩ == none
#guard knownGap? "f" false (.trace (SemDiff.traceOf (steps ["@op o0", "= int 2"]) "--- fault f\n--- gap g\n"))
  traces ⟨"D6", none⟩ == none
-- A seed-bucket program pinned as known must not print its seed step before the gap.
#guard knownGap? "f" true wrongGap traces ⟨"D6", none⟩ == some (.ok (.known "D6"))
#guard knownGap? "f" true (gapRun (steps ["@op o0", "= int 2", "@done o0", "@op seed", "= list ['a', 'b']"]))
  traces ⟨"D6", none⟩ == some (.error "f: the run prints its seed-dependent step before its gap")
-- CPython's run that doesn't end, or doesn't compile: still the judge's.
#guard knownGap? "f" false wrongGap #[SemDiff.endlessTrace] ⟨"D6", none⟩ == none
#guard knownGap? "f" false wrongGap #[SemDiff.syntaxTrace] ⟨"D6", none⟩ == none

-- A repro is written only for a shrunk program that fails the same way when it runs again.
private meta def k1 : FailureKind := .differs ⟨"o1", .value, some "= int 1", some "= int 2"⟩
#guard reproSeed? k1 (some (k1, 3)) == .ok 3
#guard reproSeed? k1 none == .error "the shrunk program no longer fails when it runs again"
#guard reproSeed? k1 (some (.fuel "o1", 0)) ==
  .error "the shrunk program fails differently when it runs again: out of fuel in step o1"

-- `stalePins` names the files of a pin directory that pin no known id, for every suffix, and
-- `checkFile` reports a difference only outside update mode.
#eval show IO Unit from do
  let dir : System.FilePath := ".lake" / "build" / "axis-source-test" / "pins"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  -- `a` has no pin suffix, so it pins nothing, though it is named like the known id.
  for n in ["a.known.trace", "a.py", "a", "b.known.trace", "c.py"] do IO.FS.writeFile (dir / n) ""
  let stale ← stalePins dir [".known.trace", ".py"] (· == "a") "program"
  let names := (stale.map fun m => (m.splitOn "/").getLast!).qsort (· < ·)
  unless names == #["a: pinned for no known program", "b.known.trace: pinned for no known program",
      "c.py: pinned for no known program"] do
    throw <| .userError s!"stalePins: {names}"
  let f := dir.parent.get! / "file.txt"
  IO.FS.writeFile f "old"
  unless (← checkFile f "old" false).isNone do throw <| .userError "checkFile: equal text differs"
  unless (← checkFile f "new" false).isSome do throw <| .userError "checkFile: missed a difference"
  unless (← checkFile f "new" true).isNone && (← IO.FS.readFile f) == "new" do
    throw <| .userError "checkFile: update mode didn't write"
  -- `pinFailures`: a known id needs its pin files, and other files are stale; no directory and no
  -- known id is fine.
  let verdicts := dir.parent.get! / "expected.txt"
  IO.FS.writeFile verdicts "a | known | a bug\nz | agree\n"
  let pf ← pinFailures "T" "program" verdicts dir [".known.trace", ".py", ".x"]
  let pf := (pf.map fun m => (m.splitOn "/").getLast!).qsort (· < ·)
  unless pf == #["a.x; run T with SEM_UPDATE=1", "a: pinned for no known program",
      "b.known.trace: pinned for no known program", "c.py: pinned for no known program"] do
    throw <| .userError s!"pinFailures: {pf}"
  IO.FS.writeFile verdicts "z | agree\n"
  unless (← pinFailures "T" "case" verdicts (dir / "none") [".py"]).isEmpty do
    throw <| .userError "pinFailures: a missing directory without known ids fails"
  unless (← sourcesStamp #[]) == "sources 7" do throw <| .userError "sourcesStamp: no files"
  -- The stamp of the sources changes with a file's bytes and with its path.
  let (g, h) := (dir.parent.get! / "g.py", dir.parent.get! / "h.py")
  IO.FS.writeFile g "x = 1\n"
  IO.FS.writeFile h "x = 1\n"
  let s1 ← sourcesStamp #[g]
  unless s1.startsWith "sources " && s1 == (← sourcesStamp #[g]) do
    throw <| .userError s!"sourcesStamp: not stable: {s1}"
  unless s1 != (← sourcesStamp #[h]) do throw <| .userError "sourcesStamp: ignores the path"
  IO.FS.writeFile g "x = 2\n"
  unless s1 != (← sourcesStamp #[g]) do throw <| .userError "sourcesStamp: ignores the bytes"
  IO.FS.removeDirAll dir.parent.get!

-- Where two outputs first differ: the step, the kind of line, CPython's line and ours.
#guard firstDiff "@op o0\n= int 2\n" "@op o0\n= int 1\n" == ⟨"o0", .value, some "= int 1", some "= int 2"⟩
#guard firstDiff "@op o0\n= int 1\n" "@op o0\nev C.__eq__\n= int 1\n" ==
  ⟨"o0", .event, some "ev C.__eq__", some "= int 1"⟩
#guard firstDiff "@op o0\n@done o0\n@op o1\n= int 2\n" "@op o0\n@done o0\n@op o1\n= int 1\n" ==
  ⟨"o1", .value, some "= int 1", some "= int 2"⟩
-- A missing line of ours and an extra line of ours differ: each side's line is kept.
#guard firstDiff "@op o0\n" "@op o0\n@done o0\n" == ⟨"o0", .marker, some "@done o0", none⟩
#guard firstDiff "@op o0\n@done o0\n" "@op o0\n" == ⟨"o0", .marker, none, some "@done o0"⟩
#guard firstDiff "@op o0\n= int 1\n" "@op o0\n" == ⟨"o0", .value, none, some "= int 1"⟩
-- Two different wrong lines of ours differ.
#guard firstDiff "@op o0\n= int 2\n" "@op o0\n= int 1\n" != firstDiff "@op o0\n= int 3\n" "@op o0\n= int 1\n"
-- Before any step, the step is empty.
#guard firstDiff "x\n" "y\n" == ⟨"", .value, some "y", some "x"⟩
-- Equal outputs: the sections after them are compared line by line, with no step.
#guard firstDiff "@op o0\n" "@op o0\n" "--- outcome\nraised X: y\n" "--- outcome\nok\n" ==
  ⟨"", .outcome, some "ok", some "raised X: y"⟩
#guard firstDiff "@op o0\n" "@op o0\n" "--- outcome\nok\n--- globals\nx = 2\n" "--- outcome\nok\n--- globals\nx = 1\n" ==
  ⟨"", .outcome, some "x = 1", some "x = 2"⟩

-- How a run fails against one of CPython's traces.
private meta def one : String := steps ["@op o0", "= int 1", "@done o0"]
private meta def two : String := steps ["@op o0", "= int 2", "@done o0"]
#guard failureKind? (.trace (okTrace one)) (okTrace one) == none
#guard failureKind? (.trace (okTrace two)) (okTrace one) ==
  some (.differs ⟨"o0", .value, some "= int 1", some "= int 2"⟩)
#guard failureKind? (.trace (okTrace one)) (okTrace (steps ["@op o0", "ev C.__eq__", "= int 1", "@done o0"])) ==
  some (.differs ⟨"o0", .event, some "ev C.__eq__", some "= int 1"⟩)
-- Two bugs in different steps have different kinds.
#guard failureKind? (.trace (okTrace (steps ["@op o0", "= int 1", "@done o0", "@op o1", "= int 3", "@done o1"])))
    (okTrace (steps ["@op o0", "= int 1", "@done o0", "@op o1", "= int 1", "@done o1"])) !=
  failureKind? (.trace (okTrace two)) (okTrace one)
-- Equal outputs, and a different outcome or different globals: different kinds.
#guard failureKind? (.trace (SemDiff.traceOf one "--- outcome\nraised X: y\n--- globals\n")) (okTrace one) ==
  some (.differs ⟨"", .outcome, some "ok", some "raised X: y"⟩)
#guard failureKind? (.trace (SemDiff.traceOf one "--- outcome\nok\n--- globals\nx = 2\n"))
    (SemDiff.traceOf one "--- outcome\nok\n--- globals\nx = 1\n") ==
  some (.differs ⟨"", .outcome, some "x = 1", some "x = 2"⟩)
#guard failureKind? (gapRun (steps ["@op o0", "= int 2"])) (okTrace one) ==
  some (.beforeGap ⟨"o0", .value, some "= int 1", some "= int 2"⟩)
#guard failureKind? (gapRun (steps ["@op o0"])) (okTrace one) == none
-- A model invariant, a fault and a run out of fuel record the step where our run stopped.
#guard failureKind? (.trace (SemDiff.traceOf one s!"--- gap {StrataPython.Dyn.Sem.modelInvariantPrefix}x\n"))
  (okTrace one) == some (.invariant "o0" s!"{StrataPython.Dyn.Sem.modelInvariantPrefix}x")
#guard failureKind? (.trace (SemDiff.traceOf one "--- fault f\n")) (okTrace one) == some (.fault "o0" "--- fault f")
#guard failureKind? (.trace (SemDiff.traceOf one "--- out of fuel\n")) (okTrace one) == some (.fuel "o0")
#guard failureKind? (.trace (SemDiff.traceOf (steps ["@op o0", "= int 1", "@done o0", "@op o1"]) "--- out of fuel\n"))
  (okTrace one) == some (.fuel "o1")
#guard failureKind? (.trace "no header") (okTrace one) == some .noOutput
-- CPython's trace that is no plain run, and a rejected program: no failure kind.
#guard failureKind? (.trace (okTrace two)) SemDiff.syntaxTrace == none
#guard failureKind? (.trace (okTrace two)) SemDiff.endlessTrace == none
#guard failureKind? (.trace (SemDiff.traceOf one "--- out of fuel\n")) SemDiff.endlessTrace == none
#guard failureKind? (.trace (okTrace two)) (SemDiff.twoRunsHeader ++ okTrace one) == none
#guard failureKind? .syntax (okTrace one) == none

-- How a fuzz program fails, over its eight traces, with the trace that shows it.
private meta def eight (t : String) : Array String := Array.replicate 8 t
#guard fuzzFailure? (prog ["o0"]) (eight (okTrace one)) (.trace (okTrace two)) ==
  some (.differs ⟨"o0", .value, some "= int 1", some "= int 2"⟩, 0)
#guard fuzzFailure? (prog ["o0"]) (eight (okTrace one)) (.trace (okTrace one)) == none
#guard fuzzFailure? (prog ["o0"]) (eight (okTrace one)) (gapRun (steps ["@op o0"])) == none
-- A generator bug isn't a failure: here CPython's run doesn't end with `ok`.
#guard fuzzFailure? (prog ["o0"]) (eight (SemDiff.traceOf one "--- outcome\nraised X: y\n--- globals\n"))
  (.trace (okTrace two)) == none
-- Nor are traces that depend on the seed outside the seed bucket, nor no traces.
#guard fuzzFailure? (prog ["o0"]) traces (.trace (okTrace two)) == none
#guard fuzzFailure? (prog ["o0"]) #[] (.trace (okTrace two)) == none
-- In the seed bucket: a run that prints seed 0's order and then gaps fails against seed 1's trace.
#guard fuzzFailure? (prog ["o0", "seed"]) traces
    (gapRun (steps ["@op o0", "= int 1", "@done o0", "@op seed", "= list ['a', 'b']", "@done seed"])) ==
  some (.beforeGap ⟨"seed", .value, some "= list ['b', 'a']", some "= list ['a', 'b']"⟩, 1)
-- A result where the seed bucket's traces differ: our run agrees with seed 0's trace, so the
-- failure shows against seed 1's.
#guard fuzzFailure? (prog ["o0", "seed"]) traces (.trace (seedTrace "['a', 'b']")) ==
  some (.differs ⟨"seed", .value, some "= list ['b', 'a']", some "= list ['a', 'b']"⟩, 1)
#guard fuzzFailure? (prog ["o0", "seed"]) traces (gapRun (steps ["@op o0", "= int 1", "@done o0", "@op seed"])) == none

-- The verdict shared by the test and the shrinker: a generator bug is a `bug`, a wrong run is
-- `wrong`.
#guard fuzzVerdict (prog ["o0"]) (eight (okTrace one)) (.trace (okTrace one)) none == .ok .agree
#guard (fuzzVerdict (prog ["o0"]) (eight (okTrace one)) (.trace (okTrace two)) none) matches .error (.wrong _)
#guard (fuzzVerdict (prog ["o0"]) traces (.trace (okTrace two)) none) ==
  .error (.bug "f: generator bug: CPython's trace depends on the hash seed or the machine")
#guard (fuzzVerdict (prog ["o0"]) #[] (.trace (okTrace two)) none) == .error (.bug "f: no CPython trace")
#guard fuzzVerdict (prog ["o0"]) (eight (okTrace one)) (.trace (okTrace two)) (some ⟨"D", some (okTrace two)⟩) ==
  .ok (.known "D")

#guard (FailureKind.differs ⟨"o1", .event, some "ev C.__eq__", none⟩).render ==
  "a difference, first at a user call in step o1"
#guard (FailureKind.fuel "o2").render == "out of fuel in step o2"
#guard (FailureKind.beforeGap ⟨"", .outcome, some "ok", none⟩).render ==
  "a difference before the gap, first at the outcome or the globals"
end StrataPython.AxisSourceTest
