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

#guard (parseCases "a | operators | A1 | result\n\nb | lookup | A3 | raises:TypeError\n").map
    (·.map fun c => (c.id, c.group, c.axis)) ==
  .ok #[("a", "operators", "A1"), ("b", "lookup", "A3")]
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

private meta def case (e : Expect) : Case := ⟨"c", "g", "A1", e⟩

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

#guard summary #[⟨"x", "ops", "A1", .result⟩, ⟨"y", "ops", "A1", .result⟩,
    ⟨"z", "lookup", "A3", .result⟩]
    #[⟨"x", .agree⟩, ⟨"y", .gap "m"⟩, ⟨"z", .known "k"⟩] ==
  "lookup | A3 | 0 agree | 0 gap | 1 known\nops | A1 | 1 agree | 1 gap | 0 known\n\
   total | 3 cases | 1 agree | 1 gap | 1 known\n"

end StrataPython.AxisSourceTest
