/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Cases
public import StrataDyn.DDMRead
public import StrataDynTest.Cases.Env
public import StrataDyn.Examples.While.Run
import all StrataDyn.Cases
import StrataDyn.Env.WF
-- The reader, the pass and the engine run as compiled code below.
meta import all StrataDyn.Cases
meta import StrataDyn.DDMRead
meta import StrataDynTest.Cases.Env
meta import StrataDyn.Examples.While.Run
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Lowering cases to plain control

The tests use hand-declared accessors (`StrataDynTest/Cases/Env.lean`).

* Every lowering here is checked alike (`lowered`): the result prints to text that reads back
  to the same text, lowering it again needs no accessor and changes nothing, the source's
  values keep their ids and names with the new values after them, and each generated
  instruction and block is annotated as the terminator it replaces.
* Printed results pin argument order, fresh names and which arms get a block: a
  three-constructor case in a body, the specification fixture, a mutually recursive pair of which
  only the first takes a type parameter, and a datatype without constructors.
* Eight modules run on Dyn's engine before and after lowering, and must end the same, print the
  same, tick as often and draw as many choices. Each of their ten functions runs on the
  thirteen arguments -6 to 6, or on its one input if it takes none: 118 inputs, each under
  three oracles. Only `loop` and `forest` draw from the oracle, so the other 92 inputs run
  three times alike. One module is lowered a second time, with a tester that it does not need.
* Specifications are lowered and checked, not run: Dyn's engine ignores contracts and rejects
  extern functions.
* Each rejection is compared structurally, beside the same source accepted with the valid
  accessors or without the feature that is refused.
-/

namespace Strata.Dyn.CasesTest

open Strata.Dyn.Exec Strata.Dyn.While

private def read (env : Env Unit) [base ≼ env] (text : String) : IO (Module env Info) := do
  match ← Module.read env text "t.dyn" with
  | .ok m => return m
  | .error e => throw (IO.userError (toString e))

private def load (text : String) : IO (Module CaseEnv.env Info) := read CaseEnv.env text

private def showError : Cases.Error → String
  | .accessor owner block reason =>
    s!"accessor {reprStr owner} {reprStr block.name} {reprStr reason}"
  | .illFormed names => s!"ill-formed {reprStr names}"
  | .internal => "internal"

private def tryLower {env : Env Unit} [base ≼ env] (m : Module env Info)
    (vocab : CaseOps := ops) :
    IO (Except Cases.Error { m' : Module env Info // Cased m'.raw }) := do
  if h : CasesInput m.raw then return cases vocab m h
  else throw (IO.userError "the test's source is not in Cases' input shape")

private def lower {env : Env Unit} [base ≼ env] (m : Module env Info) (vocab : CaseOps := ops) :
    IO { m' : Module env Info // Cased m'.raw } := do
  match ← tryLower m vocab with
  | .ok m' => return m'
  | .error e => throw (IO.userError (showError e))

private def sameInfo (a b : Info) : Bool :=
  a.range == b.range && reprStr a.attrs == reprStr b.attrs

private def instrInfo {env : Env Unit} : Instruction env Info → Info
  | .const info .. => info
  | .apply info .. => info

/-- The values defined by `olds` keep their ids, types and names, and every other value
defined by `news` has an id after them. -/
private def valuesKept {env : Env Unit} (olds news : List (ValDecl env))
    (oldNames newNames : Array Name) : Bool :=
  let added := newNames.size - oldNames.size
  olds.all (fun d => news.any (decide <| · = d)) &&
    decide (newNames.extract 0 oldNames.size = oldNames) &&
    news.length == olds.length + added &&
    (news.filter (oldNames.size ≤ ·.id.id)).length == added

/-- In the blocks `news` of one body or region, each block of `olds` keeps its terminator's
annotation and gives it to the instructions added to it and to the new blocks that follow
it. -/
private def annotatedAtTerms {env : Env Unit} (olds news : List (Block env Info)) : Bool :=
  (news.foldl (init := (true, (none : Option Info))) fun (ok, head) b =>
    match olds.find? (·.label == b.label) with
    | some old =>
      (ok && sameInfo old.term.info b.term.info &&
        (b.instrs.extract old.instrs.size).all (sameInfo b.term.info <| instrInfo ·),
        some b.term.info)
    | none =>
      (ok && head.any fun info => sameInfo info b.info && sameInfo info b.term.info &&
        b.instrs.all (sameInfo info <| instrInfo ·), head)).1

/-- The blocks `blocks` of a body, and those of each region nested in them or in `regions`, at
any depth: a list per body or region. -/
private def blockLists {env : Env Unit} (blocks : List (Block env Info))
    (regions : List (Region env Info)) : List (List (Block env Info)) :=
  blocks :: ((Block.nestedRegionsList blocks).map (·.1) ++ Region.allList regions).map
    (·.blocks.toList)

/-- Lower `text` and check what holds of every lowering here: read-back, idempotence without
accessors, kept ids and names, and annotations. The source and the result. -/
private def lowered (env : Env Unit) [base ≼ env] (text : String) (vocab : CaseOps := ops) :
    IO (Module env Info × Module env Info) := do
  let src ← read env text
  let ⟨out, h⟩ ← lower src vocab
  let back ← read env (toString out)
  unless toString back == toString out do throw (IO.userError "read-back differs")
  match cases { tester := fun _ => none, selector := fun _ _ => none } out (casesInput_cased h) with
  | .ok ⟨again, _⟩ =>
    unless toString again == toString out do throw (IO.userError "Cases is not idempotent")
  | .error e => throw (IO.userError (showError e))
  unless (src.raw.funcs.zip out.raw.funcs).all (fun (f, g) =>
        valuesKept f.defs g.defs f.names g.names) &&
      (src.raw.ghosts.zip out.raw.ghosts).all (fun (f, g) =>
        valuesKept f.defs g.defs f.names g.names) do
    throw (IO.userError "a source value changed its id or name, or a new id is not after them")
  unless (src.raw.funcs.zip out.raw.funcs).all (fun (f, g) =>
        (blockLists g.blocks.toList g.contract.regions).all (annotatedAtTerms f.allBlocks)) &&
      (src.raw.ghosts.zip out.raw.ghosts).all (fun (f, g) =>
        (blockLists [] g.regions).all (annotatedAtTerms (Region.blocksList f.regions))) do
    throw (IO.userError "a generated instruction or block is not annotated at its terminator")
  return (src, out)

/-- Compare the observables, not the administrative step count. -/
private def observe (m : Module CaseEnv.env Info) (f : String)
    (args : Array Int) (oracle : Nat → Nat) : String :=
  let o := runModule CaseSem.model m (nm f) (args.map (CaseSem.model.arg ·)) 100000 oracle
  let result := match o.result with
    | .ok _ => match o.read? Int, o.read? (Except Int Int) with
      | some n, _ => s!"ok {n}"
      | _, some (.ok n) => s!"ok {n}"
      | _, some (.error e) => s!"raised {e}"
      | _, _ => "unexpected result type"
    | .fault f => s!"fault {showFault f}"
  s!"{result}; printed {o.snapshot.world.out.items}; " ++
    s!"ticks {o.snapshot.world.ticks.n}; oracle {o.drawn}"

private def oracles : List (Nat → Nat) := [fun _ => 0, fun k => k, fun k => 7 - k % 3]

/-- Lower `text` and run each function of `tests` before and after, on its inputs under each
oracle. -/
private def check (text : String) (tests : List (String × Array (Array Int)))
    (printModule : Bool := false) (vocab : CaseOps := ops) : IO Unit := do
  let (src, cased) ← lowered CaseEnv.env text vocab
  if printModule then IO.print (toString cased)
  let mut n := 0
  for (f, inputs) in tests do
    for args in inputs do
      for oracle in oracles do
        let expected := observe src f args oracle
        unless observe cased f args oracle == expected do
          throw (IO.userError s!"{f}{args}: source {expected}; cased {observe cased f args oracle}")
      n := n + 1
  IO.println s!"source = cased on {n} inputs, each under {oracles.length} oracles"

private def singles : Array (Array Int) := (Array.range 13).map fun (n : Nat) => #[(n : Int) - 6]

/-! ## Three constructors and pre-bound arguments

The existing branch arms pass arguments. The empty arm passes nothing, so the tester branches
straight to it. The other arms pass a bound argument, then one field or two; each arm's result
changes if two of its parameters are exchanged. Existing case.9 and cases.5 reserve generated
names. The block that tests the later constructors is numbered after the blocks of their
arms. -/

private def choice := "module m {
  func @choice(%n.0 : base.Int) -> base.Int {
    cases.5(%n.0 : base.Int):
      %case.9 : base.Int = const 100
      %neg.0 : base.Bool = while.lt(%n.0, 0)
      branch(%neg.0) ^negative.0(%n.0) ^nonnegative.0(%n.0)
    negative.0(%n.1 : base.Int):
      %empty.0 : test.Choice(base.Int) = test.empty[base.Int]()
      jump ^dispatch.0(%empty.0)
    nonnegative.0(%n.2 : base.Int):
      %small.0 : base.Bool = while.le(%n.2, 2)
      branch(%small.0) ^single.0(%n.2) ^double.0(%n.2)
    single.0(%n.3 : base.Int):
      %seven.0 : base.Int = while.add(%n.3, 7)
      %one.0 : test.Choice(base.Int) = test.one[base.Int](%seven.0)
      jump ^dispatch.0(%one.0)
    double.0(%n.4 : base.Int):
      %plus.0 : base.Int = while.add(%n.4, 1)
      %pair.0 : test.Choice(base.Int) = test.pair[base.Int](%n.4, %plus.0)
      jump ^dispatch.0(%pair.0)
    dispatch.0(%value.0 : test.Choice(base.Int)):
      test.Choice.case[base.Int](%value.0) ^emptyArm.0() ^oneArm.0(%case.9) ^pairArm.0(%case.9)
    emptyArm.0():
      ret(%case.9)
    oneArm.0(%bound.1 : base.Int, %field.0 : base.Int):
      %diff.0 : base.Int = while.sub(%bound.1, %field.0)
      ret(%diff.0)
    pairArm.0(%bound.2 : base.Int, %left.0 : base.Int, %right.0 : base.Int):
      %diff.1 : base.Int = while.sub(%bound.2, %left.0)
      %tens.0 : base.Int = while.mul(%diff.1, 10)
      %sum.0 : base.Int = while.add(%tens.0, %right.0)
      ret(%sum.0)
  }
}"

/-- info: module m {
  func @choice(%n.0 : base.Int) -> base.Int {
    cases.5(%n.0 : base.Int):
      %neg.0 : base.Bool = while.lt(%n.0, 0)
      branch(%neg.0) ^cases.6() ^cases.7()
    cases.6():
      jump ^negative.0(%n.0)
    cases.7():
      jump ^nonnegative.0(%n.0)
    negative.0(%n.1 : base.Int):
      %empty.0 : test.Choice(base.Int) = test.empty[base.Int]
      jump ^dispatch.0(%empty.0)
    nonnegative.0(%n.2 : base.Int):
      %small.0 : base.Bool = while.le(%n.2, 2)
      branch(%small.0) ^cases.8() ^cases.9()
    cases.8():
      jump ^single.0(%n.2)
    cases.9():
      jump ^double.0(%n.2)
    single.0(%n.3 : base.Int):
      %seven.0 : base.Int = while.add(%n.3, 7)
      %one.0 : test.Choice(base.Int) = test.one[base.Int](%seven.0)
      jump ^dispatch.0(%one.0)
    double.0(%n.4 : base.Int):
      %plus.0 : base.Int = while.add(%n.4, 1)
      %pair.0 : test.Choice(base.Int) = test.pair[base.Int](%n.4, %plus.0)
      jump ^dispatch.0(%pair.0)
    dispatch.0(%value.0 : test.Choice(base.Int)):
      %case.10 : base.Bool = test.isNone[base.Int](%value.0)
      branch(%case.10) ^emptyArm.0() ^cases.12()
    cases.12():
      %case.11 : base.Bool = test.isOne[base.Int](%value.0)
      branch(%case.11) ^cases.10() ^cases.11()
    cases.10():
      %value.1 : base.Int = test.getOne[base.Int](%value.0)
      jump ^oneArm.0(100, %value.1)
    cases.11():
      %lhs.0 : base.Int = test.getLeft[base.Int](%value.0)
      %rhs.0 : base.Int = test.getRight[base.Int](%value.0)
      jump ^pairArm.0(100, %lhs.0, %rhs.0)
    emptyArm.0():
      ret(100)
    oneArm.0(%bound.1 : base.Int, %|field.0| : base.Int):
      %diff.0 : base.Int = while.sub(%bound.1, %|field.0|)
      ret(%diff.0)
    pairArm.0(%bound.2 : base.Int, %left.0 : base.Int, %right.0 : base.Int):
      %diff.1 : base.Int = while.sub(%bound.2, %left.0)
      %tens.0 : base.Int = while.mul(%diff.1, 10)
      %sum.0 : base.Int = while.add(%tens.0, %right.0)
      ret(%sum.0)
  }
}
source = cased on 13 inputs, each under 3 oracles -/
#guard_msgs in
#eval check choice [("choice", singles)] true

/-! ## Single-constructor cases, including a field of another type -/

private def single := "module m {
  func @unit_case() -> base.Int {
    entry.0():
      %u.0 : base.Unit = base.unit()
      %n.0 : base.Int = const 41
      base.Unit.case(%u.0) ^done.0(%n.0)
    done.0(%n.1 : base.Int):
      ret(%n.1)
  }
  func @single(%n.2 : base.Int) -> base.Int {
    start.0(%n.2 : base.Int):
      %bool.0 : base.Bool = while.lt(%n.2, 0)
      %only.0 : test.Only(base.Bool) = test.only[base.Bool](%bool.0)
      test.Only.case[base.Bool](%only.0) ^boolArm.0()
    boolArm.0(%bool.1 : base.Bool):
      branch(%bool.1) ^yes.0() ^no.0()
    yes.0():
      ret(1)
    no.0():
      ret(0)
  }
}"

/-- info: source = cased on 14 inputs, each under 3 oracles -/
#guard_msgs in
#eval check single [("unit_case", #[#[]]), ("single", singles)]

/-! A single constructor needs no tester, even if the supplied tester has a wrong rule. -/

/-- info: source = cased on 14 inputs, each under 3 oracles -/
#guard_msgs in
#eval check single [("unit_case", #[#[]]), ("single", singles)] false
  { ops with tester := fun _ => some CaseEnv.wrongIsNone.name }

/-! ## Exceptions and returned failures -/

private def exceptions := "module m {
  func @exceptions(%n.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int):
      %neg.0 : base.Bool = while.lt(%n.0, 0)
      branch(%neg.0) ^err.0() ^ok.0()
    err.0():
      %err.1 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%n.0)
      jump ^case.0(%err.1)
    ok.0():
      %ok.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%n.0)
      jump ^case.0(%ok.1)
    case.0(%result.0 : base.Except(base.Int, base.Int)):
      base.Except.case[base.Int, base.Int](%result.0) ^good.0() ^bad.0()
    good.0(%value.0 : base.Int):
      %out.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%value.0)
      ret(%out.0)
    bad.0(%exc.0 : base.Int):
      %out.1 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%exc.0)
      ret(%out.1)
  }
}"

/-- info: source = cased on 13 inputs, each under 3 oracles -/
#guard_msgs in
#eval check exceptions [("exceptions", singles)]

/-! ## Two type parameters with different field types -/

private def polymorphic := "module m {
  func @polymorphic(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %neg.0 : base.Bool = while.lt(%n.0, 0)
      branch(%neg.0) ^ok.0() ^err.0()
    ok.0():
      %ok.1 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%neg.0)
      base.Except.case[base.Int, base.Bool](%ok.1) ^bool.0(%n.0) ^int.0(%n.0)
    err.0():
      %err.1 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%n.0)
      base.Except.case[base.Int, base.Bool](%err.1) ^bool.0(%n.0) ^int.0(%n.0)
    bool.0(%bound.0 : base.Int, %b.0 : base.Bool):
      branch(%b.0) ^true.0(%bound.0) ^false.0(%bound.0)
    int.0(%bound.1 : base.Int, %e.0 : base.Int):
      %twice.0 : base.Int = while.mul(%bound.1, 2)
      %sum.0 : base.Int = while.add(%twice.0, %e.0)
      ret(%sum.0)
    true.0(%yes.0 : base.Int):
      ret(%yes.0)
    false.0(%no.0 : base.Int):
      %minus.0 : base.Int = while.neg(%no.0)
      ret(%minus.0)
  }
}"

/-- info: source = cased on 13 inputs, each under 3 oracles -/
#guard_msgs in
#eval check polymorphic [("polymorphic", singles)]

/-! ## A loop with list cases, effects and oracle choices

The nil arm passes a bound argument and no field, so it gets a block. -/

private def loop := "module m {
  func @loop(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %nil.0 : while.IntList = while.nil()
      %next.0 : base.Int = while.add(%n.0, 1)
      %tail.0 : while.IntList = while.cons(%next.0, %nil.0)
      %list.0 : while.IntList = while.cons(%n.0, %tail.0)
      jump ^head.0(%list.0, 0)
    head.0(%list.1 : while.IntList, %acc.0 : base.Int):
      while.IntList.case(%list.1) ^done.0(%acc.0) ^more.0(%acc.0)
    more.0(%acc.1 : base.Int, %h.0 : base.Int, %t.0 : while.IntList):
      %print.0 : base.Unit = while.print(%h.0)
      %tick.0 : base.Int = while.tick()
      %pick.0 : base.Int = while.pick(5)
      %twice.0 : base.Int = while.mul(%acc.1, 2)
      %a.0 : base.Int = while.add(%twice.0, %h.0)
      %a.1 : base.Int = while.add(%a.0, %pick.0)
      jump ^head.0(%t.0, %a.1)
    done.0(%r.0 : base.Int):
      ret(%r.0)
  }
}"

/-- info: source = cased on 13 inputs, each under 3 oracles -/
#guard_msgs in
#eval check loop [("loop", singles)]

/-! ## An instruction that faults before the case stays before the tests -/

private def fault := "module m {
  func @fault(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %empty.0 : test.Choice(base.Int) = test.empty[base.Int]()
      %bad.0 : base.Int = test.getOne[base.Int](%empty.0)
      test.Choice.case[base.Int](%empty.0) ^emptyArm.0() ^oneArm.0() ^pairArm.0()
    emptyArm.0():
      ret(%bad.0)
    oneArm.0(%v.0 : base.Int):
      ret(%v.0)
    pairArm.0(%l.0 : base.Int, %r.0 : base.Int):
      ret(%l.0)
  }
}"

/-- info: source = cased on 13 inputs, each under 3 oracles -/
#guard_msgs in
#eval check fault [("fault", singles)]

/-! ## Branch arms into the same block, and a named call -/

private def calls := "module m {
  func @callee(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %neg.0 : base.Int = while.neg(%x.0)
      %test.0 : base.Bool = while.lt(%x.0, 0)
      branch(%test.0) ^join.0(%x.0) ^join.0(%neg.0)
    join.0(%y.0 : base.Int):
      ret(%y.0)
  }
  func @caller(%x.1 : base.Int) -> base.Int {
    start.0(%x.1 : base.Int):
      %callee.0 : base.Fn([base.Int], base.Int) = const @callee
      %result.0 : base.Int = base.callCode[[base.Int], base.Int](%callee.0, %x.1)
      %only.0 : test.Only(base.Int) = test.only[base.Int](%result.0)
      test.Only.case[base.Int](%only.0) ^done.0()
    done.0(%value.0 : base.Int):
      ret(%value.0)
  }
}"

/-- info: source = cased on 26 inputs, each under 3 oracles -/
#guard_msgs in
#eval check calls [("callee", singles), ("caller", singles)]

/-! ## A mutually recursive pair

The case on the second datatype of the group has its nullary constructor last, which passes
nothing, so the tester's other edge goes straight to its block. Its first arm passes a bound
argument before two fields. The case on the first datatype passes two bound arguments, one of
the type of its second field. The values `first.0`, `rest.0` and `label.0` reserve field
names. -/

private def forest := "module m {
  func @forest(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %none.0 : test.Forest(base.Int) = test.bare[base.Int]()
      %leaf.0 : test.Rose(base.Int) = test.rose[base.Int](%n.0, %none.0)
      %more.0 : test.Forest(base.Int) = test.grown[base.Int](%leaf.0, %none.0)
      %seven.0 : base.Int = while.add(%n.0, 7)
      %root.0 : test.Rose(base.Int) = test.rose[base.Int](%seven.0, %none.0)
      %all.0 : test.Forest(base.Int) = test.grown[base.Int](%root.0, %more.0)
      jump ^walk.0(%all.0, 0)
    walk.0(%f.0 : test.Forest(base.Int), %acc.0 : base.Int):
      test.Forest.case[base.Int](%f.0) ^tree.0(%acc.0) ^done.0()
    tree.0(%acc.1 : base.Int, %first.0 : test.Rose(base.Int), %rest.0 : test.Forest(base.Int)):
      test.Rose.case[base.Int](%first.0) ^visit.0(%acc.1, %rest.0)
    visit.0(%acc.2 : base.Int, %rest.1 : test.Forest(base.Int), %label.0 : base.Int, %kids.0 : test.Forest(base.Int)):
      %pick.0 : base.Int = while.pick(3)
      %twice.0 : base.Int = while.mul(%acc.2, 2)
      %sum.0 : base.Int = while.add(%twice.0, %label.0)
      %next.0 : base.Int = while.add(%sum.0, %pick.0)
      jump ^walk.0(%rest.1, %next.0)
    done.0():
      ret(%acc.0)
  }
}"

/-- info: source = cased on 13 inputs, each under 3 oracles -/
#guard_msgs in
#eval check forest [("forest", singles)]

/-! ## Datatypes that the engine does not run

`StaticEnv` has a mutually recursive pair of which only the first takes a type parameter. The
case on the second, which takes none, reads its fields in order after the bound argument; the
case on the first is applied at `base.Bool`. A case on a datatype without constructors becomes
`unreachable`. -/

private def still := "module m {
  func @mixed(%u.0 : still.Untagged, %d.0 : base.Int) -> base.Int {
    entry.0(%u.0 : still.Untagged, %d.0 : base.Int):
      still.Untagged.case(%u.0) ^_(%d.0) ^stepArm.0(%d.0)
    stepArm.0(%d.1 : base.Int, %count.0 : base.Int, %next.0 : still.Tagged(base.Bool)):
      still.Tagged.case[base.Bool](%next.0) ^taggedArm.0(%count.0)
    taggedArm.0(%c.0 : base.Int, %tag.0 : base.Bool, %inner.0 : still.Untagged):
      branch(%tag.0) ^_(%c.0) ^_(%d.1)
  }
  func @never(%v.0 : still.Never) -> base.Int {
    entry.0(%v.0 : still.Never):
      still.Never.case(%v.0)
  }
}"

/-- info: module m {
  func @mixed(%u.0 : still.Untagged, %d.0 : base.Int) -> base.Int {
    entry.0(%u.0 : still.Untagged, %d.0 : base.Int):
      %case.0 : base.Bool = still.isStop(%u.0)
      branch(%case.0) ^cases.0() ^cases.1()
    cases.0():
      ret(%d.0)
    cases.1():
      %count.1 : base.Int = still.getCount(%u.0)
      %next.1 : still.Tagged(base.Bool) = still.getNext(%u.0)
      jump ^stepArm.0(%d.0, %count.1, %next.1)
    stepArm.0(%d.1 : base.Int, %count.0 : base.Int, %next.0 : still.Tagged(base.Bool)):
      %tag.1 : base.Bool = still.getTag[base.Bool](%next.0)
      %inner.1 : still.Untagged = still.getInner[base.Bool](%next.0)
      jump ^taggedArm.0(%count.0, %tag.1, %inner.1)
    taggedArm.0(%c.0 : base.Int, %tag.0 : base.Bool, %inner.0 : still.Untagged):
      branch(%tag.0) ^cases.2() ^cases.3()
    cases.2():
      ret(%c.0)
    cases.3():
      ret(%d.1)
  }
  func @never(%v.0 : still.Never) -> base.Int {
    entry.0(%v.0 : still.Never):
      unreachable
  }
} -/
#guard_msgs in
#eval do IO.print (toString (← lowered StaticEnv.env still).2)

/-! ## Specifications

The body keeps its parameters. Clauses keep their binders, free status and messages. Frames
and both regions of a ghost use the same traversal; a ghost has its own names.

* The invariant has a three-constructor case whose first arm goes to the region's exit, and a
  branch whose arms pass arguments to the exit.
* The innermost quantifier has a case whose first arm passes its field to the region's exit,
  and whose last arm passes a bound `base.Bool` before an `base.Int` field.
* The case under `old` keeps the failure successor of `old`.
* The extern function's clause has a branch whose arms pass arguments.
* The initializer's new value takes the id after the invariant's, so the ghost is not
  canonical, and its printed form reads back as a canonical one. -/

private def specs := "module m {
  ghost @m.g : base.Int = {
    init.0():
      %c.0 : test.Only(base.Int) = test.only[base.Int](7)
      test.Only.case[base.Int](%c.0) ^_()
  } invariant {
    invariant.0(%g.0 : base.Int):
      %c.1 : test.Choice(base.Int) = test.one[base.Int](%g.0)
      %zero.0 : base.Bool = test.same(%g.0, 0)
      test.Choice.case[base.Int](%c.1) ^_(%zero.0) ^some.0(%zero.0) ^both.0()
    some.0(%z.0 : base.Bool, %v.0 : base.Int):
      branch(%z.0) ^_(false) ^_(%z.0)
    both.0(%l.0 : base.Int, %r.0 : base.Int):
      %eq.0 : base.Bool = test.same(%l.0, %r.0)
      ret(%eq.0)
  }
  func @m.f(%n.0 : base.Int, %cell.0 : base.Ref(base.Int)) -> base.Int
    requires \"nested quantifiers\" {
      pre.0():
        %all.0 : base.Bool = test.all {
          outer.0(%x.0 : base.Int):
            %all.1 : base.Bool = test.all {
              inner.0(%y.0 : base.Int):
                %eq.1 : base.Bool = test.same(%x.0, %y.0)
                %e.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%eq.1)
                base.Except.case[base.Int, base.Bool](%e.0) ^_() ^innerErr.0(%eq.1)
              innerErr.0(%b.0 : base.Bool, %err.0 : base.Int):
                ret(%b.0)
            }
            ret(%all.1)
        }
        ret(%all.0)
    }
    ensures \"case under old\" {
      post.0(%r.1 : base.Int):
        %old.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.1():
            %e.2 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%n.0)
            base.Except.case[base.Int, base.Int](%e.2) ^oldOk.0() ^oldErr.0()
          oldOk.0(%v.1 : base.Int):
            %e.3 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.1)
            ret(%e.3)
          oldErr.0(%exc.0 : base.Int):
            %e.4 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%exc.0)
            ret(%e.4)
        }
        %eq.2 : base.Bool = test.same(%r.1, %old.0)
        ret(%eq.2)
      fail.0(%exc.1 : base.Int):
        ret(false)
    }
    reads(%cell.0, {
      read.0():
        %loc.0 : base.Loc = base.cellLoc[base.Int](%cell.0)
        %only.0 : test.Only(base.Loc) = test.only[base.Loc](%loc.0)
        test.Only.case[base.Loc](%only.0) ^readDone.0()
      readDone.0(%loc.1 : base.Loc):
        ret(%loc.1)
    })
    writes({
      write.0():
        %loc.2 : base.Loc = base.cellLoc[base.Int](%cell.0)
        %only.1 : test.Only(base.Loc) = test.only[base.Loc](%loc.2)
        test.Only.case[base.Loc](%only.1) ^writeDone.0()
      writeDone.0(%loc.3 : base.Loc):
        ret(%loc.3)
    })
  {
    entry.0(%n.0 : base.Int, %cell.0 : base.Ref(base.Int)):
      ret(%n.0)
  }
  extern func @m.ext(%n.1 : base.Int) -> base.Int
    free ensures \"trusted clause\" {
      extPost.0(%r.2 : base.Int):
        %only.2 : test.Only(base.Bool) = test.only[base.Bool](true)
        test.Only.case[base.Bool](%only.2) ^extDone.0()
      extDone.0(%b.1 : base.Bool):
        branch(%b.1) ^_(true) ^_(%b.1)
    }
}"

private def checkSpecs : IO Unit := do
  let (src, out) ← lowered CaseEnv.env specs
  unless sameInfo src.raw.info out.raw.info && src.raw.name == out.raw.name &&
      src.raw.funcs.size == out.raw.funcs.size && src.raw.ghosts.size == out.raw.ghosts.size do
    throw (IO.userError "module declarations or annotation changed")
  for (g, h) in src.raw.ghosts.zip out.raw.ghosts do
    unless g.name == h.name && g.type == h.type && sameInfo g.info h.info &&
        g.init.isSome == h.init.isSome && g.invariant.isSome == h.invariant.isSome do
      throw (IO.userError "ghost declaration or annotation changed")
  for (f, g) in src.raw.funcs.zip out.raw.funcs do
    unless f.name == g.name && f.params == g.params && f.retType == g.retType &&
        f.extern == g.extern && sameInfo f.info g.info do
      throw (IO.userError "function signature or annotation changed")
    unless f.contract.requires.size == g.contract.requires.size &&
        f.contract.ensures.size == g.contract.ensures.size &&
        f.contract.reads.map (·.map FrameEntry.cell?) == g.contract.reads.map (·.map FrameEntry.cell?) &&
        f.contract.writes.map (·.map FrameEntry.cell?) == g.contract.writes.map (·.map FrameEntry.cell?) do
      throw (IO.userError "clauses or frame entries changed")
    for (c, d) in (f.contract.requires ++ f.contract.ensures).zip
        (g.contract.requires ++ g.contract.ensures) do
      unless c.free == d.free && c.message == d.message &&
          c.region.blocks[0]?.map (·.params) == d.region.blocks[0]?.map (·.params) do
        throw (IO.userError "clause status, message or binders changed")
  for b in src.raw.allBlocks do
    let some c := out.raw.allBlocks.find? (·.label == b.label)
      | throw (IO.userError "an original label disappeared")
    unless sameInfo b.info c.info && b.params == c.params do
      throw (IO.userError "an original block's annotation or binders changed")
  let back ← load (toString out)
  unless out.raw.ghosts.all (!decide ·.Canonical) && back.raw.ghosts.all (decide ·.Canonical) &&
      back.raw.funcs.all (decide ·.Canonical) do
    throw (IO.userError "the ghost's ids are canonical, or a read-back's are not")
  IO.print (toString out)

/-- info: module m {
  ghost @m.g : base.Int = {
    init.0():
      %c.0 : test.Only(base.Int) = test.only[base.Int](7)
      %value.0 : base.Int = test.getOnly[base.Int](%c.0)
      ret(%value.0)
  } invariant {
    invariant.0(%g.0 : base.Int):
      %c.1 : test.Choice(base.Int) = test.one[base.Int](%g.0)
      %zero.0 : base.Bool = test.same(%g.0, 0)
      %case.0 : base.Bool = test.isNone[base.Int](%c.1)
      branch(%case.0) ^cases.0() ^cases.3()
    cases.0():
      ret(%zero.0)
    cases.3():
      %case.1 : base.Bool = test.isOne[base.Int](%c.1)
      branch(%case.1) ^cases.1() ^cases.2()
    cases.1():
      %value.1 : base.Int = test.getOne[base.Int](%c.1)
      jump ^some.0(%zero.0, %value.1)
    cases.2():
      %lhs.0 : base.Int = test.getLeft[base.Int](%c.1)
      %rhs.0 : base.Int = test.getRight[base.Int](%c.1)
      jump ^both.0(%lhs.0, %rhs.0)
    some.0(%z.0 : base.Bool, %v.0 : base.Int):
      branch(%z.0) ^cases.4() ^cases.5()
    cases.4():
      ret(false)
    cases.5():
      ret(%z.0)
    both.0(%l.0 : base.Int, %r.0 : base.Int):
      %eq.0 : base.Bool = test.same(%l.0, %r.0)
      ret(%eq.0)
  }
  func @m.f(%n.0 : base.Int, %cell.0 : base.Ref(base.Int)) -> base.Int
    requires "nested quantifiers" {
      pre.0():
        %all.0 : base.Bool = test.all {
          outer.0(%x.0 : base.Int):
            %all.1 : base.Bool = test.all {
              inner.0(%y.0 : base.Int):
                %eq.1 : base.Bool = test.same(%x.0, %y.0)
                %e.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%eq.1)
                %case.0 : base.Bool = test.isOk[base.Int, base.Bool](%e.0)
                branch(%case.0) ^cases.0() ^cases.1()
              cases.0():
                %value.0 : base.Bool = test.getOk[base.Int, base.Bool](%e.0)
                ret(%value.0)
              cases.1():
                %err.1 : base.Int = test.getError[base.Int, base.Bool](%e.0)
                jump ^innerErr.0(%eq.1, %err.1)
              innerErr.0(%b.0 : base.Bool, %err.0 : base.Int):
                ret(%b.0)
            }
            ret(%all.1)
        }
        ret(%all.0)
    }
    ensures "case under old" {
      post.0(%r.1 : base.Int):
        %old.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.1():
            %e.2 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%n.0)
            %case.1 : base.Bool = test.isOk[base.Int, base.Int](%e.2)
            branch(%case.1) ^cases.2() ^cases.3()
          cases.2():
            %value.1 : base.Int = test.getOk[base.Int, base.Int](%e.2)
            jump ^oldOk.0(%value.1)
          cases.3():
            %err.2 : base.Int = test.getError[base.Int, base.Int](%e.2)
            jump ^oldErr.0(%err.2)
          oldOk.0(%v.1 : base.Int):
            %e.3 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.1)
            ret(%e.3)
          oldErr.0(%exc.0 : base.Int):
            %e.4 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%exc.0)
            ret(%e.4)
        }
        %eq.2 : base.Bool = test.same(%r.1, %old.0)
        ret(%eq.2)
      fail.0(%exc.1 : base.Int):
        ret(false)
    }
    reads(%cell.0, {
      read.0():
        %loc.0 : base.Loc = base.cellLoc[base.Int](%cell.0)
        %only.0 : test.Only(base.Loc) = test.only[base.Loc](%loc.0)
        %value.2 : base.Loc = test.getOnly[base.Loc](%only.0)
        jump ^readDone.0(%value.2)
      readDone.0(%loc.1 : base.Loc):
        ret(%loc.1)
    })
    writes({
      write.0():
        %loc.2 : base.Loc = base.cellLoc[base.Int](%cell.0)
        %only.1 : test.Only(base.Loc) = test.only[base.Loc](%loc.2)
        %value.3 : base.Loc = test.getOnly[base.Loc](%only.1)
        jump ^writeDone.0(%value.3)
      writeDone.0(%loc.3 : base.Loc):
        ret(%loc.3)
    })
  {
    entry.0(%n.0 : base.Int, %cell.0 : base.Ref(base.Int)):
      ret(%n.0)
  }
  extern func @m.ext(%n.1 : base.Int) -> base.Int
    free ensures "trusted clause" {
      extPost.0(%r.2 : base.Int):
        %only.2 : test.Only(base.Bool) = test.only[base.Bool](true)
        %value.0 : base.Bool = test.getOnly[base.Bool](%only.2)
        jump ^extDone.0(%value.0)
      extDone.0(%b.1 : base.Bool):
        branch(%b.1) ^cases.0() ^cases.1()
      cases.0():
        ret(true)
      cases.1():
        ret(%b.1)
    }
} -/
#guard_msgs in
#eval checkSpecs

/-! ## Refused accessors

Each vocabulary is refused on a source that the valid accessors lower, with the reason, the
function or ghost and the block compared as values. The refused accessors are those of
`StaticEnv`: each differs from a valid one in one respect. -/

/-- `vocab` is refused on `text` with exactly `expected`; `ops` is accepted on it. -/
private def reject (text : String) (vocab : CaseOps) (expected : Cases.Error) : IO Unit := do
  let src ← read StaticEnv.env text
  discard <| lower src
  match ← tryLower src vocab with
  | .error e => unless decide (e = expected) do throw (IO.userError (showError e))
  | .ok _ => throw (IO.userError s!"accepted; expected {showError expected}")

private def inFunc (func block : String) (reason : Cases.Reason) : Cases.Error :=
  .accessor (nm func) ⟨.num (nm block) 0⟩ reason

private def testerIs (name : Name) : CaseOps := { ops with tester := fun _ => some name }

private def selectorIs (name : Name) : CaseOps := { ops with selector := fun _ _ => some name }

/-! An accessor that is missing, that is not an instruction, or that does not take the
datatype's type parameters. -/

#guard_msgs in
#eval do
  reject choice { ops with tester := fun _ => none }
    (inFunc "choice" "dispatch" (.noTester CaseEnv.Choice.empty.name))
  reject choice { ops with selector := fun _ _ => none }
    (inFunc "choice" "dispatch" (.noSelector CaseEnv.Choice.one.name "value"))
  reject choice (testerIs (nm "absent")) (inFunc "choice" "dispatch" (.notInstruction (nm "absent")))
  reject choice (testerIs CaseEnv.Choice.name)
    (inFunc "choice" "dispatch" (.notInstruction CaseEnv.Choice.name))
  reject choice (testerIs While.eq.name) (inFunc "choice" "dispatch" (.typeArgs While.eq.name))
  reject choice (testerIs StaticEnv.noTypeParams.name)
    (inFunc "choice" "dispatch" (.typeArgs StaticEnv.noTypeParams.name))

/-! An accessor with another signature: its result type, its effect, a successor, a region, a
second operand, variadic operands, the operand's type, and type parameters in another order. -/

#guard_msgs in
#eval do
  reject choice (testerIs StaticEnv.resultType.name)
    (inFunc "choice" "dispatch" (.accessorType StaticEnv.resultType.name))
  for name in [StaticEnv.effect.name, StaticEnv.successor.name, StaticEnv.region.name,
      StaticEnv.secondOperand.name, StaticEnv.variadic.name, CaseEnv.getOnly.name] do
    reject choice (selectorIs name) (inFunc "choice" "dispatch" (.accessorType name))
  reject polymorphic (selectorIs StaticEnv.paramOrder.name)
    (inFunc "polymorphic" "ok" (.accessorType StaticEnv.paramOrder.name))

/-! A rejection names a block of a nested region, and a ghost. Ghosts come first, as they
print, so the ghost's rejection is reported although the frames of `m.f` need the same
selector. -/

#guard_msgs in
#eval do
  reject specs { ops with tester := fun c => if c == Base.Except.ok.name then none else ops.tester c }
    (.accessor (.str (nm "m") "f") ⟨.num (nm "inner") 0⟩ (.noTester Base.Except.ok.name))
  reject specs { ops with selector := fun c f =>
      if c == CaseEnv.Only.only.name then none else ops.selector c f }
    (.accessor (.str (nm "m") "g") ⟨.num (nm "init") 0⟩ (.noSelector CaseEnv.Only.only.name "value"))

/-! ## Accessors with wrong rules

Signatures do not establish what an accessor computes: each vocabulary below passes the
signature, shape and well-formedness checks, and the comparison of runs catches it. -/

private def differs (what : String) (vocab : CaseOps) (n : Int) : IO Unit := do
  let (src, out) ← lowered CaseEnv.env choice vocab
  if observe src "choice" #[n] (fun _ => 0) == observe out "choice" #[n] (fun _ => 0) then
    throw (IO.userError s!"the comparison of runs missed {what}")
  IO.println s!"{what}: accepted, and the runs differ"

private def alwaysEmpty : CaseOps :=
  { ops with
    tester := fun c =>
      if c == CaseEnv.Choice.empty.name then some CaseEnv.wrongIsNone.name else ops.tester c }

private def fieldsExchanged : CaseOps :=
  { ops with
    selector := fun c f =>
      if c == CaseEnv.Choice.pair.name then ops.selector c (if f == "lhs" then "rhs" else "lhs")
      else ops.selector c f }

/-- info: a tester that is always true: accepted, and the runs differ
selectors of the two fields exchanged: accepted, and the runs differ -/
#guard_msgs in
#eval do
  differs "a tester that is always true" alwaysEmpty 5
  differs "selectors of the two fields exchanged" fieldsExchanged 5

/-! ## The input shape

Each module outside the input shape is beside the same module without the one feature, which
is inside it. A well-formed module has only control and cases in its specifications, so the
last module is built, not read. -/

private def secondExit := "module m {
  func @second_exit(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %r.0 : base.Int = while.div(%n.0, 0) ^error.0()
      ret(%r.0)
    error.0(%e.0 : base.Int):
      ret(%e.0)
  }
}"

private def noSecondExit := "module m {
  func @second_exit(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %r.0 : base.Int = while.mul(%n.0, 0)
      ret(%r.0)
  }
}"

private def bodyRegion := "module m {
  func @nested() -> base.Int {
    entry.0():
      %all.0 : base.Bool = test.all {
        inner.0(%x.0 : base.Int):
          ret(true)
      }
      ret(0)
  }
}"

private def noBodyRegion := "module m {
  func @nested() -> base.Int {
    entry.0():
      ret(0)
  }
}"

private def otherTerm := "module m {
  func @other_term() -> base.Int {
    entry.0():
      test.halt()
  }
}"

private def noOtherTerm := "module m {
  func @other_term() -> base.Int {
    entry.0():
      unreachable
  }
}"

private def clause := "module m {
  func @clause() -> base.Int
    requires \"holds\" {
      pre.0():
        ret(true)
    }
  {
    entry.0():
      ret(0)
  }
}"

/-- `m` with `t` as the terminator of each block of its `requires` clauses. -/
private def withClauseTerm (t : Terminator CaseEnv.env Info) (m : Module.Raw CaseEnv.env Info) :
    Module.Raw CaseEnv.env Info :=
  { m with funcs := m.funcs.map fun fn => { fn with contract := { fn.contract with
      requires := fn.contract.requires.map fun c =>
        { c with region := ⟨c.region.blocks.map ({ · with term := t })⟩ } } } }

private def inputShapes : IO Unit := do
  for (what, outside, inside) in [("a second exit", secondExit, noSecondExit),
      ("a region in a body", bodyRegion, noBodyRegion),
      ("another terminator", otherTerm, noOtherTerm)] do
    if decide (CasesInput (← load outside).raw) then throw (IO.userError s!"{what} was admitted")
    unless decide (CasesInput (← load inside).raw) do
      throw (IO.userError s!"the module without {what} was refused")
  let some halt := (← load otherTerm).raw.allBlocks.head?.map (·.term)
    | throw (IO.userError "no terminator")
  let inside := (← load clause).raw
  if decide (CasesInput (withClauseTerm halt inside)) then
    throw (IO.userError "another terminator in a specification was admitted")
  unless decide (CasesInput inside) do throw (IO.userError "a plain specification was refused")
  IO.println "outside the input shape, each beside an admitted twin: a second exit, a region \
    in a body, another terminator, another terminator in a specification"

/-- info: outside the input shape, each beside an admitted twin: a second exit, a region in a body, another terminator, another terminator in a specification -/
#guard_msgs in
#eval inputShapes

/-! ## The output shape, and the rejections that no admissible input is known to reach

`Cased` does not hold of a source with only a case, only a branch that passes arguments, or
only a case in a clause; it holds of each one's lowering, by the type of `cases`. The two halves
of `cases` are private, so that no caller can skip the input shape; they are run here on what
`cases` itself never gives them.

* A module that is not in the output shape is `internal`, as is the lowering of a terminator
  that is neither control nor a case: the terminator stays, and the output shape refuses it.
* A module in the output shape that is not well formed is `illFormed`, with its function. -/

private def caseOnly := "module m {
  func @case_only() -> base.Int {
    entry.0():
      %only.0 : test.Only(base.Int) = test.only[base.Int](1)
      test.Only.case[base.Int](%only.0) ^_()
  }
}"

private def branchOnly := "module m {
  func @branch_only(%b.0 : base.Bool) -> base.Int {
    entry.0(%b.0 : base.Bool):
      branch(%b.0) ^_(1) ^_(0)
  }
}"

private def clauseOnly := "module m {
  func @clause_only() -> base.Int
    requires \"holds\" {
      pre.0():
        %only.0 : test.Only(base.Bool) = test.only[base.Bool](true)
        test.Only.case[base.Bool](%only.0) ^_()
    }
  {
    entry.0():
      ret(0)
  }
}"

private def isInternal {α : Type} : Except Cases.Error α → Bool
  | .error .internal => true
  | _ => false

private def outputShapes : IO Unit := do
  for (what, text) in [("a case", caseOnly), ("a branch that passes arguments", branchOnly),
      ("a case in a clause", clauseOnly)] do
    let (src, out) ← lowered CaseEnv.env text
    if decide (Cased src.raw) then throw (IO.userError s!"{what} is in the output shape")
    unless isInternal (Cases.certify src.raw) do
      throw (IO.userError s!"{what}: the unlowered source is not an internal rejection")
    unless (Cases.certify out.raw).isOk do
      throw (IO.userError s!"{what}: the lowered module is refused")
  let halted := (← load otherTerm).raw
  unless isInternal (Cases.lower ops halted >>= Cases.certify) do
    throw (IO.userError "another terminator is not an internal rejection")
  unless (Cases.lower ops (← load noOtherTerm).raw >>= Cases.certify).isOk do
    throw (IO.userError "the module without the other terminator is refused")
  let (_, out) ← lowered CaseEnv.env caseOnly
  let broken := { out.raw with funcs := out.raw.funcs.map ({ · with retType := Base.Bool }) }
  match Cases.certify broken with
  | .error (.illFormed names) =>
    unless names == #[nm "case_only"] do throw (IO.userError s!"ill-formed {reprStr names}")
  | _ => throw (IO.userError "a function with another return type is not ill-formed")
  IO.println "internal: an unlowered case, branch or clause, and another terminator; \
    ill-formed: another return type; each beside an accepted twin"

/-- info: internal: an unlowered case, branch or clause, and another terminator; ill-formed: another return type; each beside an accepted twin -/
#guard_msgs in
#eval outputShapes

/-- info: source = cased on 0 inputs, each under 3 oracles -/
#guard_msgs in
#eval check "module m {}" []

/-! ## What the runs reach

Successful runs take every constructor's arm, effects consume choices, and the fault is
genuine. -/

private def outcomes : IO Unit := do
  for (text, f, ns) in [(choice, "choice", #[-1, 0, 2, 5]), (polymorphic, "polymorphic", #[-2, 2]),
      (loop, "loop", #[2]), (forest, "forest", #[2]), (exceptions, "exceptions", #[-2, 2]),
      (fault, "fault", #[0])] do
    let m ← load text
    for n in ns do IO.println s!"{f}({n}): {observe m f #[n] (fun k => k)}"

/-- info: choice(-1): ok 100; printed #[]; ticks 0; oracle 0
choice(0): ok 93; printed #[]; ticks 0; oracle 0
choice(2): ok 91; printed #[]; ticks 0; oracle 0
choice(5): ok 956; printed #[]; ticks 0; oracle 0
polymorphic(-2): ok -2; printed #[]; ticks 0; oracle 0
polymorphic(2): ok 6; printed #[]; ticks 0; oracle 0
loop(2): ok 8; printed #[2, 3]; ticks 2; oracle 2
forest(2): ok 21; printed #[]; ticks 0; oracle 2
exceptions(-2): raised -2; printed #[]; ticks 0; oracle 0
exceptions(2): ok 2; printed #[]; ticks 0; oracle 0
fault(0): fault failure: expected one; printed #[]; ticks 0; oracle 0 -/
#guard_msgs in
#eval outcomes

/-! ## The empty module, and the theorems' axioms

`decide` proves the two shapes of a module without functions, where no instance tests an
operation's name. Of any other module the instances only run as compiled code. -/

private def emptyRaw : Module.Raw CaseEnv.env Unit := { name := .base, funcs := #[], info := () }

example : CasesInput emptyRaw := by decide
example : Cased emptyRaw := by decide

/-- info: 'Strata.Dyn.casesInput_cased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Strata.Dyn.casesInput_cased

/-- info: 'Strata.Dyn.demotable_cased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Strata.Dyn.demotable_cased

/-- info: 'Strata.Dyn.Module.Raw.mem_allBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Strata.Dyn.Module.Raw.mem_allBlocks

/-- info: 'Strata.Dyn.cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Strata.Dyn.cases

end Strata.Dyn.CasesTest
