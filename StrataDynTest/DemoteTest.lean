/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Demote
public import StrataDyn.DDMRead
public import StrataDyn.Examples.While.Run
public import StrataDynTest.RefToRegSim
import all StrataDynTest.CasesTest
import StrataDyn.Env.WF
-- The reader, the pass, the printer, the engine and the simulation run as compiled code below.
meta import StrataDyn.Demote
meta import StrataDyn.DDMRead
meta import StrataDyn.Examples.While.Run
meta import StrataDynTest.RefToRegSim
meta import all StrataDynTest.CasesTest
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Demoting block parameters to private cells

Small modules over While's environment, written by hand in the shape that `demote` assumes and
read from their printed form.  `check` demotes a module and prints the result, which must read
back as it prints.  Then it compares the result with the source in three ways:

* a function of the module runs on Dyn's engine in both, on the same arguments under the same
  oracles, and must end the same and print the same;
* each function and its demoted form run side by side on symbols, along random paths and one
  path per edge (`RefToRegSim.sameRuns`, the property test of ref-to-reg, with the demoted form
  as the side that has the cells);
* ref-to-reg promotes eligible cells again; a used write result leaves its cell in place,
  so the remaining reads and writes are pinned for each fixture.

The modules: a loop whose head takes two parameters, with a swap on a back edge; parameters of
two types, in a loop that prints and makes choices, and a join; a parameter of a datatype, with
a caller-supplied default, beside a call; a parameter of `base.Except`, whose default is built
from another; existing private cells beside demoted parameters, including a used write result;
and a contract, whose clause keeps its own parameter, beside an extern function and a ghost.
Then a wrong demotion, which the side-by-side run catches, what the pass rejects, each rejection
compared with the
`Demote.Error` expected, and the shapes it does not take.
-/

namespace Strata.Dyn.DemoteTest

open Strata.Dyn.Exec Strata.Dyn.While Strata.Dyn.RefToReg
open Strata.Dyn.ToDDM (nameText)

/-! ## The comparisons -/

/-- What a run of `f` in `m` on `args` shows: how it ended, and what it printed. -/
private def observe {α : Type} (m : Module While.env α) (f : String) (oracle : Nat → Nat)
    (args : Array Int) : String :=
  let o := runModule WhileSem.model m (nm f) (args.map (WhileSem.model.arg ·)) 100000 oracle
  s!"{showOutcome o}; printed {o.snapshot.world.out.items}"

/-- The oracles the runs take their choices from. -/
private def oracles : List (Nat → Nat) := CasesTest.oracles

/-- Print whether `f` shows the same in `src` and `tgt` on each of `inputs` under each oracle,
and each run in which it does not. -/
private def sameOnEngine {α : Type} (src tgt : Module While.env α) (f : String)
    (inputs : Array (Array Int)) : IO Unit := do
  let mut same := 0
  for oracle in oracles do
    for args in inputs do
      let s := observe src f oracle args
      let t := observe tgt f oracle args
      if s == t then same := same + 1 else IO.println s!"{args}: source {s}, demoted {t}"
  IO.println s!"on the engine: the same on {same} of {oracles.length * inputs.size} runs"

/-- The first difference between `src` and its demoted form `dem`, run side by side on
symbols, or `none`.  The simulation runs a function with cells against one that promotes them,
and both keep each `refNew`.  So `dem` is the side with the cells, and the other side is `src`
with the instructions that `demote` put first in `dem`'s entry block, which make the cells. -/
private def differs {α : Type} (src dem : Func While.env α) : Option String := do
  let entry ← src.blocks[0]?
  let demEntry ← dem.blocks[0]?
  let isNew (i : Instruction While.env α) : Bool := src.names.size ≤ i.result.id.id
  let allocs := demEntry.instrs.takeWhile fun i => isNew i && !(cellOp? i matches some (.set ..))
  let promoted := { src with
    blocks := src.blocks.set! 0 { entry with instrs := allocs ++ entry.instrs } }
  let plan : Plan While.env :=
    { promoted := .ofList (allocs.toList.filterMap fun i =>
        match cellOp? i with
        | some (.new c _) => some c
        | _ => none) }
  RefToRegSim.sameRuns plan dem promoted 7 200 400

/-- Print, for each function of `src`, whether it and its form in `dem` run alike side by
side, or the first difference. -/
private def sameOnSymbols {α : Type} (src dem : Module While.env α) : IO Unit :=
  for (f, g) in src.raw.funcs.zip dem.raw.funcs do
    let result := if f.blocks.isEmpty then "no body" else (differs f g).getD "the same"
    IO.println s!"on symbols: {nameText f.name}: {result}"

/-- The reads and writes of cells in `m`'s bodies. -/
private def cellUses {α : Type} (m : Module While.env α) : Nat :=
  m.raw.funcs.foldl (init := 0) fun n fn => fn.blocks.foldl (init := n) fun n b =>
    b.instrs.foldl (init := n) fun n i =>
      match cellOp? i with
      | some (.get ..) | some (.set ..) => n + 1
      | _ => n

/-- A rejection, in words. -/
private def describe : Demote.Error → String
  | .noDefault param block =>
    s!"no default value for the type of %{nameText param}, a parameter of ^{nameText block.name}"
  | .notPrivate => "a reference is not a private cell"
  | .illFormed => "the demoted function is not well formed"

private def report (es : Array (Name × Demote.Error)) : IO Unit :=
  for (n, e) in es do IO.println s!"{nameText n}: {describe e}"

/-- Read `text` and demote it with `defaults`; print the result, and compare it with the source:
`f` on the engine on `inputs`, every function on symbols, and the result promoted again. -/
private def check (text : String) (f : String) (inputs : Array (Array Int))
    (defaults : Demote.Defaults While.env := .literals) : IO Unit := do
  match ← Module.read While.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    if h : Demotable m.raw then
      match demote defaults m h with
      | .error es => report es
      | .ok ⟨dm, _⟩ =>
        IO.print (toString dm)
        match ← Module.read While.env (toString dm) "demoted.dyn" with
        | .error e => IO.println e
        | .ok rm =>
          unless toString rm == toString dm do IO.println "the result reads back differently"
        sameOnEngine m dm f inputs
        sameOnSymbols m dm
        match refToReg dm with
        | .error es => for (n, e) in es do IO.println s!"promoted again: {nameText n}: {e}"
        | .ok pm =>
          IO.println s!"promoted again: {cellUses pm} of {cellUses dm} cell reads and writes left"
    else
      IO.println s!"not demotable: plain control: {decide (PlainControl m.raw)}, \
        bare branches: {decide (BareBranches m.raw)}"

/-- The integers from `-n` to `n`. -/
private def ints (n : Nat) : Array Int :=
  (Array.range (2 * n + 1)).map fun (k : Nat) => (k : Int) - n

/-- Each integer from `-n` to `n`, as the one argument of a run. -/
private def singles (n : Nat) : Array (Array Int) := (ints n).map (#[·])

/-- Each pair of integers from `-n` to `n`, as the two arguments of a run. -/
private def pairs (n : Nat) : Array (Array Int) :=
  (ints n).flatMap fun a => (ints n).map (#[a, ·])

/-! ## A loop with a swap

The head's two parameters become cells, made in the entry block.  Each jump to the head writes
both.  The writes of the swap in `swap.0` read `%b.1` and `%a.1`, the values that the head read,
so they need no temporary. -/

private def gcd := "module m {
  func @gcd(%a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Int):
      jump ^head.0(%a.0, %b.0)
    head.0(%a.1 : base.Int, %b.1 : base.Int):
      %z.0 : base.Bool = while.eq(%b.1, 0)
      branch(%z.0) ^done.0() ^body.0()
    body.0():
      %lt.0 : base.Bool = while.lt(%a.1, %b.1)
      branch(%lt.0) ^swap.0() ^less.0()
    swap.0():
      jump ^head.0(%b.1, %a.1)
    less.0():
      %d.0 : base.Int = while.sub(%a.1, %b.1)
      jump ^head.0(%d.0, %b.1)
    done.0():
      ret(%a.1)
  }
}
"

/--
info: module m {
  func @gcd(%a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Int):
      %a.cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %b.cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %set.0 : base.Unit = base.refSet[base.Int](%a.cell.0, %a.0)
      %set.1 : base.Unit = base.refSet[base.Int](%b.cell.0, %b.0)
      jump ^head.0()
    head.0():
      %a.1 : base.Int = base.refGet[base.Int](%a.cell.0)
      %b.1 : base.Int = base.refGet[base.Int](%b.cell.0)
      %z.0 : base.Bool = while.eq(%b.1, 0)
      branch(%z.0) ^done.0() ^body.0()
    body.0():
      %lt.0 : base.Bool = while.lt(%a.1, %b.1)
      branch(%lt.0) ^swap.0() ^less.0()
    swap.0():
      %set.2 : base.Unit = base.refSet[base.Int](%a.cell.0, %b.1)
      %set.3 : base.Unit = base.refSet[base.Int](%b.cell.0, %a.1)
      jump ^head.0()
    less.0():
      %d.0 : base.Int = while.sub(%a.1, %b.1)
      %set.4 : base.Unit = base.refSet[base.Int](%a.cell.0, %d.0)
      %set.5 : base.Unit = base.refSet[base.Int](%b.cell.0, %b.1)
      jump ^head.0()
    done.0():
      ret(%a.1)
  }
}
on the engine: the same on 147 of 147 runs
on symbols: gcd: the same
promoted again: 0 of 8 cell reads and writes left
-/
#guard_msgs in
#eval check gcd "gcd" ((pairs 6).filter fun args => args.all (0 ≤ ·))

/-! ## Two types, effects and a join

A loop that prints and takes a choice from the oracle in each iteration, over an integer
counter, an integer sum and a boolean; then a join that two blocks jump to. -/

/--
info: module m {
  func @count(%n.0 : base.Int, %k.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int, %k.0 : base.Int):
      %i.cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %acc.cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %odd.cell.0 : base.Ref(base.Bool) = base.refNew[base.Bool](false)
      %res.cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %set.0 : base.Unit = base.refSet[base.Int](%i.cell.0, %n.0)
      %set.1 : base.Unit = base.refSet[base.Int](%acc.cell.0, 0)
      %set.2 : base.Unit = base.refSet[base.Bool](%odd.cell.0, false)
      jump ^loop.0()
    loop.0():
      %i.0 : base.Int = base.refGet[base.Int](%i.cell.0)
      %acc.0 : base.Int = base.refGet[base.Int](%acc.cell.0)
      %odd.0 : base.Bool = base.refGet[base.Bool](%odd.cell.0)
      %pos.0 : base.Bool = while.lt(0, %i.0)
      branch(%pos.0) ^step.0() ^exit.0()
    step.0():
      %u.0 : base.Unit = while.print(%acc.0)
      %r.0 : base.Int = while.pick(%k.0)
      %i.1 : base.Int = while.sub(%i.0, 1)
      %acc.1 : base.Int = while.add(%acc.0, %r.0)
      %odd.1 : base.Bool = while.not(%odd.0)
      %set.3 : base.Unit = base.refSet[base.Int](%i.cell.0, %i.1)
      %set.4 : base.Unit = base.refSet[base.Int](%acc.cell.0, %acc.1)
      %set.5 : base.Unit = base.refSet[base.Bool](%odd.cell.0, %odd.1)
      jump ^loop.0()
    exit.0():
      branch(%odd.0) ^negate.0() ^keep.0()
    negate.0():
      %neg.0 : base.Int = while.neg(%acc.0)
      %set.6 : base.Unit = base.refSet[base.Int](%res.cell.0, %neg.0)
      jump ^finish.0()
    keep.0():
      %set.7 : base.Unit = base.refSet[base.Int](%res.cell.0, %acc.0)
      jump ^finish.0()
    finish.0():
      %res.0 : base.Int = base.refGet[base.Int](%res.cell.0)
      ret(%res.0)
  }
}
on the engine: the same on 243 of 243 runs
on symbols: count: the same
promoted again: 0 of 12 cell reads and writes left
-/
#guard_msgs in
#eval check "module m {
  func @count(%n.0 : base.Int, %k.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int, %k.0 : base.Int):
      %zero.0 : base.Int = const 0
      %no.0 : base.Bool = const false
      jump ^loop.0(%n.0, %zero.0, %no.0)
    loop.0(%i.0 : base.Int, %acc.0 : base.Int, %odd.0 : base.Bool):
      %pos.0 : base.Bool = while.lt(0, %i.0)
      branch(%pos.0) ^step.0() ^exit.0()
    step.0():
      %u.0 : base.Unit = while.print(%acc.0)
      %r.0 : base.Int = while.pick(%k.0)
      %i.1 : base.Int = while.sub(%i.0, 1)
      %acc.1 : base.Int = while.add(%acc.0, %r.0)
      %odd.1 : base.Bool = while.not(%odd.0)
      jump ^loop.0(%i.1, %acc.1, %odd.1)
    exit.0():
      branch(%odd.0) ^negate.0() ^keep.0()
    negate.0():
      %neg.0 : base.Int = while.neg(%acc.0)
      jump ^finish.0(%neg.0)
    keep.0():
      jump ^finish.0(%acc.0)
    finish.0(%res.0 : base.Int):
      ret(%res.0)
  }
}
" "count" (pairs 4)

/-! ## A datatype's default, and a call

`while.IntList` has no literal, so the caller gives its default: the constructor `nil`.  The
function `@inc` has no block parameter and stays as it is. -/

/-- The literals, and `nil` for `while.IntList`. -/
private def withNil : Demote.Defaults While.env := fun τ =>
  if τ = While.IntList then some (.apply While.IntList.nil.ref ⟨#[], rfl⟩ rfl [])
  else Demote.Defaults.literals τ

/-! An operation with an effect is no default: `Demote.Default.apply` takes the proof that the
operation is pure, and `while.tick`, which counts how often it ran, has none. -/

example : (While.tick.sig (e := While.env)).effect ≠ .pure := by decide

private def range := "module m {
  func @inc(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %y.0 : base.Int = while.add(%x.0, 1)
      ret(%y.0)
  }
  func @range(%n.0 : base.Int) -> while.IntList {
    entry.0(%n.0 : base.Int):
      %nil.0 : while.IntList = while.nil
      jump ^head.0(0, %nil.0)
    head.0(%i.0 : base.Int, %l.0 : while.IntList):
      %more.0 : base.Bool = while.lt(%i.0, %n.0)
      branch(%more.0) ^body.0() ^done.0()
    body.0():
      %i.1 : base.Int = base.callCode[[base.Int], base.Int](@inc, %i.0)
      %l.1 : while.IntList = while.cons(%i.1, %l.0)
      jump ^head.0(%i.1, %l.1)
    done.0():
      ret(%l.0)
  }
}
"

/--
info: module m {
  func @inc(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %y.0 : base.Int = while.add(%x.0, 1)
      ret(%y.0)
  }
  func @range(%n.0 : base.Int) -> while.IntList {
    entry.0(%n.0 : base.Int):
      %i.cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %default.1 : while.IntList = while.nil
      %l.cell.0 : base.Ref(while.IntList) = base.refNew[while.IntList](%default.1)
      %nil.0 : while.IntList = while.nil
      %set.0 : base.Unit = base.refSet[base.Int](%i.cell.0, 0)
      %set.1 : base.Unit = base.refSet[while.IntList](%l.cell.0, %nil.0)
      jump ^head.0()
    head.0():
      %i.0 : base.Int = base.refGet[base.Int](%i.cell.0)
      %l.0 : while.IntList = base.refGet[while.IntList](%l.cell.0)
      %more.0 : base.Bool = while.lt(%i.0, %n.0)
      branch(%more.0) ^body.0() ^done.0()
    body.0():
      %i.1 : base.Int = base.callCode[[base.Int], base.Int](@inc, %i.0)
      %l.1 : while.IntList = while.cons(%i.1, %l.0)
      %set.2 : base.Unit = base.refSet[base.Int](%i.cell.0, %i.1)
      %set.3 : base.Unit = base.refSet[while.IntList](%l.cell.0, %l.1)
      jump ^head.0()
    done.0():
      ret(%l.0)
  }
}
on the engine: the same on 27 of 27 runs
on symbols: inc: the same
on symbols: range: the same
promoted again: 0 of 6 cell reads and writes left
-/
#guard_msgs in
#eval check range "range" (singles 4) withNil

/-! ## A default built from a default

`base.Except` has no constructor without fields, so its default is a constructor applied to a
default of its field: `base.error` of `0`.  The entry block defines the `0` first; the printed
form folds a constant into its use. -/

/-- The literals, and `error 0` for `base.Except(base.Int, base.Int)`. -/
private def withError : Demote.Defaults While.env := fun τ =>
  if τ = Base.Except Base.Int Base.Int then
    some (.apply Base.Except.error.ref ⟨#[.ty Base.Int, .ty Base.Int], rfl⟩ rfl
      [(Base.Int, .const (.int 0))])
  else Demote.Defaults.literals τ

/--
info: module m {
  func @checked(%x.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%x.0 : base.Int):
      %default.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](0)
      %r.cell.0 : base.Ref(base.Except(base.Int, base.Int)) = base.refNew[base.Except(base.Int, base.Int)](%default.0)
      %neg.0 : base.Bool = while.lt(%x.0, 0)
      branch(%neg.0) ^bad.0() ^good.0()
    bad.0():
      %e.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%x.0)
      %set.0 : base.Unit = base.refSet[base.Except(base.Int, base.Int)](%r.cell.0, %e.0)
      jump ^out.0()
    good.0():
      %v.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
      %set.1 : base.Unit = base.refSet[base.Except(base.Int, base.Int)](%r.cell.0, %v.0)
      jump ^out.0()
    out.0():
      %r.0 : base.Except(base.Int, base.Int) = base.refGet[base.Except(base.Int, base.Int)](%r.cell.0)
      ret(%r.0)
  }
}
on the engine: the same on 27 of 27 runs
on symbols: checked: the same
promoted again: 0 of 3 cell reads and writes left
-/
#guard_msgs in
#eval check "module m {
  func @checked(%x.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%x.0 : base.Int):
      %neg.0 : base.Bool = while.lt(%x.0, 0)
      branch(%neg.0) ^bad.0() ^good.0()
    bad.0():
      %e.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%x.0)
      jump ^out.0(%e.0)
    good.0():
      %v.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
      jump ^out.0(%v.0)
    out.0(%r.0 : base.Except(base.Int, base.Int)):
      ret(%r.0)
  }
}
" "checked" (singles 4) withError

/-! ## Existing cells beside block parameters

The input's private cell stays beside the cell added for a block parameter, and both are
promoted again. A used write result is still private but excludes its cell from ref-to-reg's
candidates, leaving that write in place. -/

/--
info: module m {
  func @existing(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %y.cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      %set.0 : base.Unit = base.refSet[base.Int](%y.cell.0, %x.0)
      jump ^use.0()
    use.0():
      %y.0 : base.Int = base.refGet[base.Int](%y.cell.0)
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %y.0)
      %v.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.0)
  }
}
on the engine: the same on 27 of 27 runs
on symbols: existing: the same
promoted again: 0 of 4 cell reads and writes left
-/
#guard_msgs in
#eval check "module m {
  func @existing(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      jump ^use.0(%x.0)
    use.0(%y.0 : base.Int):
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %y.0)
      %v.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.0)
  }
}
" "existing" (singles 4)

/--
info: module m {
  func @used_set(%x.0 : base.Int) -> base.Unit {
    entry.0(%x.0 : base.Int):
      %y.cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      %set.0 : base.Unit = base.refSet[base.Int](%y.cell.0, %x.0)
      jump ^use.0()
    use.0():
      %y.0 : base.Int = base.refGet[base.Int](%y.cell.0)
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %y.0)
      ret(%u.0)
  }
}
on the engine: the same on 27 of 27 runs
on symbols: used_set: the same
promoted again: 1 of 3 cell reads and writes left
-/
#guard_msgs in
#eval check "module m {
  func @used_set(%x.0 : base.Int) -> base.Unit {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      jump ^use.0(%x.0)
    use.0(%y.0 : base.Int):
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %y.0)
      ret(%u.0)
  }
}
" "used_set" (singles 4)

/-! ## A contract, an extern function and a ghost

The clause's join keeps its parameter: a contract stays as it is.  So do the extern function
and the ghost. -/

/--
info: module m {
  ghost @count : base.Int
  extern func @ext(%x.0 : base.Int) -> base.Int
  func @abs(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        jump ^join.0(true)
      join.0(%r.0 : base.Bool):
        ret(%r.0)
    }
  {
    entry.0(%x.0 : base.Int):
      %r.cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %neg.0 : base.Bool = while.lt(%x.0, 0)
      branch(%neg.0) ^flip.0() ^keep.0()
    flip.0():
      %y.0 : base.Int = while.neg(%x.0)
      %set.0 : base.Unit = base.refSet[base.Int](%r.cell.0, %y.0)
      jump ^out.0()
    keep.0():
      %set.1 : base.Unit = base.refSet[base.Int](%r.cell.0, %x.0)
      jump ^out.0()
    out.0():
      %r.1 : base.Int = base.refGet[base.Int](%r.cell.0)
      ret(%r.1)
  }
}
on the engine: the same on 27 of 27 runs
on symbols: ext: no body
on symbols: abs: the same
promoted again: 0 of 3 cell reads and writes left
-/
#guard_msgs in
#eval check "module m {
  ghost @count : base.Int
  extern func @ext(%x.0 : base.Int) -> base.Int
  func @abs(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        jump ^join.0(true)
      join.0(%r.0 : base.Bool):
        ret(%r.0)
    }
  {
    entry.0(%x.0 : base.Int):
      %neg.0 : base.Bool = while.lt(%x.0, 0)
      branch(%neg.0) ^flip.0() ^keep.0()
    flip.0():
      %y.0 : base.Int = while.neg(%x.0)
      jump ^out.0(%y.0)
    keep.0():
      jump ^out.0(%x.0)
    out.0(%r.1 : base.Int):
      ret(%r.1)
  }
}
" "abs" (singles 4)

/-! ## A wrong demotion is caught

The side-by-side run of `gcd` against its demoted form with the swap's writes changed to write
`%a.1` to both cells. -/

/-- Read `text`, demote it, and run its first function side by side with its demoted form
changed by `spoil`. -/
private def spoiled (text : String) (spoil : ValId → ValId) : IO Unit := do
  match ← Module.read While.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    if h : Demotable m.raw then
      match demote .literals m h with
      | .error es => report es
      | .ok ⟨dm, _⟩ =>
        if let (some f, some g) := (m.raw.funcs[0]?, dm.raw.funcs[0]?) then
          let swap := g.blocks.map fun b =>
            if b.label.name == .num (nm "swap") 0 then b.mapUses spoil else b
          IO.println ((differs f { g with blocks := swap }).getD "the same")
    else IO.println "not demotable"

/--
info: while.lt defining %6: operand %2 is #37, but %2 is #31
-/
#guard_msgs in
#eval spoiled gcd fun v => if v.id == 3 then ⟨2⟩ else v

/-! ## Rejections

Each rejection is compared with the `Demote.Error` expected of each function, in the order of
the functions. -/

/-- Read `text` and demote it with `defaults`; print whether it is rejected with exactly
`expected`, or what happens instead. -/
private def rejected (text : String) (defaults : Demote.Defaults While.env)
    (expected : Array (Name × Demote.Error)) : IO Unit := do
  match ← Module.read While.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    if h : Demotable m.raw then
      match demote defaults m h with
      | .error es => if es == expected then IO.println "rejected as expected" else report es
      | .ok _ => IO.println "accepted"
    else IO.println "not demotable"

/-! A type without a default: the literals give `while.IntList` none, so `range`, which `withNil`
demotes above, is rejected at the list parameter of its loop head. -/

/-- info: rejected as expected -/
#guard_msgs in
#eval rejected range .literals #[(nm "range", .noDefault (.num (nm "l") 0) ⟨.num (nm "head") 0⟩)]

/-! Passing a cell on an edge is not private. The `noDefault` rejection here is incidental:
the pass tries to allocate the reference-typed parameter before checking privacy. The accepted
twin below keeps the entry cell in scope and reads it directly, without passing it. -/

/-- info: rejected as expected -/
#guard_msgs in
#eval rejected "module m {
  func @held(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      jump ^use.0(%c.0)
    use.0(%d.0 : base.Ref(base.Int)):
      %v.0 : base.Int = base.refGet[base.Int](%d.0)
      ret(%v.0)
  }
}
" .literals #[(nm "held", .noDefault (.num (nm "d") 0) ⟨.num (nm "use") 0⟩)]

/--
info: module m {
  func @held(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      jump ^use.0()
    use.0():
      %v.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.0)
  }
}
on the engine: the same on 27 of 27 runs
on symbols: held: the same
promoted again: 0 of 1 cell reads and writes left
-/
#guard_msgs in
#eval check "module m {
  func @held(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      jump ^use.0()
    use.0():
      %v.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.0)
  }
}
" "held" (singles 4)

/-! A default that is not of its type: `gcd`, which the literals demote above, with `true` given
for every type.  The pass does not check a default's type, so the demoted function is not well
formed. -/

/-- info: rejected as expected -/
#guard_msgs in
#eval rejected gcd (fun _ => some (.const (.bool true))) #[(nm "gcd", .illFormed)]

/-! A reference that is not a private cell: a parameter of a function that is a cell, also of
an extern function; a cell that the function returns; and a cell made outside the entry block.
`@operand` passes an entry cell to a constructor; `@stored` uses one to initialise another cell.
These exercise escaping instruction operands, rather than parameters, results or edges.
`@fine`, whose one cell is made in the entry block and stays private, is not rejected. -/

/-- info: rejected as expected -/
#guard_msgs in
#eval rejected "module m {
  func @param(%c.0 : base.Ref(base.Int)) -> base.Int {
    entry.0(%c.0 : base.Ref(base.Int)):
      %v.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.0)
  }
  func @escape(%x.0 : base.Int) -> base.Ref(base.Int) {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      ret(%c.0)
  }
  func @late(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      jump ^next.0()
    next.0():
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      %v.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.0)
  }
  func @fine(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      %v.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.0)
  }
  func @operand(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      %r.0 : base.Except(base.Int, base.Ref(base.Int)) = base.ok[base.Int, base.Ref(base.Int)](%c.0)
      ret(%x.0)
  }
  func @stored(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      %d.0 : base.Ref(base.Ref(base.Int)) = base.refNew[base.Ref(base.Int)](%c.0)
      ret(%x.0)
  }
  extern func @cellext(%c.0 : base.Ref(base.Int)) -> base.Int
}
" .literals #[(nm "param", .notPrivate), (nm "escape", .notPrivate), (nm "late", .notPrivate),
  (nm "operand", .notPrivate), (nm "stored", .notPrivate), (nm "cellext", .notPrivate)]

/-! The escaping-operand twins keep the entry cell private: the constructor and the second
allocation take the integer, not the cell. -/

/--
info: module m {
  func @operand(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      %r.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
      ret(%x.0)
  }
  func @stored(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      %d.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      ret(%x.0)
  }
}
on the engine: the same on 27 of 27 runs
on symbols: operand: the same
on symbols: stored: the same
promoted again: 0 of 0 cell reads and writes left
-/
#guard_msgs in
#eval check "module m {
  func @operand(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      %r.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
      ret(%x.0)
  }
  func @stored(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      %d.0 : base.Ref(base.Int) = base.refNew[base.Int](%x.0)
      ret(%x.0)
  }
}
" "operand" (singles 4)

/-! ## Not demotable

`demote` takes a proof of its assumption, so a module in another shape is no input of it.
`gcd` with its two jumps to the head put on the arms of the branch does not have bare
branches. -/

/--
info: not demotable: plain control: true, bare branches: false
-/
#guard_msgs in
#eval check "module m {
  func @gcd(%a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Int):
      jump ^head.0(%a.0, %b.0)
    head.0(%a.1 : base.Int, %b.1 : base.Int):
      %z.0 : base.Bool = while.eq(%b.1, 0)
      branch(%z.0) ^done.0() ^body.0()
    body.0():
      %lt.0 : base.Bool = while.lt(%a.1, %b.1)
      %d.0 : base.Int = while.sub(%a.1, %b.1)
      branch(%lt.0) ^head.0(%b.1, %a.1) ^head.0(%d.0, %b.1)
    done.0():
      ret(%a.1)
  }
}
" "gcd" #[]

/-! A division leaves along a successor when the divisor is zero, so a module that divides is
not in plain control. -/

/--
info: not demotable: plain control: false, bare branches: true
-/
#guard_msgs in
#eval check "module m {
  func @half(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %q.0 : base.Int = while.div(%a.0, 2) ^zero.0()
      ret(%q.0)
    zero.0(%e.0 : base.Int):
      ret(%e.0)
  }
}
" "half" #[]

end Strata.Dyn.DemoteTest
