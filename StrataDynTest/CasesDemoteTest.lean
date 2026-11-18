/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Demote
import all StrataDynTest.CasesTest
import StrataDyn.Env.WF
-- The reader, both passes and the engine run as compiled code below.
meta import StrataDyn.Demote
meta import all StrataDynTest.CasesTest
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Case lowering, then demotion

Each program of the tests of case lowering (`StrataDynTest/CasesTest.lean`) is lowered by
`cases`, and the result is demoted: the output shape of `cases` gives the shape that `demote`
assumes (`demotable_cased`), so the two passes compose without a check between them.  The
demoted module then runs beside the source on Dyn's engine, and must end the same, print the
same, tick as often and draw as many choices.
-/

namespace Strata.Dyn.CasesDemoteTest

open Strata.Dyn.CasesTest Strata.Dyn.While

/-- The empty forest, the default of `test.Forest(base.Int)`. -/
private def bare : Option (Demote.Default CaseEnv.env) :=
  Demote.Default.ctor? CaseEnv.Forest.bare.ref ⟨#[.ty Base.Int], rfl⟩ []

/-- The literals; `nil` for a list and the constructor without fields for `test.Choice` and for
`test.Forest`; and, each built from another default, `error 0` for `base.Except` and a tree
labelled `0` without children for `test.Rose`. -/
private def defaults : Demote.Defaults CaseEnv.env := fun τ =>
  if τ = While.IntList then Demote.Default.ctor? While.IntList.nil.ref ⟨#[], rfl⟩ []
  else if τ = CaseEnv.Choice Base.Int then
    Demote.Default.ctor? CaseEnv.Choice.empty.ref ⟨#[.ty Base.Int], rfl⟩ []
  else if τ = Base.Except Base.Int Base.Int then
    Demote.Default.ctor? Base.Except.error.ref ⟨#[.ty Base.Int, .ty Base.Int], rfl⟩
      [(Base.Int, .const (.int 0))]
  else if τ = CaseEnv.Forest Base.Int then bare
  else if τ = CaseEnv.Rose Base.Int then do
    Demote.Default.ctor? CaseEnv.Rose.rose.ref ⟨#[.ty Base.Int], rfl⟩
      [(Base.Int, .const (.int 0)), (CaseEnv.Forest Base.Int, ← bare)]
  else Demote.Defaults.literals τ

/-- The block parameters of `m`'s bodies, entry blocks aside. -/
private def blockParams {α : Type} (m : Module CaseEnv.env α) : Nat :=
  m.raw.funcs.foldl (init := 0) fun n fn =>
    (fn.blocks.extract 1).foldl (fun n b => n + b.params.size) n

/-- Lower the cases of `text`, demote the result, and run each function of `tests` in the source
and in the demoted module, on its inputs under each oracle. -/
private def check (name text : String) (tests : List (String × Array (Array Int))) : IO Unit := do
  let src ← load text
  let ⟨cased, hc⟩ ← lower src
  let demoted ← match demote defaults cased (demotable_cased hc) with
    | .ok ⟨m, _⟩ => pure m
    | .error es => throw (IO.userError s!"{name}: demote rejects {reprStr (es.map (·.1))}")
  let mut n := 0
  for (f, inputs) in tests do
    for args in inputs do
      for oracle in oracles do
        let expected := observe src f args oracle
        let got := observe demoted f args oracle
        unless got == expected do
          throw (IO.userError s!"{name}: {f}{args}: source {expected}; demoted {got}")
        n := n + 1
  IO.println s!"{name}: {blockParams cased} block parameters demoted; source = demoted on {n} runs"

/--
info: choice: 10 block parameters demoted; source = demoted on 39 runs
single: 2 block parameters demoted; source = demoted on 42 runs
exceptions: 3 block parameters demoted; source = demoted on 39 runs
polymorphic: 6 block parameters demoted; source = demoted on 39 runs
loop: 6 block parameters demoted; source = demoted on 39 runs
fault: 3 block parameters demoted; source = demoted on 39 runs
calls: 2 block parameters demoted; source = demoted on 78 runs
forest: 9 block parameters demoted; source = demoted on 39 runs
-/
#guard_msgs in
#eval do
  check "choice" choice [("choice", singles)]
  check "single" single [("unit_case", #[#[]]), ("single", singles)]
  check "exceptions" exceptions [("exceptions", singles)]
  check "polymorphic" polymorphic [("polymorphic", singles)]
  check "loop" loop [("loop", singles)]
  check "fault" fault [("fault", singles)]
  check "calls" calls [("callee", singles), ("caller", singles)]
  check "forest" forest [("forest", singles)]

end Strata.Dyn.CasesDemoteTest
