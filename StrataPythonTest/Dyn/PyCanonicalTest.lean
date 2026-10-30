/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Canonical
public import StrataDyn.DDMRead
meta import StrataPython.Dyn.Canonical
meta import StrataDyn.DDMRead
import StrataDyn.Env.WF
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Python's canonical form: the loop records and P6

`PyCanonical.records?` reads each function's `py.loops` attribute into loop records, and gives
`none` if an entry does not read, which `PyCanonical.runModule` reports.  Then the check of P6,
`PyCanonical.checkFinallyEntered`, on blocks written by hand, and its failure messages.
-/

namespace StrataPython.Dyn.PyCanonicalTest

open Strata.Dyn StrataPython.Dyn

private def lbl (s : String) (k : Nat) : Label := ⟨.num (.str .base s) k⟩

private def rec (fs : Array (String × String)) : AttrValue :=
  .record (fs.map fun (k, v) => (.str .base k, .const (.str v)))

private def infoWith (vs : Array AttrValue) : Info :=
  { attrs := #[(Shape.key "loops", .list vs)] }

#guard PyCanonical.records? (infoWith #[rec #[("head", "head.0"), ("done", "done.0")],
    rec #[("head", "head.1"), ("done", "done.1")]]) ==
  some [{ head := lbl "head" 0, done := some (lbl "done" 0) },
        { head := lbl "head" 1, done := some (lbl "done" 1) }]
-- A record without its `done` is of a loop that control never leaves.
#guard PyCanonical.records? (infoWith #[rec #[("head", "head.0")]]) ==
  some [{ head := lbl "head" 0, done := none }]
-- A record whose label is not a string, or that has no head: the attribute does not read.
#guard PyCanonical.records? (infoWith #[.record #[(.str .base "head", .const (.str "head.1")),
    (.str .base "done", .const (.int 1))]]) == none
#guard PyCanonical.records? (infoWith #[rec #[("done", "done.3")]]) == none
-- No attribute: no records.
#guard PyCanonical.records? {} == some []
-- The shape matches `py.Completion`'s constructors.
#guard PyCanonical.shape.roles? == some { normal := 0, brk := 3, cont := 4, forwarded := [1, 2] }

/-! ## Each `finally` body pushes the completion it was entered with -/

/-- `%r = py.pushPending(%x)`: the start of a `finally` body. -/
private def pushPending (r x : Nat) : Instruction Py.env Unit :=
  .apply () ⟨⟨r⟩, Py.Value⟩ Py.pushPending.ref ⟨#[], rfl⟩ #[⟨x⟩] #[] #[]

/-- `%r = py.noneLit`. -/
private def noneLit (r : Nat) : Instruction Py.env Unit :=
  .apply () ⟨⟨r⟩, Py.Value⟩ Py.noneLit.ref ⟨#[], rfl⟩ #[] #[] #[]

/-- Block `s` that takes `ps`, runs `is`, and jumps to `t`. -/
private def blkP (s : String) (ps : Array (ValDecl Py.env)) (is : Array (Instruction Py.env Unit))
    (t : String) : Block Py.env Unit :=
  { label := lbl s 0, params := ps, instrs := is, term := .jump () ⟨lbl t 0, #[]⟩, info := () }

private def comp (k : Nat) : ValDecl Py.env := ⟨⟨k⟩, Py.Completion⟩

private def val (k : Nat) : ValDecl Py.env := ⟨⟨k⟩, Py.Value⟩

private def fnOf (bs : List (Block Py.env Unit)) : Func Py.env Unit :=
  { name := .str .base "f", params := (bs.head?.map (·.params)).getD #[], retType := Py.failing,
    blocks := bs.toArray, names := #[], info := () }

-- Two `finally` bodies that both end in the same place, as two that both `return` do.
#guard PyCanonical.checkFinallyEntered
  (fnOf [blkP "fin" #[comp 0] #[pushPending 1 0] "out", blkP "fin2" #[comp 2] #[pushPending 3 2] "out"])
-- A `finally` block that pushes a completion other than its parameter: the one it was entered
-- with is lost.
#guard !PyCanonical.checkFinallyEntered (fnOf [blkP "fin" #[comp 0] #[pushPending 1 5] "out"])
-- A `finally` block whose parameter is not a completion.
#guard !PyCanonical.checkFinallyEntered (fnOf [blkP "fin" #[val 0] #[pushPending 1 0] "out"])
-- A `finally` block with no parameter.
#guard !PyCanonical.checkFinallyEntered (fnOf [blkP "fin" #[] #[pushPending 1 0] "out"])
-- The completion as its second parameter.
#guard !PyCanonical.checkFinallyEntered
  (fnOf [blkP "fin" #[val 4, comp 0] #[pushPending 1 0] "out"])
-- More parameters after the completion, as ref-to-reg adds them.
#guard PyCanonical.checkFinallyEntered (fnOf [blkP "fin" #[comp 0, val 4] #[pushPending 1 0] "out"])
-- `py.pushPending` after another instruction is rejected: `py.pushPending` may only start a block.
#guard !PyCanonical.checkFinallyEntered
  (fnOf [blkP "fin" #[comp 0] #[noneLit 2, pushPending 1 0] "out"])

-- The failure messages name the first block that fails, and its reason.
#guard PyCanonical.finallyWhy (fnOf [blkP "fin" #[comp 0] #[pushPending 1 5] "out"]) ==
  "fin.0 starts a finally body, but does not push its first parameter, the pending completion"
#guard PyCanonical.finallyWhy
    (fnOf [blkP "fin" #[comp 0] #[pushPending 1 0, pushPending 2 0] "out"]) ==
  "fin.0 runs py.pushPending after its first instruction"
#guard PyCanonical.finallyWhy
    (fnOf [blkP "fin" #[comp 0] #[noneLit 2, pushPending 1 0] "out"]) ==
  "fin.0 runs py.pushPending after its first instruction"

/-- Read `text` in `Py.env`, and print why `PyCanonical.runModule` rejects it, or that it does
not. -/
private def failures (text : String) : IO Unit := do
  match ← Module.read Py.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    match PyCanonical.runModule m with
    | .error fs => for f in fs do IO.println (toString f)
    | .ok _ => IO.println "accepted"

/-- Read `text` in `Py.env`, put it in Python's canonical form, and print whether that leaves the
module as it was. -/
private def unchanged (text : String) : IO Unit := do
  match ← Module.read Py.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    match PyCanonical.runModule m with
    | .error fs => for f in fs do IO.println (toString f)
    | .ok cm => IO.println (if toString cm.canonical.module == toString m then "unchanged" else
        toString cm.canonical.module)

-- Extern functions, with and without a contract, pass through unchanged.
/-- info: unchanged -/
#guard_msgs in
#eval unchanged "module m {
  extern func @m.g(%x.0 : py.Value) -> base.Except(py.Value, py.Value)
  extern func @m.h(%x.0 : py.Value) -> base.Except(py.Value, py.Value)
    requires \"x is defined\" {
      pre.0():
        %ok.0 : base.Bool = py.isDefined(%x.0)
        ret(%ok.0)
    }
  func @m.f(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%args.0 : py.Value, %kwargs.0 : py.Value):
      jump ^start.0()
    start.0():
      %none.0 : py.Value = py.noneLit
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.0)
      ret(%ret.0)
  }
}
"

-- A function whose `py.loops` attribute has a record with no head: it is reported, not dropped.
/-- info: m.f: its py.loops attribute does not read as loop records -/
#guard_msgs in
#eval failures "module m {
  func @m.f(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    #[py.loops = [{done = \"done.0\"}]]

    entry.0(%args.0 : py.Value, %kwargs.0 : py.Value):
      jump ^start.0()
    start.0():
      %none.0 : py.Value = py.noneLit
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.0)
      ret(%ret.0)
  }
}
"

-- The check also looks at the blocks inside a region: here `py.pushPending` runs after another
-- instruction in the body of a `py.compFor`.
/-- info: m.<module>: each.0 runs py.pushPending after its first instruction -/
#guard_msgs in
#eval failures "module m {
  func @|m.<module>|() -> base.Except(py.Value, py.Value) {
    entry.0():
      jump ^start.0()
    start.0():
      %v.0 : py.Value = py.mkList
      %each.0 : base.Unit = py.compFor(%v.0) ^propagate.0() {
        each.0(%item.0 : py.Value):
          %c.0 : py.Completion = py.completionNormal
          %p.0 : py.Value = py.pushPending(%c.0)
          %unit.0 : base.Unit = base.unit
          %ok.0 : base.Except(py.Value, base.Unit) = base.ok[py.Value, base.Unit](%unit.0)
          ret(%ok.0)
      }
      %none.0 : py.Value = py.noneLit
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.0)
      ret(%ret.0)
    propagate.0(%exc.0 : py.Value):
      %exc.1 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.0)
      ret(%exc.1)
  }
}
"

-- A module with a good function `g` and a function `f` whose `finally` block pushes a completion
-- other than its parameter: only `f` is reported, by name.
/-- info: bad_operand.f: fin.0 starts a finally body, but does not push its first parameter, the pending completion -/
#guard_msgs in
#eval failures "module bad_operand {
  func @bad_operand.g(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%args.0 : py.Value, %kwargs.0 : py.Value):
      jump ^start.0()
    start.0():
      %none.0 : py.Value = py.noneLit
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.0)
      ret(%ret.0)
  }
  func @bad_operand.f(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%args.0 : py.Value, %kwargs.0 : py.Value):
      jump ^start.0()
    start.0():
      %comp.0 : py.Completion = py.completionNormal
      %comp.1 : py.Completion = py.completionRaise(%args.0)
      jump ^fin.0(%comp.1)
    fin.0(%pending.0 : py.Completion):
      %prev.0 : py.Value = py.pushPending(%comp.0)
      %pop.0 : base.Unit = py.popExcept(%prev.0)
      py.Completion.case(%comp.0) ^join.0() ^ret.0() ^propagate.0() ^unreachable.0() ^unreachable.1()
    ret.0(%val.0 : py.Value):
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%val.0)
      ret(%ret.0)
    unreachable.0():
      unreachable
    unreachable.1():
      unreachable
    join.0():
      %none.1 : py.Value = py.noneLit
      %ret.1 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.1)
      ret(%ret.1)
    propagate.0(%exc.2 : py.Value):
      %exc.3 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.2)
      ret(%exc.3)
  }
}
"

end StrataPython.Dyn.PyCanonicalTest
