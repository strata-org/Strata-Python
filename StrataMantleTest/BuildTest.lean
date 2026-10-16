/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Build
public import StrataMantle.DDM
public import StrataMantle.WF
import StrataMantle.Env.WF
-- The builder, the checker and the printer run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.DDM
meta import StrataMantle.WF
meta import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Emitting and printing over the base environment

Functions emitted with `Mantle.Build` against `base` alone, so nothing here depends on a
language.  The builder checks each by `Mantle.WF`, and most are printed by the dialect in
`StrataMantle/DDM.lean`: every constant form, the cell operations with their type arguments,
the base's control flow, and `Except.case`.  The first is the case the builder exists for: a
forward branch names a label long before its block is finished.
-/

namespace Strata.Mantle.BuildTest

open Strata.Mantle.Build (freshVal freshLabel startBlock startBlockWith startFreshBlock
  emitConst emitApply finishBlock terminate goto build Failure region withInfo)

private def boolT : TypeExpr base := Base.Bool.ty
private def intT  : TypeExpr base := Base.Int.ty
private def strT  : TypeExpr base := Base.String.ty
private def unitT : TypeExpr base := Base.Unit.ty
private def refIntT : TypeExpr base := Base.Ref.ty intT
private def exceptStrIntT : TypeExpr base := Base.Except.ty strT intT

/-- What `build` gives: a checked function, or the `Failure`. -/
private abbrev Built (α : Type) := Except (Failure Unit) {fn : Func base α // fn.WF}

private def illFormed (fn : Func base Unit) : Bool := !decide fn.WF

/-- The label `freshLabel base` hands out `n`-th. -/
private def lbl (base : String) (n : Nat) : Label := ⟨.num (.str .base base) n⟩

/-! ## A cell written under a condition

`done` is allocated first and finished last.  Blocks are named, so the transfer to it
needs no fixing up once it is finished; the blocks appear in the order they were
finished, entry first. -/

private def f : Built Unit :=
  build (.str .base "f") intT () do
    let c ← freshVal (.str .base "c") boolT
    let done ← freshLabel "done"
    let bump ← freshLabel "bump"
    let _ ← startFreshBlock #[c] "entry"
    let zero ← emitConst (.str .base "k") (.int 0)
    let cell ← emitApply (.str .base "cell") refIntT Base.refNew #[zero]
    finishBlock (.branch () c.id (goto bump) (goto done))
    startBlock bump
    let one ← emitConst (.str .base "k") (.int (-1))
    let _ ← emitApply (.str .base "unit") unitT Base.refSet (typeArgs := ta[intT]) #[cell, one]
    finishBlock (.jump () (goto done))
    startBlock done
    let r ← emitApply (.str .base "r") intT Base.refGet #[cell]
    finishBlock (.ret () r)

#guard f.isOk

-- Every value is named, and two `k`s are distinguished by suffix rather than colliding.
#guard (f.toOption.map fun f => (f.1.names.size, f.1.names[1]?, f.1.names[3]?)) ==
  some (6, some (.num (.str .base "k") 0), some (.num (.str .base "k") 1))

/-- Every terminator's targets.  A `ret` is a jump to `Label.exit`. -/
private def targets (fn : Func base Unit) : Array Label :=
  fn.blocks.flatMap fun b => match b.term with
    | .apply _ _ _ _ succs _ => succs.map (·.target)

/-- info: module f {
  func @f(%c.0 : base.Bool) -> base.Int {
    entry.0(%c.0 : base.Bool):
      %cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      branch(%c.0) ^bump.0() ^done.0()
    bump.0():
      %unit.0 : base.Unit = base.refSet[base.Int](%cell.0, -1)
      jump ^done.0()
    done.0():
      %r.0 : base.Int = base.refGet[base.Int](%cell.0)
      ret(%r.0)
  }
} -/
#guard_msgs in
#eval do IO.println ((← IO.ofExcept f).1.format {})

/-! ## A failure built and inspected

Both `Except` constructors, and `Except.case`, whose successors are labels allocated before
the blocks they name. -/

private def h : Built Unit :=
  build (.str .base "h") intT () do
    let okL ← freshLabel "ok"
    let errL ← freshLabel "err"
    let _ ← startFreshBlock (base := "entry")
    let msg ← emitConst (.str .base "msg") (.str "boom")
    let e ← emitApply (.str .base "e") exceptStrIntT Base.Except.error #[msg]
    terminate Base.Except.case (typeArgs := ta[strT, intT]) #[e] #[goto okL, goto errL]
    let _ ← startBlockWith errL (.str .base "err") strT
    let zero ← emitConst (.str .base "zero") (.int 0)
    let o ← emitApply (.str .base "o") exceptStrIntT Base.Except.ok #[zero]
    terminate Base.Except.case (typeArgs := ta[strT, intT]) #[o] #[goto okL, goto errL]
    finishBlock (.ret () (← startBlockWith okL (.str .base "v") intT))

#guard h.isOk

-- `errL` was finished before `okL`; the successors still name the labels they were given.
#guard (h.toOption.map (targets ·.1)) ==
  some #[lbl "ok" 0, lbl "err" 0, lbl "ok" 0, lbl "err" 0, Label.exit]

#guard (h.toOption.map (·.1.blocks.map (·.label))) ==
  some #[lbl "entry" 0, lbl "err" 0, lbl "ok" 0]

/-- The successors follow `Except`'s declaration order, `ok` first: swapped, they are
rejected. -/
private def hSwapped : Option (Func base Unit) :=
  h.toOption.map fun ⟨h, _⟩ => { h with blocks := h.blocks.modify 0 fun b =>
      { b with
        term := .apply () Base.Except.case ⟨#[.ty strT, .ty intT], rfl⟩ #[⟨1⟩]
          #[⟨lbl "err" 0, #[]⟩, ⟨lbl "ok" 0, #[]⟩] #[] } }

#guard hSwapped.map illFormed == some true

/-! ## The other constants, and a failure inspected, as a module

`Except.case` ending in `unreachable`, and every constant form `f` and `h` do not use. -/

private def hConsts : Built Unit :=
  build (.str .base "h") intT () do
    let okL ← freshLabel "ok"
    let errL ← freshLabel "err"
    let _ ← startFreshBlock (base := "entry")
    let _ ← emitConst (.str .base "u") .unit
    let _ ← emitConst (.str .base "b") (.bool true)
    let _ ← emitConst (.str .base "x") (.float 1.5)
    let msg ← emitConst (.str .base "msg") (.str "boom")
    let e ← emitApply (.str .base "e") exceptStrIntT Base.Except.error #[msg]
    terminate Base.Except.case (typeArgs := ta[strT, intT]) #[e] #[goto okL, goto errL]
    finishBlock (.ret () (← startBlockWith okL (.str .base "v") intT))
    let _ ← startBlockWith errL (.str .base "err") strT
    finishBlock (.unreachable ())

#guard hConsts.isOk

/-- info: module m {
  func @f(%c.0 : base.Bool) -> base.Int {
    entry.0(%c.0 : base.Bool):
      %cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      branch(%c.0) ^bump.0() ^done.0()
    bump.0():
      %unit.0 : base.Unit = base.refSet[base.Int](%cell.0, -1)
      jump ^done.0()
    done.0():
      %r.0 : base.Int = base.refGet[base.Int](%cell.0)
      ret(%r.0)
  }
  func @h() -> base.Int {
    entry.0():
      %u.0 : base.Unit = const unit
      %b.0 : base.Bool = const true
      %x.0 : base.Float64 = const 1.5
      %e.0 : base.Except(base.String, base.Int) = base.error[base.String, base.Int]("boom")
      base.Except.case[base.String, base.Int](%e.0) ^ok.0() ^err.0()
    ok.0(%v.0 : base.Int):
      ret(%v.0)
    err.0(%err.0 : base.String):
      unreachable
  }
} -/
#guard_msgs in
#eval do
  match Module.ofChecked (.str .base "m") #[← IO.ofExcept f, ← IO.ofExcept hConsts] () with
  | .ok m => IO.println m
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

/-! ## Annotations

An emitter given no annotation uses the default, which starts as the function's own and
which `withInfo` replaces for what it emits.  An explicit one wins over both. -/

private def annotated : Built Nat :=
  build (.str .base "a") exceptStrIntT 0 do
    let _ ← startFreshBlock
    let a ← emitConst (.str .base "a") (.int 1)
    let _ ← withInfo 7 (emitConst (.str .base "b") (.int 2))
    let _ ← withInfo 7 (emitConst (.str .base "c") (.int 3) (some 9))
    let r ← emitApply (.str .base "ret") exceptStrIntT Base.Except.ok #[a]
    withInfo 5 (finishBlock (.ret 5 r))

private def instrInfos (fn : Func base Nat) : Array Nat :=
  fn.blocks.flatMap fun b => b.instrs.map fun
    | .const i .. | .apply i .. => i

#guard (annotated.toOption.map (instrInfos ·.1)) == some #[0, 7, 9, 0]

#guard (annotated.toOption.map (·.1.blocks.map (·.info))) == some #[5]

/-! ## Misuse

Each is an error, and `build` fails.  `errors` shows the misuses it fails with. -/

/-- The misuses `build` fails with for `m`, a function returning `Int`, or none. -/
private def errors (m : BuildM base Unit Unit) : Array String :=
  match build (.str .base "f") intT () m with
  | .ok _ => #[]
  | .error e => e.misuses

/-- An instruction emitted after the block is closed. -/
private def afterClose : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  let r ← emitConst (.str .base "r") (.int 0)
  finishBlock (.ret () r)
  let _ ← emitConst (.str .base "dead") (.int 1)

/-- info: #["instruction %1 emitted with no block open"] -/
#guard_msgs in
#eval errors afterClose

/-- A body that never closes its entry block. -/
private def neverClosed : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  let _ ← emitConst (.str .base "r") (.int 0)

/-- info: #["the function ends with block entry.0 open"] -/
#guard_msgs in
#eval errors neverClosed

/-- A block opened over an open one. -/
private def overOpen : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  let r ← emitConst (.str .base "r") (.int 0)
  let _ ← startFreshBlock (base := "next")
  finishBlock (.ret () r)

/-- info: #["block next.0 opened while block entry.0 is open"] -/
#guard_msgs in
#eval errors overOpen

/-- A block finished when none is open. -/
private def noneOpen : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  let r ← emitConst (.str .base "r") (.int 0)
  finishBlock (.ret () r)
  finishBlock (.ret () r)

/-- info: #["a block finished with no block open"] -/
#guard_msgs in
#eval errors noneOpen

/-- A region whose entry block is left open. -/
private def openRegion : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  let r ← emitConst (.str .base "r") (.int 0)
  let _ ← region #[] (base := "then") (discard <| emitConst (.str .base "k") (.int 1))
  finishBlock (.ret () r)

/-- info: #["region then ends with block then.0 open"] -/
#guard_msgs in
#eval errors openRegion

/-- Two errors, printed a line each. -/
private def twoErrors : BuildM base Unit Unit := do
  afterClose
  neverClosed

/-- info: instruction %1 emitted with no block open
the function ends with block entry.1 open -/
#guard_msgs in
#eval match build (.str .base "f") intT () twoErrors with
  | .ok _ => IO.println "built"
  | .error e => IO.println (toString e)

/-! ## Not well formed

A body with no misuse whose function is not well formed: `build` fails with no misuse. -/

/-- A function declared to return `Int` that returns a `Bool`. -/
private def wrongResult : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  finishBlock (.ret () (← emitConst (.str .base "r") (.bool true)))

/-- info: misuses: #[]
f is not well formed -/
#guard_msgs in
#eval match build (.str .base "f") intT () wrongResult with
  | .ok _ => IO.println "built"
  | .error e => IO.println s!"misuses: {e.misuses}\n{e}"

/-! ## Stubs

A stub takes the parameters it is given, each named after its position, so that two of one
name stay apart. -/

/-- info: module f {
  func @f(%x.0 : base.Int, %x.1 : base.Bool) -> base.Int {
    entry.0(%x.0 : base.Int, %x.1 : base.Bool):
      unreachable
  }
} -/
#guard_msgs in
#eval IO.println ((Build.stub (.str .base "f") #[(.str .base "x", intT), (.str .base "x", boolT)]
  intT ()).val.format .full)

end Strata.Mantle.BuildTest
