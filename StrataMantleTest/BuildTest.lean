/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Build
public import StrataMantle.DDM
public import StrataMantle.WF
import StrataMantle.Env.WF
-- The builder and the printer run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.DDM
meta import StrataMantle.Env.WF
-- `decide +kernel` unfolds the checker, the environment and core's array operations.
import all StrataMantle.WF
import all StrataMantle.Env
import all StrataMantle.Base
import all StrataMantle.Build
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq

set_option autoImplicit false

/-!
# Emitting and printing over the base environment

Functions emitted with `Mantle.Build` against `base` alone, so nothing here depends on a
language.  Each is checked by `Mantle.WF`, and most are printed by the dialect in
`Mantle/DDM.lean`: every constant form, the cell operations with their type arguments, the
base's control flow, and `Except.case`.  The first is the case the builder exists for: a
forward branch names a label long before its block is finished, and the label becomes an
index only once every block is in.
-/

namespace Strata.Mantle.BuildTest

open Strata.Mantle.Build (freshVal freshLabel startBlock startBlockWith startFreshBlock
  emitConst emitApply finishBlock terminate goto build Errors Holds region withInfo)

private def boolT : TypeExpr base 0 := Base.Bool.ty
private def intT  : TypeExpr base 0 := Base.Int.ty
private def strT  : TypeExpr base 0 := Base.String.ty
private def unitT : TypeExpr base 0 := Base.Unit.ty
private def refIntT : TypeExpr base 0 := Base.Ref.ty intT
private def exceptStrIntT : TypeExpr base 0 := Base.Except.ty strT intT

/-- The label `freshLabel base` hands out `n`-th. -/
private def lbl (base : String) (n : Nat) : Label := ⟨.num (.str .base base) n⟩

/-! ## A cell written under a condition

`done` is allocated first and finished last.  Blocks are named, so the transfer to it
needs no fixing up once it is finished; the blocks appear in the order they were
finished, entry first. -/

private def f : Except Errors (Func base Unit) :=
  build (.str .base "f") intT () do
    let c ← freshVal "c" boolT
    let done ← freshLabel "done"
    let bump ← freshLabel "bump"
    let _ ← startFreshBlock #[c] "entry"
    let zero ← emitConst "k" (.int 0)
    let cell ← emitApply "cell" refIntT Base.refNew #v[intT] #[zero]
    finishBlock (.branch () c.id (goto bump) (goto done))
    startBlock bump
    let one ← emitConst "k" (.int (-1))
    let _ ← emitApply "unit" unitT Base.refSet #v[intT] #[cell, one]
    finishBlock (.jump () (goto done))
    startBlock done
    let r ← emitApply "r" intT Base.refGet #v[intT] #[cell]
    finishBlock (.ret () r)

example : Holds (Func.WF #[]) f := by decide +kernel

example : Holds (·.blocks.size = 3) f := by decide +kernel

/-- Every value is named, and two `k`s are distinguished by suffix rather than colliding. -/
example : Holds (·.names.size = 6) f := by decide +kernel

example : Holds (fun f => f.names[1]? = some ⟨"k", 0⟩ ∧ f.names[3]? = some ⟨"k", 1⟩) f := by
  decide +kernel

/-- Every terminator's targets.  A `ret` is a jump to `Label.exit`. -/
private def targets (fn : Func base Unit) : Array Label :=
  fn.blocks.flatMap fun b => match b.term with
    | .apply _ _ _ _ succs _ => succs.map (·.target)

example : Holds (·.blocks.map (·.label) = #[lbl "entry" 0, lbl "bump" 0, lbl "done" 0]) f := by
  decide +kernel

example : Holds (targets · = #[lbl "bump" 0, lbl "done" 0, lbl "done" 0, Label.exit]) f := by
  decide +kernel

/-- info: module f {
  func @f(%0 : base.Bool) -> base.Int {
    entry.0(%0 : base.Bool):
      %1 : base.Int = const int 0
      %2 : base.Ref(base.Int) = base.refNew[base.Int] %1
      branch %0 ^bump.0() ^done.0()
    bump.0():
      %3 : base.Int = const int (-1)
      %4 : base.Unit = base.refSet[base.Int] %2 %3
      jump ^done.0()
    done.0():
      %5 : base.Int = base.refGet[base.Int] %2
      ret %5
  }
}
-/
#guard_msgs in
#eval do IO.println (Func.toString (← IO.ofExcept f))

/-! ## A failure built and inspected

Both `Except` constructors, and `Except.case`, whose successors are labels allocated before
the blocks they name. -/

private def h : Except Errors (Func base Unit) :=
  build (.str .base "h") intT () do
    let okL ← freshLabel "ok"
    let errL ← freshLabel "err"
    let _ ← startFreshBlock (base := "entry")
    let msg ← emitConst "msg" (.str "boom")
    let e ← emitApply "e" exceptStrIntT Base.Except.error #v[strT, intT] #[msg]
    terminate Base.Except.case #v[strT, intT] #[e] #[goto okL, goto errL]
    let _ ← startBlockWith errL "err" strT
    let zero ← emitConst "zero" (.int 0)
    let o ← emitApply "o" exceptStrIntT Base.Except.ok #v[strT, intT] #[zero]
    terminate Base.Except.case #v[strT, intT] #[o] #[goto okL, goto errL]
    finishBlock (.ret () (← startBlockWith okL "v" intT))

example : Holds (Func.WF #[]) h := by decide +kernel

/-- `errL` was finished before `okL`; the successors still name the labels they were
given. -/
example :
    Holds (targets · = #[lbl "ok" 0, lbl "err" 0, lbl "ok" 0, lbl "err" 0, Label.exit]) h := by
  decide +kernel

example : Holds (·.blocks.map (·.label) = #[lbl "entry" 0, lbl "err" 0, lbl "ok" 0]) h := by
  decide +kernel

/-- The successors follow `Except`'s declaration order, `ok` first: swapped, they are
rejected. -/
private def hSwapped : Except Errors (Func base Unit) :=
  h.map fun h => { h with blocks := h.blocks.modify 0 fun b =>
      { b with
        term := .apply () Base.Except.case #v[strT, intT] #[⟨1⟩]
          #[⟨lbl "err" 0, #[]⟩, ⟨lbl "ok" 0, #[]⟩] #[] } }

example : Holds (¬ Func.WF #[] ·) hSwapped := by decide +kernel

/-! ## The other constants, and a failure inspected, as a module

`Except.case` ending in `unreachable`, and every constant form `f` and `h` do not use. -/

private def hConsts : Except Errors (Func base Unit) :=
  build (.str .base "h") intT () do
    let okL ← freshLabel "ok"
    let errL ← freshLabel "err"
    let _ ← startFreshBlock (base := "entry")
    let _ ← emitConst "u" .unit
    let _ ← emitConst "b" (.bool true)
    let _ ← emitConst "x" (.float 1.5)
    let msg ← emitConst "msg" (.str "boom")
    let e ← emitApply "e" exceptStrIntT Base.Except.error #v[strT, intT] #[msg]
    terminate Base.Except.case #v[strT, intT] #[e] #[goto okL, goto errL]
    finishBlock (.ret () (← startBlockWith okL "v" intT))
    let _ ← startBlockWith errL "err" strT
    finishBlock (.unreachable ())

example : Holds (Func.WF #[]) hConsts := by decide +kernel

private def m : Except Errors (Module base Unit) :=
  return { name := .str .base "m", funcs := #[← f, ← hConsts], info := () }

/-- info: module m {
  func @f(%0 : base.Bool) -> base.Int {
    entry.0(%0 : base.Bool):
      %1 : base.Int = const int 0
      %2 : base.Ref(base.Int) = base.refNew[base.Int] %1
      branch %0 ^bump.0() ^done.0()
    bump.0():
      %3 : base.Int = const int (-1)
      %4 : base.Unit = base.refSet[base.Int] %2 %3
      jump ^done.0()
    done.0():
      %5 : base.Int = base.refGet[base.Int] %2
      ret %5
  }
  func @h() -> base.Int {
    entry.0():
      %0 : base.Unit = const unit
      %1 : base.Bool = const bool (true)
      %2 : base.Float64 = const float "1.5"
      %3 : base.String = const str "boom"
      %4 : base.Except(base.String, base.Int) = base.error[base.String, base.Int] %3
      base.Except.case[base.String, base.Int] %4 ^ok.0() ^err.0()
    ok.0(%5 : base.Int):
      ret %5
    err.0(%6 : base.String):
      unreachable
  }
}
-/
#guard_msgs in
#eval do IO.println (toString (← IO.ofExcept m))

/-! ## Annotations

An emitter given no annotation uses the default, which starts as the function's own and
which `withInfo` replaces for what it emits.  An explicit one wins over both. -/

private def annotated : Except Errors (Func base Nat) :=
  build (.str .base "a") exceptStrIntT 0 do
    let _ ← startFreshBlock
    let a ← emitConst "a" (.int 1)
    let _ ← withInfo 7 (emitConst "b" (.int 2))
    let _ ← withInfo 7 (emitConst "c" (.int 3) (some 9))
    let r ← emitApply "ret" exceptStrIntT Base.Except.ok #v[strT, intT] #[a]
    withInfo 5 (finishBlock (.ret 5 r))

private def instrInfos (fn : Func base Nat) : Array Nat :=
  fn.blocks.flatMap fun b => b.instrs.map fun
    | .const i .. | .apply i .. => i

example : Holds (instrInfos · = #[0, 7, 9, 0]) annotated := by decide +kernel

example : Holds (·.blocks.map (·.info) = #[5]) annotated := by decide +kernel

/-! ## Misuse

Each is an error, and `build` fails.  `errors` shows the `Errors` it fails with. -/

/-- The errors `build` fails with for `m`, a function returning `Int`, or none. -/
private def errors (m : BuildM base Unit Unit) : Array String :=
  match build (.str .base "f") intT () m with
  | .ok _ => #[]
  | .error e => e.toArray

/-- An instruction emitted after the block is closed. -/
private def afterClose : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  let r ← emitConst "r" (.int 0)
  finishBlock (.ret () r)
  let _ ← emitConst "dead" (.int 1)

example : (build (.str .base "f") intT () afterClose).isOk = false := by decide +kernel

/-- info: #["instruction %1 emitted with no block open"] -/
#guard_msgs in
#eval errors afterClose

/-- A body that never closes its entry block. -/
private def neverClosed : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  let _ ← emitConst "r" (.int 0)

example : (build (.str .base "f") intT () neverClosed).isOk = false := by decide +kernel

/-- info: #["the function ends with block entry.0 open"] -/
#guard_msgs in
#eval errors neverClosed

/-- A block opened over an open one. -/
private def overOpen : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  let r ← emitConst "r" (.int 0)
  let _ ← startFreshBlock (base := "next")
  finishBlock (.ret () r)

example : (build (.str .base "f") intT () overOpen).isOk = false := by decide +kernel

/-- info: #["block next.0 opened while block entry.0 is open"] -/
#guard_msgs in
#eval errors overOpen

/-- A block finished when none is open. -/
private def noneOpen : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  let r ← emitConst "r" (.int 0)
  finishBlock (.ret () r)
  finishBlock (.ret () r)

example : (build (.str .base "f") intT () noneOpen).isOk = false := by decide +kernel

/-- info: #["a block finished with no block open"] -/
#guard_msgs in
#eval errors noneOpen

/-- A region whose entry block is left open. -/
private def openRegion : BuildM base Unit Unit := do
  let _ ← startFreshBlock (base := "entry")
  let r ← emitConst "r" (.int 0)
  let _ ← region #[] (base := "then") (discard <| emitConst "k" (.int 1))
  finishBlock (.ret () r)

example : (build (.str .base "f") intT () openRegion).isOk = false := by decide +kernel

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

/-- A well-built function has no errors, and `build` succeeds. -/
example : (build (.str .base "f") intT () do
    let _ ← startFreshBlock
    finishBlock (.ret () (← emitConst "r" (.int 0)))).isOk = true := by decide +kernel

end Strata.Mantle.BuildTest
