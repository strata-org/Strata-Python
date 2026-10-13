/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataMantle.DDM
public import StrataMantleTest.DSLTest
import StrataMantle.Env.WF
import StrataMantle.DSL
-- The builder and the printer run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.DDM
meta import StrataMantle.Env.WF
meta import StrataMantleTest.DSLTest
-- `decide +kernel` unfolds the checker, the environment and core's array operations.
import all StrataMantle.WF
import all StrataMantle.Env
import all StrataMantle.Base
import all StrataMantle.Build
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq

set_option autoImplicit false

/-!
# Operations with regions

An environment with an `if` whose branches are regions returning the result, and a `try`
whose body and handler are regions returning a completion.  Functions using them are emitted
with `Build.region`, checked, and printed; then the mistakes the region rules reject.
-/

namespace Strata.Mantle.RegionTest

open Strata.Mantle.DSLTest

/-- Two region operations over the base. -/
public environment Reg extends Base where
  namespace reg
  open base
  /-- An exception. -/
  type Exc
  /-- How a protected body finished. -/
  data Completion (+a) where
    | normal (value : a)
    | raise (exc : Exc)
  /-- Run `then` if `cond` holds, else `else`. -/
  insn «if» [a] (cond : Bool) (&«then» &«else» : a) : a
  /-- Run `body`; if it raises, run `handler` on the exception. -/
  insn «try» [a] (&body : Completion a) (&handler (exc : Exc) : Completion a) : Completion a
  end reg

open Strata.Mantle.Build (freshVal freshLabel startBlock startBlockWith startFreshBlock
  emitConst emitApply finishBlock goto build Errors Holds region)

private abbrev E := Reg.env

private def boolT : TypeExpr E 0 := Base.Bool.ty
private def intT : TypeExpr E 0 := Base.Int.ty
private def excT : TypeExpr E 0 := Reg.Exc.ty
private def complT : TypeExpr E 0 := Reg.Completion.ty intT

/-! ## An `if`

The `then` region has two blocks of its own, and passes a value between them; its labels
are `then.0` and `join.0`, numbered with the function's.  Both regions use values the
function defined outside them. -/

private def pick : Except Errors (Func E Unit) :=
  build (.str .base "pick") intT () do
    let c ← freshVal (.str .base "c") boolT
    let x ← freshVal (.str .base "x") intT
    let _ ← startFreshBlock #[c, x] "entry"
    let thn := region #[] (base := "then") do
      let j ← freshLabel "join"
      let one ← emitConst (.str .base "one") (.int 1)
      finishBlock (.jump () (goto j #[one]))
      finishBlock (.ret () (← startBlockWith j (.str .base "v") intT))
    let els := region #[] (finishBlock (.ret () x.id)) "else"
    let r ← emitApply (.str .base "r") intT Reg.«if» #v[intT] #[c.id] (regions := #[thn, els])
    finishBlock (.ret () r)

example : Holds (Func.WF ∅) pick := by decide +kernel

/-- The open entry block survives the regions: one top-level block, holding the `if`. -/
example : Holds (fun f => f.blocks.size = 1 ∧ (f.blocks.map (·.instrs.size)) = #[1]) pick := by
  decide +kernel

/-- Every label, regions included. -/
example : Holds (·.labels.map (·.name) =
    [.num (.str .base "entry") 0, .num (.str .base "then") 0, .num (.str .base "join") 0,
     .num (.str .base "else") 0]) pick := by
  decide +kernel

/-! ## A `try`, with an `if` nested in its body

The inner `ret` leaves the `if`, not the `try` body: each region's `ret` is a jump to its own
exit, and the `if`'s regions return what it is instantiated at, which here is the completion
the body returns. -/

private def guarded : Except Errors (Func E Unit) :=
  build (.str .base "guarded") complT () do
    let c ← freshVal (.str .base "c") boolT
    let _ ← startFreshBlock #[c] "entry"
    let body := region #[] (base := "body") do
      let ok := region #[] (base := "ok") do
        let k ← emitConst (.str .base "k") (.int 0)
        let n ← emitApply (.str .base "n") complT Reg.Completion.normal #v[intT] #[k]
        finishBlock (.ret () n)
      let bad := region #[] (base := "bad") do
        let k ← emitConst (.str .base "k") (.int 1)
        let n ← emitApply (.str .base "n") complT Reg.Completion.normal #v[intT] #[k]
        finishBlock (.ret () n)
      let r ← emitApply (.str .base "r") complT Reg.«if» #v[complT] #[c.id] (regions := #[ok, bad])
      finishBlock (.ret () r)
    let handler := do
      let exc ← freshVal (.str .base "exc") excT
      region #[exc] (base := "handler") do
        let z ← emitApply (.str .base "z") complT Reg.Completion.raise #v[intT] #[exc.id]
        finishBlock (.ret () z)
    let r ← emitApply (.str .base "r") complT Reg.«try» #v[intT] #[] (regions := #[body, handler])
    finishBlock (.ret () r)

example : Holds (Func.WF ∅) guarded := by decide +kernel

private def m : Except Errors (Module.Raw E Unit) :=
  return { name := .str .base "regions", funcs := #[← pick, ← guarded], info := () }

/-! ## Printed -/

/-- info: module regions {
  func @pick(%c.0 : base.Bool, %x.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %x.0 : base.Int):
      %r.0 : base.Int = reg.if[base.Int](%c.0) {
        then.0():
          jump ^join.0(1)
        join.0(%v.0 : base.Int):
          ret(%v.0)
      } {
        else.0():
          ret(%x.0)
      }
      ret(%r.0)
  }
  func @guarded(%c.0 : base.Bool) -> reg.Completion(base.Int) {
    entry.0(%c.0 : base.Bool):
      %r.0 : reg.Completion(base.Int) = reg.try[base.Int] {
        body.0():
          %r.1 : reg.Completion(base.Int) = reg.if[reg.Completion(base.Int)](%c.0) {
            ok.0():
              %n.0 : reg.Completion(base.Int) = reg.normal[base.Int](0)
              ret(%n.0)
          } {
            bad.0():
              %n.1 : reg.Completion(base.Int) = reg.normal[base.Int](1)
              ret(%n.1)
          }
          ret(%r.1)
      } {
        handler.0(%exc.0 : reg.Exc):
          %z.0 : reg.Completion(base.Int) = reg.raise[base.Int](%exc.0)
          ret(%z.0)
      }
      ret(%r.0)
  }
} -/
#guard_msgs in
#eval do
  match (← IO.ofExcept m).check with
  | .ok m => IO.println m
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

/-- The builder allocates a result before the regions `emitApply` emits, so the ids follow
the printed order: what reading the printed function gives. -/
example : Holds Func.Canonical pick := by decide +kernel

example : Holds Func.Canonical guarded := by decide +kernel

/-! ## What it rejects -/

/-- `f(c : Bool, x : Int) : ret`: `body c x entry` emits the entry block and what follows. -/
private def fCX (body : ValId → ValId → Label → BuildM E Unit Unit) (ret : TypeExpr E 0 := intT) :
    Except Errors (Func E Unit) :=
  build (.str .base "f") ret () do
    let c ← freshVal (.str .base "c") boolT
    let x ← freshVal (.str .base "x") intT
    body c.id x.id (← startFreshBlock #[c, x])

/-- A region returning `v`. -/
private def retRegion (v : ValId) : BuildM E Unit (Region E Unit) :=
  region #[] (finishBlock (.ret () v))

/-- An `if` with its `else` missing. -/
example : Holds (¬ Func.WF ∅ ·) (fCX fun c x _ => do
    let r ← emitApply (.str .base "r") intT Reg.«if» #v[intT] #[c] (regions := #[retRegion x])
    finishBlock (.ret () r)) := by
  decide +kernel

/-- A handler region whose entry takes an `Int` rather than the exception. -/
private def wrongEntry : Except Errors (Func E Unit) :=
  build (.str .base "f") complT () do
    let _ ← startFreshBlock
    let body := region #[] do
      let k ← emitConst (.str .base "k") (.int 0)
      finishBlock (.ret () (← emitApply (.str .base "n") complT Reg.Completion.normal #v[intT]
          #[k]))
    let handler := do
      let i ← freshVal (.str .base "i") intT
      region #[i] do
        finishBlock (.ret () (← emitApply (.str .base "n") complT Reg.Completion.normal #v[intT]
            #[i.id]))
    let r ← emitApply (.str .base "r") complT Reg.«try» #v[intT] #[] (regions := #[body, handler])
    finishBlock (.ret () r)

example : Holds (¬ Func.WF ∅ ·) wrongEntry := by decide +kernel

/-- A `then` region returning the condition, not an `Int`. -/
example : Holds (¬ Func.WF ∅ ·) (fCX fun c x _ => do
    let regions := #[retRegion c, retRegion x]
    finishBlock (.ret () (← emitApply (.str .base "r") intT Reg.«if» #v[intT]
        #[c] (regions := regions)))) := by
  decide +kernel

/-- A `then` region that jumps to a block of the function rather than returning. -/
private def escape (escapes : Bool) : Except Errors (Func E Unit) :=
  fCX fun c x _ => do
    let done ← freshLabel "done"
    let thn := region #[] (finishBlock (if escapes then .jump () (goto done) else .ret () x))
    let _ ← emitApply (.str .base "r") intT Reg.«if» #v[intT] #[c] (regions := #[thn, retRegion x])
    finishBlock (.jump () (goto done))
    startBlock done
    finishBlock (.ret () x)

example : Holds (Func.WF ∅) (escape false) := by decide +kernel

example : Holds (¬ Func.WF ∅ ·) (escape true) := by decide +kernel

/-- A region's exit is its own, and the function's is not visible inside it: `ret` in the
`then` region leaves the `if` with an `Int`, so it cannot return the function's `Bool`. -/
private def outerExit (fromRegion : Bool) : Except Errors (Func E Unit) :=
  fCX (ret := boolT) fun c x _ => do
    let regions := #[retRegion (if fromRegion then c else x), retRegion x]
    let _ ← emitApply (.str .base "r") intT Reg.«if» #v[intT] #[c] (regions := regions)
    finishBlock (.ret () c)

example : Holds (Func.WF ∅) (outerExit false) := by decide +kernel

example : Holds (¬ Func.WF ∅ ·) (outerExit true) := by decide +kernel

/-- A region block reusing the function entry's label. -/
example : Holds (¬ Func.WF ∅ ·) (fCX fun c x entry => do
    let thn := region #[] do
      finishBlock (.jump () (goto entry))
      startBlock entry
      finishBlock (.ret () x)
    let r ← emitApply (.str .base "r") intT Reg.«if» #v[intT] #[c] (regions := #[thn, retRegion x])
    finishBlock (.ret () r)) := by
  decide +kernel

-- Two functions under one name.
#guard decide (Holds (¬ Module.Raw.WF ·) (do return { ← m with funcs := #[← pick, ← pick] }))

end Strata.Mantle.RegionTest
