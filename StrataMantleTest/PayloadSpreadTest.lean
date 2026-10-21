/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataMantle.DDM
public import StrataMantle.DDMRead
public import StrataMantle.Env.Refine
import StrataMantle.Env.WF
import StrataMantle.DSL
-- The builder, the checker, the printer and the reader run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.DDM
meta import StrataMantle.DDMRead
meta import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Spreads in successor payloads

A successor's payload may spread a list, `(^k (*xs : ts))`: the successor receives one value
per element of `ts`, of that element's type.  `untuple` takes a tuple apart this way, and
`split` passes a fixed value before a spread.
-/

namespace Strata.Mantle.PayloadSpreadTest

/-- Tuples, built from and taken apart into one value per element. -/
public environment Tup extends Base where
  namespace tup
  open base
  /-- A tuple of values of the types `ts`. -/
  type Tuple (ts : list)
  /-- A tuple of `xs`. -/
  insn tuple [(ts : list)] (*xs : ts) : Tuple ts
  /-- Continue at `k` with the tuple's elements. -/
  terminal insn untuple [(ts : list)] (t : Tuple ts) (^k (*xs : ts))
  /-- Continue at `k` with `n` and then the tuple's elements. -/
  terminal insn split [(ts : list)] (n : Int) (t : Tuple ts) (^k (m : Int) (*xs : ts))
  end tup

/-- A spread payload entry is a list: `ts`, the literal `[*ts]`. -/
example : Tup.untuple.sig (e := Tup.env) =
    { ann := (), typeParams := #[⟨"ts", .list⟩],
      argTypes := #[⟨"t", Tup.Tuple.ty (.var 0 (by decide))⟩],
      returnType := none, succs := #[⟨"k", #[.list (.var 0 (by decide))]⟩],
      distinct := by decide } := rfl

/-- A fixed entry before it is a type. -/
example : (Tup.split.sig (e := Tup.env)).succs =
    #[⟨"k", #[.ty Base.Int.ty, .list (.var 0 (by decide))]⟩] := rfl

open Build (freshVal startFreshBlock emitApply emitConst terminate finishBlock build goto
  freshLabel startBlock FailedFunc)

private def intT : TypeExpr Tup.env := Base.Int.ty
private def boolT : TypeExpr Tup.env := Base.Bool.ty

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc Tup.env Unit Unit) {fn : Func Tup.env Unit // fn.WF}

/-- The build failed because its function is not well formed, not by a misuse. -/
private def rejects (f : Built) : Bool :=
  match f with
  | .error e => e.misuses.isEmpty
  | .ok _ => false

/-- `f(%a : Int, %b : Bool) : Int`: the tuple of `a` and `b`, taken apart into a block that takes
`params` and returns its first. -/
private def roundTrip (params : Array (TypeExpr Tup.env)) : Built :=
  build (.str .base "f") intT () do
    let a ← freshVal (.str .base "a") intT
    let b ← freshVal (.str .base "b") boolT
    let _ ← startFreshBlock #[a, b] "entry"
    let t ← emitApply (.str .base "t") (Tup.Tuple.ty (.ofTypes #[intT, boolT])) Tup.tuple
      #[a.id, b.id]
    let k ← freshLabel "k"
    terminate Tup.untuple #[t] #[goto k]
    let ps ← params.mapM (freshVal (.str .base "p"))
    startBlock k ps
    finishBlock (.ret () ((ps[0]?.map (·.id)).getD a.id))

-- The block takes one value per element, of its type: not one too few, nor one of the wrong
-- type.
#guard (roundTrip #[intT, boolT]).isOk
#guard rejects (roundTrip #[intT])
#guard rejects (roundTrip #[intT, intT])

/-- `g(%a : Int, %b : Bool) : Int`: `split` of `0` and the tuple, into a block that takes
`params` and returns its first. -/
private def splitInto (params : Array (TypeExpr Tup.env)) : Built :=
  build (.str .base "g") intT () do
    let a ← freshVal (.str .base "a") intT
    let b ← freshVal (.str .base "b") boolT
    let _ ← startFreshBlock #[a, b] "entry"
    let t ← emitApply (.str .base "t") (Tup.Tuple.ty (.ofTypes #[intT, boolT])) Tup.tuple
      #[a.id, b.id]
    let n ← emitConst (.str .base "n") (.int 0)
    let k ← freshLabel "k"
    terminate Tup.split #[n, t] #[goto k]
    let ps ← params.mapM (freshVal (.str .base "p"))
    startBlock k ps
    finishBlock (.ret () ((ps[0]?.map (·.id)).getD a.id))

-- The fixed value, then the elements.
#guard (splitInto #[intT, intT, boolT]).isOk
#guard rejects (splitInto #[intT, boolT])

/-! ## Printing and reading -/

/-- Read `text` in `Tup.env`, and print the module or the diagnostics. -/
private def readBack (text : String) : IO Unit := do
  match ← Module.read Tup.env text "t.mantle" with
  | .error e => IO.println e
  | .ok m => IO.println (toString m)

/-- info: module f {
  func @f(%a.0 : base.Int, %b.0 : base.Bool) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Bool):
      %t.0 : tup.Tuple([base.Int, base.Bool]) = tup.tuple[[base.Int, base.Bool]](%a.0, %b.0)
      tup.untuple[[base.Int, base.Bool]](%t.0) ^k.0()
    k.0(%p.0 : base.Int, %p.1 : base.Bool):
      ret(%p.0)
  }
}
-/
#guard_msgs in
#eval do readBack ((← IO.ofExcept (roundTrip #[intT, boolT])).val.format .full)

end Strata.Mantle.PayloadSpreadTest
