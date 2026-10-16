/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Build
public import StrataMantle.DDM
public import StrataMantle.WF
public import StrataMantleTest.RegionTest
import StrataMantle.Env.WF
-- The builder, the checker and the printer run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.DDM
meta import StrataMantle.WF
meta import StrataMantle.Env.WF
meta import StrataMantleTest.RegionTest

set_option autoImplicit false

/-!
# Printing with constants folded

Each module is printed twice: in full, with `PrintOptions.full`, and folded, the default,
which writes a constant at its uses and drops its line.  Between them they cover a constant
used once, one used twice, one never used, one passed to a successor or returned, a function
reference, and one defined outside the region that uses it.
-/

namespace Strata.Mantle.PrintFoldTest

open Strata.Mantle.Build (freshVal freshLabel startBlock startBlockWith startFreshBlock
  emitConst emitApply finishBlock goto build Failure region)
open Strata.Mantle.RegionTest

private abbrev E := Reg.env

private def boolT : TypeExpr E := Base.Bool.ty
private def intT : TypeExpr E := Base.Int.ty
private def codeT : TypeExpr E := Base.Code.ty
private def refIntT : TypeExpr E := Base.Ref.ty intT
private def unitT : TypeExpr E := Base.Unit.ty

/-- What `build` gives: a checked function, or the `Failure`. -/
private abbrev Built := Except (Failure Unit) {fn : Func E Unit // fn.WF}

/-- `zero` is used three times, `one` once, as a successor's argument, and `unused` never. -/
private def counter : Built :=
  build (.str (.str .base "m") "counter") intT () do
    let c ← freshVal (.str .base "c") boolT
    let done ← freshLabel "done"
    let _ ← startFreshBlock #[c] "entry"
    let zero ← emitConst (.str .base "zero") (.int 0)
    let _ ← emitConst (.str .base "unused") (.bool true)
    let cell ← emitApply (.str .base "cell") refIntT Base.refNew #[zero]
    let _ ← emitApply (.str .base "unit") unitT Base.refSet (typeArgs := ta[intT]) #[cell, zero]
    let one ← emitConst (.str .base "one") (.int (-1))
    finishBlock (.branch () c.id (goto done #[one]) (goto done #[zero]))
    let _ ← startBlockWith done (.str .base "v") intT
    let r ← emitApply (.str .base "r") intT Base.refGet #[cell]
    finishBlock (.ret () r)

/-- A reference to `counter`, returned. -/
private def code : Built :=
  build (.str (.str .base "m") "code") codeT () do
    let _ ← startFreshBlock (base := "entry")
    let f ← emitConst (.str .base "f") (.func (.str (.str .base "m") "counter"))
    finishBlock (.ret () f)

/-- `one` is defined in the entry block and used inside the `then` region. -/
private def pick : Built :=
  build (.str (.str .base "m") "pick") intT () do
    let c ← freshVal (.str .base "c") boolT
    let _ ← startFreshBlock #[c] "entry"
    let one ← emitConst (.str .base "one") (.int 1)
    let thn := region #[] (finishBlock (.ret () one)) "then"
    let els := region #[] (base := "else") do
      let two ← emitConst (.str .base "two") (.int 2)
      finishBlock (.ret () two)
    let r ← emitApply (.str .base "r") intT Reg.«if» #[c.id] (regions := #[thn, els])
    finishBlock (.ret () r)

private def m : Except (Failure Unit) (Module.Raw E Unit) :=
  return { name := .str .base "m", funcs := #[(← counter).1, (← code).1, (← pick).1], info := () }

/-! ## In full -/

/-- info: module m {
  func @m.counter(%c.0 : base.Bool) -> base.Int {
    entry.0(%c.0 : base.Bool):
      %zero.0 : base.Int = const 0
      %unused.0 : base.Bool = const true
      %cell.0 : base.Ref(base.Int) = base.refNew[base.Int](%zero.0)
      %unit.0 : base.Unit = base.refSet[base.Int](%cell.0, %zero.0)
      %one.0 : base.Int = const -1
      branch(%c.0) ^done.0(%one.0) ^done.0(%zero.0)
    done.0(%v.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%cell.0)
      ret(%r.0)
  }
  func @m.code() -> base.Code {
    entry.0():
      %f.0 : base.Code = const @m.counter
      ret(%f.0)
  }
  func @m.pick(%c.0 : base.Bool) -> base.Int {
    entry.0(%c.0 : base.Bool):
      %one.0 : base.Int = const 1
      %r.0 : base.Int = reg.if[base.Int](%c.0) {
        then.0():
          ret(%one.0)
      } {
        else.0():
          %two.0 : base.Int = const 2
          ret(%two.0)
      }
      ret(%r.0)
  }
} -/
#guard_msgs in
#eval do IO.println ((← IO.ofExcept m).format .full)

/-! ## Folded

Every used constant is written at each of its uses, and its line is gone; `%unused.0`,
unused, keeps its own.  The other values keep their names, so the two forms can be read side
by side. -/

/-- info: module m {
  func @m.counter(%c.0 : base.Bool) -> base.Int {
    entry.0(%c.0 : base.Bool):
      %unused.0 : base.Bool = const true
      %cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %unit.0 : base.Unit = base.refSet[base.Int](%cell.0, 0)
      branch(%c.0) ^done.0(-1) ^done.0(0)
    done.0(%v.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%cell.0)
      ret(%r.0)
  }
  func @m.code() -> base.Code {
    entry.0():
      ret(@m.counter)
  }
  func @m.pick(%c.0 : base.Bool) -> base.Int {
    entry.0(%c.0 : base.Bool):
      %r.0 : base.Int = reg.if[base.Int](%c.0) {
        then.0():
          ret(1)
      } {
        else.0():
          ret(2)
      }
      ret(%r.0)
  }
} -/
#guard_msgs in
#eval do
  match (← IO.ofExcept m).check with
  | .ok m => IO.println m
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

end Strata.Mantle.PrintFoldTest
