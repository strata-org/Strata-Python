/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataMantle.DDM
public import StrataMantle.DDMRead
import StrataMantle.Env.WF
-- The builder, the checker, the printer and the reader run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.DDM
meta import StrataMantle.DDMRead
meta import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Typed code pointers

`base.Fn as r` is the type of a code pointer to a function that takes arguments of the types
`as` and returns an `r`, and `base.callCode` calls through one.  A reference `@m.f` has `f`'s
code type, or the untyped `base.Code`, which cannot be called.

A module of two functions: `pos`, which takes an `Int` and returns a `Bool`, and `apply`, which
calls `pos` through a reference.  The module checks a reference's type against its target's
code type, and the reader reads `@m.pos` at the type where it is used.
-/

namespace Strata.Mantle.CodePtrTest

open Strata.Mantle.Build (freshVal startFreshBlock emitConst emitFunc emitApply finishBlock build
  FailedFunc)

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc base Unit Unit) {fn : Func base Unit // fn.WF}


/-- `Fn [Int] Bool`, `pos`'s code type. -/
private def posT : TypeExpr base := Base.Fn [Base.Int] Base.Bool

/-- `m.<s>`. -/
private def mn (s : String) : Name := .str (.str .base "m") s

/-- `pos(%x : Int) : Bool`. -/
private def pos : Built :=
  build (mn "pos") Base.Bool () do
    let x ← freshVal (.str .base "x") Base.Int
    let _ ← startFreshBlock #[x] "entry"
    finishBlock (.ret () (← emitConst (.str .base "t") (.bool true)))

/-- `apply(%x : Int) : Bool`: `callCode` of `pos`, through a reference at `ty`, on `x`.  The
builder infers `callCode`'s type arguments from the reference's type. -/
private def apply (ty : TypeExpr base) : Built :=
  build (mn "apply") Base.Bool () do
    let x ← freshVal (.str .base "x") Base.Int
    let _ ← startFreshBlock #[x] "entry"
    let p ← emitFunc (mn "pos") ty
    let r ← emitApply (.str .base "r") Base.Bool Base.callCode #[p, x.id]
    finishBlock (.ret () r)

/-- `ref() : Bool`, which only takes a reference to `pos` at `ty`. -/
private def ref (ty : TypeExpr base) : Built :=
  build (mn "ref") Base.Bool () do
    let _ ← startFreshBlock #[] "entry"
    let _ ← emitFunc (mn "pos") ty
    finishBlock (.ret () (← emitConst (.str .base "t") (.bool true)))

/-- The module `m` of `fs`, assembled from checked functions, or the names it rejects. -/
private def assemble (fs : Array Built) : Except String (Module base Unit) := do
  let fs ← fs.mapM fun f => f.mapError fun _ => "a function does not build"
  (Module.ofChecked (.str .base "m") fs ()).mapError fun bad => s!"{bad.map ToDDM.nameText}"

/-- The module of `fs`, or what rejects it. -/
private def describe (fs : Array Built) : String :=
  match assemble fs with
  | .ok m => "ok: " ++ toString m
  | .error e => e

/-! ## The function's code type -/

#guard match pos with
  | .ok p => p.val.codeType == posT
  | .error _ => false

/-! ## `callCode`'s operands

At `as := [Int]` and `r := Bool`, `callCode` takes a `Fn [Int] Bool` and then one `Int`: its
spread takes the list's types. -/

/-- `callCode`'s type arguments `[Int], Bool`. -/
private def callArgs : TypeArgs base (Base.callCode.sig (e := base)).scope :=
  ⟨#[.list (.ofTypes #[Base.Int]), .ty Base.Bool], rfl⟩

#guard (Base.callCode.sig (e := base)).operandTypes? callArgs 2 == some #[posT, Base.Int]
#guard (Base.callCode.sig (e := base)).operandTypes? callArgs 3 == none

-- The spread's types are its list's elements: here `ofTypes`'s types.
example : (TypeList.ofTypes (env := base) #[Base.Int]).elems = #[Base.Int] :=
  TypeExpr.elems_ofTypes _

/-! ## Calling through a reference

At `pos`'s code type `apply` builds, and the module is well formed.  At `base.Code` the builder
cannot infer `callCode`'s type arguments, since `callCode` takes a `Fn`. -/

#guard (apply posT).isOk
#guard match apply Base.Code with
  | .error e => e.misuses == #["cannot infer the type arguments of base.callCode: the types of \
      its operands and result do not fit its signature"]
  | .ok _ => false

/-- info: ok: module m {
  func @m.pos(%x.0 : base.Int) -> base.Bool {
    entry.0(%x.0 : base.Int):
      ret(true)
  }
  func @m.apply(%x.0 : base.Int) -> base.Bool {
    entry.0(%x.0 : base.Int):
      %r.0 : base.Bool = base.callCode[[base.Int], base.Bool](@m.pos, %x.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval IO.println (describe #[pos, apply posT])

/-! ## A reference's type

A reference is a code pointer, so the builder rejects `ref` at `base.Int`: the function is not
well formed.  At `base.Code` and at a `Fn` the function is well formed.  Its module accepts the
reference at `pos`'s code type and at `base.Code`, and names `ref` for a `Fn` with another result
or another parameter. -/

#guard match ref Base.Int with
  | .error e => toString e == "m.ref is not well formed"
  | .ok _ => false

/-- info: ok: module m {
  func @m.pos(%x.0 : base.Int) -> base.Bool {
    entry.0(%x.0 : base.Int):
      ret(true)
  }
  func @m.ref() -> base.Bool {
    entry.0():
      %code.0 : base.Fn([base.Int], base.Bool) = const @m.pos
      ret(true)
  }
}

ok: module m {
  func @m.pos(%x.0 : base.Int) -> base.Bool {
    entry.0(%x.0 : base.Int):
      ret(true)
  }
  func @m.ref() -> base.Bool {
    entry.0():
      %code.0 : base.Code = const @m.pos
      ret(true)
  }
}

#[m.ref]
#[m.ref] -/
#guard_msgs in
#eval do
  IO.println (describe #[pos, ref posT])
  IO.println (describe #[pos, ref Base.Code])
  IO.println (describe #[pos, ref (Base.Fn [Base.Int] Base.Int)])
  IO.println (describe #[pos, ref (Base.Fn [Base.Bool] Base.Bool)])

/-! ## Reading

The printed module reads back, and prints the same.  The reader takes `@m.pos` at the type
where it is used, which must be `pos`'s code type or `base.Code`. -/

/-- Read `text`, and print the module or the diagnostics. -/
private def readBack (text : String) : IO Unit := do
  match ← Module.read base text "t.mantle" with
  | .error e => IO.println e
  | .ok m => IO.println (toString m)

/-- `m` with `apply`'s reference written `ref`, a constant at type `ty`. -/
private def withRef (ty ref : String) : String := s!"module m \{
  func @m.pos(%x.0 : base.Int) -> base.Bool \{
    entry.0(%x.0 : base.Int):
      ret(true)
  }
  func @m.apply(%x.0 : base.Int) -> base.Bool \{
    entry.0(%x.0 : base.Int):
      %p.0 : {ty} = const {ref}
      %r.0 : base.Bool = base.callCode[[base.Int], base.Bool](%p.0, %x.0)
      ret(%r.0)
  }
}"

#guard_msgs in
#eval do
  let text := (← IO.ofExcept (assemble #[pos, apply posT])).raw.format .full
  match ← Module.read base text "t.mantle" with
  | .error e => IO.println e
  | .ok m => if m.raw.format .full != text then IO.println "differs"

/-- info: module m {
  func @m.pos(%x.0 : base.Int) -> base.Bool {
    entry.0(%x.0 : base.Int):
      ret(true)
  }
  func @m.apply(%x.0 : base.Int) -> base.Bool {
    entry.0(%x.0 : base.Int):
      %r.0 : base.Bool = base.callCode[[base.Int], base.Bool](@m.pos, %x.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval readBack (withRef "base.Fn([base.Int], base.Bool)" "@m.pos")

/-- info: t.mantle:8:51: @m.pos has type base.Fn([base.Int], base.Bool), or base.Code, where base.Fn([base.Int], base.Int) is expected -/
#guard_msgs in
#eval readBack (withRef "base.Fn([base.Int], base.Int)" "@m.pos")

-- At `base.Bool` it does not read, beside the same reference at `Fn` above.
/-- info: t.mantle:8:31: @m.pos has type base.Fn([base.Int], base.Bool), or base.Code, where base.Bool is expected -/
#guard_msgs in
#eval readBack (withRef "base.Bool" "@m.pos")

/- At `base.Code` the reference reads, but `callCode` does not take it. -/
/-- info: t.mantle:9:62: %p.0 has type base.Code, but base.callCode, operand 1 takes base.Fn([base.Int], base.Bool) -/
#guard_msgs in
#eval readBack (withRef "base.Code" "@m.pos")

/-- info: t.mantle:9:6: base.callCode takes 2 operand(s), given 3 -/
#guard_msgs in
#eval readBack ((withRef "base.Fn([base.Int], base.Bool)" "@m.pos").replace "%x.0)" "%x.0, %x.0)")

end Strata.Mantle.CodePtrTest
