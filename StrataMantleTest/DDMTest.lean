/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataMantle.DDM
public import StrataMantle.DDMRead
public import StrataMantleTest.DSLTest
import StrataMantle.Env.WF
-- The builder and the printer run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.DDM
meta import StrataMantle.DDMRead
meta import StrataMantle.Env.WF
meta import StrataMantleTest.DSLTest

set_option autoImplicit false

/-!
# Printing list types, and instructions with list parameters

A function over `DSLTest`'s `Fns` takes a `base.Fn([base.Int, base.Bool], base.Int)` and
applies it.  A list of types prints as a bracketed literal, and reads back.  A type where a
list is expected does not read, nor does a list where a type is, a list in a list, or a list
variable outside a signature.

Then instructions with list parameters: applied at a literal, with a splice, and instantiated
through a list variable; the operands a spread takes; kind errors at a use site, from the
builder and the reader; and the applications printed and read back.
-/

namespace Strata.Mantle.DDMTest

open Strata.Mantle.Build (freshVal startFreshBlock emitApply finishBlock build FailedFunc)
open Strata.Mantle.DSLTest

/-- What `build` gives in `env`: a checked function, or the `FailedFunc`. -/
private abbrev Built (env : Env Unit) [base ⊑ env] :=
  Except (FailedFunc env Unit Unit) {fn : Func env Unit // fn.WF}

private def intT : TypeExpr Fns.env := Base.Int.ty
private def boolT : TypeExpr Fns.env := Base.Bool.ty
private def fnT : TypeExpr Fns.env := Base.Fn.ty (.lit #[.ty intT, .ty boolT]) intT

private def f : Built Fns.env :=
  build (.str .base "f") intT () do
    let g ← freshVal (.str .base "g") fnT
    let x ← freshVal (.str .base "x") intT
    let y ← freshVal (.str .base "y") boolT
    let _ ← startFreshBlock #[g, x, y] "entry"
    let r ← emitApply (.str .base "r") intT Fns.apply #[g.id, x.id, y.id]
    finishBlock (.ret () r)

#guard f.isOk

/-- Read `text` in `Fns.env`, and print the module or the diagnostics.  The golden below is
the printed `f`, read back and printed again. -/
private def readBack (text : String) : IO Unit := do
  match ← Module.read Fns.env text "t.mantle" with
  | .error e => IO.println e
  | .ok m => IO.println (toString m)

/-- info: module f {
  func @f(%g.0 : base.Fn([base.Int, base.Bool], base.Int), %x.0 : base.Int, %y.0 : base.Bool) -> base.Int {
    entry.0(%g.0 : base.Fn([base.Int, base.Bool], base.Int), %x.0 : base.Int, %y.0 : base.Bool):
      %r.0 : base.Int = fns.apply(%g.0, %x.0, %y.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval do readBack ((← IO.ofExcept f).val.format .full)

/-- info: module f {
  func @f(%g.0 : base.Fn([], base.Int)) -> base.Int {
    entry.0(%g.0 : base.Fn([], base.Int)):
      ret(0)
  }
}
-/
#guard_msgs in
#eval readBack "module f {
  func @f(%g.0 : base.Fn([], base.Int)) -> base.Int {
    entry.0(%g.0 : base.Fn([], base.Int)):
      ret(0)
  }
}"

/-- info: t.mantle:3:19: argument 1 of type base.Fn is a type, but its parameter takes a list of types -/
#guard_msgs in
#eval readBack "module f {
  func @f(%g.0 : base.Fn(base.Int, base.Int)) -> base.Int {
    entry.0(%g.0 : base.Fn(base.Int, base.Int)):
      ret(0)
  }
}"

/-- info: t.mantle:3:19: argument 2 of type base.Fn is a list of types, but its parameter takes a type -/
#guard_msgs in
#eval readBack "module f {
  func @f(%g.0 : base.Fn([base.Int], [base.Int])) -> base.Int {
    entry.0(%g.0 : base.Fn([base.Int], [base.Int])):
      ret(0)
  }
}"

/-- info: t.mantle:3:28: a list of types may not hold a list -/
#guard_msgs in
#eval readBack "module f {
  func @f(%g.0 : base.Fn([[base.Int]], base.Int)) -> base.Int {
    entry.0(%g.0 : base.Fn([[base.Int]], base.Int)):
      ret(0)
  }
}"

/-- info: t.mantle:3:19: a list of types where a type is expected -/
#guard_msgs in
#eval readBack "module f {
  func @f(%g.0 : [base.Int]) -> base.Int {
    entry.0(%g.0 : [base.Int]):
      ret(0)
  }
}"

/-- info: t.mantle:3:27: list variable *#0 outside a signature -/
#guard_msgs in
#eval readBack "module f {
  func @f(%g.0 : base.Fn(*#0, base.Int)) -> base.Int {
    entry.0(%g.0 : base.Fn(*#0, base.Int)):
      ret(0)
  }
}"

/-! ## Instructions with list parameters

`callFn [(as : list) r] (f : Fn as r) (*args : as) : r` applies `f` to one operand per element
of `as`; `callLast` splices `as` into its function's arguments and its spread, and `bindFirst`
returns a function of `as`.  An application passes a list for each list parameter, which
prints as a literal among the type arguments. -/

/-- The build succeeds, so its function is well formed. -/
private def accepts (f : Built Fns.env) : Bool := f.isOk

/-- The build failed because its function is not well formed, not by a misuse. -/
private def rejects (f : Built Fns.env) : Bool :=
  match f with
  | .error e => e.misuses.isEmpty
  | .ok _ => false

/-- The misuses a build fails with, or none. -/
private def errors (f : Built Fns.env) : Array String :=
  match f with
  | .ok _ => #[]
  | .error e => e.misuses

/-- `[Int, Bool]`. -/
private def intBool : TypeList Fns.env := .ofTypes #[intT, boolT]

/-- A function of `g : Fn [Int, Bool] Int`, `x : Int` and `y : Bool` that returns
`callFn[targs]` of `g` and the parameters at `ops`.  `targs` are data, so they are checked when
the builder runs, by `checkTypeArgs`. -/
private def callF (targs : Array (TypeArg Fns.env)) (ops : Array Nat) :
    Built Fns.env :=
  build (.str .base "f") intT () do
    let g ← freshVal (.str .base "g") fnT
    let x ← freshVal (.str .base "x") intT
    let y ← freshVal (.str .base "y") boolT
    let _ ← startFreshBlock #[g, x, y] "entry"
    let ps := #[g.id, x.id, y.id]
    let some ta ← Build.checkTypeArgs Fns.callFn targs | finishBlock (.ret () x.id)
    let r ← emitApply (.str .base "r") intT Fns.callFn (#[g.id] ++ ops.filterMap (ps[·]?))
      (typeArgs := .given ta)
    finishBlock (.ret () r)

/-- `as` is `[Int, Bool]`, and `r` is `Int`. -/
private def callArgs : Array (TypeArg Fns.env) := #[.list intBool, .ty intT]

/- The spread takes exactly `as`'s elements: one operand short is rejected, and so are one too
many and an `Int` where the `Bool` belongs. -/
#guard accepts (callF callArgs #[1, 2])
#guard rejects (callF callArgs #[1])
#guard rejects (callF callArgs #[1, 2, 2])
#guard rejects (callF callArgs #[1, 1])

/- A type where the list belongs is an error, and nothing is emitted. -/
/-- info: #["fns.callFn: type argument 1 is a type, but its parameter takes a list of types"] -/
#guard_msgs in
#eval errors (callF #[.ty intT, .ty intT] #[1, 2])

/-- info: #["fns.callFn: 1 type argument(s) given, but it takes 2"] -/
#guard_msgs in
#eval errors (callF #[.list intBool] #[1, 2])

/- A wrong count is reported before a wrong kind, as the reader and the DSL report it. -/
/-- info: #["fns.callFn: 3 type argument(s) given, but it takes 2"] -/
#guard_msgs in
#eval errors (callF #[.ty intT, .ty intT, .ty intT] #[1, 2])

#guard KindError.check? #[.list, .type] #[.type, .type] = some (.kind 0 .type .list)
#guard KindError.check? #[.list, .type] #[.type] = some (.count 1 2)
#guard KindError.check? #[.list, .type] #[.list, .type] = none

/-- `bindFirst[Int, [Bool], Int](g, x)`, a `Fn [Bool] Int` declared `ret`, applied by
`callFn[[Bool], Int]` to `y`; then `callLast[[Bool], Int]` applying `h : Fn [Bool, Int] Int` to
`y` and `x`. -/
private def chainF (ret : TypeExpr Fns.env) : Built Fns.env :=
  build (.str .base "chain") intT () do
    let g ← freshVal (.str .base "g") fnT
    let h ← freshVal (.str .base "h") (Base.Fn.ty (.ofTypes #[boolT, intT]) intT)
    let x ← freshVal (.str .base "x") intT
    let y ← freshVal (.str .base "y") boolT
    let _ ← startFreshBlock #[g, h, x, y] "entry"
    let bools : TypeList Fns.env := .ofTypes #[boolT]
    let b ← emitApply (.str .base "b") ret Fns.bindFirst (typeArgs := ta[intT, bools, intT])
      #[g.id, x.id]
    let _ ← emitApply (.str .base "c") intT Fns.callFn (typeArgs := ta[bools, intT]) #[b, y.id]
    let r ← emitApply (.str .base "r") intT Fns.callLast (typeArgs := ta[bools, intT])
      #[h.id, y.id, x.id]
    finishBlock (.ret () r)

#guard accepts (chainF (Base.Fn.ty (.ofTypes #[boolT]) intT))

/-- `bindFirst[Int, [Bool], Int](g, x)`, declared `ret` and unused. -/
private def bindF (ret : TypeExpr Fns.env) : Built Fns.env :=
  build (.str .base "bind") intT () do
    let g ← freshVal (.str .base "g") fnT
    let x ← freshVal (.str .base "x") intT
    let _ ← startFreshBlock #[g, x] "entry"
    let _ ← emitApply (.str .base "b") ret Fns.bindFirst
      (typeArgs := ta[intT, [boolT], intT]) #[g.id, x.id]
    finishBlock (.ret () x.id)

/- `bindFirst` returns `Fn as r` at its arguments: `Fn [Bool] Int`, not `f`'s own type. -/
#guard accepts (bindF (Base.Fn.ty (.ofTypes #[boolT]) intT))
#guard rejects (bindF fnT)

/-- info: module f {
  func @f(%g.0 : base.Fn([base.Int, base.Bool], base.Int), %x.0 : base.Int, %y.0 : base.Bool) -> base.Int {
    entry.0(%g.0 : base.Fn([base.Int, base.Bool], base.Int), %x.0 : base.Int, %y.0 : base.Bool):
      %r.0 : base.Int = fns.callFn[[base.Int, base.Bool], base.Int](%g.0, %x.0, %y.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval do readBack ((← IO.ofExcept (callF callArgs #[1, 2])).val.format .full)

/-- info: module chain {
  func @chain(%g.0 : base.Fn([base.Int, base.Bool], base.Int), %h.0 : base.Fn([base.Bool, base.Int], base.Int), %x.0 : base.Int, %y.0 : base.Bool) -> base.Int {
    entry.0(%g.0 : base.Fn([base.Int, base.Bool], base.Int), %h.0 : base.Fn([base.Bool, base.Int], base.Int), %x.0 : base.Int, %y.0 : base.Bool):
      %b.0 : base.Fn([base.Bool], base.Int) = fns.bindFirst[base.Int, [base.Bool], base.Int](%g.0, %x.0)
      %c.0 : base.Int = fns.callFn[[base.Bool], base.Int](%b.0, %y.0)
      %r.0 : base.Int = fns.callLast[[base.Bool], base.Int](%h.0, %y.0, %x.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval do readBack ((← IO.ofExcept (chainF (Base.Fn.ty (.ofTypes #[boolT]) intT))).val.format .full)

/-- `f(%g.0, %x.0, %y.0) = callFn[targs](args)`, as text. -/
private def callText (targs args : String) : String := s!"module f \{
  func @f(%g.0 : base.Fn([base.Int, base.Bool], base.Int), %x.0 : base.Int, %y.0 : base.Bool) -> base.Int \{
    entry.0(%g.0 : base.Fn([base.Int, base.Bool], base.Int), %x.0 : base.Int, %y.0 : base.Bool):
      %r.0 : base.Int = fns.callFn{targs}({args})
      ret(%r.0)
  }
}"

/- The reader rejects a type where a list belongs, and a spread's operands short of its list;
the same application with a list and every operand reads back, above. -/
/-- info: t.mantle:4:6: type argument 1 of fns.callFn is a type, but its parameter takes a list of types -/
#guard_msgs in
#eval readBack (callText "[base.Int, base.Int]" "%g.0, %x.0, %y.0")

/-- info: t.mantle:4:6: fns.callFn takes 3 operand(s), given 2 -/
#guard_msgs in
#eval readBack (callText "[[base.Int, base.Bool], base.Int]" "%g.0, %x.0")

/-- `f(%g.0, %x.0) = callFn[[], base.Int](args)`, for `g : Fn [] Int`, as text. -/
private def callEmptyText (args : String) : String := s!"module f \{
  func @f(%g.0 : base.Fn([], base.Int), %x.0 : base.Int) -> base.Int \{
    entry.0(%g.0 : base.Fn([], base.Int), %x.0 : base.Int):
      %r.0 : base.Int = fns.callFn[[], base.Int]({args})
      ret(%r.0)
  }
}"

/- At the empty list, the spread takes no operand: `g` alone reads back, and `g` with `x` does
not. -/
/-- info: module f {
  func @f(%g.0 : base.Fn([], base.Int), %x.0 : base.Int) -> base.Int {
    entry.0(%g.0 : base.Fn([], base.Int), %x.0 : base.Int):
      %r.0 : base.Int = fns.callFn[[], base.Int](%g.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval readBack (callEmptyText "%g.0")

/-- info: t.mantle:4:6: fns.callFn takes 1 operand(s), given 2 -/
#guard_msgs in
#eval readBack (callEmptyText "%g.0, %x.0")

/-! ## Datatypes with list parameters

`Clos.Closure (as : list) (+r)` pairs a `Fn as r` with an `Int`.  Its constructor is applied
at the list `[Int]`, inferred from the result type, and its case instruction at `[Int]`
written out; its successor receives the function and the `Int`, and calls the one with the
other. -/

open Build (freshLabel startBlock terminate goto checkTypeArgs) in
/-- Build a closure of `g : Fn [Int] Int` and `x`, take it apart, and call its function on its
environment.  The case instruction's type arguments are `caseArgs`, given as data. -/
private def closF (caseArgs : Array (TypeArg Clos.env)) : Built Clos.env :=
  build (.str .base "clos") (Base.Int.ty) () do
    let fnInt : TypeExpr Clos.env := Base.Fn.ty (.ofTypes #[Base.Int.ty]) Base.Int.ty
    let closT : TypeExpr Clos.env := Clos.Closure.ty (.ofTypes #[Base.Int.ty]) Base.Int.ty
    let g ← freshVal (.str .base "g") fnInt
    let x ← freshVal (.str .base "x") Base.Int.ty
    let _ ← startFreshBlock #[g, x] "entry"
    let k ← freshLabel "mk"
    let c ← emitApply (.str .base "c") closT Clos.Closure.mk #[g.id, x.id]
    let some ta ← checkTypeArgs Clos.Closure.case caseArgs | finishBlock (.ret () x.id)
    terminate Clos.Closure.case #[c] #[goto k] (typeArgs := .given ta)
    let f ← freshVal (.str .base "f") fnInt
    let v ← freshVal (.str .base "v") Base.Int.ty
    startBlock k #[f, v]
    let r ← emitApply (.str .base "r") Base.Int.ty Fns.callFn (typeArgs := ta[[Base.Int], Base.Int])
      #[f.id, v.id]
    finishBlock (.ret () r)

private def intList : TypeList Clos.env := .ofTypes #[Base.Int.ty]

#guard (closF #[.list intList, .ty Base.Int.ty]).isOk

/- A type where the list belongs is an error. -/
/-- info: #["clos.Closure.case: type argument 1 is a type, but its parameter takes a list of types"] -/
#guard_msgs in
#eval match closF #[.ty Base.Int.ty, .ty Base.Int.ty] with
  | .ok _ => #[]
  | .error e => e.misuses

/-- Read `text` in `Clos.env`, and print the module or the diagnostics. -/
private def readBackClos (text : String) : IO Unit := do
  match ← Module.read Clos.env text "t.mantle" with
  | .error e => IO.println e
  | .ok m => IO.println (toString m)

/-- info: module clos {
  func @clos(%g.0 : base.Fn([base.Int], base.Int), %x.0 : base.Int) -> base.Int {
    entry.0(%g.0 : base.Fn([base.Int], base.Int), %x.0 : base.Int):
      %c.0 : clos.Closure([base.Int], base.Int) = clos.mk[[base.Int], base.Int](%g.0, %x.0)
      clos.Closure.case[[base.Int], base.Int](%c.0) ^mk.0()
    mk.0(%f.0 : base.Fn([base.Int], base.Int), %v.0 : base.Int):
      %r.0 : base.Int = fns.callFn[[base.Int], base.Int](%f.0, %v.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval do readBackClos ((← IO.ofExcept (closF #[.list intList, .ty Base.Int.ty])).val.format .full)

/-- info: t.mantle:3:19: argument 1 of type clos.Closure is a type, but its parameter takes a list of types -/
#guard_msgs in
#eval readBackClos "module f {
  func @f(%c.0 : clos.Closure(base.Int, base.Int)) -> base.Int {
    entry.0(%c.0 : clos.Closure(base.Int, base.Int)):
      ret(0)
  }
}"

/-! ## Instantiating through a list variable

A list argument may itself be a list variable of the scope instantiated into: where the
parameter is spliced, the variable is spliced in its place. -/

/-- `Fn [*as, Int] r`, in `callLast`'s scope. -/
private def lastArg : TypeExpr Fns.env #[.list, .type] :=
  Base.Fn.ty (.lit #[.splice 0 (by decide), .ty Base.Int.ty]) (.var 1 (by decide))

/-- `as` as the list variable `0` of a scope of one list. -/
private def throughVar : TypeArgs Fns.env #[.list, .type] #[.list] :=
  ⟨#[.list (.var 0 (by decide)), .ty Base.Int.ty], rfl⟩

/-- `as` as the literal `[Bool]`. -/
private def throughLit : TypeArgs Fns.env #[.list, .type] :=
  ⟨#[.list (.ofTypes #[boolT]), .ty intT], rfl⟩

private def fnName : Name := bn "Fn"

#guard (lastArg.instantiate throughVar).toRaw ==
  .app fnName #[.list #[.var 0, intT.toRaw], intT.toRaw]
#guard (lastArg.instantiate throughLit).toRaw ==
  .app fnName #[.list #[boolT.toRaw, intT.toRaw], intT.toRaw]

/-- `Fn as r`, whose list parameter is the whole argument. -/
private def callArg : TypeExpr Fns.env #[.list, .type] :=
  Base.Fn.ty (.var 0 (by decide)) (.var 1 (by decide))

#guard (callArg.instantiate throughVar).toRaw == .app fnName #[.list #[.var 0], intT.toRaw]
#guard (callArg.instantiate throughLit).toRaw == .app fnName #[.list #[boolT.toRaw], intT.toRaw]

/-! ### A list's elements

`toElems` reads any list as the elements of its literal, one built by `instantiate` included. -/

/-- `[*as, Int]`, in `callLast`'s scope. -/
private def lastList : TypeList Fns.env #[.list, .type] :=
  .lit #[.splice 0 (by decide), .ty Base.Int.ty]

#guard lastList.toElems.map (·.toRaw) == #[.var 0, intT.toRaw]
#guard (lastList.instantiate throughLit).toElems.map (·.toRaw) ==
  #[boolT.toRaw, intT.toRaw]
#guard (lastList.instantiate throughVar).toElems.map (·.toRaw) ==
  #[.var 0, intT.toRaw]
#guard (TypeList.ofTypes (env := Fns.env) #[boolT, intT]).toElems.map (·.toRaw) ==
  #[boolT.toRaw, intT.toRaw]

/-! ### Equality and hashing of type arguments

An application's type arguments key its instances: equal arguments, built apart, compare and
hash equal, and a type and the list of it differ. -/

/-- `throughLit`'s arguments, built again. -/
private def throughLit₂ : TypeArgs Fns.env #[.list, .type] :=
  ⟨#[.list (.lit #[.ty boolT]), .ty intT], rfl⟩

#guard throughLit == throughLit₂
#guard hash throughLit == hash throughLit₂
#guard throughLit != ⟨#[.list (.ofTypes #[intT]), .ty intT], rfl⟩
#guard (TypeArg.ty intT : TypeArg Fns.env) == .ty intT
#guard hash (TypeArg.ty intT : TypeArg Fns.env) == hash (TypeArg.ty intT : TypeArg Fns.env)
#guard (TypeArg.ty intT : TypeArg Fns.env) != .list (.ofTypes #[intT])

/- `bs` is the literal `[*bs]` by definition, so the two cannot differ.  What can is the result:
instantiating at `bs` gives the type built directly with `bs`. -/
example (h : (#[.list] : Array Kind)[0]? = some .list) :
    TypeList.var (env := Fns.env) 0 h = .lit #[.splice 0 h] := rfl
#guard callArg.instantiate throughVar ==
  Base.Fn.ty (e := Fns.env) (s := #[.list]) (.var 0 (by decide)) Base.Int.ty
#guard lastArg.instantiate throughVar ==
  Base.Fn.ty (e := Fns.env) (s := #[.list]) (.lit #[.splice 0 (by decide), .ty Base.Int.ty])
    Base.Int.ty

end Strata.Mantle.DDMTest
