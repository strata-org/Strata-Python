/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.DDM
public import StrataMantle.WF
public import StrataPython.Mantle.Build
import StrataMantle.Env.WF
-- The builder and the printer run as compiled code below.
meta import StrataMantle.DDM
meta import StrataPython.Mantle.Build
meta import StrataMantle.Env.WF
-- `decide +kernel` unfolds the checker, the environment and core's array operations.
import all StrataMantle.WF
import all StrataMantle.Env
import all StrataMantle.Base
import all StrataMantle.Build
import all StrataPython.Mantle.Env
import all StrataPython.Mantle.Build
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq

set_option autoImplicit false

/-!
# Python functions, emitted

Functions written against `PyBuild`, checked by `Mantle.WF` and printed by the dialect in
`StrataMantle/DDM.lean`: a local as a cell, a failing operation reporting to the enclosing
handler, `try` changing that handler, `finally` by completion, a closure, and globals and
imports.  `StrataMantleTest/BuildTest.lean` has the base-only printing cases.
-/

namespace StrataPython.Mantle.PyBuildTest

open Strata.Mantle

open Strata.Mantle.Build (Errors Holds)

open StrataPython.Mantle.PyBuild

/-- The label `freshLabel base` hands out `n`-th. -/
private def lbl (base : String) (n : Nat) : Label := ⟨.num (.str .base base) n⟩

/-- The successor targets of `fn`'s instructions, in order. -/
private def errTargets (fn : Func Py.env Unit) : Array Label :=
  fn.blocks.flatMap fun b => b.instrs.flatMap fun
    | .apply _ _ _ _ _ ks _ => ks.map (·.target)
    | _ => #[]

/-! ## `def f(x): y = x + 1; return y`

The local `y` is a cell: the assignment is a `refSet` and the read a `refGet`.  `add` can
raise, so it reports to the handler `buildFunc` installs, which returns the failure to
the caller. -/

private def f : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "f") #["x"] () fun args => do
    let y ← declareLocal "y"
    let _ ← writeCell y (← emitFailing "sum" Py.add #v[] #[args[0]!, ← intLit 1])
    emitReturn (← readCell y "y")

example : Holds (Func.WF #[]) f := by decide +kernel

/-- `f`'s only failing operation reports to the handler `buildFunc` installs. -/
example : Holds (errTargets · = #[lbl "propagate" 0]) f := by decide +kernel

/-- info: module py.f {
  func @py.f(%0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%0 : py.Value):
      %1 : base.String = const str "y"
      %2 : py.Value = py.undef %1
      %3 : base.Ref(py.Value) = base.refNew[py.Value] %2
      %4 : base.Int = const int 1
      %5 : py.Value = py.intLit %4
      %6 : py.Value = py.add %0 %5 ^propagate.0()
      %7 : base.Unit = base.refSet[py.Value] %3 %6
      %8 : py.Value = base.refGet[py.Value] %3
      %9 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value] %8
      ret %9
    propagate.0(%10 : py.Value):
      %11 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value] %10
      ret %11
  }
}
-/
#guard_msgs in
#eval do IO.println (Func.toString (← IO.ofExcept f))

/-! ## `def g(): pass`

Falling off the end returns `None`.  The handler is emitted even though nothing reaches
it. -/

private def g : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "g") #[] () fun _ => emitReturnNone

example : Holds (Func.WF #[]) g := by decide +kernel

example : Holds (·.blocks.size = 2) g := by decide +kernel

/-! ## `def h(x):` / `try: return x.foo` / `except: return None`

Inside `withHandler`, a failing operation reports to the `except` block instead of to the
caller.  The exception arrives as that block's parameter, supplied by the `err`
successor. -/

/-- `h`, whose `except` block declares the exception if `takesExc`. -/
private def hWith (takesExc : Bool) : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "h") #["x"] () fun args => do
    let except ← freshLabel
    withHandler except do emitReturn (← getAttr args[0]! "foo")
    -- `except:` — the exception is bound and ignored.
    if takesExc then discard <| startBlockWith except "exc" else startBlock except
    emitReturnNone

private def h : Except Errors (Func Py.env Unit) := hWith true

example : Holds (Func.WF #[]) h := by decide +kernel

/-- Three blocks: the body, the `except` block, and the propagating handler `buildFunc`
installs.  The last is unreachable here, because nothing outside the `try` can fail. -/
example : Holds (·.blocks.size = 3) h := by decide +kernel

/-- The `attr` failure goes to the `except` block, `bb.0`, not to the caller's handler. -/
example : Holds (errTargets · = #[lbl "bb" 0]) h := by decide +kernel

/-- The blocks in the order they were finished: the body, `except`, then `propagate`. -/
example :
    Holds (·.blocks.map (·.label) = #[lbl "entry" 0, lbl "bb" 0, lbl "propagate" 0]) h := by
  decide +kernel

/-- A handler must take the exception: `err` supplies it to its target, so an `except`
block that declares no parameter is ill formed. -/
example : Holds (¬ Func.WF #[] ·) (hWith false) := by decide +kernel

/-! ## `try` / `finally`, by completion

    def k(x):
      try:
        return x.foo
      finally:
        x.cleanup

`tryFinally` emits the `finally` body once, in `fin.0`, reached from both exits of the `try`
with how it finished: `return` with the value, or `raise` from `finRaise.0`.  The cleanup's
`err` successor `superseded.0` uses a partial `BlockValue`: the site pre-binds the pending
completion and `err` supplies the exception, so a failure in the `finally` supersedes what
was pending.  Both reach `disp.0`, one `py.Completion.case` with a successor per
constructor, each binding its own payload, so `val` exists only on the path where the
completion is a `return`. -/

/-- `k`, with the `finally` body's failure routed through `superseded.0` if `superseded`. -/
private def kWith (superseded : Bool) : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "k") #["x"] () fun args => do
    let x := args[0]!
    tryFinally (superseded := superseded)
      (fun fin => do jump (Build.goto fin #[← compReturn (← getAttr x "foo")]))
      (discard <| getAttr x "cleanup")
      { normal := .block "normal" fun _ => emitReturnNone
        «return» := .block "ret" emitReturn
        raise := .block "raise" emitPropagate }

private def k : Except Errors (Func Py.env Unit) := kWith true

example : Holds (Func.WF #[]) k := by decide +kernel

/-- The cleanup body appears once: block 2, with two instructions. -/
example : Holds (fun k => (k.blocks.map (·.instrs.size))[2]? = some 2) k := by decide +kernel

/-- Eleven blocks: the entry, `finRaise`, `fin`, `superseded` and `disp`; the five successors
of the dispatch, `return` and `raise` taking their payload and fall-through, `break` and
`continue` taking none; and `buildFunc`'s propagating handler. -/
example : Holds (·.blocks.size = 11) k := by decide +kernel

/-- Without `superseded`, the `finally` body fails to the enclosing handler and `fin`
dispatches itself: no `superseded` or `disp` block. -/
example : Holds (fun k => Func.WF #[] k ∧ k.blocks.size = 9) (kWith false) := by decide +kernel

/-- info: module py.k {
  func @py.k(%0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%0 : py.Value):
      %1 : base.String = const str "foo"
      %2 : py.Value = py.attr %0 %1 ^finRaise.0()
      %3 : py.Completion = py.completionReturn %2
      jump ^fin.0(%3)
    finRaise.0(%4 : py.Value):
      %5 : py.Completion = py.completionRaise %4
      jump ^fin.0(%5)
    fin.0(%6 : py.Completion):
      %7 : base.String = const str "cleanup"
      %8 : py.Value = py.attr %0 %7 ^superseded.0(%6)
      jump ^disp.0(%6)
    superseded.0(%9 : py.Completion, %10 : py.Value):
      %11 : py.Completion = py.completionRaise %10
      jump ^disp.0(%11)
    disp.0(%12 : py.Completion):
      py.Completion.case %12 ^normal.0() ^ret.0() ^raise.0() ^unreachable.0() ^unreachable.1()
    normal.0():
      %13 : py.Value = py.noneLit
      %14 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value] %13
      ret %14
    ret.0(%15 : py.Value):
      %16 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value] %15
      ret %16
    raise.0(%17 : py.Value):
      %18 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value] %17
      ret %18
    unreachable.0():
      unreachable
    unreachable.1():
      unreachable
    propagate.0(%19 : py.Value):
      %20 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value] %19
      ret %20
  }
}
-/
#guard_msgs in
#eval do IO.println (Func.toString (← IO.ofExcept k))

/-! ## A closure

    def outer(x):
      def inner():
        return x          # captures `x` by cell, read late
      return inner

`inner` is a function of the module: `emitFunc` names it, and the checker verifies that
the module defines it.  `mkClosure` pairs the code with the cell holding `x`.  The two
functions are printed as a module. -/

private def inner : Except Errors (Func Py.env Unit) :=
  buildFuncTyped (Py.pn "inner") #[("x.cell", Py.cell.ty)] () fun args => do
    emitReturn (← readCell args[0]! "x")

/-- `outer`, whose closure names `target` and captures the cell holding `x`, or `x` itself if
`byValue`. -/
private def outerWith (target : Name) (byValue : Bool) : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "outer") #["x"] () fun args => do
    let cell ← declareLocal "x"
    let _ ← writeCell cell args[0]!
    emitReturn (← mkClosure (← emitFunc target) #[if byValue then args[0]! else cell])

/-- The module of `outer`, whose closure names `target` and captures `x` as `outerWith` does,
and `inner`. -/
private def closuresWith (target : Name) (byValue : Bool) : Except Errors (Module Py.env Unit) :=
  return { name := Py.pn "closures", funcs := #[← outerWith target byValue, ← inner], info := () }

private def closures : Except Errors (Module Py.env Unit) := closuresWith (Py.pn "inner") false

example : Holds Module.WF closures := by decide +kernel

/-- info: module py.closures {
  func @py.outer(%0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%0 : py.Value):
      %1 : base.String = const str "x"
      %2 : py.Value = py.undef %1
      %3 : base.Ref(py.Value) = base.refNew[py.Value] %2
      %4 : base.Unit = base.refSet[py.Value] %3 %0
      %5 : base.Code = const @py.inner
      %6 : py.Value = py.mkClosure %5 %3
      %7 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value] %6
      ret %7
    propagate.0(%8 : py.Value):
      %9 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value] %8
      ret %9
  }
  func @py.inner(%0 : base.Ref(py.Value)) -> base.Except(py.Value, py.Value) {
    entry.0(%0 : base.Ref(py.Value)):
      %1 : py.Value = base.refGet[py.Value] %0
      %2 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value] %1
      ret %2
    propagate.0(%3 : py.Value):
      %4 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value] %3
      ret %4
  }
}
-/
#guard_msgs in
#eval do IO.println (toString (← IO.ofExcept closures))

/-- A code pointer to a function the module does not define. -/
example : Holds (¬ Module.WF ·) (closuresWith (Py.pn "nonesuch") false) := by decide +kernel

/-- A closure captures cells, so that a late read sees a late write.  Passing the value
instead is ill typed. -/
example : Holds (¬ Module.WF ·) (closuresWith (Py.pn "inner") true) := by decide +kernel

/-! ## Globals and imports

    import a.b
    import a.b as c
    from a.b import x as y
    n = n + 1

A module body, so every name is a global of module `m`.  `import a.b` imports `a.b` and binds
the package `a`; the other two bind what they import. -/

private def globals : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "<module>") #[] () fun _ => do
    let _ ← importModule "a.b"
    let _ ← writeGlobal "m" "a" (← importModule "a")
    let _ ← writeGlobal "m" "c" (← importModule "a.b")
    let _ ← writeGlobal "m" "y" (← importFrom "a.b" "x")
    let n ← readGlobal "m" "n"
    let sum ← emitFailing "sum" Py.add #v[] #[n, ← intLit 1]
    let _ ← writeGlobal "m" "n" sum
    emitReturnNone

example : Holds (Func.WF #[]) globals := by decide +kernel

/-- info: module py.|<module>| {
  func @py.|<module>|() -> base.Except(py.Value, py.Value) {
    entry.0():
      %0 : base.String = const str "a.b"
      %1 : py.Value = py.importModule %0 ^propagate.0()
      %2 : base.String = const str "a"
      %3 : py.Value = py.importModule %2 ^propagate.0()
      %4 : base.String = const str "m"
      %5 : base.String = const str "a"
      %6 : base.Ref(py.Value) = py.globalCell %4 %5
      %7 : base.Unit = base.refSet[py.Value] %6 %3
      %8 : base.String = const str "a.b"
      %9 : py.Value = py.importModule %8 ^propagate.0()
      %10 : base.String = const str "m"
      %11 : base.String = const str "c"
      %12 : base.Ref(py.Value) = py.globalCell %10 %11
      %13 : base.Unit = base.refSet[py.Value] %12 %9
      %14 : base.String = const str "a.b"
      %15 : base.String = const str "x"
      %16 : py.Value = py.importFrom %14 %15 ^propagate.0()
      %17 : base.String = const str "m"
      %18 : base.String = const str "y"
      %19 : base.Ref(py.Value) = py.globalCell %17 %18
      %20 : base.Unit = base.refSet[py.Value] %19 %16
      %21 : base.String = const str "m"
      %22 : base.String = const str "n"
      %23 : base.Ref(py.Value) = py.globalCell %21 %22
      %24 : py.Value = base.refGet[py.Value] %23
      %25 : base.String = const str "NameError"
      %26 : base.String = const str "name 'n' is not defined"
      %27 : py.Value = py.requireDefined %24 %25 %26 ^propagate.0()
      %28 : base.Int = const int 1
      %29 : py.Value = py.intLit %28
      %30 : py.Value = py.add %27 %29 ^propagate.0()
      %31 : base.String = const str "m"
      %32 : base.String = const str "n"
      %33 : base.Ref(py.Value) = py.globalCell %31 %32
      %34 : base.Unit = base.refSet[py.Value] %33 %30
      %35 : py.Value = py.noneLit
      %36 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value] %35
      ret %36
    propagate.0(%37 : py.Value):
      %38 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value] %37
      ret %38
  }
}
-/
#guard_msgs in
#eval do IO.println (Func.toString (← IO.ofExcept globals))

/-! ## A function named like an operation

    def add(x):          # in module `m`
      add              # the function itself
      return x + x

The function `m.add` prints as `@m.add`, in its header and in the constant that refers to it,
so neither reads as the operation `py.add`. -/

private def mAdd : Name := .str (.str .base "m") "add"

private def addFn : Except Errors (Func Py.env Unit) :=
  buildFunc mAdd #["x"] () fun args => do
    let _ ← funcValue mAdd
    emitReturn (← emitFailing "sum" Py.add #v[] #[args[0]!, args[0]!])

example : Holds (Func.WF #[mAdd]) addFn := by decide +kernel

/-- info: module m.add {
  func @m.add(%0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%0 : py.Value):
      %1 : base.Code = const @m.add
      %2 : py.Value = py.mkClosure %1
      %3 : py.Value = py.add %0 %0 ^propagate.0()
      %4 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value] %3
      ret %4
    propagate.0(%5 : py.Value):
      %6 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value] %5
      ret %6
  }
}
-/
#guard_msgs in
#eval do IO.println (Func.toString (← IO.ofExcept addFn))

/-! ## Misuse

Emitting where no block is open, or leaving a block open, is an error, and `buildFunc`
fails. -/

/-- The errors `buildFunc` fails with for `body`, as the body of a function of `x`, or none. -/
private def errors (body : Array ValId → PyM Unit Unit) : Array String :=
  match buildFunc (Py.pn "f") #["x"] () body with
  | .ok _ => #[]
  | .error e => e.toArray

/-- A write after `return None`, which has closed the block. -/
private def writeAfterReturn (args : Array ValId) : PyM Unit Unit := do
  let y ← declareLocal "y"
  emitReturnNone
  let _ ← writeCell y args[0]!

example : (buildFunc (Py.pn "f") #["x"] () writeAfterReturn).isOk = false := by decide +kernel

/-- info: #["instruction %6 emitted with no block open"] -/
#guard_msgs in
#eval errors writeAfterReturn

/-- A body that never closes the entry block: the handler would open over it. -/
private def entryLeftOpen (args : Array ValId) : PyM Unit Unit := do
  let y ← declareLocal "y"
  let _ ← writeCell y args[0]!

example : (buildFunc (Py.pn "f") #["x"] () entryLeftOpen).isOk = false := by decide +kernel

/-- info: #["block propagate.0 opened while block entry.0 is open"] -/
#guard_msgs in
#eval errors entryLeftOpen

/-! ## A module of the functions above -/

private def m : Except Errors (Module Py.env Unit) :=
  return { name := Py.pn "test", funcs := #[← f, ← g, ← h, ← k], info := () }

example : Holds Module.WF m := by decide +kernel

end StrataPython.Mantle.PyBuildTest
