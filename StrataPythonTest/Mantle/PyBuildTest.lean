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
meta import StrataPythonTest.Mantle.TestUtil
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
    let _ ← writeCell y (← emitFailing (.str .base "sum") Py.add #v[] #[args[0]!, ← intLit 1])
    emitReturn (← readCell y (stem "y"))

example : Holds (Func.WF ∅) f := by decide +kernel

/-- `f`'s only failing operation reports to the handler `buildFunc` installs. -/
example : Holds (errTargets · = #[lbl "propagate" 0]) f := by decide +kernel

/-- info: module py.f {
  func @py.f(%x.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%x.0 : py.Value):
      %y.0 : py.Value = py.undef("y")
      %y.cell.0 : base.Ref(py.Value) = base.refNew[py.Value](%y.0)
      %int.0 : py.Value = py.intLit(1)
      %sum.0 : py.Value = py.add(%x.0, %int.0) ^propagate.0()
      %set.0 : base.Unit = base.refSet[py.Value](%y.cell.0, %sum.0)
      %y.1 : py.Value = base.refGet[py.Value](%y.cell.0)
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%y.1)
      ret(%ret.0)
    propagate.0(%exc.0 : py.Value):
      %exc.1 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.0)
      ret(%exc.1)
  }
} -/
#guard_msgs in
#eval do IO.println ((← IO.ofExcept f).format {})

/-! ## `def g(): pass`

Falling off the end returns `None`.  The handler is emitted even though nothing reaches
it. -/

private def g : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "g") #[] () fun _ => emitReturnNone

example : Holds (Func.WF ∅) g := by decide +kernel

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
    if takesExc then discard <| startBlockWith except (.str .base "exc") else startBlock except
    emitReturnNone

private def h : Except Errors (Func Py.env Unit) := hWith true

example : Holds (Func.WF ∅) h := by decide +kernel

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
example : Holds (¬ Func.WF ∅ ·) (hWith false) := by decide +kernel

/-! ## `raise x` under a handler with a pre-bound argument

`raiseTo e` passes `e` after the arguments the enclosing handler pre-binds, as an `err`
successor does.  Here the handler `bb.0(c, exc)` pre-binds `c` to `None`. -/

private def r : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "r") #["x"] () fun args => do
    let k ← freshLabel
    let c ← noneLit
    withHandlerTo (Build.goto k #[c]) do jump (← raiseTo args[0]!)
    let pc ← freshVal (.str .base "c")
    let pe ← freshVal (.str .base "exc")
    startBlock k #[pc, pe]
    emitReturn pe.id

example : Holds (Func.WF ∅) r := by decide +kernel

/-- Whether the entry block jumps with two arguments, the second its parameter `x`. -/
private def raisesX (fn : Func Py.env Unit) : Bool :=
  fn.blocks[0]?.any fun b =>
    let .apply _ _ _ _ ks _ := b.term
    let args := ks.flatMap (·.args)
    args.size == 2 && args[1]? == (b.params.map (·.id))[0]?

/-- The entry block jumps to `bb.0` with `None`, then `x`. -/
example : Holds (raisesX · = true) r := by decide +kernel

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

example : Holds (Func.WF ∅) k := by decide +kernel

/-- The cleanup body appears once: block 2, with two instructions. -/
example : Holds (fun k => (k.blocks.map (·.instrs.size))[2]? = some 2) k := by decide +kernel

/-- Eleven blocks: the entry, `finRaise`, `fin`, `superseded` and `disp`; the five successors
of the dispatch, `return` and `raise` taking their payload and fall-through, `break` and
`continue` taking none; and `buildFunc`'s propagating handler. -/
example : Holds (·.blocks.size = 11) k := by decide +kernel

/-- Without `superseded`, the `finally` body fails to the enclosing handler and `fin`
dispatches itself: no `superseded` or `disp` block. -/
example : Holds (fun k => Func.WF ∅ k ∧ k.blocks.size = 9) (kWith false) := by decide +kernel

/-- info: module py.k {
  func @py.k(%x.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%x.0 : py.Value):
      %foo.0 : py.Value = py.attr(%x.0, "foo") ^finRaise.0()
      %comp.0 : py.Completion = py.completionReturn(%foo.0)
      jump ^fin.0(%comp.0)
    finRaise.0(%exc.0 : py.Value):
      %comp.1 : py.Completion = py.completionRaise(%exc.0)
      jump ^fin.0(%comp.1)
    fin.0(%pending.0 : py.Completion):
      %cleanup.0 : py.Value = py.attr(%x.0, "cleanup") ^superseded.0(%pending.0)
      jump ^disp.0(%pending.0)
    superseded.0(%carried.0 : py.Completion, %exc.1 : py.Value):
      %comp.2 : py.Completion = py.completionRaise(%exc.1)
      jump ^disp.0(%comp.2)
    disp.0(%comp.3 : py.Completion):
      py.Completion.case(%comp.3) ^normal.0() ^ret.0() ^raise.0() ^unreachable.0() ^unreachable.1()
    normal.0():
      %none.0 : py.Value = py.noneLit
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.0)
      ret(%ret.0)
    ret.0(%val.0 : py.Value):
      %ret.1 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%val.0)
      ret(%ret.1)
    raise.0(%exc.2 : py.Value):
      %exc.3 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.2)
      ret(%exc.3)
    unreachable.0():
      unreachable
    unreachable.1():
      unreachable
    propagate.0(%exc.4 : py.Value):
      %exc.5 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.4)
      ret(%exc.5)
  }
} -/
#guard_msgs in
#eval do IO.println ((← IO.ofExcept k).format {})

/-! ## A closure

    def outer(x):
      def inner():
        return x          # captures `x` by cell, read late
      return inner

`inner` is a function of the module: `emitFunc` names it, and the checker verifies that
the module defines it.  `mkClosure` pairs the code with the cell holding `x`.  The two
functions are printed as a module. -/

private def inner : Except Errors (Func Py.env Unit) :=
  buildFuncTyped (Py.pn "inner") #[(cellStem "x", Py.cell.ty)] () fun args => do
    emitReturn (← readCell args[0]! (stem "x"))

/-- `outer`, whose closure names `target` and captures the cell holding `x`, or `x` itself if
`byValue`. -/
private def outerWith (target : Name) (byValue : Bool) : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "outer") #["x"] () fun args => do
    let cell ← declareLocal "x"
    let _ ← writeCell cell args[0]!
    emitReturn (← mkClosure (← emitFunc target) #[if byValue then args[0]! else cell])

/-- The module of `outer`, whose closure names `target` and captures `x` as `outerWith` does,
and `inner`. -/
private def closuresWith (target : Name) (byValue : Bool) :
    Except Errors (Module.Raw Py.env Unit) :=
  return { name := Py.pn "closures", funcs := #[← outerWith target byValue, ← inner], info := () }

private def closures : Except Errors (Module.Raw Py.env Unit) := closuresWith (Py.pn "inner") false

-- No name has a `.` inside a segment: `x.cell` is two segments.
#guard match closures with | .ok m => (TestUtil.dottedNames m).isEmpty | .error _ => false

/-- info: module py.closures {
  func @py.outer(%x.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%x.0 : py.Value):
      %x.1 : py.Value = py.undef("x")
      %x.cell.0 : base.Ref(py.Value) = base.refNew[py.Value](%x.1)
      %set.0 : base.Unit = base.refSet[py.Value](%x.cell.0, %x.0)
      %clo.0 : py.Value = py.mkClosure(@py.inner, %x.cell.0)
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%clo.0)
      ret(%ret.0)
    propagate.0(%exc.0 : py.Value):
      %exc.1 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.0)
      ret(%exc.1)
  }
  func @py.inner(%x.cell.0 : base.Ref(py.Value)) -> base.Except(py.Value, py.Value) {
    entry.0(%x.cell.0 : base.Ref(py.Value)):
      %x.0 : py.Value = base.refGet[py.Value](%x.cell.0)
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%x.0)
      ret(%ret.0)
    propagate.0(%exc.0 : py.Value):
      %exc.1 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.0)
      ret(%exc.1)
  }
} -/
#guard_msgs in
#eval do
  match (← IO.ofExcept closures).check with
  | .ok m => IO.println m
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

-- A code pointer to a function the module does not define.
#guard decide (Holds (¬ Module.Raw.WF ·) (closuresWith (Py.pn "nonesuch") false))

-- A closure captures cells, so that a late read sees a late write.  Passing the value
-- instead is ill typed.
#guard decide (Holds (¬ Module.Raw.WF ·) (closuresWith (Py.pn "inner") true))

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
    let n ← loadGlobal "m" "n"
    let sum ← emitFailing (.str .base "sum") Py.add #v[] #[n, ← intLit 1]
    let _ ← writeGlobal "m" "n" sum
    emitReturnNone

example : Holds (Func.WF ∅) globals := by decide +kernel

/-- info: module |py.<module>| {
  func @|py.<module>|() -> base.Except(py.Value, py.Value) {
    entry.0():
      %mod.0 : py.Value = py.importModule("a.b") ^propagate.0()
      %mod.1 : py.Value = py.importModule("a") ^propagate.0()
      %a.cell.0 : base.Ref(py.Value) = py.globalCell("m", "a")
      %set.0 : base.Unit = base.refSet[py.Value](%a.cell.0, %mod.1)
      %mod.2 : py.Value = py.importModule("a.b") ^propagate.0()
      %c.cell.0 : base.Ref(py.Value) = py.globalCell("m", "c")
      %set.1 : base.Unit = base.refSet[py.Value](%c.cell.0, %mod.2)
      %x.0 : py.Value = py.importFrom("a.b", "x") ^propagate.0()
      %y.cell.0 : base.Ref(py.Value) = py.globalCell("m", "y")
      %set.2 : base.Unit = base.refSet[py.Value](%y.cell.0, %x.0)
      %n.5 : py.Value = py.loadGlobal("m", "n") ^propagate.0()
      %int.0 : py.Value = py.intLit(1)
      %sum.0 : py.Value = py.add(%n.5, %int.0) ^propagate.0()
      %n.cell.0 : base.Ref(py.Value) = py.globalCell("m", "n")
      %set.3 : base.Unit = base.refSet[py.Value](%n.cell.0, %sum.0)
      %none.0 : py.Value = py.noneLit
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.0)
      ret(%ret.0)
    propagate.0(%exc.0 : py.Value):
      %exc.1 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.0)
      ret(%exc.1)
  }
} -/
#guard_msgs in
#eval do IO.println ((← IO.ofExcept globals).format {})

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
    emitReturn (← emitFailing (.str .base "sum") Py.add #v[] #[args[0]!, args[0]!])

example : OptHolds (NameSet.of? #[mAdd]) (fun fs => Holds (Func.WF fs) addFn) := by
  decide +kernel

/-- info: module m.add {
  func @m.add(%x.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%x.0 : py.Value):
      %clo.0 : py.Value = py.mkClosure(@m.add)
      %sum.0 : py.Value = py.add(%x.0, %x.0) ^propagate.0()
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%sum.0)
      ret(%ret.0)
    propagate.0(%exc.0 : py.Value):
      %exc.1 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.0)
      ret(%exc.1)
  }
} -/
#guard_msgs in
#eval do IO.println ((← IO.ofExcept addFn).format {})

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

/-! ## `def c(xs, ys): [x + y for x in xs for y in ys]`

Two nested `forEach`s.  Each failure goes to the nearest handler: the outer `forEach`'s to the
function's, the inner one's to the outer region's, and the `add`'s to the inner region's, so no
transfer leaves its region. -/

private def c : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "c") #["xs", "ys"] () fun args => do
    let acc ← emitTotal (.str .base "acc") Py.mkList #v[] #[]
    forEach args[0]! fun x => do
      forEach args[1]! fun y => do
        let s ← emitFailing (.str .base "s") Py.add #v[] #[x, y]
        let _ ← emitEffect (.str .base "append") Py.listAppend #v[] #[acc, s]
    emitReturn acc

example : Holds (Func.WF ∅) c := by decide +kernel

/-- Ids follow the printed order: the `forEach` result before its region's values. -/
example : Holds Func.Canonical c := by decide +kernel

/-- The `err` successors of `bs`' instructions, regions included, in order. -/
private partial def errTargetsDeep (bs : Array (Block Py.env Unit)) : List Label :=
  bs.toList.flatMap fun b => b.instrs.toList.flatMap fun
    | .apply _ _ _ _ _ ks rs =>
      ks.toList.map (·.target) ++ rs.toList.flatMap (errTargetsDeep ·.blocks)
    | _ => []

-- The handlers `c`'s failures go to, as the docstring above says.
#guard match c with
  | .ok fn =>
    errTargetsDeep fn.blocks == [lbl "propagate" 0, lbl "propagate" 1, lbl "propagate" 2]
  | .error _ => false

/-- A body that ends closed, raising to the region's handler, is well formed too. -/
private def cClosed : Except Errors (Func Py.env Unit) :=
  buildFunc (Py.pn "c") #["xs"] () fun args => do
    forEach args[0]! fun x => do jump (← raiseTo x)
    emitReturnNone

example : Holds (Func.WF ∅) cClosed := by decide +kernel

/-- Ids follow the printed order: the `forEach` result before its region's values. -/
example : Holds Func.Canonical cClosed := by decide +kernel

/-! ## A module of the functions above -/

private def m : Except Errors (Module.Raw Py.env Unit) :=
  return { name := Py.pn "test", funcs := #[← f, ← g, ← h, ← k, ← c], info := () }

#guard match m with | .ok m => (TestUtil.dottedNames m).isEmpty | .error _ => false

end StrataPython.Mantle.PyBuildTest
