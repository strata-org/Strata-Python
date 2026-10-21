/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.DDM
public import StrataMantle.WF
public import StrataPython.Mantle.Build
import StrataMantle.Env.WF
-- The builder, the checker and the printer run as compiled code below.
meta import StrataMantle.DDM
meta import StrataMantle.WF
meta import StrataPython.Mantle.Build
meta import StrataPythonTest.Mantle.TestUtil
meta import StrataMantle.Env.WF

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

open Strata.Mantle.Build (FailedFunc)

open StrataPython.Mantle.PyBuild

/-- What `buildFunc` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc Py.env Unit Unit) {fn : Func Py.env Unit // fn.WF}

/-- The build failed because its function is not well formed, not by a misuse. -/
private def rejected (b : Built) : Bool :=
  match b with
  | .error e => e.misuses.isEmpty
  | .ok _ => false

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

private def f : Built :=
  buildFunc (Py.pn "f") #["x"] () fun args => do
    let y ← declareLocal "y"
    let _ ← writeCell y (← emitFailing (.str .base "sum") Py.add #[args[0]!, ← intLit 1])
    emitReturn (← readCell y (stem "y"))

#guard f.isOk

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
#eval do IO.println ((← IO.ofExcept f).1.format {})

/-! ## `def g(): pass`

Falling off the end returns `None`.  Nothing can fail, so nothing reaches the handler, and the
builder drops it: one block is left. -/

private def g : Built :=
  buildFunc (Py.pn "g") #[] () fun _ => emitReturnNone

#guard g.isOk

#guard (g.toOption.map (·.1.blocks.size)) == some 1

/-! ## `def h(x):` / `try: return x.foo` / `except: return None`

Inside `withHandler`, a failing operation reports to the `except` block instead of to the
caller.  The exception arrives as that block's parameter, supplied by the `err`
successor. -/

/-- `h`, whose `except` block declares the exception if `takesExc`. -/
private def hWith (takesExc : Bool) : Built :=
  buildFunc (Py.pn "h") #["x"] () fun args => do
    let except ← freshLabel
    withHandler except do emitReturn (← getAttr args[0]! "foo")
    -- `except:` — the exception is bound and ignored.
    if takesExc then discard <| startBlockWith except (.str .base "exc") else startBlock except
    emitReturnNone

private def h : Built := hWith true

#guard h.isOk

-- The blocks in the order they were finished: the body and the `except` block.  The builder
-- drops the propagating handler `buildFunc` installs: nothing outside the `try` can fail, so
-- nothing reaches it.
#guard (h.toOption.map (·.1.blocks.map (·.label))) == some #[lbl "entry" 0, lbl "bb" 0]

-- The `attr` failure goes to the `except` block, `bb.0`, not to the caller's handler.
#guard (h.toOption.map (errTargets ·.1)) == some #[lbl "bb" 0]

-- A handler must take the exception: `err` supplies it to its target, so an `except`
-- block that declares no parameter is ill formed.
#guard rejected (hWith false)

/-! ## `raise x` under a handler with a pre-bound argument

`raiseTo e` passes `e` after the arguments the enclosing handler pre-binds, as an `err`
successor does.  Here the handler `bb.0(c, exc)` pre-binds `c` to `None`. -/

private def r : Built :=
  buildFunc (Py.pn "r") #["x"] () fun args => do
    let k ← freshLabel
    let c ← noneLit
    withHandlerTo (Build.goto k #[c]) do jump (← raiseTo args[0]!)
    let pc ← freshVal (.str .base "c")
    let pe ← freshVal (.str .base "exc")
    startBlock k #[pc, pe]
    emitReturn pe.id

#guard r.isOk

/-- Whether the entry block jumps with two arguments, the second its parameter `x`. -/
private def raisesX (fn : Func Py.env Unit) : Bool :=
  fn.blocks[0]?.any fun b =>
    let .apply _ _ _ _ ks _ := b.term
    let args := ks.flatMap (·.args)
    args.size == 2 && args[1]? == (b.params.map (·.id))[0]?

-- The entry block jumps to `bb.0` with `None`, then `x`.
#guard r.toOption.any (raisesX ·.1)

/-! ## `try` / `finally`, by completion

    def k(x):
      try:
        return x.foo
      finally:
        x.cleanup

`tryFinally` emits the `finally` body once, in `fin.0`, reached from both exits of the `try`
with how it finished: `return` with the value, or `raise` from `finRaise.0`.  The body runs
after `pushPending`, so a raise reaching it makes its exception the one being handled.  It
ends by restoring the exception handled before, then one `py.Completion.case` with a
successor per constructor, each binding its own payload, so `val` exists only on the path
where the completion is a `return`.  A failure in the cleanup goes to `superseded.0`, which
restores the exception handled before and raises to the enclosing handler, so it supersedes
what was pending. -/

private def k : Built :=
  buildFunc (Py.pn "k") #["x"] () fun args => do
    let #[x] := args | return
    discard <| tryFinally
      (fun fin => do jump (Build.goto fin #[← compReturn (← getAttr x "foo")]))
      (fun _ => discard <| getAttr x "cleanup")
      (pure { normal := .block "normal" fun _ => emitReturnNone
              «return» := .block "ret" emitReturn
              raise := .block "raise" emitPropagate })

#guard k.isOk

-- The cleanup body appears once: block 2, between `pushPending` and `popExcept`, then the
-- dispatch.
#guard (k.toOption.map fun k => (k.1.blocks.map (·.instrs.size))[2]?) == some (some 4)

-- Ten blocks: the entry, `finRaise` and `fin`; the five successors of the dispatch,
-- `return` and `raise` taking their payload and fall-through, `break` and `continue` taking
-- none; `superseded`; and `buildFunc`'s propagating handler.
#guard (k.toOption.map (·.1.blocks.size)) == some 10

/-- A `finally` body that always leaves by itself, here by returning, emits no dispatch: only
the entry, `finRaise` and `fin`.  Nothing in it can fail, so nothing reaches `superseded` or the
propagating handler, and the builder drops them. -/
private def kReturns : Built :=
  buildFunc (Py.pn "k") #["x"] () fun args => do
    let #[x] := args | return
    discard <| tryFinally
      (fun _ => discard <| getAttr x "foo")
      (fun prev => do
        discard <| emitEffect (.str .base "pop") Py.popExcept #[prev]
        emitReturnNone)
      (pure { normal := .unreachable, «return» := .unreachable, raise := .unreachable })

#guard kReturns.isOk

#guard (kReturns.toOption.map (·.1.blocks.size)) == some 3

/-- Under a handler `bb.0(c, exc)` that pre-binds `c`, a failure in the cleanup reaches
`superseded.0`, which raises to `bb.0` with `c`, then the failure. -/
private def kBound : Built :=
  buildFunc (Py.pn "k") #["x"] () fun args => do
    let #[x] := args | return
    let h ← freshLabel
    let c ← noneLit
    withHandlerTo (Build.goto h #[c]) do
      discard <| tryFinally (fun _ => pure ()) (fun _ => discard <| getAttr x "cleanup")
        (pure { normal := .block "normal" fun _ => emitReturnNone
                «return» := .unreachable
                raise := .block "raise" fun e => jump (Build.goto h #[c, e]) })
    let pc ← freshVal (.str .base "c")
    let pe ← freshVal (.str .base "exc")
    startBlock h #[pc, pe]
    emitReturn pe.id

/-- Whether `superseded.0` jumps to `bb.0` with two arguments, the second its parameter. -/
private def supersededPassesExc (fn : Func Py.env Unit) : Bool :=
  fn.blocks.any fun b =>
    let .apply _ _ _ _ ks _ := b.term
    let args := ks.flatMap (·.args)
    b.label == lbl "superseded" 0 && ks.map (·.target) == #[lbl "bb" 0] &&
      args.size == 2 && args[1]? == (b.params.map (·.id))[0]?

#guard kBound.isOk

#guard kBound.toOption.any (supersededPassesExc ·.1)

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
      %prev.0 : py.Value = py.pushPending(%pending.0)
      %cleanup.0 : py.Value = py.attr(%x.0, "cleanup") ^superseded.0()
      %pop.0 : base.Unit = py.popExcept(%prev.0)
      py.Completion.case(%pending.0) ^normal.0() ^ret.0() ^raise.0() ^unreachable.0() ^unreachable.1()
    normal.0():
      %none.0 : py.Value = py.noneLit
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.0)
      ret(%ret.0)
    ret.0(%val.0 : py.Value):
      %ret.1 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%val.0)
      ret(%ret.1)
    raise.0(%exc.1 : py.Value):
      %exc.2 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.1)
      ret(%exc.2)
    unreachable.0():
      unreachable
    unreachable.1():
      unreachable
    superseded.0(%exc.3 : py.Value):
      %pop.1 : base.Unit = py.popExcept(%prev.0)
      jump ^propagate.0(%exc.3)
    propagate.0(%exc.4 : py.Value):
      %exc.5 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.4)
      ret(%exc.5)
  }
} -/
#guard_msgs in
#eval do IO.println ((← IO.ofExcept k).1.format {})

/-! ## A closure

    def outer(x):
      def inner():
        return x          # captures `x` by cell, read late
      return inner

`inner` is a function of the module: `emitFunc` names it, and the module's check verifies
that the module defines it.  `mkClosure` pairs the code with the cell holding `x`.  The two
functions are printed as a module. -/

private def inner : Built :=
  buildFuncTyped (Py.pn "inner") #[(cellStem "x", Py.cell.ty)] () fun args => do
    emitReturn (← readCell args[0]! (stem "x"))

/-- `outer`, whose closure names `target` and captures the cell holding `x`, or `x` itself if
`byValue`. -/
private def outerWith (target : Name) (byValue : Bool) : Built :=
  buildFunc (Py.pn "outer") #["x"] () fun args => do
    let cell ← declareLocal "x"
    let _ ← writeCell cell args[0]!
    emitReturn (← mkClosure (← emitFunc target) #[if byValue then args[0]! else cell])

/-- The module of `outer`, whose closure names `target` and captures `x` as `outerWith` does,
and `inner`. -/
private def closuresWith (target : Name) (byValue : Bool) :
    Except (FailedFunc Py.env Unit Unit) (Module.Raw Py.env Unit) :=
  return { name := Py.pn "closures", funcs := #[(← outerWith target byValue).1, (← inner).1],
           info := () }

private def closures : Except (FailedFunc Py.env Unit Unit) (Module.Raw Py.env Unit) :=
  closuresWith (Py.pn "inner") false

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
  }
  func @py.inner(%x.cell.0 : base.Ref(py.Value)) -> base.Except(py.Value, py.Value) {
    entry.0(%x.cell.0 : base.Ref(py.Value)):
      %x.0 : py.Value = base.refGet[py.Value](%x.cell.0)
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%x.0)
      ret(%ret.0)
  }
} -/
#guard_msgs in
#eval do
  match (← IO.ofExcept closures).check with
  | .ok m => IO.println m
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

/-! A code pointer to a function the module does not define: each function is well formed on
its own, and the module names the one with the dangling reference. -/

/-- info: not well formed: #[py.outer] -/
#guard_msgs in
#eval do
  match (← IO.ofExcept (closuresWith (Py.pn "nonesuch") false)).check with
  | .ok _ => IO.println "well formed"
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

-- Assembled from the checked functions, the module is rejected the same way.
#guard match outerWith (Py.pn "nonesuch") false, inner with
  | .ok o, .ok i => match Module.ofChecked (Py.pn "closures") #[o, i] () with
    | .error bad => bad == #[Py.pn "outer"]
    | .ok _ => false
  | _, _ => false

-- A closure captures cells, so that a late read sees a late write.  Passing the value
-- instead is ill typed.
#guard rejected (outerWith (Py.pn "inner") true)

/-! ## Globals and imports

    import a.b
    import a.b as c
    from a.b import x as y
    n = n + 1

A module body, so every name is a global of module `m`.  `import a.b` imports `a.b` and binds
the package `a`; the other two bind what they import. -/

private def globals : Built :=
  buildFunc (Py.pn "<module>") #[] () fun _ => do
    let _ ← importModule "a.b"
    let _ ← writeGlobal "m" "a" (← importModule "a")
    let _ ← writeGlobal "m" "c" (← importModule "a.b")
    let _ ← writeGlobal "m" "y" (← importFrom "a.b" "x")
    let n ← loadGlobal "m" "n"
    let sum ← emitFailing (.str .base "sum") Py.add #[n, ← intLit 1]
    let _ ← writeGlobal "m" "n" sum
    emitReturnNone

#guard globals.isOk

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
#eval do IO.println ((← IO.ofExcept globals).1.format {})

/-! ## A function named like an operation

    def add(x):          # in module `m`
      add              # the function itself
      return x + x

The function `m.add` prints as `@m.add`, in its header and in the constant that refers to it,
so neither reads as the operation `py.add`. -/

private def mAdd : Name := .str (.str .base "m") "add"

private def addFn : Built :=
  buildFunc mAdd #["x"] () fun args => do
    let _ ← funcValue mAdd
    emitReturn (← emitFailing (.str .base "sum") Py.add #[args[0]!, args[0]!])

-- It refers to itself, so it is a module on its own.
#guard addFn.toOption.any fun f => (Module.ofChecked mAdd #[f] ()).isOk

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
#eval do IO.println ((← IO.ofExcept addFn).1.format {})

/-! ## Misuse

Emitting where no block is open, or leaving a block open, is an error, and `buildFunc`
fails. -/

/-- The errors `buildFunc` fails with for `body`, as the body of a function of `x`, or none. -/
private def errors (body : Array ValId → PyM Unit Unit) : Array String :=
  match buildFunc (Py.pn "f") #["x"] () body with
  | .ok _ => #[]
  | .error e => e.misuses

/-- A write after `return None`, which has closed the block. -/
private def writeAfterReturn (args : Array ValId) : PyM Unit Unit := do
  let y ← declareLocal "y"
  emitReturnNone
  let _ ← writeCell y args[0]!

/-- info: #["instruction %6 emitted with no block open"] -/
#guard_msgs in
#eval errors writeAfterReturn

/-- A body that never closes the entry block: the handler would open over it. -/
private def entryLeftOpen (args : Array ValId) : PyM Unit Unit := do
  let y ← declareLocal "y"
  let _ ← writeCell y args[0]!

/-- info: #["block propagate.0 opened while block entry.0 is open"] -/
#guard_msgs in
#eval errors entryLeftOpen

/-! ## `def c(xs, ys): [x + y for x in xs for y in ys]`

Two nested `forEach`s.  Each failure goes to the nearest handler: the outer `forEach`'s to the
function's, the inner one's to the outer region's, and the `add`'s to the inner region's, so no
transfer leaves its region. -/

private def c : Built :=
  buildFunc (Py.pn "c") #["xs", "ys"] () fun args => do
    let acc ← emitTotal (.str .base "acc") Py.mkList #[]
    forEach args[0]! fun x => do
      forEach args[1]! fun y => do
        let s ← emitFailing (.str .base "s") Py.add #[x, y]
        let _ ← emitEffect (.str .base "append") Py.listAppend #[acc, s]
    emitReturn acc

#guard c.isOk

-- Ids follow the printed order: the `forEach` result before its region's values.
#guard c.toOption.any (decide ·.1.Canonical)

/-- The `err` successors of `bs`' instructions, regions included, in order. -/
private partial def errTargetsDeep (bs : Array (Block Py.env Unit)) : List Label :=
  bs.toList.flatMap fun b => b.instrs.toList.flatMap fun
    | .apply _ _ _ _ _ ks rs =>
      ks.toList.map (·.target) ++ rs.toList.flatMap (errTargetsDeep ·.blocks)
    | _ => []

-- The handlers `c`'s failures go to, as the docstring above says.
#guard match c with
  | .ok fn =>
    errTargetsDeep fn.1.blocks == [lbl "propagate" 0, lbl "propagate" 1, lbl "propagate" 2]
  | .error _ => false

/-- A body that ends closed, raising to the region's handler, is well formed too. -/
private def cClosed : Built :=
  buildFunc (Py.pn "c") #["xs"] () fun args => do
    forEach args[0]! fun x => do jump (← raiseTo x)
    emitReturnNone

#guard cClosed.isOk

-- Ids follow the printed order: the `forEach` result before its region's values.
#guard cClosed.toOption.any (decide ·.1.Canonical)

/-! ## A module of the functions above -/

private def m : Except (FailedFunc Py.env Unit Unit) (Module.Raw Py.env Unit) :=
  return { name := Py.pn "test", funcs := #[(← f).1, (← g).1, (← h).1, (← k).1, (← c).1],
           info := () }

#guard match m with | .ok m => (TestUtil.dottedNames m).isEmpty | .error _ => false

/-! ## Blocks the entry does not reach

The builder drops them.  Two shapes the translator's `try` lowering emits: a clause's `clear`
block that nothing enters, jumping to the `unwind` block a reachable clause test also fails to;
and a `catch` block that nothing enters, using a value the entry defines after its first failing
instruction.  Under the flat parent the first would pull `unwind` above `catch`, where `%prev.0`
is defined, and the second would not see `%ns.0`. -/

/-- `except KeyError as e: continue` in a function: `clear.0` has no predecessor. -/
private def leave : Except (FailedFunc Py.env Unit Unit) {fn : Func Py.env Unit // fn.WF} :=
  buildFuncTyped (Py.pn "leave") #[(stem "f", Py.Value.ty)] () fun ps => do
    let some f := ps[0]? | return
    let catchL ← freshLabel "catch"
    let clearL ← freshLabel "clear"
    let unwindL ← freshLabel "unwind"
    let join ← freshLabel "join"
    let outer ← handler
    withHandler catchL do
      let _ ← emitFailing (.str .base "call") Py.getItem #[f, f]
    jump (Build.goto join)
    let exc ← startBlockWith catchL (.str .base "exc")
    let prev ← emitTotal (.str .base "prev") Py.mkTuple #[exc]
    withHandler unwindL do
      let _ ← emitFailing (.str .base "match") Py.getItem #[exc, exc]
    jump (Build.goto join)
    let x ← startBlockWith clearL (.str .base "exc")
    jump { Build.goto unwindL with args := #[x] }
    let y ← startBlockWith unwindL (.str .base "exc")
    let _ ← emitTotal (.str .base "pop") Py.mkTuple #[prev]
    jump { outer with args := outer.args.push y }
    startBlock join
    emitReturnNone

/-- info: module py.leave {
  func @py.leave(%f.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%f.0 : py.Value):
      %call.0 : py.Value = py.getItem(%f.0, %f.0) ^catch.0()
      jump ^join.0()
    catch.0(%exc.0 : py.Value):
      %prev.0 : py.Value = py.mkTuple(%exc.0)
      %match.0 : py.Value = py.getItem(%exc.0, %exc.0) ^unwind.0()
      jump ^join.0()
    unwind.0(%exc.2 : py.Value):
      %pop.0 : py.Value = py.mkTuple(%prev.0)
      jump ^propagate.0(%exc.2)
    join.0():
      %none.0 : py.Value = py.noneLit
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.0)
      ret(%ret.0)
    propagate.0(%exc.3 : py.Value):
      %exc.4 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.3)
      ret(%exc.4)
  }
} -/
#guard_msgs in
#eval match leave with
  | .ok f => IO.println (f.1.format {})
  | .error e => IO.println (toString e)

/-- `try: pass` / `except Exception: ...` in a class body: `catch.0` has no predecessor. -/
private def classBody : Except (FailedFunc Py.env Unit Unit) {fn : Func Py.env Unit // fn.WF} :=
  buildFuncTyped (Py.pn "C_body") #[(stem "args", Py.Value.ty)] () fun ps => do
    let some args := ps[0]? | return
    let ns ← emitFailing (.str .base "ns") Py.getItem #[args, ← intLit 0]
    let catchL ← freshLabel "catch"
    let join ← freshLabel "join"
    jump (Build.goto join)
    let exc ← startBlockWith catchL (.str .base "exc")
    let _ ← emitFailing (.str .base "Exception") Py.getItem #[ns, exc]
    jump (Build.goto join)
    startBlock join
    emitReturnNone

/-- info: module py.C_body {
  func @py.C_body(%args.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%args.0 : py.Value):
      %int.0 : py.Value = py.intLit(0)
      %ns.0 : py.Value = py.getItem(%args.0, %int.0) ^propagate.0()
      jump ^join.0()
    join.0():
      %none.0 : py.Value = py.noneLit
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.0)
      ret(%ret.0)
    propagate.0(%exc.1 : py.Value):
      %exc.2 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.1)
      ret(%exc.2)
  }
} -/
#guard_msgs in
#eval match classBody with
  | .ok f => IO.println (f.1.format {})
  | .error e => IO.println (toString e)

end StrataPython.Mantle.PyBuildTest
