/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Build.Typed
public import StrataDyn.DDM
import StrataDyn.Env.WF
import StrataDyn.DSL
-- The builder and the printer run as compiled code below.
meta import StrataDyn.Build.Typed
meta import StrataDyn.DDM
meta import StrataDyn.Env.WF
meta import Lean.Elab.Command

set_option autoImplicit false

/-!
# Values and blocks named after their binders

`let% x ← e`, where `Strata.Dyn.Emit` is open, names the value or block `e` returns after
`x`, if `e` made it and nothing named it.  Each case is tested here by the function it prints: a
nested emit, an emit in the arms of an `if` and a `match`, a helper that emits several values, a
binder that names nothing, a pattern, an explicit name, a region, and blocks.  `let%` in a
monad that does not emit is rejected beside its accepted twin.
-/

namespace Strata.Dyn.LetNamedTest

open Strata.Dyn.Emit

/-- A child of `Base` with a region. -/
public environment Ln extends Base where
  namespace ln
  open base
  /-- A region returning its result. -/
  insn block [a] (&body : a) : a
  end ln

/-- The environment the functions below are built in. -/
abbrev W := Ln.env

/-- What `build` gives. -/
abbrev Built := Except (Build.FailedFunc W Unit Unit) {fn : Func W Unit // fn.WF}

/-- The name `s`. -/
def n (s : String) : Name := .str .base s

/-- The module `m` of `f`, printed, or why it was not built. -/
private def showMod (f : Built) : String :=
  match f with
  | .error e => toString e
  | .ok f => match Module.ofChecked (.str .base "m") #[f] () with
    | .ok m => toString m
    | .error _ => "the module is not well formed"

/-! ## Which value takes the name

The value the statement returns takes the binder's name.  A value `e` emits on the way keeps its
instruction's name, and so does one `e` returns without emitting it. -/

/-- Read `cell`, then write `v` to it, and return what was read.  The caller's binder names the
result. -/
private def swapIn {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
    [base ≼ env] {t : TypeExpr env} (cell : Val env (Base.Ref t)) (v : Val env t) :
    m (Val env t) := do
  let old ← Base.refGet cell
  let _ ← Base.refSet cell v
  return old

/-- `swapIn`, whose own `let%` names its result: the innermost name wins. -/
private def swapNamed {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
    [base ≼ env] {t : TypeExpr env} (cell : Val env (Base.Ref t)) (v : Val env t) :
    m (Val env t) := do
  let% prev ← Base.refGet cell
  let _ ← Base.refSet cell v
  return prev

private def f (c : Bool) (k : Nat) : Built :=
  Build.build (n "f") Base.Int () do
    let _ ← Build.startFreshBlock (base := "entry")
    let zero ← int (n "k") 0
    let% cell ← Base.refNew zero
    -- Nested: the inner value is emitted before the statement runs.
    let% r ← Base.refGet (← Base.refNew zero)
    -- The arms of an `if` and a `match`: the value returned takes the name, a temporary does not.
    let% z ← if c then Base.refNew r else do
      let w ← Base.refGet cell
      Base.refNew w
    let% y ← match k with
      | 0 => Base.refGet z
      | _ => do Base.refGet (← Base.refNew (← Base.refGet z))
    -- Helpers: the binder names the result, unless the helper named it.
    let% old ← swapIn cell y
    let% older ← swapNamed cell old
    -- No name: the instruction's.
    let plain ← Base.refNew older
    let _ ← Base.refNew older
    -- An explicit name overrides the binder.
    let% given ← Base.refGet plain (result := n "read")
    -- Returned, not emitted: `given` keeps its name.
    let% same ← pure given
    ret same

/-- info: module m {
  func @f() -> base.Int {
    entry.0():
      %cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %refNew.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %r.0 : base.Int = base.refGet[base.Int](%refNew.0)
      %z.0 : base.Ref(base.Int) = base.refNew[base.Int](%r.0)
      %y.0 : base.Int = base.refGet[base.Int](%z.0)
      %old.0 : base.Int = base.refGet[base.Int](%cell.0)
      %refSet.0 : base.Unit = base.refSet[base.Int](%cell.0, %y.0)
      %prev.0 : base.Int = base.refGet[base.Int](%cell.0)
      %refSet.1 : base.Unit = base.refSet[base.Int](%cell.0, %old.0)
      %refNew.1 : base.Ref(base.Int) = base.refNew[base.Int](%prev.0)
      %refNew.2 : base.Ref(base.Int) = base.refNew[base.Int](%prev.0)
      %read.0 : base.Int = base.refGet[base.Int](%refNew.1)
      ret(%read.0)
  }
} -/
#guard_msgs in
#eval IO.println (showMod (f true 0))

-- The other arms: the temporaries keep their instructions' names.
/-- info: module m {
  func @f() -> base.Int {
    entry.0():
      %cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %refNew.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %r.0 : base.Int = base.refGet[base.Int](%refNew.0)
      %refGet.0 : base.Int = base.refGet[base.Int](%cell.0)
      %z.0 : base.Ref(base.Int) = base.refNew[base.Int](%refGet.0)
      %refGet.1 : base.Int = base.refGet[base.Int](%z.0)
      %refNew.1 : base.Ref(base.Int) = base.refNew[base.Int](%refGet.1)
      %y.0 : base.Int = base.refGet[base.Int](%refNew.1)
      %old.0 : base.Int = base.refGet[base.Int](%cell.0)
      %refSet.0 : base.Unit = base.refSet[base.Int](%cell.0, %y.0)
      %prev.0 : base.Int = base.refGet[base.Int](%cell.0)
      %refSet.1 : base.Unit = base.refSet[base.Int](%cell.0, %old.0)
      %refNew.2 : base.Ref(base.Int) = base.refNew[base.Int](%prev.0)
      %refNew.3 : base.Ref(base.Int) = base.refNew[base.Int](%prev.0)
      %read.0 : base.Int = base.refGet[base.Int](%refNew.2)
      ret(%read.0)
  }
} -/
#guard_msgs in
#eval IO.println (showMod (f false 1))

/-! ## `mut`, a type, a region and a loop

`let% mut` and `let% x : T` are `let`'s.  A region's result takes the binder's name, and the
values its body emits keep their own.  A reassignment is plain Lean: it names nothing. -/

private def g : Built :=
  Build.build (n "g") Base.Int () do
    let _ ← Build.startFreshBlock (base := "entry")
    let zero ← int (n "k") 0
    let% mut cell : Val W (Base.Ref Base.Int) ← Base.refNew zero
    for _ in [0:2] do
      cell ← Base.refNew (← Base.refGet cell)
    let% total ← Ln.block (fun exit => do
      let% inside ← Base.refGet cell
      Base.jump (exit.bind inside))
    ret total

/-- info: module m {
  func @g() -> base.Int {
    entry.0():
      %cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %refGet.0 : base.Int = base.refGet[base.Int](%cell.0)
      %refNew.0 : base.Ref(base.Int) = base.refNew[base.Int](%refGet.0)
      %refGet.1 : base.Int = base.refGet[base.Int](%refNew.0)
      %refNew.1 : base.Ref(base.Int) = base.refNew[base.Int](%refGet.1)
      %total.0 : base.Int = ln.block[base.Int] {
        body.0():
          %inside.0 : base.Int = base.refGet[base.Int](%refNew.1)
          ret(%inside.0)
      }
      ret(%total.0)
  }
} -/
#guard_msgs in
#eval IO.println (showMod g)

/-! ## Patterns

`let%` takes an identifier.  A pattern is bound with plain `let`, and names nothing. -/

/-- Two fresh cells of `v`. -/
private def twoCells {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
    [base ≼ env] {t : TypeExpr env} (v : Val env t) :
    m (Val env (Base.Ref t) × Val env (Base.Ref t)) := do
  return (← Base.refNew v, ← Base.refNew v)

private def p : Built :=
  Build.build (n "p") Base.Int () do
    let _ ← Build.startFreshBlock (base := "entry")
    let (a, b) ← twoCells (← int (n "k") 0)
    let% x ← Base.refGet a
    let _ ← Base.refGet b
    ret x

/-- info: module m {
  func @p() -> base.Int {
    entry.0():
      %refNew.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %refNew.1 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %x.0 : base.Int = base.refGet[base.Int](%refNew.0)
      %refGet.0 : base.Int = base.refGet[base.Int](%refNew.1)
      ret(%x.0)
  }
} -/
#guard_msgs in
#eval IO.println (showMod p)

/-- info: <input>:1:5: expected identifier -/
#guard_msgs in
open Lean Elab Command in
#eval show CommandElabM Unit from do
  match Parser.runParserCategory (← getEnv) `doElem "let% (a, b) ← twoCells v" with
  | .ok _ => logInfo "parsed"
  | .error e => logInfo e
/-- info: parsed -/
#guard_msgs in
open Lean Elab Command in
#eval show CommandElabM Unit from do
  match Parser.runParserCategory (← getEnv) `doElem "let% a ← twoCells v" with
  | .ok _ => logInfo "parsed"
  | .error e => logInfo e

/-! ## Blocks

`let%` labels a block from `freshLabel` after its binder, unless `freshLabel` is given a base,
and names `startBlock₁`'s parameter, unless it is given a stem.  A block the statement returns
without making it keeps its label.  Labels are numbered when the function is finished, so the
renamed blocks leave no gap among the `bb`s. -/

/-- A fresh block taking an `Int`, labelled by its caller's binder. -/
private def intBlock {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
    [base ≼ env] : m (BlockRef env [Base.Int]) :=
  freshLabel [Base.Int]

private def blocks : Built :=
  Build.build (n "blocks") Base.Int () do
    let% ok ← freshLabel [Base.Int]
    let% given ← freshLabel [Base.Int] "explicit"
    let% made ← intBlock
    let% same ← pure ok
    let plain ← freshLabel [Base.Int]
    let first := ok
    let% ok ← freshLabel [Base.Int]
    let _ ← Build.startFreshBlock (base := "entry")
    Base.jump (same.goto.bind (← int (n "k") 0))
    let% x ← startBlock₁ first
    Base.jump (given.goto.bind x)
    let y ← startBlock₁ given
    Base.jump (made.goto.bind y)
    let% z ← startBlock₁ made (n "named")
    Base.jump (ok.goto.bind z)
    let% w ← startBlock₁ ok
    Base.jump (plain.goto.bind w)
    ret (← startBlock₁ plain)

/-- info: module m {
  func @blocks() -> base.Int {
    entry.0():
      jump ^ok.0(0)
    ok.0(%x.0 : base.Int):
      jump ^explicit.0(%x.0)
    explicit.0(%v.0 : base.Int):
      jump ^made.0(%v.0)
    made.0(%named.0 : base.Int):
      jump ^ok.1(%named.0)
    ok.1(%w.0 : base.Int):
      jump ^bb.0(%w.0)
    bb.0(%v.1 : base.Int):
      ret(%v.1)
  }
} -/
#guard_msgs in
#eval IO.println (showMod blocks)

/-! A misuse names a block by the label the finished function gives it: `ok`, allocated `bb.0`,
is `ok.0` in the message, as in the function. -/

/-- A function whose block `ok` is left open, unless `close`. -/
private def leftOpen (close : Bool) : Built :=
  Build.build (n "leftOpen") Base.Int () do
    let _ ← Build.startFreshBlock (base := "entry")
    let% ok ← freshLabel [Base.Int]
    Base.jump (ok.goto.bind (← int (n "k") 0))
    let x ← startBlock₁ ok
    if close then ret x

/-- info: the function ends with block ok.0 open -/
#guard_msgs in
#eval IO.println (showMod (leftOpen false))
/-- info: module m {
  func @leftOpen() -> base.Int {
    entry.0():
      jump ^ok.0(0)
    ok.0(%v.0 : base.Int):
      ret(%v.0)
  }
} -/
#guard_msgs in
#eval IO.println (showMod (leftOpen true))

/-! ## Only in a builder

`let%` names a value of the function being emitted, so it needs a monad that emits one.  A
monad that does not is an error at the statement. -/

/--
error: failed to synthesize instance of type class
  MonadBuild
-/
#guard_msgs (substring := true) in
example (v : Val W Base.Int) : Id (Val W Base.Int) := do
  let% x ← pure v
  return x
example (v : Val W Base.Int) : BuildM W Unit (Val W Base.Int) := do
  let% x ← pure v
  return x

/-! A result that is neither a value nor a block is bound, and names nothing. -/

example : BuildM W Unit Nat := do
  let% x ← pure 5
  let% bs ← pure #[(← freshLabel [] : BlockRef W [])]
  return x + bs.size

end Strata.Dyn.LetNamedTest
