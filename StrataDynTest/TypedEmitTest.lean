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
meta import Lean.DocString

set_option autoImplicit false

/-!
# Typed emitters

Each instruction `o` has an emitter under its own name, `o`, whose Lean type is its signature
over type expressions.  Each shape is tested here: a generic instruction, a variadic, a spread, a
terminal instruction with successors, a spread payload and regions, in a child of `Base` and in
its own child.  Lean infers the type arguments by unification and rejects an ill-typed emit; each
rejection is beside its accepted twin.  The functions built still pass `Build.run`'s check.
`TypedEmitNamesTest` tests the names an emitter binds and generates, and `LetNamedTest` the
names `let%` gives values.
-/

/-- `vals[` is a token only where `Strata.Dyn` is open, so here a local named `vals` is
indexed as usual; below, in the namespace, `vals[…]` is a spread. -/
private def firstOf (vals : Array Nat) : Option Nat := vals[0]?

#guard firstOf #[3, 4] = some 3

namespace Strata.Dyn.TypedEmitTest

open Strata.Dyn.Emit

/-- A child of `Base` with an instruction of every shape. -/
public environment Te extends Base where
  namespace te
  open base
  type Value
  type IntList
  abbrev IntRef := Ref Int
  abbrev raising (a) := Except Value a
  abbrev PairRef (a) := Ref (Except a Int)
  /-- Generic: one of two values. -/
  insn pick [a] (cond : Bool) (x y : a) : a
  /-- Variadic: a sequence of its operands. -/
  insn seq [a] (*xs : a) : Sequence a
  /-- A result nesting one application of a parameter in another. -/
  insn box [a] (x : a) : Ref (Sequence a)
  /-- A raising call through a typed code pointer: a spread and a successor. -/
  insn invoke [(as : list) r] (f : Fn as r) (*args : as) (^err (exc : Value)) : r
  /-- Regions, returning their result. -/
  insn «if» [a] (cond : Bool) (&«then» &«else» : a) : a
  /-- A region with a parameter, leaving with a `raising Unit`. -/
  insn forEach (n : Int) (&body (i : Int) : raising Unit) (^err (exc : Value)) : Unit
  /-- Terminal, with a spread payload. -/
  terminal insn unpack [(as : list)] (f : Fn as Int) (^k (*xs : as))
  /-- Terminal, with a region. -/
  terminal insn guard [a] (&body : a) (^k (v : a))
  /-- A region whose parameter applies a constructor to a type parameter. -/
  insn withRef [a] (init : a) (&body (r : Ref a) : Unit) : Unit
  /-- A region whose exit applies a constructor to a type parameter. -/
  insn attempt [a] (&body : raising a) : a
  /-- A region returning its result. -/
  insn block [a] (&body : a) : a
  /-- A datatype, whose constructors and case instruction get emitters. -/
  data L (+a) where
    | nil
    | cons (h : a) (t : L a)
  end te

/-- A child of `Te`. -/
public environment TeKid extends Te where
  namespace kid
  open base
  type Leaf
  /-- An instruction of a grandchild of `Base`. -/
  insn wrap (x : Leaf) : Ref Leaf
  end kid

/-- The environment the functions below are built in. -/
abbrev W := Te.env

/-- The name `s`. -/
def n (s : String) : Name := .str .base s

/-! ## Signatures

A type parameter is an implicit type expression of `env`, and a successor takes a `Target` of its
payload.  Nothing else is bound: the emitter's instance `[Te.env ⊑ env]` defines every type its
signature names. -/

/--
info: Strata.Dyn.TypedEmitTest.Te.pick {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
  [Te.env ⊑ env] {a : TypeExpr env} (cond : Val env Base.Bool) (x y : Val env a) (result : Option Name := none)
  (info : Option α := none) : m (Val env a)
-/
#guard_msgs in #check Te.pick
/--
info: Strata.Dyn.TypedEmitTest.Te.invoke {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
  [Te.env ⊑ env] {as : List (TypeExpr env)} {r : TypeExpr env} (f : Val env (↑Base.Fn as r)) (args : Vals env as)
  (err : Target env [Te.Value]) (result : Option Name := none) (info : Option α := none) : m (Val env r)
-/
#guard_msgs in #check Te.invoke
/--
info: Strata.Dyn.TypedEmitTest.Te.forEach {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
  [Te.env ⊑ env] (n : Val env Base.Int)
  (body : Val env Base.Int → Target env [↑Base.Except Te.Value Base.Unit] → m Unit) (err : Target env [Te.Value])
  (result : Option Name := none) (info : Option α := none) (bodyBase : String := "body") : m (Val env Base.Unit)
-/
#guard_msgs in #check Te.forEach
/--
info: Strata.Dyn.TypedEmitTest.Te.unpack {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
  [Te.env ⊑ env] {as : List (TypeExpr env)} (f : Val env (↑Base.Fn as Base.Int)) (k : Target env as)
  (info : Option α := none) : m Unit
-/
#guard_msgs in #check Te.unpack
-- A type only the result has is computed from the type parameters.
/--
info: Strata.Dyn.Base.refNew {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m] [Base.env ⊑ env]
  {a : TypeExpr env} (value : Val env a) (result : Option Name := none) (info : Option α := none) :
  m (Val env (↑Base.Ref a))
-/
#guard_msgs in #check Base.refNew
/--
info: Strata.Dyn.TypedEmitTest.Te.box {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
  [Te.env ⊑ env] {a : TypeExpr env} (x : Val env a) (result : Option Name := none) (info : Option α := none) :
  m (Val env (↑Base.Ref (↑Base.Sequence a)))
-/
#guard_msgs in #check Te.box

/-! ## Building

`f` is `HandleTest`'s function, at typed values: a cell written and read, and an `Except`
built and taken apart.  No type argument is written: each is inferred from an operand, a
successor, or, for `Except.ok`'s error type, the expected result. -/

/-- What `build` gives in the environment `e`. -/
abbrev BuiltIn (e : Env Unit) [base ⊑ e] :=
  Except (Build.FailedFunc e Unit Unit) {fn : Func e Unit // fn.WF}

/-- What `build` gives in `W`. -/
abbrev Built := BuiltIn W

/-- The module `m` of `f`, printed, or why it was not built. -/
private def showMod {e : Env Unit} [base ⊑ e] (f : BuiltIn e) : String :=
  match f with
  | .error e => toString e
  | .ok f => match Module.ofChecked (.str .base "m") #[f] () with
    | .ok m => toString m
    | .error _ => "the module is not well formed"

private def f : Built :=
  Build.build (n "f") Base.Int () do
    let% ok ← freshLabel [Base.Int]
    let% err ← freshLabel [Te.IntList]
    let _ ← Build.startFreshBlock (base := "entry")
    let zero ← int (n "k") 0
    let% cell ← Base.refNew zero
    let _ ← Base.refSet (result := n "u") cell zero
    let% r ← Base.refGet cell
    let% x : Val W (Base.Except Te.IntList Base.Int) ← Base.Except.ok r
    Base.Except.case x ok.goto err.goto
    let _ ← startBlock₁ err (n "e")
    ret zero
    ret (← startBlock₁ ok)

/-- info: module m {
  func @f() -> base.Int {
    entry.0():
      %cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = base.refSet[base.Int](%cell.0, 0)
      %r.0 : base.Int = base.refGet[base.Int](%cell.0)
      %x.0 : base.Except(te.IntList, base.Int) = base.ok[te.IntList, base.Int](%r.0)
      base.Except.case[te.IntList, base.Int](%x.0) ^ok.0() ^err.0()
    err.0(%e.0 : te.IntList):
      ret(0)
    ok.0(%v.0 : base.Int):
      ret(%v.0)
  }
} -/
#guard_msgs in
#eval IO.println (showMod f)

/-- `g(%fn : Fn [Int, Bool] Int)`: `callCode` and `invoke`, whose spread is `vals[…]` and whose
list type argument is inferred from the code pointer's type. -/
private def g : Built :=
  Build.build (n "g") Base.Int () do
    let (fd, fv) ← param (n "fn") (Base.Fn [Base.Int, Base.Bool] Base.Int)
    let% err ← freshLabel [Te.Value]
    let _ ← Build.startFreshBlock #[fd] "entry"
    let a ← int (n "a") 1
    let b ← bool (n "b") true
    let% r ← Base.callCode fv vals[a, b]
    let% s ← Te.invoke fv vals[r, b] err.goto
    ret s
    let _ ← startBlock₁ err (n "exc")
    Base.unreachable

/-- info: module m {
  func @g(%fn.0 : base.Fn([base.Int, base.Bool], base.Int)) -> base.Int {
    entry.0(%fn.0 : base.Fn([base.Int, base.Bool], base.Int)):
      %r.0 : base.Int = base.callCode[[base.Int, base.Bool], base.Int](%fn.0, 1, true)
      %s.0 : base.Int = te.invoke[[base.Int, base.Bool], base.Int](%fn.0, %r.0, true) ^err.0()
      ret(%s.0)
    err.0(%exc.0 : te.Value):
      unreachable
  }
} -/
#guard_msgs in
#eval IO.println (showMod g)

/-- Regions: an `if` whose branches leave by their exit with the result, and a `forEach` whose
body leaves with `ok ()`, and a `guard`, which ends the block. -/
private def h : Built :=
  Build.build (n "h") Base.Int () do
    let (cd, c) ← param (n "c") Base.Bool
    let% k ← freshLabel [Base.Int]
    let% err ← freshLabel [Te.Value]
    let _ ← Build.startFreshBlock #[cd] "entry"
    let one ← int (n "one") 1
    let% r ← Te.if c
      (fun exit => Base.jump (exit.bind one))
      (fun exit => do Base.jump (exit.bind (← int (n "two") 2)))
    let _ ← Te.forEach (result := n "loop") r
      (fun i exit => do
        let _ ← Te.pick (result := n "p") c i r
        let% u ← Base.Unit.unit
        Base.jump (exit.bind (← Base.Except.ok u)))
      err.goto
    Te.guard (fun exit => Base.jump (exit.bind r)) k.goto
    ret (← startBlock₁ k)
    let _ ← startBlock₁ err (n "exc")
    Base.unreachable

/--
info: module m {
  func @h(%c.0 : base.Bool) -> base.Int {
    entry.0(%c.0 : base.Bool):
      %r.0 : base.Int = te.if[base.Int](%c.0) {
        then.0():
          ret(1)
      } {
        else.0():
          ret(2)
      }
      %loop.0 : base.Unit = te.forEach(%r.0) ^err.0() {
        body.0(%i.0 : base.Int):
          %p.0 : base.Int = te.pick[base.Int](%c.0, %i.0, %r.0)
          %u.0 : base.Unit = base.unit
          %ok.0 : base.Except(te.Value, base.Unit) = base.ok[te.Value, base.Unit](%u.0)
          ret(%ok.0)
      }
      te.guard[base.Int] ^k.0() {
        body.1():
          ret(%r.0)
      }
    k.0(%v.0 : base.Int):
      ret(%v.0)
    err.0(%exc.0 : te.Value):
      unreachable
  }
}
-/
#guard_msgs in
#eval IO.println (showMod h)

/-- A spread payload: `unpack`'s successor takes one value per argument type of `f`, so its
block's parameters are `as`. -/
private def u : Built :=
  Build.build (n "u") Base.Int () do
    let (fd, fv) ← param (n "fn") (Base.Fn [Base.Int, Base.Bool] Base.Int)
    let kL ← freshLabel [Base.Int, Base.Bool] "k"
    let _ ← Build.startFreshBlock #[fd] "entry"
    Te.unpack fv kL.goto
    let .cons x (.cons _ .nil) ← startBlock kL (n "x")
    ret x

/-- info: module m {
  func @u(%fn.0 : base.Fn([base.Int, base.Bool], base.Int)) -> base.Int {
    entry.0(%fn.0 : base.Fn([base.Int, base.Bool], base.Int)):
      te.unpack[[base.Int, base.Bool]](%fn.0) ^k.0()
    k.0(%x.0 : base.Int, %x.1 : base.Bool):
      ret(%x.0)
  }
} -/
#guard_msgs in
#eval IO.println (showMod u)

/-! ## Regions whose types apply a constructor to a type parameter

A region's parameter or exit type that applies a constructor to a type parameter is a type
expression of the parameter, so the lambda needs no annotation: an operand, or the expected
result type, fixes the parameter. -/

/--
info: Strata.Dyn.TypedEmitTest.Te.withRef {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
  [Te.env ⊑ env] {a : TypeExpr env} (init : Val env a) (body : Val env (↑Base.Ref a) → Target env [Base.Unit] → m Unit)
  (result : Option Name := none) (info : Option α := none) (bodyBase : String := "body") : m (Val env Base.Unit)
-/
#guard_msgs in #check Te.withRef
/--
info: Strata.Dyn.TypedEmitTest.Te.attempt {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
  [Te.env ⊑ env] {a : TypeExpr env} (body : Target env [↑Base.Except Te.Value a] → m Unit)
  (result : Option Name := none) (info : Option α := none) (bodyBase : String := "body") : m (Val env a)
-/
#guard_msgs in #check Te.attempt

section
variable (vInt : Val W Base.Int)

-- With annotations, the types Lean infers for the binders.
example : BuildM W Unit (Val W Base.Unit) :=
  Te.withRef (result := n "w") vInt (fun (r : Val W (Base.Ref Base.Int)) exit => do
    let _ ← Base.refGet (result := n "g") r
    Base.jump (exit.bind (← Base.Unit.unit (result := n "u"))))

example : BuildM W Unit (Val W Base.Int) :=
  Te.attempt (result := n "t") (fun (exit : Target W [Te.raising Base.Int]) => do
    Base.jump (exit.bind (← Base.Except.ok vInt)))

end

/-- `w(%x : Int)`: both, without annotations. -/
private def w : Built :=
  Build.build (n "w") Base.Int () do
    let (xd, x) ← param (n "x") Base.Int
    let _ ← Build.startFreshBlock #[xd] "entry"
    let _ ← Te.withRef (result := n "w") x (fun r exit => do
      let _ ← Base.refGet (result := n "g") r
      Base.jump (exit.bind (← Base.Unit.unit (result := n "u"))))
    let% t ← Te.attempt (fun exit => do
      Base.jump (exit.bind (← Base.Except.ok x)))
    ret t

/--
info: module m {
  func @w(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %w.0 : base.Unit = te.withRef[base.Int](%x.0) {
        body.0(%r.0 : base.Ref(base.Int)):
          %g.0 : base.Int = base.refGet[base.Int](%r.0)
          %u.0 : base.Unit = base.unit
          ret(%u.0)
      }
      %t.0 : base.Int = te.attempt[base.Int] {
        body.1():
          %ok.0 : base.Except(te.Value, base.Int) = base.ok[te.Value, base.Int](%x.0)
          ret(%ok.0)
      }
      ret(%t.0)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod w)

/-! ## A datatype an environment declares

`L`'s constructors and case instruction get emitters: `nil`'s type parameter only its result
has, and `case`'s `cons` successor takes both of `cons`'s fields. -/

/--
info: Strata.Dyn.TypedEmitTest.Te.L.case {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
  [Te.env ⊑ env] {a : TypeExpr env} (scrutinee : Val env (↑Te.L a)) (nil : Target env [])
  (cons : Target env [a, ↑Te.L a]) (info : Option α := none) : m Unit
-/
#guard_msgs in #check Te.L.case

/-- `list(%x : Int)`: the list `[x]`, taken apart. -/
private def list : Built :=
  Build.build (n "list") Base.Int () do
    let (xd, x) ← param (n "x") Base.Int
    let nilL ← freshLabel [] "nil"
    let consL ← freshLabel [Base.Int, Te.L Base.Int] "cons"
    let _ ← Build.startFreshBlock #[xd] "entry"
    let% e ← Te.L.nil
    let% l ← Te.L.cons x e
    Te.L.case l nilL.goto consL.goto
    let _ ← startBlock nilL
    ret x
    let .cons h (.cons _ .nil) ← startBlock consL (n "c")
    ret h

/--
info: module m {
  func @list(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %e.0 : te.L(base.Int) = te.nil[base.Int]
      %l.0 : te.L(base.Int) = te.cons[base.Int](%x.0, %e.0)
      te.L.case[base.Int](%l.0) ^nil.0() ^cons.0()
    nil.0():
      ret(%x.0)
    cons.0(%c.0 : base.Int, %c.1 : te.L(base.Int)):
      ret(%c.0)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod list)

/-! ## An instruction of a grandchild

`kid.wrap` is declared by `TeKid`, a child of `Te`, and its emitter is used beside `Base`'s. -/

/-- `kid(%x : Leaf)`: `x` wrapped, and read back. -/
private def kid : BuiltIn TeKid.env :=
  Build.build (n "kid") TeKid.Leaf () do
    let (xd, x) ← param (n "x") TeKid.Leaf
    let _ ← Build.startFreshBlock #[xd] "entry"
    let% c ← TeKid.wrap x
    ret (← Base.refGet (result := n "r") c)

/--
info: module m {
  func @kid(%x.0 : kid.Leaf) -> kid.Leaf {
    entry.0(%x.0 : kid.Leaf):
      %c.0 : base.Ref(kid.Leaf) = kid.wrap(%x.0)
      %r.0 : kid.Leaf = base.refGet[kid.Leaf](%c.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod kid)

/-! ## Region exits

Every region's exit is `ret`, which leaves the innermost body.  So the builder records a misuse
when a block is closed with the exit of a region other than the innermost open one: an
enclosing region's, which would leave the inner region instead, or one that has ended. -/

/-- `outer` and, inside it, `inner`.  With `wrong`, `inner`'s body leaves with `outer`'s exit,
meaning to leave `outer` with `1`; otherwise it leaves `inner` with its own. -/
private def nested (wrong : Bool) : Built :=
  Build.build (n "nested") Base.Int () do
    let _ ← Build.startFreshBlock (base := "entry")
    let r ← Te.block (result := n "outer") (fun (outer : Target W [Base.Int]) => do
      let one ← int (n "one") 1
      let _ ← Te.block (result := n "inner") (fun (inner : Target W [Base.Int]) =>
        Base.jump ((if wrong then outer else inner).bind one))
      Base.jump (outer.bind (← int (n "two") 2)))
    ret r

/--
info: module m {
  func @nested() -> base.Int {
    entry.0():
      %outer.0 : base.Int = te.block[base.Int] {
        body.0():
          %inner.0 : base.Int = te.block[base.Int] {
            body.1():
              ret(1)
          }
          ret(2)
      }
      ret(%outer.0)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod (nested false))
/-- info: the exit of region body.0 is used inside region body.1, which it does not leave -/
#guard_msgs in
#eval IO.println (showMod (nested true))

/-- A region whose exit is kept, in the state of a `StateT` over the builder, and, with `wrong`,
used after the region ends. -/
private def kept (wrong : Bool) : Built :=
  Build.build (n "kept") Base.Int () <| StateT.run' (s := none) (show
      StateT (Option (Target W [Base.Int])) (BuildM W Unit) Unit from do
    let _ ← liftBuild (Build.startFreshBlock (base := "entry"))
    let one ← int (n "one") 1
    let r ← Te.block (result := n "b") (fun exit => do
      set (some exit)
      Base.jump (exit.bind one))
    match ← get with
    | some exit => if wrong then Base.jump (exit.bind r) else ret r
    | none => ret r)

/--
info: module m {
  func @kept() -> base.Int {
    entry.0():
      %b.0 : base.Int = te.block[base.Int] {
        body.0():
          ret(1)
      }
      ret(%b.0)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod (kept false))
/-- info: the exit of region body.0 is used after the region ends -/
#guard_msgs in
#eval IO.println (showMod (kept true))

/-! ## A region body that throws

A front end in `ExceptT` can throw out of a region's body and catch the error outside it.  The
region is then never closed, and the enclosing block is lost, so `Build.run` records a misuse. -/

/-- A cell of `1`, then a block whose body, with `fail`, throws, which is caught. -/
private def lower (fail : Bool) : ExceptT String (BuildM W Unit) Unit := do
  let _ ← liftBuild (Build.startFreshBlock (base := "entry"))
  let _ ← Base.refNew (result := n "c") (← int (n "one") 1)
  try
    let _ ← Te.block (result := n "b") (fun (exit : Target W [Base.Int]) => do
      if fail then throw "unsupported"
      Base.jump (exit.bind (← int (n "two") 2)))
  catch _ => pure ()
  ret (← int (n "zero") 0)

/-- `lower fail`, built. -/
private def lowered (fail : Bool) : Built :=
  Build.build (n "lowered") Base.Int () do let _ ← (lower fail).run

/--
info: module m {
  func @lowered() -> base.Int {
    entry.0():
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](1)
      %b.0 : base.Int = te.block[base.Int] {
        body.0():
          ret(2)
      }
      ret(0)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod (lowered false))
/-- info: region body.0 is still open when the function ends: its body did not return -/
#guard_msgs in
#eval IO.println (showMod (lowered true))

/-! ## Unification through type expressions -/

section
variable (vInt : Val W Base.Int) (vBool : Val W Base.Bool) (vList : Val W Te.IntList)

-- `Ref ?a` against `Ref Int`.
example (c : Val W (Base.Ref Base.Int)) : BuildM W Unit (Val W Base.Int) :=
  Base.refGet c
-- An abbreviation against its expansion, either way round.
example (c : Val W Te.IntRef) : BuildM W Unit (Val W Base.Int) := Base.refGet c
example : BuildM W Unit (Val W Te.IntRef) := Base.refNew vInt
-- An abbreviation with a parameter, its parameter at the top of an argument: `raising a` is
-- `Except Value a`, against `Except ?e ?a`.
example (c : Val W (Te.raising (Base.Ref Base.Bool))) (k : Target W [Base.Ref Base.Bool])
    (err : Target W [Te.Value]) : BuildM W Unit Unit :=
  Base.Except.case c k err
-- One whose body nests a type under a constructor: `PairRef Bool` is `Ref (Except Bool Int)`,
-- its handle applying its body's handles, so `?a` is `Except Bool Int`.
example (c : Val W (Te.PairRef Base.Bool)) :
    BuildM W Unit (Val W (Base.Except Base.Bool Base.Int)) :=
  Base.refGet c
example (c : Val W (Base.Ref (Base.Except Base.Bool Base.Int))) :
    BuildM W Unit (Val W (Base.Except Base.Bool Base.Int)) :=
  Base.refGet c
-- The type a successor's payload takes through such an abbreviation fixes `Except.ok`'s `e`.
example (k : Target W [Te.raising Base.Unit]) : BuildM W Unit Unit := do
  let% u ← Base.Unit.unit
  Base.jump (k.bind (← Base.Except.ok u))
-- A parent's type and a child's, in either order.
example : BuildM W Unit (Val W (Base.Except Te.IntList Base.Int)) :=
  Base.Except.ok vInt
example : BuildM W Unit (Val W (Base.Except Base.Int Te.IntList)) :=
  Base.Except.ok vList
-- A grandchild's type, in the grandchild, through a grandparent's constructor.
example (v : Val TeKid.env TeKid.Leaf) : BuildM TeKid.env Unit (Val TeKid.env TeKid.Leaf) := do
  let% c ← Base.refNew v
  Base.refGet c
-- A list: `Fn [Int, Bool] Int` against `Fn ?as ?r`.
example (fv : Val W (Base.Fn [Base.Int, Base.Bool] Base.Int)) : BuildM W Unit (Val W Base.Int) :=
  Base.callCode fv vals[vInt, vBool]
-- A type only the result has: from the operands, with an expected type or without, and
-- nested.
example : BuildM W Unit (Val W (Base.Sequence Base.Int)) := Te.seq #[vInt, vInt]
example : BuildM W Unit (Val W (Base.Sequence Te.IntList)) := do
  let r ← Te.box vList
  Base.refGet r
example : BuildM W Unit (Val W (Base.Ref (Base.Sequence Base.Int))) := Te.box vInt
-- In a front end's monad over the builder: `env` comes from it.
example : StateT Nat (BuildM W Unit) (Val W Base.Int) := do
  let% c ← Base.refNew vInt
  Base.refGet c
-- And in one that can fail, as a lowering that reports errors is.
example : ReaderT Nat (StateT Nat (ExceptT String (BuildM W Unit))) (Val W Base.Int) := do
  let% c ← Base.refNew vInt
  Base.refGet c
-- Generic in the environment.
example {e : Env Unit} [W ⊑ e] (c : Val e (Base.Ref Te.Value)) : BuildM e Unit (Val e Te.Value) :=
  Base.refGet c

end

/-! ## Rejections

Each ill-typed emit is followed by its accepted twin. -/

section
variable (vInt : Val W Base.Int) (vBool : Val W Base.Bool)
  (fv : Val W (Base.Fn [Base.Int, Base.Bool] Base.Int))

-- An operand of the wrong type.
/--
error: Application type mismatch: The argument
  vInt
has type
  Val W Base.Int
but is expected to have type
  Val W (↑Base.Ref Base.Int)
-/
#guard_msgs (substring := true) in
example : BuildM W Unit (Val W Base.Int) := Base.refGet vInt
example (c : Val W (Base.Ref Base.Int)) : BuildM W Unit (Val W Base.Int) :=
  Base.refGet c

-- A spread operand of the wrong type, and one too few.
/--
error: Application type mismatch: The argument
  vBool
has type
  Val W Base.Bool
but is expected to have type
  Val W Base.Int
in the application
  Vals.cons vBool
-/
#guard_msgs (substring := true) in
example : BuildM W Unit (Val W Base.Int) := Base.callCode fv vals[vBool, vBool]
/--
error: Application type mismatch: The argument
  Vals.nil
has type
  Vals ?m.47 []
but is expected to have type
  Vals W [Base.Bool]
in the application
  Vals.cons vInt Vals.nil
-/
#guard_msgs in
example : BuildM W Unit (Val W Base.Int) := Base.callCode fv vals[vInt]
example : BuildM W Unit (Val W Base.Int) := Base.callCode fv vals[vInt, vBool]

-- Too few operands, and too many.
/--
error: Type mismatch
  fun y => Te.pick vBool vInt y
has type
  Val W Base.Int → ?m.38 (Val W Base.Int)
but is expected to have type
  BuildM W Unit (Val W Base.Int)
-/
#guard_msgs in
example : BuildM W Unit (Val W Base.Int) := Te.pick vBool vInt
/--
error: Application type mismatch: The last
  vInt
argument has type
  Val W Base.Int
but is expected to have type
  optParam (Option Name) none
in the application
  @Te.pick W ?m.37 (BuildM W Unit) ?m.39 ?m.40 ?m.41 Base.Int vBool vInt vInt vInt
-/
#guard_msgs in
example : BuildM W Unit (Val W Base.Int) := Te.pick vBool vInt vInt vInt
example : BuildM W Unit (Val W Base.Int) := Te.pick vBool vInt vInt

-- Two operands that disagree on a type argument.
/--
error: Application type mismatch: The last
  vBool
argument has type
  Val W Base.Bool
but is expected to have type
  Val W Base.Int
-/
#guard_msgs (substring := true) in
example : BuildM W Unit (Val W Base.Int) := Te.pick vBool vInt vBool

-- A successor whose payload is missing, and the result's declared type wrong.
/--
error: Application type mismatch: The argument
  okL.goto
has type
  Target W []
but is expected to have type
  Target W [Base.Int]
-/
#guard_msgs (substring := true) in
example (okL : BlockRef W []) (errL : BlockRef W [Base.String])
    (x : Val W (Base.Except Base.String Base.Int)) :
    BuildM W Unit Unit :=
  Base.Except.case x okL.goto errL.goto
example (okL : BlockRef W [Base.Int]) (errL : BlockRef W [Base.String])
    (x : Val W (Base.Except Base.String Base.Int)) : BuildM W Unit Unit :=
  Base.Except.case x okL.goto errL.goto
/--
error: Application type mismatch: The argument
  __do_lift✝
has type
  Val W (↑Base.Ref Base.Int)
but is expected to have type
  Val W (↑Base.Ref Base.Bool)
-/
#guard_msgs (substring := true) in
example : BuildM W Unit (Val W Base.Bool) := do
  Base.refGet (← Base.refNew vInt)
example : BuildM W Unit (Val W Base.Int) := do
  Base.refGet (← Base.refNew vInt)

-- A child's type in the parent's builder: a value of it has no type there, and one of the
-- child's builder is not the parent's.
/--
error: failed to synthesize instance of type class
  TeKid.env ⊑ W

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (_v : Val W TeKid.Leaf) : BuildM W Unit Unit := pure ()
example (_v : Val TeKid.env TeKid.Leaf) : BuildM TeKid.env Unit Unit := pure ()
/--
error: Application type mismatch: The argument
  v
has type
  Val TeKid.env TeKid.Leaf
but is expected to have type
  Val W Base.Int
-/
#guard_msgs (substring := true) in
example (v : Val TeKid.env TeKid.Leaf) :
    BuildM W Unit (Val W (Base.Ref Base.Int)) :=
  Base.refNew v
example (v : Val TeKid.env TeKid.Leaf) :
    BuildM TeKid.env Unit (Val TeKid.env (Base.Ref TeKid.Leaf)) :=
  Base.refNew v

end

/-! ## Escapes

A type known only when the builder runs is cast in: `Val.ofId` or `Val.cast` give a value the
type they are told, and `Build.run` checks it as before.  Here a value is cast to the wrong
type: Lean accepts the emit, and the check rejects the function. -/

/-- `refGet` of a `Bool` cast to a `Ref Int`, or, the accepted twin, of a `Ref Int` cast to
itself. -/
private def castAs (wrong : Bool) : Built :=
  Build.build (n "castAs") Base.Int () do
    let _ ← Build.startFreshBlock (base := "entry")
    let% c ← Base.refNew (← int (n "one") 1)
    let b ← bool (n "b") true
    let% r ← Base.refGet (if wrong then b.cast (Base.Ref Base.Int) else c.cast (Base.Ref Base.Int))
    ret r

/--
info: module m {
  func @castAs() -> base.Int {
    entry.0():
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](1)
      %b.0 : base.Bool = const true
      %r.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod (castAs false))
/-- info: castAs is not well formed -/
#guard_msgs in
#eval IO.println (showMod (castAs true))

/-- `Emit.ret` does not check its value against the function's result type: leaving `Int`'s
function with a `Bool`, or, the accepted twin, with an `Int`. -/
private def retAs (wrong : Bool) : Built :=
  Build.build (n "retAs") Base.Int () do
    let _ ← Build.startFreshBlock (base := "entry")
    if wrong then ret (← bool (n "b") true) else ret (← int (n "i") 1)

/-- info: module m {
  func @retAs() -> base.Int {
    entry.0():
      ret(1)
  }
} -/
#guard_msgs in
#eval IO.println (showMod (retAs false))
/-- info: retAs is not well formed -/
#guard_msgs in
#eval IO.println (showMod (retAs true))

/-- `Target.ofRaw` gives a target the payload it is told: `Except.case`'s `ok` successor,
a block taking a `Bool` claimed to take an `Int`, or, the accepted twin, one taking an `Int`. -/
private def succAs (wrong : Bool) : Built :=
  Build.build (n "succAs") Base.Int () do
    let (xd, x) ← param (n "x") (Base.Except Base.String Base.Int)
    let okB ← freshLabel [Base.Bool] "okB"
    let okI ← freshLabel [Base.Int] "okI"
    let errL ← freshLabel [Base.String] "err"
    let _ ← Build.startFreshBlock #[xd] "entry"
    let ok : Target W [Base.Int] := if wrong then Target.ofRaw [Base.Int] okB.goto.raw
      else okI.goto
    Base.Except.case x ok errL.goto
    let _ ← startBlock₁ okB (n "b")
    ret (← int (n "zero") 0)
    ret (← startBlock₁ okI (n "i"))
    let _ ← startBlock₁ errL (n "e")
    ret (← int (n "one") 1)

/--
info: module m {
  func @succAs(%x.0 : base.Except(base.String, base.Int)) -> base.Int {
    entry.0(%x.0 : base.Except(base.String, base.Int)):
      base.Except.case[base.String, base.Int](%x.0) ^okI.0() ^err.0()
    okI.0(%i.0 : base.Int):
      ret(%i.0)
    err.0(%e.0 : base.String):
      ret(1)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod (succAs false))
/-- info: succAs is not well formed -/
#guard_msgs in
#eval IO.println (showMod (succAs true))

/-! ## Blocks and targets come from the builder

`BlockRef` and `Target` have private constructors, so a block is made by `freshLabel`, and a
target by `goto`, `bind`, `bindAll`, a region's exit or `Target.ofRaw`.  Making either directly
from a label or a raw target is rejected, beside its accepted twin. -/

/-- error: Invalid `⟨...⟩` notation: Constructor for `Strata.Dyn.BlockRef` is marked as private -/
#guard_msgs in
example (l : Label) : BlockRef W [] := ⟨l⟩
example : BuildM W Unit (BlockRef W []) := freshLabel []

/-- error: Invalid `⟨...⟩` notation: Constructor for `Strata.Dyn.Target` is marked as private -/
#guard_msgs in
example (r : Target.Raw) : Target W [] := ⟨r, none⟩
example (r : Target.Raw) : Target W [] := Target.ofRaw [] r

/-! ## Docstrings

An emitter's docstring starts with its instruction's.  `Base`'s emitters are generated in
another module, from the record `Base`'s `environment` command leaves, which keeps each
instruction's docstring. -/

/-- The docstring of the declaration `n`. -/
private meta def docOf (n : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  match ← Lean.findDocString? (← Lean.getEnv) n with
  | some d => Lean.logInfo d
  | none => Lean.logInfo "no docstring"

/-- The docstring the record of the instruction `n` keeps. -/
private meta def recordDocOf (n : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  match DSL.findDecl? (← Lean.getEnv) n with
  | some (.op _ o) => Lean.logInfo (o.doc.getD "no docstring")
  | _ => Lean.logInfo "no instruction"

/-- info: Generic: one of two values.

Emit `te.pick`, its type arguments inferred from its operands' and successors' types. -/
#guard_msgs in
#eval docOf ``Te.pick
/-- info: `base.refNew`, a new cell holding `value`. -/
#guard_msgs in
#eval recordDocOf ``Base.refNew
/-- info: `base.ok`, a success. -/
#guard_msgs in
#eval recordDocOf ``Base.Except.ok

end Strata.Dyn.TypedEmitTest
