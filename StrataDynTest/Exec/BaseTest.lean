/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Base
public import StrataDyn.Exec.Run
public import StrataDyn.DomCompute
import StrataDyn.Env.WF
import StrataDynTest.Exec.Demo
-- `#guard` runs the engine and the programs as compiled code.
meta import StrataDyn.Exec.Base
meta import StrataDyn.Exec.Run
meta import StrataDyn.Env.WF
meta import StrataDyn.DomCompute

set_option autoImplicit false

/-!
# The base's rules

`#dyn_coverage (complete)` holds of the base and fails on an environment with missing
rules.  The base's own table, `BaseSem`, runs programs that use nothing but the base: its
control flow through `Terminator.ret`, `.jump`, `.branch` and `.unreachable`, `Except` and
`Unit` and their case instructions, cells, and calls through typed code pointers.
-/

namespace Strata.Dyn.ExecTest.BaseTest

open Strata.Dyn.Exec

/-! ## Coverage -/

#guard_msgs in
#dyn_coverage Base (complete)

/-- error: Strata.Dyn.ExecTest.Demo is not fully covered: no rule for demo.isqrt -/
#guard_msgs in
#dyn_coverage Strata.Dyn.ExecTest.Demo (complete)

/-! ## Programs -/

@[expose] public section

#dyn_sem_table BaseSem for Base

abbrev E := Base.env

def intT : TypeExpr E := Base.Int
def boolT : TypeExpr E := Base.Bool
def unitT : TypeExpr E := Base.Unit
def excT : TypeExpr E := Base.Except intT intT
def fnT : TypeExpr E := Base.Fn [intT] intT

def d (n : Nat) (t : TypeExpr E) : ValDecl E := ⟨⟨n⟩, t⟩
def nm (s : String) : Name := .str .base s
def to (s : String) (args : List Nat := []) : Target.Raw := ⟨⟨nm s⟩, (args.map ValId.mk).toArray⟩

def blk (s : String) (params : List (ValDecl E)) (instrs : List (Instruction E Unit))
    (t : Terminator E Unit) : Block E Unit :=
  ⟨⟨nm s⟩, params.toArray, instrs.toArray, t, ()⟩

/-- A function, its values named. -/
def fn (s : String) (ret : TypeExpr E) (bs : List (Block E Unit)) : Func E Unit :=
  let f : Func E Unit := ⟨nm s, ret, bs.toArray, #[], ()⟩
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

def cst (n : Nat) (t : TypeExpr E) (c : Const) : Instruction E Unit := .const () (d n t) c

def app {isig : InsnSig E} (n : Nat) (t : TypeExpr E) (r : InsnRef E isig)
    (targs : TypeArgs E isig.scope) (args : List Nat) : Instruction E Unit :=
  .apply () (d n t) r targs (args.map ValId.mk).toArray #[] #[]

def ret (x : Nat) : Terminator E Unit := .ret () ⟨x⟩

/-- `pick(c, x, y)`: `x` if `c`, else `y`. -/
def pick : Func E Unit := fn "pick" intT [
  blk "entry" [d 0 boolT, d 1 intT, d 2 intT] [] (.branch () ⟨0⟩ (to "yes") (to "no")),
  blk "yes" [] [] (ret 1),
  blk "no" [] [] (ret 2)]

/-- `unwrap(e)`: the value or the error `e` holds, by `Except.case`. -/
def unwrap : Func E Unit := fn "unwrap" intT [
  blk "entry" [d 0 excT] []
    (.apply () Base.Except.case.ref ⟨#[.ty intT, .ty intT], rfl⟩ #[⟨0⟩] #[to "ok", to "err"] #[]),
  blk "ok" [d 1 intT] [] (ret 1),
  blk "err" [d 2 intT] [] (ret 2)]

/-- `wrap(x)`: `ok x`, unwrapped again through a call. -/
def wrap : Func E Unit := fn "wrap" intT [
  blk "entry" [d 0 intT] [
    app 1 excT Base.Except.ok.ref ⟨#[.ty intT, .ty intT], rfl⟩ [0],
    cst 2 (Base.Fn [excT] intT) (.func (nm "unwrap")),
    app 3 intT Base.callCode.ref ⟨#[.list (.ofTypes #[excT]), .ty intT], rfl⟩ [2, 1]]
  (ret 3)]

/-- `flip()`: a loop over a cell, which runs its body once and returns `7`. -/
def flip : Func E Unit := fn "flip" intT [
  blk "entry" [] [cst 0 boolT (.bool true), app 1 (Base.Ref boolT) Base.refNew.ref ⟨#[.ty boolT], rfl⟩ [0]]
    (.jump () (to "head")),
  blk "head" [] [app 2 boolT Base.refGet.ref ⟨#[.ty boolT], rfl⟩ [1]] (.branch () ⟨2⟩ (to "body") (to "done")),
  blk "body" [] [cst 3 boolT (.bool false), app 4 unitT Base.refSet.ref ⟨#[.ty boolT], rfl⟩ [1, 3]]
    (.jump () (to "head")),
  blk "done" [] [cst 5 intT (.int 7)] (ret 5)]

/-- `twice(x)`: `x`, through `Unit.case` and a typed code pointer to `idI`. -/
def idI : Func E Unit := fn "idI" intT [blk "entry" [d 0 intT] [] (ret 0)]

def twice : Func E Unit := fn "twice" intT [
  blk "entry" [d 0 intT] [cst 1 unitT .unit]
    (.apply () Base.Unit.case.ref ⟨#[], rfl⟩ #[⟨1⟩] #[to "go"] #[]),
  blk "go" [] [
    cst 2 fnT (.func (nm "idI")),
    app 3 intT Base.callCode.ref ⟨#[.list (.ofTypes #[intT]), .ty intT], rfl⟩ [2, 0],
    app 4 intT Base.callCode.ref ⟨#[.list (.ofTypes #[intT]), .ty intT], rfl⟩ [2, 3]]
  (ret 4)]

/-- `never()`: control reaches `unreachable`. -/
def never : Func E Unit := fn "never" intT [blk "entry" [] [] (.unreachable ())]

/-- The module of every function above, checked. -/
def all : Except (Array Name) (Module E Unit) :=
  Module.Raw.check ⟨nm "base", #[pick, unwrap, wrap, flip, idI, twice, never], ()⟩

/-- `n` as an argument. -/
def int (n : Int) : BaseSem.model.Arg := BaseSem.model.arg n

/-- `e : Except Int Int` as an argument. -/
def exc (e : Except Int Int) : BaseSem.model.Arg := BaseSem.model.arg e

def run (f : String) (args : Array BaseSem.model.Arg) (engine : Engine := .fused) :
    Outcome BaseSem.model :=
  match all with
  | .ok m => runModule BaseSem.model m (nm f) args 1000 (engine := engine)
  | .error _ => .failed BaseSem.model (.invalid "not well formed")

def intOf (o : Outcome BaseSem.model) : Option Int := o.read? Int

end

/-! ## Runs -/

-- `branch` and `ret`.
#guard intOf (run "pick" #[BaseSem.model.arg true, int 1, int 2]) = some 1
#guard intOf (run "pick" #[BaseSem.model.arg false, int 1, int 2]) = some 2

-- `Except.case` on each constructor.
#guard intOf (run "unwrap" #[exc (.ok 3)]) = some 3
#guard intOf (run "unwrap" #[exc (.error 4)]) = some 4

-- `Except.ok`, and a call that takes an `Except`.
#guard intOf (run "wrap" #[int 5]) = some 5

-- `jump`, a loop and a cell.
#guard intOf (run "flip" #[]) = some 7

-- `Unit.case` and two calls.
#guard intOf (run "twice" #[int 6]) = some 6

-- `unreachable`.
#guard match (run "never" #[]).result with
  | .fault (.failure _) => true
  | _ => false

-- The step loop agrees.
#guard intOf (run "flip" #[] (engine := .frames)) = some 7
#guard intOf (run "twice" #[int 6] (engine := .frames)) = some 6

end Strata.Dyn.ExecTest.BaseTest
