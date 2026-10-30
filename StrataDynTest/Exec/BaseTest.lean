/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Base
public import StrataDyn.Exec.Run
public import StrataDyn.DomCompute
import StrataDyn.DDMRead
import StrataDyn.Env.WF
import StrataDynTest.Exec.Demo
-- `#guard` runs the engine and the programs as compiled code, and `#eval` the reader too.
meta import StrataDyn.Exec.Base
meta import StrataDyn.Exec.Run
meta import StrataDyn.DDMRead
meta import StrataDyn.Env.WF
meta import StrataDyn.DomCompute

set_option autoImplicit false

/-!
# The base's rules

`#dyn_coverage (complete)` holds of the base and fails on an environment with missing
rules.  The base's own table, `BaseSem`, runs programs that use nothing but the base: its
control flow through `Terminator.ret`, `.jump`, `.branch` and `.unreachable`, `Except` and
`Unit` and their case instructions, cells, and calls through typed code pointers.  `base.cellLoc`
stops with a gap.  A run ignores a function's contract and the module's ghosts, and rejects a
module with an extern function.
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

/-- A function, its parameters its entry block's, its values named. -/
def fn (s : String) (ret : TypeExpr E) (bs : List (Block E Unit)) : Func E Unit :=
  let f : Func E Unit :=
    { name := nm s, params := (bs.head?.map (·.params)).getD #[], retType := ret,
      blocks := bs.toArray, names := #[], info := () }
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

/-- `loc()`: the location of a new cell, by `base.cellLoc`, then `0`. -/
def loc : Func E Unit := fn "loc" intT [
  blk "entry" [] [cst 0 intT (.int 0), app 1 (Base.Ref intT) Base.refNew.ref ⟨#[.ty intT], rfl⟩ [0],
    app 2 Base.Loc Base.cellLoc.ref ⟨#[.ty intT], rfl⟩ [1]]
  (ret 0)]

/-- The module of every function above, checked. -/
def all : Except (Array Name) (Module E Unit) :=
  Module.Raw.check
    { name := nm "base", funcs := #[pick, unwrap, wrap, flip, idI, twice, never, loc], info := () }

/-- `n` as an argument. -/
def int (n : Int) : BaseSem.model.Arg := BaseSem.model.arg n

/-- `e : Except Int Int` as an argument. -/
def exc (e : Except Int Int) : BaseSem.model.Arg := BaseSem.model.arg e

def run (f : String) (args : Array BaseSem.model.Arg) : Outcome BaseSem.model :=
  match all with
  | .ok m => runModule BaseSem.model m (nm f) args 1000
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

-- `cellLoc` stops with a gap: frames have no meaning at run time.
#guard match (run "loc" #[]).result with
  | .fault (.gap m) => m == "base.cellLoc: frames have no meaning at run time"
  | _ => false

/-! ## What a run ignores

Linking reads only function bodies, so a run ignores contracts and ghosts.  `@m.f`'s `requires`
and `ensures` clauses both return `false`, its `ensures` clause applies `base.old`, its `requires`
clause reads the ghost `@m.count` and its `writes` frame is that ghost's cell.  `@m.main` still
calls `@m.f` and gets its result, `7`.  A module with an extern function does not run yet: the
extern has no blocks, so its code pointer has a signature other than its declared one. -/

/-- A module of a ghost, a function whose contract names it, and a caller of that function. -/
private def contractText : String := "module m {
  ghost @m.count : base.Int = {
    init.0():
      ret(0)
  }
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int
    requires {
      pre.0():
        %n.0 : base.Int = base.refGet[base.Int](ghost @m.count)
        ret(false)
    }
    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
            ret(%w.0)
        }
        ret(false)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
    writes({
      loc.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](ghost @m.count)
        ret(%l.0)
    })
  {
    entry.0(%c.0 : base.Ref(base.Int)):
      %v.1 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.1)
  }
  func @m.main() -> base.Int {
    entry.0():
      %c.1 : base.Ref(base.Int) = base.refNew[base.Int](7)
      %p.0 : base.Fn([base.Ref(base.Int)], base.Int) = const @m.f
      %r.1 : base.Int = base.callCode[[base.Ref(base.Int)], base.Int](%p.0, %c.1)
      ret(%r.1)
  }
}
"

/-- A module of an extern function and a caller of it. -/
private def externText : String := "module m {
  extern func @m.e(%x.0 : base.Int) -> base.Int
  func @m.main() -> base.Int {
    entry.0():
      %p.0 : base.Fn([base.Int], base.Int) = const @m.e
      %r.0 : base.Int = base.callCode[[base.Int], base.Int](%p.0, 1)
      ret(%r.0)
  }
}
"

/-- Read `text`, run its `@m.main`, and print the result as an `Int`, or the fault, or the
reader's diagnostics. -/
private def runMain (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    let o := runModule BaseSem.model m (.str (nm "m") "main") #[] 1000
    match o.result with
    | .fault (.invalid msg) => IO.println s!"invalid: {msg}"
    | .fault f => IO.println (repr f)
    | _ => IO.println (repr (o.read? Int))

/-- info: some 7 -/
#guard_msgs in
#eval runMain contractText

/-- info: invalid: m.e: a code pointer at another signature than its function's -/
#guard_msgs in
#eval runMain externText

end Strata.Dyn.ExecTest.BaseTest
