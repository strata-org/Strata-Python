/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataPython.Mantle.Env
import StrataMantle.Env.WF
-- The `#guard`s below run as compiled code.
meta import StrataPython.Mantle.Env
meta import StrataMantle.Env.WF
-- `decide +kernel` unfolds the checker, the environment and core's array operations.
import all StrataMantle.WF
import all StrataMantle.Env
import all StrataMantle.Base
import all StrataMantle.Build
import all StrataPython.Mantle.Env
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq

set_option autoImplicit false

/-!
# Python functions, written as IR

Functions over `Py.env` written directly as blocks and checked by `Mantle.WF`: a literal
boxed into a Python value, a raising operation whose failure goes to a handler, a `truthy`
feeding a `branch`, a function returning `Except py.Value py.Value`, variadic operations,
and a completion dispatch.  Ill-formed variants check what the checker rejects.
-/

namespace StrataPython.Mantle.PyEnvTest

open Strata.Mantle

/-- The value `%n`, of type `t`. -/
private def d (n : Nat) (t : TypeExpr Py.env 0) : ValDecl Py.env := ⟨⟨n⟩, t⟩

/-- The block called `s`. -/
private def lbl (s : String) : Label := ⟨.str .base s⟩

/-- A transfer to `s`, binding nothing. -/
private def to (s : String) : BlockValue := ⟨lbl s, #[]⟩

/-- `%n = ok[Value, Value] %v`: a success, which a translated function returns. -/
private def mkOk (n v : Nat) : Instruction Py.env Unit :=
  .apply () (d n Py.failing.ty) Base.Except.ok #v[Py.Value.ty, Py.Value.ty] #[⟨v⟩] #[] #[]

/-- `%n = error[Value, Value] %v`: a failure, which a translated function returns. -/
private def mkError (n v : Nat) : Instruction Py.env Unit :=
  .apply () (d n Py.failing.ty) Base.Except.error #v[Py.Value.ty, Py.Value.ty] #[⟨v⟩] #[] #[]

/-! ## `def f(x): return x + 1`

    f(%0 : Value) : Except Value Value
      entry:
        %1 = const int 1
        %2 = py.intLit %1
        %3 = py.add %0 %2 ^propagate()    -- %3 : Value
        %4 = ok[Value, Value] %3
        ret %4
      propagate(%5 : Value):
        %6 = error[Value, Value] %5
        ret %6

`add`'s `err` successor is the handler, which receives the exception; the fall-through
result is the sum.  The function returns `Except Value Value`, so returning is `ok` and
propagating is `error`. -/

/-- `%2 = py.intLit %1`: the constant, boxed. -/
private def box : Instruction Py.env Unit :=
  .apply () (d 2 Py.Value.ty) Py.intLit #v[] #[⟨1⟩] #[] #[]

/-- `%3 = r args ^ks`, of type `t`. -/
private def op3 {isig : InsnSig Py.env} (r : InsnRef Py.env isig)
    (typeArgs : Vector (TypeExpr Py.env 0) isig.typeArgc) (args : Array Nat)
    (ks : Array BlockValue := #[to "propagate"]) (t : TypeExpr Py.env 0 := Py.Value.ty) :
    Instruction Py.env Unit :=
  .apply () (d 3 t) r typeArgs (args.map (⟨·⟩)) ks #[]

/-- The handler at `%n`: it takes the exception and returns it as a failure. -/
private def propagateAt (n : Nat) : Block Py.env Unit :=
  { label := lbl "propagate", params := #[d n Py.Value.ty], instrs := #[mkError (n + 1) n]
    term := .ret () ⟨n + 1⟩, info := () }

/-- `f`, with `%1 = const int 1`, then `box` and `op` given, then `ok`: each variant below
changes one of them. -/
private def fWith (box op : Instruction Py.env Unit) (ok : Instruction Py.env Unit := mkOk 4 3) :
    Func Py.env Unit where
  name    := Py.pn "f"
  retType := Py.failing.ty
  blocks  := #[{ label := lbl "entry", params := #[d 0 Py.Value.ty]
                 instrs := #[.const () (d 1 Base.Int.ty) (.int 1), box, op, ok]
                 term := .ret () ⟨4⟩, info := () }, propagateAt 5]
  names   := #[⟨"x", 0⟩]
  info    := ()

private def f : Func Py.env Unit := fWith box (op3 Py.add #v[] #[0, 2])

example : Func.WF #[] f := by decide +kernel

/-! ## `def g(x): return 1 if x else 2`

    g(%0 : Value) : Except Value Value
      entry:
        %1 = py.truthy %0 ^propagate()    -- %1 : Bool
        branch %1 yes() no()
      yes:
        %2 = const int 1
        %3 = py.intLit %2
        %4 = ok[Value, Value] %3
        ret %4
      no:
        %5 = const int 2
        %6 = py.intLit %5
        %7 = ok[Value, Value] %6
        ret %7
      propagate(%8 : Value):
        %9 = error[Value, Value] %8
        ret %9

`truthy` returns the base `Bool` a `branch` takes, and can fail because `__bool__` is
arbitrary code. -/

/-- The block `s`, returning the integer `k` boxed, from `%n` on. -/
private def retInt (s : String) (n : Nat) (k : Int) : Block Py.env Unit where
  label  := lbl s
  params := #[]
  instrs := #[.const () (d n Base.Int.ty) (.int k),
    .apply () (d (n + 1) Py.Value.ty) Py.intLit #v[] #[⟨n⟩] #[] #[], mkOk (n + 2) (n + 1)]
  term := .ret () ⟨n + 2⟩
  info := ()

private def gEntry : Block Py.env Unit where
  label  := lbl "entry"
  params := #[d 0 Py.Value.ty]
  instrs := #[.apply () (d 1 Base.Bool.ty) Py.truthy #v[] #[⟨0⟩] #[to "propagate"] #[]]
  term := .branch () ⟨1⟩ (to "yes") (to "no")
  info := ()

private def g : Func Py.env Unit where
  name    := Py.pn "g"
  retType := Py.failing.ty
  blocks  := #[gEntry, retInt "yes" 2 1, retInt "no" 5 2, propagateAt 8]
  names   := #[⟨"x", 0⟩]
  info    := ()

example : Func.WF #[] g := by decide +kernel

private def m : Module Py.env Unit where
  name  := Py.pn "test"
  funcs := #[f, g]
  info  := ()

example : Module.WF m := by decide +kernel

/-! ## What the checker catches

An operand of the wrong type, a handler where none is declared or none where one is, a
result of the wrong type, and the wrong number of operands. -/

/-- `add` applied to the base integer rather than to the boxed Python value. -/
example : ¬ Func.WF #[] (fWith box (op3 Py.add #v[] #[0, 1])) := by decide +kernel

/-- A handler on `intLit`, which cannot fail. -/
example : ¬ Func.WF #[] (fWith
    (.apply () (d 2 Py.Value.ty) Py.intLit #v[] #[⟨1⟩] #[to "propagate"] #[])
    (op3 Py.add #v[] #[0, 2])) := by
  decide +kernel

/-- `add` with no handler: it declares an `err` successor, so a use site must name one. -/
example : ¬ Func.WF #[] (fWith box (op3 Py.add #v[] #[0, 2] (ks := #[]))) := by decide +kernel

/-- `add`'s result is the success type, not `Except`. -/
example : ¬ Func.WF #[] (fWith box (op3 Py.add #v[] #[0, 2] (t := Py.failing.ty)) (mkOk 4 2)) := by
  decide +kernel

/-- Two operands for a unary operation. -/
example : ¬ Func.WF #[] (fWith box (op3 Py.uSub #v[] #[0, 2])) := by decide +kernel

/-! ## Variadic operations

`mkTuple`, `mkDict`, `mkClosure` and `strConcat` end in a variadic run of operands. -/

#guard ((Py.mkTuple.sig (e := Py.env)).variadic.map (·.name)) == some "elems"
#guard ((Py.mkDict.sig (e := Py.env)).variadic.map (·.name)) == some "kvs"
#guard ((Py.mkClosure.sig (e := Py.env)).variadic.map (·.name)) == some "cells"
#guard ((Py.strConcat.sig (e := Py.env)).variadic.map (·.name)) == some "parts"

example : Func.WF #[] (fWith box (op3 Py.mkTuple #v[] #[0, 2, 0] (ks := #[]))) := by
  decide +kernel

/-- A variadic run is still typed: a base integer is not a Python value. -/
example : ¬ Func.WF #[] (fWith box (op3 Py.mkTuple #v[] #[0, 1] (ks := #[]))) := by
  decide +kernel

/-! ## `py.Completion`'s constructors

Each is an instruction of `Py.env`, with the signature `addData` derived from the group, and
`py.Completion.case` has one successor per constructor, each receiving its payload. -/

example : (Py.Completion.completionReturn.sig (e := Py.env)).typeArgc = 0 := rfl
#guard (Py.Completion.completionReturn.sig (e := Py.env)).argTypes.map (·.name) ==
  #["value"]
#guard (Py.Completion.completionNormal.sig (e := Py.env)).argTypes.isEmpty
#guard (Py.Completion.completionNormal (e := Py.env)).ctorAddr?.map (·.idx) == some 0
#guard (Py.Completion.completionContinue (e := Py.env)).ctorAddr?.map (·.idx) == some 4

/-- `return x` as a completion, then dispatched: only the `return` successor is reached. -/
private def compBlock : Block Py.env Unit where
  label  := lbl "entry"
  params := #[d 0 Py.Value.ty]
  instrs := #[.apply () (d 1 Py.Completion.ty) Py.Completion.completionReturn #v[] #[⟨0⟩] #[] #[]]
  term := .apply () Py.Completion.case #v[] #[⟨1⟩]
    #[to "normal", to "return", to "raise", to "break", to "continue"] #[]
  info := ()

/-- The successor `s`: given a payload `%n`, it returns it as a success; given none, it is
unreachable. -/
private def arm (s : String) (payload : Option Nat) : Block Py.env Unit :=
  match payload with
  | some n =>
    { label := lbl s, params := #[d n Py.Value.ty]
      instrs := #[mkOk (n + 1) n]
      term := .ret () ⟨n + 1⟩, info := () }
  | none => { label := lbl s, params := #[], instrs := #[], term := .unreachable (), info := () }

private def compFunc : Func Py.env Unit where
  name    := .str .base "comp"
  retType := Py.failing.ty
  blocks  := #[compBlock, arm "normal" none, arm "return" (some 2), arm "raise" (some 4),
    arm "break" none, arm "continue" none]
  names   := #[]
  info    := ()

example : Func.WF #[] compFunc := by decide +kernel

/-- `completionReturn` takes its payload: one with none is rejected. -/
example : ¬ Func.WF #[] { compFunc with blocks := compFunc.blocks.set! 0 { compBlock with
    instrs := #[.apply () (d 1 Py.Completion.ty) Py.Completion.completionReturn #v[] #[] #[] #[]] } } := by
  decide +kernel

/-! ## Membership

`simp` decides membership in `Py.env` from `Py.mem_env` alone, for a base name and a `py`
name. -/

example : bn "Unit" ∈ Py.env := by simp
example : .str (.str .base "py") "Value" ∈ Py.env := by simp
example : .str (.str .base "py") "add" ∈ Py.env := by simp
example : .str (.str .base "py") "nope" ∉ Py.env := by simp
example : bn "Nope" ∉ Py.env := by simp

end StrataPython.Mantle.PyEnvTest
