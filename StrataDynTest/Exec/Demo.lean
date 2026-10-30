/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Env.Handle
import StrataDyn.Env.WF
import StrataDyn.DSL
public import StrataDyn.Exec

set_option autoImplicit false

/-!
# A small environment and its rules

`Demo` declares one of each kind of instruction a rule can implement: pure, raising, with a
two-value payload, polymorphic, variadic, terminal, with a region, and a semantic gap; a
datatype with a parameter and a recursive one; and an instruction with no rule.  `DemoChild`
extends it.  The table and registration tests read them.
-/

namespace Strata.Dyn.ExecTest

/-- A demo language, with no parent. -/
public environment Demo where
  namespace demo
  type Int
  type Bool
  type Seq (+a)
  data Box (+a) where
    | box (contents : a)
    | empty
  data IntList where
    | nil
    | cons (head : Int) (tail : IntList)
  insn add (lhs rhs : Int) : Int
  insn div (lhs rhs : Int) (^err (code : Int)) : Int
  insn divBig (lhs rhs : Int) (^err (code : Int)) (^big (q r : Int)) : Int
  insn pick [a] (cond : Bool) (x y : a) : a
  insn unbox [a] (b : Box a) (^none) : a
  insn sum (*xs : Int) : Int
  insn pow (lhs rhs : Int) : Int
  insn isqrt (x : Int) : Int
  insn loop [a] (&body (i : Int) : a) : a
  terminal insn branch (cond : Bool) (^t ^f)
  end demo

/-- A child of `Demo`. -/
public environment DemoChild extends Demo where
  namespace child
  open demo
  insn neg (x : Int) : Int
  insn abs (x : Int) : Int
  end child

attribute [dyn_type Demo.Int] Int
attribute [dyn_type Demo.Bool] Bool
attribute [dyn_type Demo.Seq] Array

-- The codes, and the datatypes `Demo.Box.Val` and `Demo.IntList.Val`.
#dyn_types Demo

/-- `demo.Box`'s Lean type. -/
public abbrev DBox := Demo.Box.Val

/-- `demo.IntList`'s Lean type. -/
public abbrev DList := Demo.IntList.Val

namespace Rules

open Strata.Dyn.Exec

@[expose] public section

variable {ε : Eff} {E : Type}

@[dyn_sem Demo.add] def add (a b : Int) : Int := a + b

@[dyn_sem Demo.div] def div (a b : Int) (err : Target E [Int]) : Sem ε E Int := do
  if b = 0 then jump err 1
  return a / b

@[dyn_sem Demo.divBig]
def divBig (a b : Int) (err : Target E [Int]) (big : Target E [Int, Int]) : Sem ε E Int := do
  if b = 0 then jump err 1
  if a > 100 then jump big (a / b, a % b)
  return a / b

@[dyn_sem Demo.pick] def pick {α : Type} (c : Bool) (x y : α) : α := if c then x else y

@[dyn_sem Demo.unbox] def unbox {α : Type} (b : DBox α) (none : Target E []) : Sem ε E α :=
  match b with
  | .box x => pure x
  | .empty => jump none ()

@[dyn_sem Demo.sum] def sum (xs : Array Int) : Int := xs.foldl (· + ·) 0

@[dyn_sem Demo.pow] def pow (_a _b : Int) : Sem ε E Int := semanticGap "demo.pow"

@[dyn_sem Demo.loop] def loop {α : Type} (body : Region ε [Int] α) : Sem ε E α :=
  runRegion body 0

@[dyn_sem Demo.branch] def branch (c : Bool) (t f : Target E []) : Sem ε E Empty :=
  if c then jump t () else jump f ()

@[dyn_sem DemoChild.neg] def neg (a : Int) : Int := -a

end

end Rules

end Strata.Dyn.ExecTest
