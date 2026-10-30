/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Base
import StrataDyn.Env.WF
import StrataDyn.DSL
public import StrataDyn.Exec
public import StrataDyn.Exec.Base

set_option autoImplicit false

/-!
# The While environment and its rules

`While` refines `Base` with what the While language needs and the base lacks:

* the datatypes `IntList` and `Flow`, how a body region ended: `next`, or `raise e`;
* integer arithmetic and comparisons, and the boolean operations;
* `div` and `mod`, which leave along `^err` with `1` on a zero divisor;
* `pow`, whose rule is a `semanticGap`: a run that reaches it faults with `Fault.gap`;
* `print`, `tick` and `pick`, which reach the world and the oracle;
* `Cell`, an abbreviation of `Ref Int`, whose cells rules make, read and write, with
  `cellNew`, `cellGet` and `cellSet`: a rule that allocates and returns a cell;
* `if` and `loop`, operations on regions.  `if` runs one of its two body regions, and `loop`
  runs its body region while its condition region yields `true`.  A body region yields a
  `Flow`, and an operation raises a `Flow.raise e` along its `^err`.  `loop`'s rule runs one
  iteration and then jumps to its `Again`, with the state `()`, so each iteration is a step of
  the machine.

Everything else is the base's: its types, `base.Ref` cells on the machine's heap, calls through
`base.callCode`, `base.Except` for functions that raise, and the rules of its control flow, which
`WhileSem` inherits.  While's world, `WhileRules.World`, has two parts, `Output` and `Ticks`;
Base's rules need none.

`WhileSem` is the generated table, and `#dyn_coverage` checks that it covers `While` and
`Base` completely.
-/

namespace Strata.Dyn

/-- The While language's operations. -/
public environment While extends Base where
  namespace «while»
  open base
  /-- A list of integers. -/
  data IntList where
    | nil
    | cons (head : Int) (tail : IntList)
  /-- How a body region ended: it fell off its end, or raised `e`. -/
  data Flow where
    | next
    | raise (e : Int)
  insn add (lhs rhs : Int) : Int
  insn sub (lhs rhs : Int) : Int
  insn mul (lhs rhs : Int) : Int
  insn neg (x : Int) : Int
  /-- `lhs / rhs`, or `^err` with `1` if `rhs` is `0`. -/
  insn div (lhs rhs : Int) (^err (code : Int)) : Int
  /-- `lhs % rhs`, or `^err` with `1` if `rhs` is `0`. -/
  insn mod (lhs rhs : Int) (^err (code : Int)) : Int
  /-- Exponentiation, which the semantics leaves out. -/
  insn pow (lhs rhs : Int) : Int
  insn lt (lhs rhs : Int) : Bool
  insn le (lhs rhs : Int) : Bool
  insn eq (lhs rhs : Int) : Bool
  insn ne (lhs rhs : Int) : Bool
  insn not_ as "not" (x : Bool) : Bool
  insn and_ as "and" (lhs rhs : Bool) : Bool
  insn or_ as "or" (lhs rhs : Bool) : Bool
  /-- Append `x` to the run's output. -/
  insn print (x : Int) : Unit
  /-- Count, and return how often `tick` has run. -/
  insn tick : Int
  /-- A number from `0` to `n`, chosen by the oracle. -/
  insn pick (n : Int) : Int
  /-- A cell of an `Int`, which the rules make on the machine's heap. -/
  abbrev Cell := Ref Int
  insn cellNew (value : Int) : Cell
  insn cellGet (cell : Cell) : Int
  insn cellSet (cell : Cell) (value : Int) : Unit
  /-- Run `then` if `cond` holds and `else` otherwise; a raise leaves along `^err`. -/
  insn «if» (cond : Bool) (&«then» &«else» : Flow) (^err (code : Int)) : Unit
  /-- Run `body` while `cond` yields `true`; a raise leaves along `^err`. -/
  insn loop (&cond : Bool) (&body : Flow) (^err (code : Int)) : Unit
  end «while»

-- The types' codes, and `IntList` and `Flow`'s Lean types, `While.IntList.Val` and
-- `While.Flow.Val`.
#dyn_types While

namespace WhileRules

open Strata.Dyn.Exec

/-- How a body region ended. -/
public abbrev Flow := While.Flow.Val

/-- `while.Cell`'s Lean type at the token `σ`: a ref to a cell of the machine's heap holding an
`Int`. -/
public abbrev Cell (σ : Type) [Store σ] : Type := Ref σ Int

@[expose] public section

/-- What a run has printed, oldest first. -/
structure Output where
  items : Array Int := #[]
  deriving Inhabited, Repr, DecidableEq

/-- How often `while.tick` ran. -/
structure Ticks where
  n : Nat := 0
  deriving Inhabited, Repr, DecidableEq

/-- While's world. -/
structure World where
  out : Output := {}
  ticks : Ticks := {}
  deriving Inhabited, Repr, DecidableEq

#dyn_world World

variable {ε : Eff} {E : Type}

@[dyn_sem While.add] def add (a b : Int) : Int := a + b
@[dyn_sem While.sub] def sub (a b : Int) : Int := a - b
@[dyn_sem While.mul] def mul (a b : Int) : Int := a * b
@[dyn_sem While.neg] def neg (a : Int) : Int := -a
@[dyn_sem While.lt] def lt (a b : Int) : Bool := decide (a < b)
@[dyn_sem While.le] def le (a b : Int) : Bool := decide (a ≤ b)
@[dyn_sem While.eq] def eq (a b : Int) : Bool := decide (a = b)
@[dyn_sem While.ne] def ne (a b : Int) : Bool := !decide (a = b)
@[dyn_sem While.not_] def not (a : Bool) : Bool := !a
@[dyn_sem While.and_] def and (a b : Bool) : Bool := a && b
@[dyn_sem While.or_] def or (a b : Bool) : Bool := a || b

/-- While's capabilities, as one class: its world's two parts, the machine's cells, and the tag
of `Int`, the one Lean type its rules' cells hold.  Its fields are instances, so a rule that
takes it has each capability, and the rule's wrapper builds it. -/
@[dyn_lang] class Lang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  out : HasPart ε.W Output
  ticks : HasPart ε.W Ticks
  heap : HasHeap σ ε
  tagInt : TagOf σ Int

variable {σ : Type} [Store σ] [Decode σ] [Lang σ ε]

/-- What `/` and `%` raise on a zero divisor. -/
def divByZero : Int := 1

@[dyn_sem While.div] def div (a b : Int) (err : Target E [Int]) : Sem ε E Int := do
  if b = 0 then jump err divByZero
  return a / b

@[dyn_sem While.mod] def mod (a b : Int) (err : Target E [Int]) : Sem ε E Int := do
  if b = 0 then jump err divByZero
  return a % b

@[dyn_sem While.pow] def pow (_a _b : Int) : Sem ε E Int :=
  semanticGap "while.pow: not implemented"

@[dyn_sem While.print] def print (x : Int) : Sem ε E Unit :=
  modifyThe Output fun o => { o with items := o.items.push x }

@[dyn_sem While.tick] def tick : Sem ε E Int := do
  let t ← modifyGetThe Ticks fun t => (t.n + 1, { n := t.n + 1 })
  return t

/-- A number from `0` to `n`, chosen by the oracle; `0` if `n` is negative. -/
@[dyn_sem While.pick] def pick (n : Int) : Sem ε E Int := do
  let k ← choose n.toNat
  return k.val

/-- A new cell holding `v`, on the machine's heap. -/
@[dyn_sem While.cellNew] def cellNew (v : Int) : Sem ε E (Cell σ) := newRef v

/-- The contents of cell `c`, which the machine checks. -/
@[dyn_sem While.cellGet] def cellGet (c : Cell σ) : Sem ε E Int := readRef c

@[dyn_sem While.cellSet] def cellSet (c : Cell σ) (v : Int) : Sem ε E Unit := writeRef c v

/-- Leave along `err` if a body region raised. -/
def flow (f : Flow) (err : Target E [Int]) : Sem ε E Unit := do
  if let .raise e := f then jump err e

@[dyn_sem While.if]
def «if» (c : Bool) (thenR elseR : Region ε [] Flow) (err : Target E [Int]) :
    Sem ε E Unit := do
  flow (← runRegion (if c then thenR else elseR) ()) err

/-- One iteration: if the condition holds, run the body and the operation again.  Its state
is `Unit`: a loop's variables are cells. -/
@[dyn_sem While.loop]
def loop (cond : Region ε [] Bool) (body : Region ε [] Flow) (err : Target E [Int])
    (_st : Option Unit) (again : Again E Unit) : Sem ε E Unit := do
  if ← runRegion cond () then
    flow (← runRegion body ()) err
    jump again ()

end

end WhileRules

#dyn_coverage While (complete)

public section

#dyn_sem_table WhileSem for While (world := WhileRules.World)

end

end Strata.Dyn
