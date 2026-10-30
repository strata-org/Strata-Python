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
# A small environment to run

`Ex` extends `Base` with one instruction per thing the machine does: pure arithmetic, a
raising division, a print and a counter in the world, choices, an assumption, a gap, a loop
over two regions, two comprehensions and a fold, each with a state of its rule's own, calls of
closures, their partial application and a closure over a list of cells, three terminators of
its own, and an instruction with no rule.  For the heap it has rules that make, read and write
cells, one that hands a cell it made to a region,
updates a cell in place, generic rules at any type, a rule that retypes a ref, and datatypes
that hold a ref, a closure, refs of a type parameter, a ref of themselves and a closure that
returns themselves.  Its rules and its table, `ExSem`, are here; `RunTest.lean`
and `HeapTest.lean` run modules against them.

The base's rules come from `StrataDyn.Exec.Base`.  The programs take their control flow from
`Ex`'s own terminators, which are rules as the base's are: the machine has no terminator built
in.
-/

namespace Strata.Dyn.ExecTest

/-- A language to run. -/
public environment Ex extends Base where
  namespace ex
  open base
  insn add (lhs rhs : Int) : Int
  insn sub (lhs rhs : Int) : Int
  insn mul (lhs rhs : Int) : Int
  insn rem (lhs rhs : Int) : Int
  insn lt (lhs rhs : Int) : Bool
  insn le (lhs rhs : Int) : Bool
  insn ne (lhs rhs : Int) : Bool
  /-- `lhs / rhs`, or `^err` with `1` if `rhs` is `0`. -/
  insn div (lhs rhs : Int) (^err (code : Int)) : Int
  /-- Append `x` to the world's output. -/
  insn print (x : Int) : Unit
  /-- Count, in the world, and return the count. -/
  insn tick : Int
  /-- A number from `0` to `n`, by the oracle. -/
  insn pick (n : Int) : Int
  /-- A natural number, by the oracle, unbounded. -/
  insn pickNat : Int
  /-- An integer, by the oracle, unbounded. -/
  insn pickInt : Int
  /-- Continue if `b` holds; otherwise the path is infeasible. -/
  insn assume (b : Bool) : Unit
  /-- Not covered by the semantics. -/
  insn gap (x : Int) : Int
  /-- Run `body` while `cond` yields `true`. -/
  insn loop (&cond : Bool) (&body : Unit) : Unit
  /-- `0, …, n - 1`. -/
  insn range (n : Int) : Sequence Int
  /-- `xs` in base 100, its first element the most significant: a number that shows the
  elements in order. -/
  insn pack (xs : Sequence Int) : Int
  /-- A comprehension: the results of `body` on each element of `xs`, in order.  A body's
  `error` raises along `^err`. -/
  insn mapList (xs : Sequence Int) (&body (x : Int) : Except Int Int) (^err (code : Int)) :
    Sequence Int
  /-- `body` on each of `0, …, n - 1`, as `mapList` does. -/
  insn mapRange (n : Int) (&body (x : Int) : Except Int Int) (^err (code : Int)) : Sequence Int
  /-- A fold over an accumulator: from `init`, while `cond` holds of the accumulator, replace
  it by `body`'s result on it; the last accumulator. -/
  insn fold (init : Int) (&cond (acc : Int) : Bool) (&body (acc : Int) : Int) : Int
  /-- Call `f` on `x`; its `error` raises along `^err`. -/
  insn call (f : Fn [Int] (Except Int Int)) (x : Int) (^err (code : Int)) : Int
  /-- Call `f`, which cannot raise, on `x`. -/
  insn callInt (f : Fn [Int] Int) (x : Int) : Int
  /-- `f` with its first argument bound to `x`, at any types. -/
  insn bind [a b r] (f : Fn [a, b] r) (x : a) : Fn [b] r
  /-- `code` with its first arguments bound to `cells`, one per element of `cs`: the shape of
  Python's `mkClosure`. -/
  insn mkClo [(cs : list)] (code : Fn [*cs, Int] Int) (*cells : cs) : Fn [Int] Int
  /-- Continue at `k`. -/
  terminal insn goto (^k)
  /-- Continue at `t` if `cond` holds, else at `f`. -/
  terminal insn br (cond : Bool) (^t ^f)
  /-- Control never gets here. -/
  terminal insn halt
  /-- Has no rule. -/
  insn nope (x : Int) : Int
  /-- A new cell holding `v`, which a rule makes. -/
  insn cellNew (v : Int) : Ref Int
  /-- The contents of `c`, which a rule reads. -/
  insn cellGet (c : Ref Int) : Int
  /-- Replace the contents of `c` with `v`, as a rule. -/
  insn cellSet (c : Ref Int) (v : Int) : Unit
  /-- Add `d` to the contents of `c`, as a rule, in one request. -/
  insn cellAdd (c : Ref Int) (d : Int) : Unit
  /-- Push `x` onto the sequence in `c`, as a rule, in one request. -/
  insn cellPush (c : Ref (Sequence Int)) (x : Int) : Unit
  /-- `c`, as a ref of `Bool`: a rule that retypes a ref, which no rule should do. -/
  insn retype (c : Ref Int) : Ref Bool
  /-- Make a cell holding `v`, run `body` on it, and add the body's result to the cell's final
  contents. -/
  insn withCell (v : Int) (&body (c : Ref Int) : Int) : Int
  /-- A new cell holding `v`, of any type, which a generic rule makes. -/
  insn newAt [a] (v : a) : Ref a
  /-- The contents of `c`, of any type, which a generic rule reads. -/
  insn getAt [a] (c : Ref a) : a
  /-- A ref in a datatype. -/
  data Slot where
    | slot (c : Ref Int)
  /-- A closure in a datatype. -/
  data Clo where
    | clo (f : Fn [Int] Int)
  /-- A ref of a type parameter. -/
  data Box (a) where
    | box (c : Ref a)
  /-- Two refs of a type parameter. -/
  data Two (a) where
    | two (x y : Ref a)
  /-- A box of a new cell holding `b`'s contents. -/
  insn dup [a] (b : Box a) : Box a
  /-- `t`'s refs, the other way round. -/
  insn swap [a] (t : Two a) : Two a
  /-- A new cell holding a box of a new cell holding `v`. -/
  insn boxCell [a] (v : a) : Ref (Box a)
  /-- A chain of cells: each link holds a ref of the next. -/
  data Chain where
    | done
    | link (next : Ref Chain)
  /-- A closure that returns its own type. -/
  data Thunk where
    | thunk (f : Fn [Int] Thunk)
  end ex

#dyn_types Ex

namespace ExRules

open Strata.Dyn.Exec

@[expose] public section

/-- What a run has printed, oldest first. -/
structure Output where
  items : Array Int := #[]
  deriving Inhabited, Repr, DecidableEq

/-- How often `ex.tick` ran. -/
structure Ticks where
  n : Nat := 0
  deriving Inhabited, Repr, DecidableEq

/-- `Ex`'s world. -/
structure World where
  out : Output := {}
  ticks : Ticks := {}
  deriving Inhabited, Repr, DecidableEq

instance : HasPart World Output := ⟨(·.out), fun w o => { w with out := o }⟩
instance : HasPart World Ticks := ⟨(·.ticks), fun w t => { w with ticks := t }⟩

variable {ε : Eff} {E : Type}

/-- Ex's capabilities, as one class: its world's parts, the machine's cells and calls, and the
tags its rules reach cells and calls at: `Int`, `Except`'s, and `Box`'s. -/
@[dyn_lang] class Lang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  out : HasPart ε.W Output
  ticks : HasPart ε.W Ticks
  heap : HasHeap σ ε
  call : HasCall σ ε
  tagInt : TagOf σ Int
  tagSeq : TagCon σ Array
  tagExcept : TagCon₂ σ Except
  tagBox : TagCon σ (Ex.Box.Val σ)

variable {σ : Type} [Store σ] [Decode σ] [Lang σ ε]

@[dyn_sem Ex.add] def add (a b : Int) : Int := a + b
@[dyn_sem Ex.sub] def sub (a b : Int) : Int := a - b
@[dyn_sem Ex.mul] def mul (a b : Int) : Int := a * b
@[dyn_sem Ex.rem] def rem (a b : Int) : Int := a % b
@[dyn_sem Ex.lt] def lt (a b : Int) : Bool := decide (a < b)
@[dyn_sem Ex.le] def le (a b : Int) : Bool := decide (a ≤ b)
@[dyn_sem Ex.ne] def ne (a b : Int) : Bool := !decide (a = b)

@[dyn_sem Ex.div] def div (a b : Int) (err : Target E [Int]) : Sem ε E Int := do
  if b = 0 then jump err 1
  return a / b

@[dyn_sem Ex.print] def print (x : Int) : Sem ε E Unit :=
  modifyThe Output fun o => { o with items := o.items.push x }

@[dyn_sem Ex.tick] def tick : Sem ε E Int := do
  let t ← modifyGetThe Ticks fun t => (t.n + 1, { n := t.n + 1 })
  return t

@[dyn_sem Ex.pick] def pick (n : Int) : Sem ε E Int := do
  let k ← choose n.toNat
  return k.val

@[dyn_sem Ex.pickNat] def pickNat : Sem ε E Int := do
  return Int.ofNat (← chooseNat)

@[dyn_sem Ex.pickInt] def pickInt : Sem ε E Int := chooseInt

@[dyn_sem Ex.assume] def assume (b : Bool) : Sem ε E Unit := Exec.assume b "ex.assume"

@[dyn_sem Ex.gap] def gap (_x : Int) : Sem ε E Int := semanticGap "ex.gap"

/-- One iteration: if the condition holds, run the body and the operation again.  Its state
is `Unit`: the loop keeps its state in the regions' cells. -/
@[dyn_sem Ex.loop]
def loop (cond : Region ε [] Bool) (body : Region ε [] Unit) (_st : Option Unit)
    (again : Again E Unit) : Sem ε E Unit := do
  if ← runRegion cond () then
    runRegion body ()
    jump again ()

/-- One step of a fold: its state is the accumulator, which starts at `init`. -/
@[dyn_sem Ex.fold]
def fold (init : Int) (cond : Region ε [Int] Bool) (body : Region ε [Int] Int) (st : Option Int)
    (again : Again E Int) : Sem ε E Int := do
  let acc := st.getD init
  if ← runRegion cond acc then jump again (← runRegion body acc)
  return acc

/-! ### Comprehensions

Each run of a comprehension's rule handles one element, and jumps to its `Again` with the
elements left and the results so far, so each element is a step of the machine and the
comprehension's state is its rule's own. -/

@[dyn_sem Ex.range] def range (n : Int) : Array Int := (Array.range n.toNat).map Int.ofNat

@[dyn_sem Ex.pack] def pack (xs : Array Int) : Int := xs.foldl (fun a x => a * 100 + x) 0

/-- One element of a comprehension whose state is `(xs, acc)`, the elements left and the
results so far: `acc` if `xs` is empty, or else `body` on the first element of `xs`, then a
jump to `again` with the rest and `acc` with the body's result, or `^err` if the body
raised. -/
def mapStep (xs acc : Array Int) (body : Region ε [Int] (Except Int Int)) (err : Target E [Int])
    (again : Again E (Array Int × Array Int)) : Sem ε E (Array Int) := do
  match xs[0]? with
  | none => return acc
  | some x =>
    match ← runRegion body x with
    | .ok y => jump again (xs.extract 1, acc.push y)
    | .error e => jump err e

/-- Its first run starts from all of `xs` and no results. -/
@[dyn_sem Ex.mapList]
def mapList (xs : Array Int) (body : Region ε [Int] (Except Int Int)) (err : Target E [Int])
    (st : Option (Array Int × Array Int)) (again : Again E (Array Int × Array Int)) :
    Sem ε E (Array Int) :=
  let (rest, acc) := st.getD (xs, #[])
  mapStep rest acc body err again

/-- Its first run sets the state up, from `n`, and jumps to its `Again` with it; each later run
handles one element, as `mapList`'s does. -/
@[dyn_sem Ex.mapRange]
def mapRange (n : Int) (body : Region ε [Int] (Except Int Int)) (err : Target E [Int])
    (st : Option (Array Int × Array Int)) (again : Again E (Array Int × Array Int)) :
    Sem ε E (Array Int) :=
  match st with
  | none => jump again (range n, #[])
  | some (rest, acc) => mapStep rest acc body err again

section

-- The machine checks each call against the signature's tags.
@[dyn_sem Ex.call]
def call (f : FnRef σ [Int] (Except Int Int)) (x : Int) (err : Target E [Int]) :
    Sem ε E Int := do
  match ← callFn f x with
  | .ok v => return v
  | .error e => jump err e

@[dyn_sem Ex.callInt]
def callInt (f : FnRef σ [Int] Int) (x : Int) : Sem ε E Int := callFn f x

/-- A partial application at any types: the tags of the closure's signatures come from the
type arguments'. -/
@[dyn_sem Ex.bind]
def bind {A B R : Type} [TagOf σ A] [TagOf σ B] [TagOf σ R] (f : FnRef σ [A, B] R) (x : A) :
    Sem ε E (FnRef σ [B] R) :=
  bindFn f x

/-- A closure over a list of cells: one bind per cell, at the tags `TagsOf` gives. -/
@[dyn_sem Ex.mkClo]
def mkClo {cs : List Type} [TagsOf σ cs] (code : FnRef σ (cs ++ [Int]) Int) (cells : Payload cs) :
    Sem ε E (FnRef σ [Int] Int) :=
  bindAll cs code cells

end

@[dyn_sem Ex.goto] def goto (k : Target E []) : Sem ε E Empty := jump k ()

@[dyn_sem Ex.br] def br (c : Bool) (t f : Target E []) : Sem ε E Empty :=
  if c then jump t () else jump f ()

@[dyn_sem Ex.halt] def halt : Sem ε E Empty := semanticFailure "ex.halt"

section

@[dyn_sem Ex.cellNew] def cellNew (v : Int) : Sem ε E (Ref σ Int) := newRef v

@[dyn_sem Ex.cellGet] def cellGet (c : Ref σ Int) : Sem ε E Int := readRef c

@[dyn_sem Ex.cellSet] def cellSet (c : Ref σ Int) (v : Int) : Sem ε E Unit :=
  writeRef c v

@[dyn_sem Ex.cellAdd] def cellAdd (c : Ref σ Int) (d : Int) : Sem ε E Unit :=
  modifyRef c (· + d)

@[dyn_sem Ex.cellPush] def cellPush (c : Ref σ (Array Int)) (x : Int) : Sem ε E Unit :=
  modifyRef c (·.push x)

/-- A ref at another contents' type, which the machine's check at the access catches. -/
@[dyn_sem Ex.retype] def retype (c : Ref σ Int) : Ref σ Bool := ⟨c.raw⟩

@[dyn_sem Ex.withCell]
def withCell (v : Int) (body : Region ε [Ref σ Int] Int) : Sem ε E Int := do
  let c ← newRef v
  let r ← runRegion body c
  return r + (← readRef c)

/-- A new cell at any type: the rule makes a cell at `A`, so it takes `A`'s tag. -/
@[dyn_sem Ex.newAt]
def newAt {A : Type} [TagOf σ A] (v : A) : Sem ε E (Ref σ A) := newRef v

@[dyn_sem Ex.getAt]
def getAt {A : Type} [TagOf σ A] (c : Ref σ A) : Sem ε E A := readRef c

/-- It reads and makes a cell at `A`, so it takes `A`'s tag. -/
@[dyn_sem Ex.dup]
def dup {A : Type} [TagOf σ A] : Ex.Box.Val σ A → Sem ε E (Ex.Box.Val σ A)
  | .box c => do return .box (← newRef (← readRef c))

/-- It moves refs and touches no cell, so it takes no tag. -/
@[dyn_sem Ex.swap]
def swap {A : Type} : Ex.Two.Val σ A → Ex.Two.Val σ A
  | .two x y => .two y x

/-- It makes a cell at `Box A`, whose tag comes from `A`'s through `Lang.tagBox`. -/
@[dyn_sem Ex.boxCell]
def boxCell {A : Type} [TagOf σ A] (v : A) : Sem ε E (Ref σ (Ex.Box.Val σ A)) := do
  newRef (.box (← newRef v))

end

end

end ExRules

public section

/-- info: ExSem: no rule for ex.nope -/
#guard_msgs in
#dyn_sem_table ExSem for Ex (world := ExRules.World)

end

end Strata.Dyn.ExecTest
