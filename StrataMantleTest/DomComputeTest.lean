/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataMantleTest.DSLTest
import StrataMantle.Env.WF
-- The checks below run the computation, the checker and the reference as compiled code.
meta import StrataMantle.Env.WF
meta import StrataMantle.WF
meta import StrataMantle.DomProps
meta import StrataMantle.DomFast
meta import StrataMantle.Build
meta import StrataMantleTest.DSLTest
meta import StrataMantleTest.DomRef
import StrataMantleTest.DomRef

set_option autoImplicit false

/-!
# Computing the dominator tree

`Body.domTree?` on hand-written control-flow graphs: a diamond, a loop, an irreducible loop, a
loop entered at two blocks (where a later pass must move a parent up, and then the parent of a
block below it), exception edges, unreachable blocks, which `Body.dropUnreached` drops, a join
finished before the blocks that jump to it, regions through the builder, one with a block its
entry does not reach, and a long chain of diamonds built in two orders.  Each case states the
parents it gives, that they agree with the set-intersection reference
(`StrataMantleTest/DomRef.lean`), and that the function is reachable and scopable.  All are
compiled checks.
-/

namespace Strata.Mantle.DomComputeTest

open Strata.Mantle.DSLTest
open Strata.Mantle.Build (freshVal freshLabel startBlock startFreshBlock emitApply emitConst
  finishBlock region goto build FailedFunc)

private abbrev E := Demo.env




private def d (n : Nat) : ValDecl E := ⟨⟨n⟩, Demo.Value⟩

private def lbl (s : String) : Label := ⟨.str .base s⟩

/-- Block `s` after `k` instructions. -/
private def pt (s : String) (k : Nat) : Point := ⟨lbl s, k⟩

/-- `%r = add %a %b ^h()`. -/
private def add (r a b : Nat) (h : String) : Instruction E Unit :=
  .apply () (d r) Demo.add ⟨#[], rfl⟩ #[⟨a⟩, ⟨b⟩] #[⟨lbl h, #[]⟩] #[]

/-- `ret %x`. -/
private def ret (x : Nat) : Terminator E Unit := .ret () ⟨x⟩

/-- `jump ^s()`. -/
private def jump (s : String) : Terminator E Unit := .jump () ⟨lbl s, #[]⟩

/-- `br %c ^t() ^f()`. -/
private def br (c : Nat) (t f : String) : Terminator E Unit :=
  .apply () Demo.br ⟨#[], rfl⟩ #[⟨c⟩] #[⟨lbl t, #[]⟩, ⟨lbl f, #[]⟩] #[]

/-- Block `s` with parameters `ps` (ids), instructions `is` and terminator `t`. -/
private def blk (s : String) (ps : Array Nat) (is : Array (Instruction E Unit))
    (t : Terminator E Unit) : Block E Unit :=
  { label := lbl s, params := ps.map d, instrs := is, term := t, info := () }

/-- The parents `domTree?` gives the blocks the entry reaches, in their order. -/
private def idoms (bs : List (Block E Unit)) : List (Option Point) :=
  let kept := Body.dropUnreached bs
  match Body.domTree? kept with
  | some t => kept.map (t ·.label)
  | none => []

/-- The parents `domTree?` gives agree with the set-intersection reference. -/
private def agrees (bs : List (Block E Unit)) : Bool :=
  (DomRef.idomMismatches (Body.dropUnreached bs).toArray).isEmpty

/-- The function of the blocks the entry reaches. -/
private def fn (bs : List (Block E Unit)) : Func E Unit :=
  { name := .str .base "f", retType := Demo.Value, blocks := (Body.dropUnreached bs).toArray,
    names := #[], info := () }

/-- Whether the function is reachable and scopable, as `Func.WF` asks. -/
private def rule (fn : Func E Unit) : Bool := decide (fn.Reachable ∧ fn.Scopable)

/-! ## A diamond

`entry` computes `%1`, then branches to `l` and `r`, which both jump to `j`.  All three are
under the branch, so `j` sees `%1`; the handler is under the `add` that fails to it. -/

private def diamond : List (Block E Unit) :=
  [blk "entry" #[0] #[add 1 0 0 "h"] (br 0 "l" "r"),
   blk "l" #[] #[] (jump "j"), blk "r" #[] #[add 2 1 1 "h"] (jump "j"),
   blk "j" #[] #[] (ret 1), blk "h" #[3] #[] (ret 3)]

#guard idoms diamond =
    [none, pt "entry" 1, pt "entry" 1, pt "entry" 1, pt "entry" 0]
#guard rule (fn diamond)
#guard agrees diamond

/-! ## A loop

`head` is entered from the entry and from `body`'s back edge, so it is under the entry's jump;
`body` and `exit` are under `head`'s branch, after `%2`. -/

private def loop : List (Block E Unit) :=
  [blk "entry" #[0] #[add 1 0 0 "h"] (jump "head"),
   blk "head" #[] #[add 2 1 1 "h"] (br 0 "body" "exit"),
   blk "body" #[] #[add 3 2 2 "h"] (jump "head"),
   blk "exit" #[] #[] (ret 2), blk "h" #[4] #[] (ret 4)]

#guard idoms loop =
    [none, pt "entry" 1, pt "head" 1, pt "head" 1, pt "entry" 0]
#guard rule (fn loop)
#guard agrees loop

/-! ## An irreducible loop

`a` and `b` jump to each other, and the entry enters both, so neither dominates the other. -/

private def irreducible : List (Block E Unit) :=
  [blk "entry" #[0] #[add 1 0 0 "h"] (br 0 "a" "b"),
   blk "a" #[] #[add 2 1 1 "h"] (br 0 "b" "x"), blk "b" #[] #[] (br 0 "a" "x"),
   blk "x" #[] #[] (ret 1), blk "h" #[3] #[] (ret 3)]

#guard idoms irreducible =
    [none, pt "entry" 1, pt "entry" 1, pt "entry" 1, pt "entry" 0]
#guard rule (fn irreducible)
#guard agrees irreducible

/-! ## A loop entered twice

`b` and `c` form a loop that `a` enters at `b` and the entry at `c`, and `w` is entered from `a`
and `b`.  Taken in block order, the first pass puts `b` under `a` and `w` under `a`; the next
pass moves `b` up to the entry, for `c`'s jump, and then `w`, for `b`'s. -/

private def twice : List (Block E Unit) :=
  [blk "entry" #[0] #[] (br 0 "a" "c"), blk "a" #[] #[] (br 0 "b" "w"),
   blk "b" #[] #[] (br 0 "c" "w"), blk "w" #[] #[] (ret 0), blk "c" #[] #[] (jump "b")]

#guard idoms twice =
    [none, pt "entry" 0, pt "entry" 0, pt "entry" 0, pt "entry" 0]
#guard rule (fn twice)
#guard agrees twice

/-! ## Exception edges

An instruction's successor leaves from before it, so a handler of the second `add` sees the
first's result but not the second's.  A handler that two blocks fail to is under their nearest
common ancestor. -/

private def raising : List (Block E Unit) :=
  [blk "entry" #[0] #[add 1 0 0 "h", add 2 1 1 "h2"] (jump "b"),
   blk "b" #[] #[add 3 2 2 "h2"] (ret 3),
   blk "h" #[4] #[] (ret 4), blk "h2" #[5] #[] (ret 1)]

#guard idoms raising = [none, pt "entry" 2, pt "entry" 0, pt "entry" 1]
#guard rule (fn raising)
#guard agrees raising

/-! ## Unreachable blocks

The entry reaches neither `u` nor `v`, so `Body.dropUnreached` drops them, with their jumps.
`j` is then entered only from the entry's jump, and sees `%1`. -/

private def entryJ : Block E Unit := blk "entry" #[0] #[add 1 0 0 "h"] (jump "j")
private def j : Block E Unit := blk "j" #[] #[] (ret 0)
private def h : Block E Unit := blk "h" #[3] #[] (ret 3)

private def unreached : List (Block E Unit) :=
  [entryJ, blk "u" #[] #[] (jump "j"), blk "v" #[] #[] (jump "u"), j, h]

#guard (Body.dropUnreached unreached).map (·.label) = [lbl "entry", lbl "j", lbl "h"]
-- Kept, they make the function unreachable.
#guard !rule { fn unreached with blocks := unreached.toArray }
#guard idoms unreached = [none, pt "entry" 1, pt "entry" 0]
#guard rule (fn unreached)
#guard agrees unreached

/-! ## A join finished before the blocks that jump to it

`d` computes `%1` and branches to `q1` and `q2`, which both jump to `j`, so `j` is under `d`
after `%1`, and sees it.  Finished after `q1` and `q2` or before them, `j` gets the same
parent: the computation runs in the depth-first search's reverse postorder from the entry, not
in the order the blocks were finished. -/

private def joinLast : List (Block E Unit) :=
  [blk "entry" #[0] #[] (jump "d"), blk "d" #[] #[add 1 0 0 "h"] (br 0 "q1" "q2"),
   blk "q1" #[] #[] (jump "j"), blk "q2" #[] #[] (jump "j"), blk "j" #[] #[] (ret 1),
   blk "h" #[3] #[] (ret 3)]

#guard idoms joinLast =
    [none, pt "entry" 0, pt "d" 1, pt "d" 1, pt "d" 1, pt "d" 0]
#guard rule (fn joinLast)
#guard agrees joinLast

private def joinFirst : List (Block E Unit) :=
  [blk "entry" #[0] #[] (jump "d"), blk "d" #[] #[add 1 0 0 "h"] (br 0 "q1" "q2"),
   blk "j" #[] #[] (ret 1), blk "q1" #[] #[] (jump "j"), blk "q2" #[] #[] (jump "j"),
   blk "h" #[3] #[] (ret 3)]

#guard idoms joinFirst =
    [none, pt "entry" 0, pt "d" 1, pt "d" 1, pt "d" 1, pt "d" 0]
#guard rule (fn joinFirst)
#guard agrees joinFirst

/-- The same shape through the builder, `j` finished last or first: `j` returns `v`, which `d`
defines. -/
private def joinBuilt (first : Bool) :
    Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF} :=
  build (.str .base "f") Base.Int () do
    let c ← freshVal (.str .base "c") Base.Bool
    let d ← freshLabel "d"
    let q1 ← freshLabel "q1"
    let q2 ← freshLabel "q2"
    let j ← freshLabel "j"
    let _ ← startFreshBlock #[c] "entry"
    finishBlock (.jump () (goto d))
    startBlock d
    let v ← emitConst (.str .base "v") (.int 1)
    finishBlock (.branch () c.id (goto q1) (goto q2))
    let join := do
      startBlock j
      finishBlock (.ret () v)
    if first then join
    startBlock q1
    finishBlock (.jump () (goto j))
    startBlock q2
    finishBlock (.jump () (goto j))
    if !first then join

#guard match joinBuilt false with
  | .ok f => (DomRef.idomMismatches f.1.blocks).isEmpty
  | .error _ => false
#guard match joinBuilt true with
  | .ok f => (DomRef.idomMismatches f.1.blocks).isEmpty
  | .error _ => false

/-! ## A region, through the builder

Each region's blocks get a tree of their own, rooted at the region's entry: `t2` is entered from
`t` before and after its `add`, so it is under `t` before it. -/

private def withRegion : Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF} :=
  build (.str .base "f") Demo.Value () do
    let x ← freshVal (.str .base "x") Demo.Value
    let c ← freshVal (.str .base "c") Base.Bool
    let _ ← startFreshBlock #[x, c] "entry"
    let thn := region #[] (base := "t") do
      let t2 ← freshLabel "t2"
      -- `add` fails to `t2` with the exception; the jump passes `%x`.
      let _ ← emitApply (.str .base "s") Demo.Value Demo.add #[x.id, x.id] #[goto t2]
      finishBlock (.jump () (goto t2 #[x.id]))
      let v ← freshVal (.str .base "v") Demo.Value
      startBlock t2 #[v]
      finishBlock (.ret () v.id)
    let els := region #[] (finishBlock (.ret () x.id)) "e"
    let r ← emitApply (.str .base "r") Demo.Value Demo.«if» #[c.id] (regions := #[thn, els])
    finishBlock (.ret () r)

/-- Block `s.0` after `k` instructions, as the builder names it. -/
private def bpt (s : String) (k : Nat) : Point := ⟨⟨.num (.str .base s) 0⟩, k⟩

/-- The parents `domTree?` gives a region's blocks, in their order. -/
private def regionIdoms (bs : List (Block E Unit)) : List (Option Point) :=
  match Body.domTree? bs with
  | some t => bs.map (t ·.label)
  | none => []

-- The build succeeds, so the function is well formed.
#guard match withRegion with
  | .ok f => decide (f.1.blocks.toList.flatMap (fun b => b.instrs.toList.flatMap
      fun i => i.regions.toList.map fun r => regionIdoms r.blocks.toList) =
    [[none, some (bpt "t" 0)], [none]]) && (DomRef.idomMismatches f.1.blocks).isEmpty
  | .error _ => false

/-! A region with a block its entry does not reach: the builder drops `dead.0`, which jumps to
`t2.0`, so `t2.0` is still under `t.0` before its `add`. -/

private def withDeadRegion : Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF} :=
  build (.str .base "f") Demo.Value () do
    let x ← freshVal (.str .base "x") Demo.Value
    let c ← freshVal (.str .base "c") Base.Bool
    let _ ← startFreshBlock #[x, c] "entry"
    let thn := region #[] (base := "t") do
      let t2 ← freshLabel "t2"
      let _ ← emitApply (.str .base "s") Demo.Value Demo.add #[x.id, x.id] #[goto t2]
      finishBlock (.jump () (goto t2 #[x.id]))
      let d ← freshVal (.str .base "d") Demo.Value
      startBlock (← freshLabel "dead") #[d]
      finishBlock (.jump () (goto t2 #[d.id]))
      let v ← freshVal (.str .base "v") Demo.Value
      startBlock t2 #[v]
      finishBlock (.ret () v.id)
    let els := region #[] (finishBlock (.ret () x.id)) "e"
    let r ← emitApply (.str .base "r") Demo.Value Demo.«if» #[c.id] (regions := #[thn, els])
    finishBlock (.ret () r)

#guard match withDeadRegion with
  | .ok f => decide (f.1.blocks.toList.flatMap (fun b => b.instrs.toList.flatMap
      fun i => i.regions.toList.map fun r => regionIdoms r.blocks.toList) =
    [[none, some (bpt "t" 0)], [none]]) && (DomRef.idomMismatches f.1.blocks).isEmpty
  | .error _ => false

/-! ## A chain of diamonds

Each diamond's arms `l` and `r` jump to its join `j`, which defines a value and passes the value
the join before it defined to the next diamond's `l`.  So each join is under the join before
it, after its value, and in scope there only if its parent is exactly that point.  Built with
each join finished after its arms or before them, every parent agrees with the reference. -/

/-- The diamonds `k` to `1` of the chain, entered at the arms `l` and `r`, `w` the value the
block before them defines. -/
private def diamonds (c : ValId) (joinFirst : Bool) :
    Nat → Label → Label → ValId → BuildM E Unit Unit
  | 0, _, _, _ => pure ()
  | k + 1, l, r, w => do
    let j ← freshLabel "j"
    let l₁ ← freshLabel "l"
    let r₁ ← freshLabel "r"
    let join : BuildM E Unit ValId := do
      startBlock j
      let w₁ ← emitConst (.str .base "w") (.int k)
      finishBlock (if k = 0 then .ret () w else .branch () c (goto l₁ #[w]) (goto r₁))
      pure w₁
    let arms : BuildM E Unit Unit := do
      startBlock l #[← freshVal (.str .base "p") Base.Int]
      finishBlock (.jump () (goto j))
      startBlock r
      finishBlock (.jump () (goto j))
    let w₁ ← if joinFirst then do let w₁ ← join; arms; pure w₁ else do arms; join
    diamonds c joinFirst k l₁ r₁ w₁

/-- A chain of `n` diamonds after the entry. -/
private def chain (n : Nat) (joinFirst : Bool) :
    Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF} :=
  build (.str .base "f") Base.Int () do
    let c ← freshVal (.str .base "c") Base.Bool
    let l ← freshLabel "l"
    let r ← freshLabel "r"
    let _ ← startFreshBlock #[c] "entry"
    let w ← emitConst (.str .base "w") (.int 0)
    finishBlock (.branch () c.id (goto l #[w]) (goto r))
    diamonds c.id joinFirst n l r w

#guard match chain 100 false with
  | .ok f => f.1.blocks.size == 301 && (DomRef.idomMismatches f.1.blocks).isEmpty
  | .error _ => false
#guard match chain 100 true with
  | .ok f => f.1.blocks.size == 301 && (DomRef.idomMismatches f.1.blocks).isEmpty
  | .error _ => false

end Strata.Mantle.DomComputeTest
