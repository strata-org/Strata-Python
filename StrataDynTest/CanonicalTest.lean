/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Canonical
public import StrataDynTest.Blocks
import StrataDyn.Env.WF
meta import StrataDyn.Canonical
meta import StrataDynTest.Blocks

set_option autoImplicit false

/-!
# The canonical form

`Func.checkCanonicalCFG` on functions written as blocks.  First a canonical `while` loop, then
bodies that each break one property:

* P1: a second entry into the head, a block before the head with a second successor, an entry
  from inside the preheader, a preheader that runs a region before it jumps, and one that ends
  in an operation other than `jump`;
* P2: two back edges, a back edge from inside the latch, and a latch with a second successor;
* P3: an exit block that code before the loop also enters, and a block of the loop that returns;
* F2: two blocks that return, a return from inside a block, and a return block with a second
  successor.

Then a `break` with its own exit block, nested loops, a loop inside a region, and a loop with two
entries, which the form does not cover but the check of one entry per loop rejects, with edge
cases of that check.
-/

namespace Strata.Dyn.CanonicalTest

open Strata.Dyn.DSLTest Strata.Dyn.Blocks

private def canon (bs : List (Block E Unit)) : Bool := (fn bs).checkCanonicalCFG

/-! ## A canonical `while` loop

    entry: jump ^pre
    pre:   jump ^head
    head:  branch ^body ^exit
    body:  jump ^latch
    latch: jump ^head
    exit:  ret
-/

private def whileLoop : List (Block E Unit) :=
  [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
   blk "head" #[] (branch "body" "exit"), blk "body" #[] (jump "latch"),
   blk "latch" #[] (jump "head"), blk "exit" #[] ret]

#guard canon whileLoop

/-! ## P1: the head entered from two blocks outside the loop -/

#guard !canon
  [blk "entry" #[] (branch "a" "b"), blk "a" #[] (jump "head"), blk "b" #[] (jump "head"),
   blk "head" #[] (branch "latch" "exit"), blk "latch" #[] (jump "head"), blk "exit" #[] ret]

/-! ## P1: a block before the head that has another successor -/

#guard !canon
  [blk "entry" #[] (branch "head" "x"), blk "x" #[] (jump "post"),
   blk "head" #[] (branch "latch" "done"), blk "latch" #[] (jump "head"),
   blk "done" #[] (jump "post"), blk "post" #[] ret]

/-! ## P1: an entry into the head from inside the preheader -/

#guard !canon
  [blk "entry" #[] (jump "pre"), blk "pre" #[add 1 "head"] (jump "head"),
   blk "head" #[] (branch "latch" "exit"), blk "latch" #[] (jump "head"), blk "exit" #[] ret]

/-! ## P1: a preheader that runs a region before it jumps -/

#guard !canon
  [blk "entry" #[] (jump "pre"), blk "pre" #[] (loopT ⟨#[blk "r" #[] ret]⟩ "head"),
   blk "head" #[] (branch "latch" "exit"), blk "latch" #[] (jump "head"), blk "exit" #[] ret]

/-! ## P1: a preheader that ends in an operation other than `jump`

`raise %0 ^head` transfers to the head and nowhere else, but it is not a plain jump. -/

#guard !canon
  [blk "entry" #[] (jump "pre"),
   blk "pre" #[] (.apply () Demo.raise.ref ⟨#[], rfl⟩ #[⟨0⟩] #[⟨lbl "head", #[]⟩] #[]),
   blk "head" #[] (branch "latch" "exit"), blk "latch" #[] (jump "head"), blk "exit" #[] ret]

/-! ## P2: two back edges, as a `continue` makes -/

#guard !canon
  [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
   blk "head" #[] (branch "body" "exit"), blk "body" #[] (branch "cont" "rest"),
   blk "cont" #[] (jump "head"), blk "rest" #[] (jump "head"), blk "exit" #[] ret]

/-! ## P2: a back edge from inside the latch -/

#guard !canon
  [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
   blk "head" #[] (branch "latch" "exit"), blk "latch" #[add 1 "head"] (jump "head"),
   blk "exit" #[] ret]

/-! ## P2: a latch with a second successor -/

#guard !canon
  [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
   blk "head" #[] (branch "latch" "done"), blk "latch" #[] (branch "head" "done"),
   blk "done" #[] ret]

/-! ## P3: a handler that code before the loop and code in the loop both raise to -/

private def sharedHandler : List (Block E Unit) :=
  [blk "entry" #[add 1 "catch"] (jump "pre"), blk "pre" #[] (jump "head"),
   blk "head" #[add 2 "catch"] (branch "latch" "exit"), blk "latch" #[] (jump "head"),
   blk "catch" #[] (jump "exit"), blk "exit" #[] ret]

#guard !canon sharedHandler

-- With blocks of their own between the loop and the handler, and between the loop and `exit`,
-- the exits are dedicated.
#guard canon
  [blk "entry" #[add 1 "catch"] (jump "pre"), blk "pre" #[] (jump "head"),
   blk "head" #[add 2 "raised"] (branch "latch" "done"), blk "latch" #[] (jump "head"),
   blk "raised" #[] (jump "catch"), blk "done" #[] (jump "exit"), blk "catch" #[] (jump "exit"),
   blk "exit" #[] ret]

/-! ## P3: a block of the loop that returns

`body` returns, but its failure goes to `handler`, which repeats the loop, so `body` is in the
loop.  Its return leaves the loop without passing an exit block.

    head:    jump ^body
    body:    %1 = add ^handler; ret
    handler: jump ^latch
    latch:   jump ^head
-/

#guard !canon
  [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"), blk "head" #[] (jump "body"),
   blk "body" #[add 1 "handler"] ret, blk "handler" #[] (jump "latch"),
   blk "latch" #[] (jump "head")]

/-! ## F2: two blocks that return -/

#guard !canon
  [blk "entry" #[] (branch "a" "b"), blk "a" #[] ret, blk "b" #[] ret]

-- One block that returns, after both.
#guard canon
  [blk "entry" #[] (branch "a" "b"), blk "a" #[] (jump "post"), blk "b" #[] (jump "post"),
   blk "post" #[] ret]

-- A return from inside a block, before the one at its end.
#guard !canon [blk "entry" #[] (jump "post"), blk "post" #[addExit 1] ret]

-- A return from inside a block, and one from another block.
#guard !canon [blk "entry" #[addExit 1] (jump "post"), blk "post" #[] ret]

-- A return block whose terminator has a second successor.
#guard !canon
  [blk "entry" #[] (jump "post"),
   blk "post" #[] (.branch () ⟨0⟩ ⟨Label.exit, #[⟨0⟩]⟩ ⟨lbl "x", #[]⟩),
   blk "x" #[] (.unreachable ())]

/-! ## A `break` with its own exit block

The block after a `break` is outside the loop, so `brk` is an exit of its own.

    head:  branch ^body ^done
    body:  branch ^brk ^latch
    brk:   jump ^after
    done:  jump ^after
-/

#guard canon
  [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
   blk "head" #[] (branch "body" "done"), blk "body" #[] (branch "brk" "latch"),
   blk "latch" #[] (jump "head"), blk "brk" #[] (jump "after"), blk "done" #[] (jump "after"),
   blk "after" #[] ret]

-- Without `done`, the guard's false edge and the `break` share `after`.  It is still entered
-- only from the loop, so it is dedicated.
#guard canon
  [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
   blk "head" #[] (branch "body" "after"), blk "body" #[] (branch "after" "latch"),
   blk "latch" #[] (jump "head"), blk "after" #[] ret]

/-! ## Nested loops, each canonical -/

private def nestedLoops : List (Block E Unit) :=
  [blk "entry" #[] (jump "opre"), blk "opre" #[] (jump "oh"),
   blk "oh" #[] (branch "ipre" "exit"), blk "ipre" #[] (jump "ih"),
   blk "ih" #[] (branch "ilatch" "iexit"), blk "ilatch" #[] (jump "ih"),
   blk "iexit" #[] (jump "olatch"), blk "olatch" #[] (jump "oh"), blk "exit" #[] ret]

#guard canon nestedLoops

-- The inner loop's head entered straight from the outer head: no preheader.
#guard !canon
  [blk "entry" #[] (jump "opre"), blk "opre" #[] (jump "oh"),
   blk "oh" #[] (branch "ih" "exit"),
   blk "ih" #[] (branch "ilatch" "iexit"), blk "ilatch" #[] (jump "ih"),
   blk "iexit" #[] (jump "olatch"), blk "olatch" #[] (jump "oh"), blk "exit" #[] ret]

/-! ## A loop inside a region

The loop properties hold in every body.  The region's loop has two back edges. -/

/-- `%9 = if %0 { rentry: …; rh: branch ^rl ^rexit … } { e: ret }`. -/
private def ifLoop (twoBack : Bool) : Instruction E Unit :=
  let r : Region E Unit := ⟨#[blk "rentry" #[] (jump "rh"),
    blk "rh" #[] (branch "rl" "rexit"),
    blk "rl" #[] (if twoBack then branch "rh" "rh2" else jump "rh"), blk "rexit" #[] ret] ++
    if twoBack then #[blk "rh2" #[] (jump "rh")] else #[]⟩
  ifI 9 r ⟨#[blk "e" #[] ret]⟩

#guard canon [blk "entry" #[ifLoop false] ret]
#guard !canon [blk "entry" #[ifLoop true] ret]

/-! ## A loop with two entries

`a` and `b` form a cycle with no back edge, so the form says nothing about it.  `Body.reducibleB`,
the check of one entry per loop, rejects it, and accepts the canonical `while` loop and the
nested loops above. -/

private def twoEntries : List (Block E Unit) :=
  [blk "entry" #[] (branch "a" "b"), blk "a" #[] (jump "b"), blk "b" #[] (jump "a")]

#guard canon twoEntries
#guard !Body.reducibleB twoEntries
#guard Body.reducibleB whileLoop
#guard Body.reducibleB nestedLoops

-- A second entry into a cycle can be an exception edge from inside a block.
#guard !Body.reducibleB
  [blk "entry" #[add 1 "b"] (jump "a"), blk "a" #[] (jump "b"), blk "b" #[] (branch "a" "x"),
   blk "x" #[] ret]

-- A self-loop from inside a block, and one from its terminator, are back edges.
#guard Body.reducibleB
  [blk "entry" #[] (jump "h"), blk "h" #[add 1 "h"] (branch "h" "x"), blk "x" #[] ret]

-- A loop with two entries inside a region is found through `Body.everyB`.
#guard !Body.everyB Body.reducibleB
  [blk "entry" #[] (loopT ⟨#[blk "r" #[] (branch "a" "b"), blk "a" #[] (jump "b"),
     blk "b" #[] (branch "a" "rx"), blk "rx" #[] ret]⟩ "x"), blk "x" #[] ret]

-- The check depends on the order it is given: the canonical loop in reverse order fails.
#guard !Body.reducibleWithB whileLoop (lbls ["exit", "latch", "body", "head", "pre", "entry"])

/-! ## Each loop's roles, in work that grows with the body

`Body.loopRoles` of `n` sequential loops, counted in heartbeats, on two bodies: canonical loops,
and loops that always return, which only their records make loops.  Four times the loops must
take less than six times the heartbeats, where a scan of the body's transfers per loop takes about
eight at these sizes.  The labels carry counters, as every label that the builder and the
pass make does, and the records' heads are a label set built once. -/

/-- The label `s.i`. -/
private def lc (s : String) (i : Nat) : Label := ⟨.num (.str .base s) i⟩

/-- Block `s.i`, empty, ending in `t`. -/
private def blkC (s : String) (i : Nat) (t : Terminator E Unit) : Block E Unit :=
  { label := lc s i, params := #[], instrs := #[], term := t, info := () }

/-- `n` sequential loops: `pre.i` jumps to `head.i`, which branches to `body.i` or to `exit.i`,
which goes on to `pre.(i+1)`; `pre.n` returns.  With `back`, `body.i` is the latch, a jump back
to `head.i`; without, it returns, so no back edge enters `head.i`. -/
private def loops (back : Bool) (n : Nat) : List (Block E Unit) :=
  blk "entry" #[] (.jump () ⟨lc "pre" 0, #[]⟩) ::
    ((List.range n).flatMap fun i =>
      [blkC "pre" i (.jump () ⟨lc "head" i, #[]⟩),
       blkC "head" i (.branch () ⟨0⟩ ⟨lc "body" i, #[]⟩ ⟨lc "exit" i, #[]⟩),
       blkC "body" i (if back then .jump () ⟨lc "head" i, #[]⟩ else ret),
       blkC "exit" i (.jump () ⟨lc "pre" (i + 1), #[]⟩)]) ++ [blkC "pre" n ret]

/-- The heartbeats of `Body.loopRoles` on `loops back n`, with the heads `head.i` as the
records' heads, after checking that it names every loop. -/
private def rolesHeartbeats (back : Bool) (n : Nat) : IO Nat := do
  let bs ← IO.lazyPure fun _ => loops back n
  let rs ← IO.lazyPure fun _ => LabelMap.setOf ((List.range n).map (lc "head"))
  unless bs.length == 4 * n + 2 && (rs.find? (lc "head" 0)).isSome do
    throw <| IO.userError "the body was not built"
  let h₀ ← IO.getNumHeartbeats
  let roles ← IO.lazyPure fun _ => Body.loopRoles bs fun l => (rs.find? l).isSome
  let h₁ ← IO.getNumHeartbeats
  unless roles.length == n do throw <| IO.userError s!"loopRoles names {roles.length} of {n} loops"
  return h₁ - h₀

#guard canon (loops true 3)

#eval show IO Unit from do
  for back in [true, false] do
    let a ← rolesHeartbeats back 400
    let b ← rolesHeartbeats back 1600
    unless b < 6 * max a 1 do
      throw <| IO.userError s!"loopRoles: 1600 loops took {b} heartbeats, at least six times the \
        {a} of 400 (back edges: {back})"

-- Compiled code runs `Body.loopRolesFastB` in place of `Body.loopRoles` through the `@[csimp]`
-- lemma `Body.loopRoles_eq_fast`, which Lean accepts even when it is an axiom or is proved with
-- `sorry`.  So the lemma must be a theorem that rests on Lean's standard axioms only.
/-- info: 'Strata.Dyn.Body.loopRoles_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Body.loopRoles_eq_fast

end Strata.Dyn.CanonicalTest
