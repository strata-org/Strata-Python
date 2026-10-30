/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.LoopsFast
public import StrataDynTest.Blocks
import StrataDyn.Env.WF
meta import StrataDyn.LoopsFast
meta import StrataDynTest.Blocks

set_option autoImplicit false

/-!
# Loops

Bodies written as blocks, each with the back edges and natural loops that `Body.backEdges` and
`Body.loopBlocks` must find.  The tests run their fast versions (`StrataDyn/LoopsFast.lean`).
The bodies are a `while` loop, a `continue`, a branch that names its target twice, a `break`, an
exception edge, nested loops, a tail that cannot repeat the loop, a self-loop, a loop with two
entries, which has no back edge, a loop inside a region, which is not a loop of the body around
it, and a body with an unreachable block, which has no dominator tree.
-/

namespace Strata.Dyn.LoopsTest

open Strata.Dyn.DSLTest Strata.Dyn.Blocks

private def loopsOf (bs : List (Block E Unit)) : List (Point × List Label) :=
  (Body.backEdges bs).map fun (u, h) => (u, Body.loopBlocks bs u h)

/-! ## A `while` loop

    entry: jump ^head
    head:  branch ^body ^exit
    body:  jump ^head          -- the back edge
    exit:  ret
-/

private def whileLoop : List (Block E Unit) :=
  [blk "entry" #[] (jump "head"), blk "head" #[] (branch "body" "exit"),
   blk "body" #[] (jump "head"), blk "exit" #[] ret]

#guard Body.backEdges whileLoop == [(pt "body" 0, lbl "head")]
#guard loopsOf whileLoop == [(pt "body" 0, lbls ["head", "body"])]

/-! ## A `continue`: two back edges to one head, each with its own loop

    head: branch ^body ^exit
    body: branch ^cont ^rest
    cont: jump ^head         -- back edge 1
    rest: jump ^head         -- back edge 2
-/

private def withContinue : List (Block E Unit) :=
  [blk "entry" #[] (jump "head"), blk "head" #[] (branch "body" "exit"),
   blk "body" #[] (branch "cont" "rest"), blk "cont" #[] (jump "head"),
   blk "rest" #[] (jump "head"), blk "exit" #[] ret]

#guard loopsOf withContinue ==
  [(pt "cont" 0, lbls ["head", "body", "cont"]), (pt "rest" 0, lbls ["head", "body", "rest"])]

/-! ## A branch that names its target twice gives one back edge -/

private def twice : List (Block E Unit) :=
  [blk "entry" #[] (jump "h"), blk "h" #[] (branch "h" "h")]

#guard Body.backEdges twice == [(pt "h" 0, lbl "h")]

/-! ## A `break`: `brk` leaves the loop, so it is outside, though it is in the source loop

    head: branch ^body ^exit
    body: branch ^brk ^cont
    brk:  jump ^exit
    cont: jump ^head
-/

private def withBreak : List (Block E Unit) :=
  [blk "entry" #[] (jump "head"), blk "head" #[] (branch "body" "exit"),
   blk "body" #[] (branch "brk" "cont"), blk "brk" #[] (jump "exit"),
   blk "cont" #[] (jump "head"), blk "exit" #[] ret]

#guard loopsOf withBreak == [(pt "cont" 0, lbls ["head", "body", "cont"])]

/-! ## Exception edges

A failure in the body goes to `catch`, outside the loop.  A failure of the second instruction
goes back to `head`: a back edge that leaves from inside the block, at count 1.

    head: %1 = add ^catch
          %2 = add ^head    -- a back edge, from count 1
          branch ^head ^exit
-/

private def withRaise : List (Block E Unit) :=
  [blk "entry" #[] (jump "head"),
   blk "head" #[add 1 "catch", add 2 "head"] (branch "head" "exit"),
   blk "catch" #[] ret, blk "exit" #[] ret]

#guard loopsOf withRaise ==
  [(pt "head" 1, lbls ["head"]), (pt "head" 2, lbls ["head"])]

/-! ## Nested loops: the inner loop is in the outer one

    oh: branch ^ih ^exit      -- outer head
    ih: branch ^ib ^olatch    -- inner head
    ib: jump ^ih              -- inner back edge
    olatch: jump ^oh          -- outer back edge
-/

private def nested : List (Block E Unit) :=
  [blk "entry" #[] (jump "oh"), blk "oh" #[] (branch "ih" "exit"),
   blk "ih" #[] (branch "ib" "olatch"), blk "ib" #[] (jump "ih"),
   blk "olatch" #[] (jump "oh"), blk "exit" #[] ret]

#guard loopsOf nested ==
  [(pt "ib" 0, lbls ["ih", "ib"]), (pt "olatch" 0, lbls ["oh", "ih", "ib", "olatch"])]

/-! ## A tail that cannot repeat the loop

From Python's `while g(): if h(): continue; while k(): m(); return v`.  The inner loop and the
`return` are in the outer loop's source, but no path from them reaches the outer back edge, so
they are not in its natural loop.

    oh:   branch ^ob ^exit
    ob:   branch ^then ^ih
    then: jump ^oh             -- outer back edge
    ih:   branch ^ib ^tail
    ib:   jump ^ih             -- inner back edge
    tail: ret
-/

private def tail : List (Block E Unit) :=
  [blk "entry" #[] (jump "oh"), blk "oh" #[] (branch "ob" "exit"),
   blk "ob" #[] (branch "then" "ih"), blk "then" #[] (jump "oh"),
   blk "ih" #[] (branch "ib" "tail"), blk "ib" #[] (jump "ih"),
   blk "tail" #[] ret, blk "exit" #[] ret]

#guard loopsOf tail ==
  [(pt "then" 0, lbls ["oh", "ob", "then"]), (pt "ib" 0, lbls ["ih", "ib"])]

/-! ## A self-loop -/

private def selfLoop : List (Block E Unit) :=
  [blk "entry" #[] (jump "h"), blk "h" #[] (branch "h" "exit"), blk "exit" #[] ret]

#guard loopsOf selfLoop == [(pt "h" 0, lbls ["h"])]

/-! ## A loop with two entries

`a` and `b` form a cycle, but neither dominates the other, so neither transfer is a back edge.

    entry: branch ^a ^b
    a: jump ^b
    b: jump ^a
-/

private def twoEntries : List (Block E Unit) :=
  [blk "entry" #[] (branch "a" "b"), blk "a" #[] (jump "b"), blk "b" #[] (jump "a")]

#guard Body.backEdges twoEntries == []

/-! ## A loop inside a region

The region's blocks form their own body.  Its loop is found there, and not in the body around
it, which has no loop. -/

/-- The region `rentry: jump ^rh; rh: branch ^rh ^rexit; rexit: ret`. -/
private def loopRegion : Region E Unit :=
  ⟨#[blk "rentry" #[] (jump "rh"), blk "rh" #[] (branch "rh" "rexit"), blk "rexit" #[] ret]⟩

/-- `%9 = if %0 { loopRegion } { e: ret }`. -/
private def ifLoop : Instruction E Unit := ifI 9 loopRegion ⟨#[blk "e" #[] ret]⟩

private def withRegion : List (Block E Unit) :=
  [blk "entry" #[ifLoop] (jump "exit"), blk "exit" #[] ret]

#guard Body.backEdges withRegion == []
#guard loopsOf loopRegion.blocks.toList == [(pt "rh" 0, lbls ["rh"])]

/-! ## An unreachable block

`dead` is not reached, so `Body.domTree?` gives no tree, and dominance falls back to the search.
Every point dominates an unreachable one, so `dead`'s transfer counts as a back edge.  `Func.WF`
rules such bodies out.

    entry: jump ^a
    a:     ret
    dead:  jump ^a
-/

private def unreachable : List (Block E Unit) :=
  [blk "entry" #[] (jump "a"), blk "a" #[] ret, blk "dead" #[] (jump "a")]

#guard (Body.domTree? unreachable).isNone
#guard loopsOf unreachable == [(pt "dead" 0, lbls ["a", "dead"])]

end Strata.Dyn.LoopsTest
