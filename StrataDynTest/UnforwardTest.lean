/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Unforward
public import StrataDynTest.Blocks
import StrataDyn.Env.WF
meta import StrataDynTest.Unforward
meta import StrataDynTest.Blocks

set_option autoImplicit false

/-!
# The oracle that undoes the pass

`Unforward.undoesTo fn g` accepts a function `g` that only adds forwarding blocks to `fn`, and
rejects one whose added block jumps somewhere else, does any work, runs a region, passes its
parameters in another order, or forwards in a loop, and one whose region's transfer goes to a block outside
the region.
-/

namespace Strata.Dyn.UnforwardTest

open Strata.Dyn.Blocks

/-- `entry: jump ^h; h: branch ^h ^x; x: ret`. -/
private def loop : Func E Unit :=
  fn [blk "entry" #[] (jump "h"), blk "h" #[] (branch "h" "x"), blk "x" #[] ret]

-- A latch that forwards to the head undoes to the loop.
#guard Unforward.undoesTo loop
  (fn [blk "entry" #[] (jump "h"), blk "h" #[] (branch "l" "x"), blk "x" #[] ret,
       blk "l" #[] (jump "h")])

-- A chain of two forwarding blocks undoes too.
#guard Unforward.undoesTo loop
  (fn [blk "entry" #[] (jump "h"), blk "h" #[] (branch "l" "x"), blk "x" #[] ret,
       blk "l" #[] (jump "m"), blk "m" #[] (jump "h")])

-- A block that forwards to the wrong place is a forwarding block, but the result differs.
private def wrongPlace : Func E Unit :=
  fn [blk "entry" #[] (jump "h"), blk "h" #[] (branch "l" "x"), blk "x" #[] ret,
      blk "l" #[] (jump "x")]

#guard (Unforward.unforward loop wrongPlace).isSome
#guard !Unforward.undoesTo loop wrongPlace

-- A block that does work is not a forwarding block.
#guard (Unforward.unforward loop
  (fn [blk "entry" #[] (jump "h"), blk "h" #[] (branch "l" "x"), blk "x" #[] ret,
       blk "l" #[add 1 "x"] (jump "h")])).isNone

-- A block that runs a region is not a forwarding block.
#guard (Unforward.unforward loop
  (fn [blk "entry" #[] (jump "h"), blk "h" #[] (branch "l" "x"), blk "x" #[] ret,
       blk "l" #[] (loopT ⟨#[]⟩ "h")])).isNone

-- A block that passes its parameters in another order is not a forwarding block.
private def forwardsWith (fwd : Array Nat) : Block E Unit :=
  { label := lbl "f", params := #[⟨⟨5⟩, valT⟩, ⟨⟨6⟩, valT⟩], instrs := #[],
    term := .jump () ⟨lbl "t", fwd.map (⟨·⟩)⟩, info := () }

#guard Unforward.forwardTarget? (forwardsWith #[5, 6]) == some (lbl "t")
#guard Unforward.forwardTarget? (forwardsWith #[6, 5]) == none

-- A chain of forwarding blocks that loops does not undo.
#guard !Unforward.undoesTo loop
  (fn [blk "entry" #[] (jump "h"), blk "h" #[] (branch "l" "x"), blk "x" #[] ret,
       blk "l" #[] (jump "m"), blk "m" #[] (jump "l")])

-- A transfer inside a region sent to a forwarding block of the body around it does not undo:
-- that block is not in the region's body, so the transfer is left pointing at it.
private def inRegion (target : String) : Func E Unit :=
  fn [blk "entry" #[ifI 9 ⟨#[blk "r" #[] (jump target)]⟩ ⟨#[blk "e" #[] ret]⟩] (jump "x"),
      blk "x" #[] ret, blk "rfwd" #[] (jump "x")]

#guard !Unforward.undoesTo
  (fn [blk "entry" #[ifI 9 ⟨#[blk "r" #[] (jump "x")]⟩ ⟨#[blk "e" #[] ret]⟩] (jump "x"),
       blk "x" #[] ret])
  (inRegion "rfwd")

end Strata.Dyn.UnforwardTest
