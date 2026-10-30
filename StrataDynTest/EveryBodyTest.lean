/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.EveryBodyProps
public import StrataDynTest.Blocks
import StrataDyn.Env.WF
meta import StrataDyn.EveryBodyProps
meta import StrataDynTest.Blocks

set_option autoImplicit false

/-!
# A property of every body

`Body.everyB` with the property "at most two blocks", on a body whose regions nest: it holds
when every body has at most two blocks, and fails when one region does not, whether that region
is an instruction's or a terminator's, and at any depth.
-/

namespace Strata.Dyn.EveryBodyTest

open Strata.Dyn.Blocks

/-- A region of `n` blocks, the first holding the instructions `is`. -/
private def region (s : String) (n : Nat) (is : Array (Instruction E Unit) := #[]) :
    Region E Unit :=
  ⟨(List.range n).toArray.map fun i => blk s!"{s}{i}" (if i = 0 then is else #[]) ret⟩

private def atMostTwo (bs : List (Block E Unit)) : Bool := bs.length ≤ 2

/-- A function body whose entry has an `if` with regions `thn` and `els`, and whose second block
ends in a `loop` with the region `body`. -/
private def nest (thn els body : Region E Unit) : List (Block E Unit) :=
  [blk "entry" #[ifI 1 thn els] ret, blk "exit" #[] (loopT body "exit")]

#guard Body.everyB atMostTwo (nest (region "t" 2) (region "e" 1) (region "l" 2))
#guard !Body.everyB atMostTwo (nest (region "t" 3) (region "e" 1) (region "l" 2))
#guard !Body.everyB atMostTwo (nest (region "t" 2) (region "e" 3) (region "l" 2))
#guard !Body.everyB atMostTwo (nest (region "t" 2) (region "e" 1) (region "l" 3))

/-- The `then` region holds an `if` of its own, whose `else` region has `n` blocks. -/
private def deep (n : Nat) : List (Block E Unit) :=
  nest (region "t" 1 #[ifI 2 (region "tt" 1) (region "te" n)]) (region "e" 1) (region "l" 1)

#guard Body.everyB atMostTwo (deep 2)
#guard !Body.everyB atMostTwo (deep 3)

-- The body itself is checked too.
#guard !Body.everyB atMostTwo
  [blk "a" #[] ret, blk "b" #[] ret, blk "c" #[] ret]

end Strata.Dyn.EveryBodyTest
