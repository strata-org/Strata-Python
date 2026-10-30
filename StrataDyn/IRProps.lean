/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR

set_option autoImplicit false

/-!
# The IR: properties

Size facts for recursion on a body's nested regions, in `sizeOf`: a region of an instruction or
a terminator is smaller than it, a block's instruction array and its terminator are smaller
than the block, and a region's block array is smaller than the region.

* `Instruction.sizeOf_lt_of_mem_regions`, `Terminator.sizeOf_lt_of_mem_regions`
* `Block.sizeOf_instrs_lt`, `Block.sizeOf_term_lt`, `Region.sizeOf_blocks_lt`
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

/-- A region of an instruction has a smaller `sizeOf` than the instruction. -/
theorem Instruction.sizeOf_lt_of_mem_regions {i : Instruction env α} {r : Region env α}
    (h : r ∈ i.regions) : sizeOf r < sizeOf i := by
  cases i with
  | const => simp [Instruction.regions] at h
  | apply =>
    have hlt := Array.sizeOf_lt_of_mem h
    simp only [Instruction.regions] at hlt
    simp; omega

/-- A region of a terminator has a smaller `sizeOf` than the terminator. -/
theorem Terminator.sizeOf_lt_of_mem_regions {t : Terminator env α} {r : Region env α}
    (h : r ∈ t.regions) : sizeOf r < sizeOf t := by
  cases t with
  | apply =>
    have hlt := Array.sizeOf_lt_of_mem h
    simp only [Terminator.regions] at hlt
    simp; omega

/-- A block's instruction array has a smaller `sizeOf` than the block. -/
theorem Block.sizeOf_instrs_lt (b : Block env α) : sizeOf b.instrs < sizeOf b := by
  cases b; simp; omega

/-- A block's terminator has a smaller `sizeOf` than the block. -/
theorem Block.sizeOf_term_lt (b : Block env α) : sizeOf b.term < sizeOf b := by
  cases b; simp; omega

/-- A region's block array has a smaller `sizeOf` than the region. -/
theorem Region.sizeOf_blocks_lt (r : Region env α) : sizeOf r.blocks < sizeOf r := by
  cases r; simp

end -- public section

end Strata.Dyn
