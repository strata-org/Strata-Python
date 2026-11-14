/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR

set_option autoImplicit false

/-!
# Traversing blocks and contract regions

A bottom-up traversal may replace a block by several blocks. It visits nested regions first,
so the callback sees rewritten instructions and a rewritten terminator. The callback's new
blocks are not visited again. Labels and value ids stay in the enclosing function's scope.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type} {m : Type → Type} [Monad m]

mutual

/-- Rewrite every block in an instruction's regions, at any depth. -/
def Instruction.traverseBlocks (f : Block env α → m (List (Block env α))) :
    Instruction env α → m (Instruction env α)
  | .const info d c => pure (.const info d c)
  | .apply info d r ts args ks ⟨rs⟩ => do
    return .apply info d r ts args ks ⟨← Region.traverseBlocksList f rs⟩

/-- Rewrite every block in a terminator's regions, at any depth. -/
def Terminator.traverseBlocks (f : Block env α → m (List (Block env α))) :
    Terminator env α → m (Terminator env α)
  | .apply info r ts args ks ⟨rs⟩ => do
    return .apply info r ts args ks ⟨← Region.traverseBlocksList f rs⟩

/-- Traverse nested regions before replacing the block itself. -/
def Block.traverseBlocks (f : Block env α → m (List (Block env α))) :
    Block env α → m (List (Block env α))
  | ⟨label, params, ⟨instrs⟩, term, info⟩ => do
    let instrs ← Instruction.traverseBlocksList f instrs
    let term ← term.traverseBlocks f
    f ⟨label, params, ⟨instrs⟩, term, info⟩

/-- Traverse each instruction's regions. -/
def Instruction.traverseBlocksList (f : Block env α → m (List (Block env α))) :
    List (Instruction env α) → m (List (Instruction env α))
  | [] => pure []
  | i :: is => do return (← i.traverseBlocks f) :: (← Instruction.traverseBlocksList f is)

/-- Traverse each block and concatenate its replacement blocks. -/
def Block.traverseBlocksList (f : Block env α → m (List (Block env α))) :
    List (Block env α) → m (List (Block env α))
  | [] => pure []
  | b :: bs => do return (← b.traverseBlocks f) ++ (← Block.traverseBlocksList f bs)

/-- Rewrite every block of a region, nested blocks included. -/
def Region.traverseBlocks (f : Block env α → m (List (Block env α))) :
    Region env α → m (Region env α)
  | ⟨⟨bs⟩⟩ => do return ⟨⟨← Block.traverseBlocksList f bs⟩⟩

/-- Traverse each region. -/
def Region.traverseBlocksList (f : Block env α → m (List (Block env α))) :
    List (Region env α) → m (List (Region env α))
  | [] => pure []
  | r :: rs => do return (← r.traverseBlocks f) :: (← Region.traverseBlocksList f rs)

end

/-- Traverse a clause's region, retaining its status and message. -/
def Clause.traverseRegions (f : Region env α → m (Region env α)) (c : Clause env α) :
    m (Clause env α) := do
  return { c with region := ← f c.region }

/-- Traverse a frame region; a cell entry stays as it is. -/
def FrameEntry.traverseRegions (f : Region env α → m (Region env α)) :
    FrameEntry env α → m (FrameEntry env α)
  | .cell v => pure (.cell v)
  | .region r => do return .region (← f r)

/-- Traverse contract regions in their printed order. -/
def Contract.traverseRegions (f : Region env α → m (Region env α)) (c : Contract env α) :
    m (Contract env α) := do
  return {
    requires := ← c.requires.mapM (·.traverseRegions f)
    ensures := ← c.ensures.mapM (·.traverseRegions f)
    reads := ← c.reads.mapM (·.mapM (·.traverseRegions f))
    writes := ← c.writes.mapM (·.mapM (·.traverseRegions f)) }

/-- Traverse a ghost's initializer and invariant. -/
def Ghost.traverseRegions (f : Region env α → m (Region env α)) (g : Ghost env α) :
    m (Ghost env α) := do
  return { g with init := ← g.init.mapM f, invariant := ← g.invariant.mapM f }

end

end Strata.Dyn
