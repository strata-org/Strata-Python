/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Dom
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# A property of every body

A function's top-level blocks are a body, and so are the blocks of each region of its
instructions and terminators, at any depth.  `Body.Every P bs` says that `P` holds of the body
`bs` and of every body nested in it.  `Body.everyB p bs` decides it, given a Boolean `p` that
decides `P`; `StrataDyn/EveryBodyProps.lean` proves it (`Body.everyB_iff`).

## Main definitions

* `Body.Every`: `P` holds of the body and of every body nested in it;
* `Body.everyB`: its decision, from a decision of `P`.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

namespace Body

/-- `P` holds of the body and, for each region of an instruction or terminator of it, of the
region's blocks, and so on at every depth. -/
inductive Every (P : List (Block env α) → Prop) : List (Block env α) → Prop
  | mk {bs : List (Block env α)} : P bs →
      (∀ y r, RegionAt bs y r → Every P r.blocks.toList) → Every P bs

end Body

mutual

/-- `p` holds of the blocks of each region of the instruction, and of every body nested in
them. -/
@[expose] def Instruction.everyB (p : List (Block env α) → Bool) : Instruction env α → Bool
  | .const .. => true
  | .apply _ _ _ _ _ _ ⟨regions⟩ => Region.everyListB p regions

/-- `Instruction.everyB` of each. -/
@[expose] def Instruction.everyListB (p : List (Block env α) → Bool) :
    List (Instruction env α) → Bool
  | [] => true
  | i :: is => i.everyB p && Instruction.everyListB p is

/-- `p` holds of the blocks of each region of the terminator, and of every body nested in
them. -/
@[expose] def Terminator.everyB (p : List (Block env α) → Bool) : Terminator env α → Bool
  | .apply _ _ _ _ _ ⟨regions⟩ => Region.everyListB p regions

/-- `p` holds of every body nested in the blocks' instructions and terminators. -/
@[expose] def Block.everyListB (p : List (Block env α) → Bool) : List (Block env α) → Bool
  | [] => true
  | ⟨_, _, ⟨instrs⟩, term, _⟩ :: bs =>
    Instruction.everyListB p instrs && term.everyB p && Block.everyListB p bs

/-- `p` holds of the region's blocks and of every body nested in them. -/
@[expose] def Region.everyB (p : List (Block env α) → Bool) : Region env α → Bool
  | ⟨⟨bs⟩⟩ => p bs && Block.everyListB p bs

/-- `Region.everyB` of each. -/
@[expose] def Region.everyListB (p : List (Block env α) → Bool) : List (Region env α) → Bool
  | [] => true
  | r :: rs => r.everyB p && Region.everyListB p rs

end

/-- Whether `p` holds of the body and of every body nested in it. -/
@[expose] def Body.everyB (p : List (Block env α) → Bool) (bs : List (Block env α)) : Bool :=
  Region.everyB p ⟨bs.toArray⟩

end

end Strata.Dyn
