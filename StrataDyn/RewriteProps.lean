/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Rewrite
public import StrataDyn.WF

set_option autoImplicit false

/-!
# Rewriting uses keeps the control-flow graph

* `Func.edgeShape_mapUses`: `Func.mapUses` keeps every block's label and every edge's target,
  in every body, regions included, in order.

`edgeShape` lists, for each block with what is nested in it (`Block.withNestedList`), its label
and the targets of its instructions' and its terminator's edges (`blockShape`).
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

/-- A block's label, and the targets of its instructions' edges, then of its terminator's. -/
@[expose] def blockShape (b : Block env α) : Label × List Label :=
  (b.label, b.instrs.toList.flatMap (·.succs.toList.map (·.label)) ++
    b.term.succs.toList.map (·.label))

/-- The shape of each block of `bs`, with what is nested in them. -/
@[expose] def edgeShape (bs : List (Block env α)) : List (Label × List Label) :=
  (Block.withNestedList bs).map blockShape

/-- `mapUses` keeps the target's label. -/
@[simp] theorem Target.Raw.mapUses_label (f : ValId → ValId) (k : Target.Raw) :
    (k.mapUses f).label = k.label := rfl

section mapUses
variable (f : ValId → ValId)

mutual

/-- Mapping uses keeps a terminator's edge targets and the shapes of its nested blocks. -/
private theorem Terminator.mapUses_shape : ∀ (t : Terminator env α),
    (t.mapUses f).succs.toList.map (·.label) = t.succs.toList.map (·.label) ∧
      (t.mapUses f).nestedBlocks.map blockShape = t.nestedBlocks.map blockShape
  | .apply _ _ _ _ succs ⟨regions⟩ => by
    refine ⟨?_, Region.mapUsesList_shape regions⟩
    simp [Terminator.mapUses, Terminator.succs, Function.comp_def]

/-- Mapping uses keeps an instruction's edge targets and the shapes of its nested blocks. -/
private theorem Instruction.mapUses_shape : ∀ (i : Instruction env α),
    (i.mapUses f).succs.toList.map (·.label) = i.succs.toList.map (·.label) ∧
      (i.mapUses f).nestedBlocks.map blockShape = i.nestedBlocks.map blockShape
  | .const .. => ⟨rfl, rfl⟩
  | .apply _ _ _ _ _ succs ⟨regions⟩ => by
    refine ⟨?_, Region.mapUsesList_shape regions⟩
    simp [Instruction.mapUses, Instruction.succs, Function.comp_def]

/-- Mapping uses keeps instructions' edge targets and the shapes of their nested blocks. -/
private theorem Instruction.mapUsesList_shape : ∀ (is : List (Instruction env α)),
    (Instruction.mapUsesList f is).flatMap (·.succs.toList.map (·.label)) =
        is.flatMap (·.succs.toList.map (·.label)) ∧
      (Instruction.nestedBlocksList (Instruction.mapUsesList f is)).map blockShape =
        (Instruction.nestedBlocksList is).map blockShape
  | [] => ⟨rfl, rfl⟩
  | i :: is => by
    have hi := Instruction.mapUses_shape i
    have ih := Instruction.mapUsesList_shape is
    simp only [Instruction.mapUsesList, List.flatMap_cons, Instruction.nestedBlocksList,
      List.map_append, hi.1, hi.2, ih.1, ih.2]
    constructor <;> first | rfl | trivial

/-- Mapping uses keeps the shapes of regions' nested blocks. -/
private theorem Region.mapUsesList_shape : ∀ (rs : List (Region env α)),
    (Region.blocksList (Region.mapUsesList f rs)).map blockShape =
      (Region.blocksList rs).map blockShape
  | [] => rfl
  | ⟨⟨blocks⟩⟩ :: rs => by
    simp only [Region.mapUsesList, Region.mapUses, Region.blocksList, List.map_append]
    rw [Block.mapUsesList_shape blocks, Region.mapUsesList_shape rs]

/-- Mapping uses keeps the shapes of blocks, with what is nested in them. -/
private theorem Block.mapUsesList_shape : ∀ (bs : List (Block env α)),
    (Block.withNestedList (Block.mapUsesList f bs)).map blockShape =
      (Block.withNestedList bs).map blockShape
  | [] => rfl
  | ⟨l, ps, ⟨instrs⟩, t, info⟩ :: bs => by
    have hi := Instruction.mapUsesList_shape instrs
    have ht := Terminator.mapUses_shape t
    simp only [Block.mapUsesList, Block.mapUses, Block.withNestedList, List.map_cons,
      List.map_append, hi.2, ht.2, Block.mapUsesList_shape bs]
    simp only [blockShape, hi.1, ht.1]

end

end mapUses

/-- `Func.mapUses` keeps every block's label and every edge's target, regions included. -/
theorem Func.edgeShape_mapUses (f : ValId → ValId) (fn : Func env α) :
    edgeShape (fn.mapUses f).blocks.toList = edgeShape fn.blocks.toList :=
  Block.mapUsesList_shape f fn.blocks.toList

end

end Strata.Dyn
