/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.EveryBody
import all StrataDyn.EveryBody
public import StrataDyn.DomComplete
public import StrataDyn.WF

set_option autoImplicit false

/-!
# A property of every body, decided

## Main theorems

* `Body.everyB_iff`: `Body.everyB p` decides `Body.Every P`, if `p` decides `P`;
* `Body.everyB_iff_of`: the same, if `p` decides `P` only on bodies where some `Q` holds, and `Q`
  holds of every body;
* `Body.distinct_iff_every`: `Body.Distinct`, which `Body.Scopable.distinct` gives for a
  well-formed function, is `Every` of distinct labels;
* `Body.every_not_label_iff`, `Body.Every.exists_label`: the blocks that `Block.withNestedList`
  lists are those of the bodies that `Every` visits, so each label of `Func.bodyLabels` labels a
  block of one of those bodies.
-/

namespace Strata.Dyn

mutual

/-- `Instruction.everyB` decides `Every` of each region of the instruction. -/
theorem Instruction.everyB_iff {env : Env Unit} {α : Type} {P : List (Block env α) → Prop}
    {p : List (Block env α) → Bool} (hp : ∀ bs, p bs = true ↔ P bs) :
    ∀ i : Instruction env α, i.everyB p = true ↔ ∀ r ∈ i.regions, Body.Every P r.blocks.toList
  | .const .. => by simp [Instruction.everyB, Instruction.regions]
  | .apply _ _ _ _ _ _ ⟨regions⟩ => by
    rw [Instruction.everyB, Region.everyListB_iff hp regions]
    simp only [Instruction.regions, Array.mem_def]

/-- `Instruction.everyListB` decides `Every` of each region of each instruction. -/
theorem Instruction.everyListB_iff {env : Env Unit} {α : Type} {P : List (Block env α) → Prop}
    {p : List (Block env α) → Bool} (hp : ∀ bs, p bs = true ↔ P bs) :
    ∀ is : List (Instruction env α), Instruction.everyListB p is = true ↔
      ∀ i ∈ is, ∀ r ∈ i.regions, Body.Every P r.blocks.toList
  | [] => by simp [Instruction.everyListB]
  | i :: is => by
    rw [Instruction.everyListB, Bool.and_eq_true, Instruction.everyB_iff hp i,
      Instruction.everyListB_iff hp is, List.forall_mem_cons]

/-- `Terminator.everyB` decides `Every` of each region of the terminator. -/
theorem Terminator.everyB_iff {env : Env Unit} {α : Type} {P : List (Block env α) → Prop}
    {p : List (Block env α) → Bool} (hp : ∀ bs, p bs = true ↔ P bs) :
    ∀ t : Terminator env α, t.everyB p = true ↔ ∀ r ∈ t.regions, Body.Every P r.blocks.toList
  | .apply _ _ _ _ _ ⟨regions⟩ => by
    rw [Terminator.everyB, Region.everyListB_iff hp regions]
    simp only [Terminator.regions, Array.mem_def]

/-- `Block.everyListB` decides `Every` of each region of each instruction and terminator. -/
theorem Block.everyListB_iff {env : Env Unit} {α : Type} {P : List (Block env α) → Prop}
    {p : List (Block env α) → Bool} (hp : ∀ bs, p bs = true ↔ P bs) :
    ∀ bs : List (Block env α), Block.everyListB p bs = true ↔
      ∀ b ∈ bs, (∀ i ∈ b.instrs.toList, ∀ r ∈ i.regions, Body.Every P r.blocks.toList) ∧
        ∀ r ∈ b.term.regions, Body.Every P r.blocks.toList
  | [] => by simp [Block.everyListB]
  | ⟨l, ps, ⟨instrs⟩, term, info⟩ :: bs => by
    rw [Block.everyListB, Bool.and_eq_true, Bool.and_eq_true,
      Instruction.everyListB_iff hp instrs, Terminator.everyB_iff hp term,
      Block.everyListB_iff hp bs, List.forall_mem_cons, and_assoc]

/-- `Region.everyB` decides `Every` of the region's blocks. -/
theorem Region.everyB_iff {env : Env Unit} {α : Type} {P : List (Block env α) → Prop}
    {p : List (Block env α) → Bool} (hp : ∀ bs, p bs = true ↔ P bs) :
    ∀ r : Region env α, r.everyB p = true ↔ Body.Every P r.blocks.toList
  | ⟨⟨bs⟩⟩ => by
    rw [Region.everyB, Bool.and_eq_true, hp, Block.everyListB_iff hp bs]
    constructor
    · rintro ⟨hP, h⟩
      refine .mk hP fun y r hr => ?_
      cases hr with
      | instr hb hk hri =>
        exact (h _ hb).1 _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk)) r hri
      | term hb hri => exact (h _ hb).2 r hri
    · rintro ⟨hP, h⟩
      refine ⟨hP, fun b hb => ⟨fun i hi r hri => ?_, fun r hri => h _ r (.term hb hri)⟩⟩
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hi
      rw [Array.getElem?_toList] at hk
      exact h _ r (.instr hb hk hri)

/-- `Region.everyListB` decides `Every` of each region's blocks. -/
theorem Region.everyListB_iff {env : Env Unit} {α : Type} {P : List (Block env α) → Prop}
    {p : List (Block env α) → Bool} (hp : ∀ bs, p bs = true ↔ P bs) :
    ∀ rs : List (Region env α), Region.everyListB p rs = true ↔
      ∀ r ∈ rs, Body.Every P r.blocks.toList
  | [] => by simp [Region.everyListB]
  | r :: rs => by
    rw [Region.everyListB, Bool.and_eq_true, Region.everyB_iff hp r,
      Region.everyListB_iff hp rs, List.forall_mem_cons]

end

namespace Body

variable {env : Env Unit} {α : Type}

/-- `everyB p bs` is true exactly when `P` holds of `bs` and of the blocks of every region nested
in it, at any depth, provided `p` is true exactly where `P` holds. -/
public theorem everyB_iff {P : List (Block env α) → Prop} {p : List (Block env α) → Bool}
    (hp : ∀ bs, p bs = true ↔ P bs) (bs : List (Block env α)) :
    everyB p bs = true ↔ Every P bs :=
  Region.everyB_iff hp ⟨bs.toArray⟩

/-- If `Q` and `A` hold of every body, and `Q` and `A` together give `B` of a body, then `B`
holds of every body. -/
public theorem Every.imp {Q A B : List (Block env α) → Prop} (h : ∀ bs, Q bs → A bs → B bs)
    {bs : List (Block env α)} (hq : Every Q bs) (ha : Every A bs) : Every B bs := by
  induction hq with
  | mk hQ _ ih =>
    cases ha with
    | mk hA hAr => exact .mk (h _ hQ hA) fun y r hr => ih y r hr (hAr y r hr)

/-- `everyB p bs` is true exactly when `P` holds of `bs` and of every body nested in it, provided
`Q` holds of every such body and, on a body where `Q` holds, `p` is true exactly where `P`
holds.  For example, `Q` says that a body's labels are distinct. -/
public theorem everyB_iff_of {Q P : List (Block env α) → Prop} {p : List (Block env α) → Bool}
    (hp : ∀ bs, Q bs → (p bs = true ↔ P bs)) {bs : List (Block env α)} (hq : Every Q bs) :
    everyB p bs = true ↔ Every P bs :=
  (everyB_iff (P := (p · = true)) (fun _ => Iff.rfl) bs).trans
    ⟨Every.imp (fun bs hQ h => (hp bs hQ).mp h) hq,
      Every.imp (fun bs hQ h => (hp bs hQ).mpr h) hq⟩

/-- A body and every body nested in it have distinct labels exactly when `Distinct` says so. -/
public theorem distinct_iff_every (bs : List (Block env α)) :
    Distinct bs ↔ Every (fun bs => (bs.map (·.label)).Nodup) bs := by
  constructor
  · intro h
    induction h with
    | mk hr _ ih => exact .mk hr ih
  · intro h
    induction h with
    | mk hr _ ih => exact .mk hr ih

end Body

/-! ## The bodies' blocks

The blocks that `Block.withNestedList` lists are those of the bodies that `Body.Every` visits. -/

section

variable {env : Env Unit} {α : Type}

mutual

/-- `q` holds of every block nested in the instruction exactly when, in each body nested in its
regions, `q` holds of every block. -/
private theorem Instruction.nestedBlocks_all (q : Block env α → Bool) :
    ∀ i : Instruction env α, i.nestedBlocks.all q = i.everyB (·.all q)
  | .const .. => rfl
  | .apply _ _ _ _ _ _ ⟨regions⟩ => Region.blocksList_all q regions

/-- `q` holds of every block nested in the instructions exactly when, in each body nested in
them, `q` holds of every block. -/
private theorem Instruction.nestedBlocksList_all (q : Block env α → Bool) :
    ∀ is : List (Instruction env α),
      (Instruction.nestedBlocksList is).all q = Instruction.everyListB (·.all q) is
  | [] => rfl
  | i :: is => by
    rw [Instruction.nestedBlocksList, Instruction.everyListB, List.all_append,
      Instruction.nestedBlocks_all q i, Instruction.nestedBlocksList_all q is]

/-- `q` holds of every block nested in the terminator exactly when, in each body nested in its
regions, `q` holds of every block. -/
private theorem Terminator.nestedBlocks_all (q : Block env α → Bool) :
    ∀ t : Terminator env α, t.nestedBlocks.all q = t.everyB (·.all q)
  | .apply _ _ _ _ _ ⟨regions⟩ => Region.blocksList_all q regions

/-- `q` holds of the blocks and of every block nested in them exactly when it holds of the
blocks, and, in each body nested in them, of every block. -/
private theorem Block.withNestedList_all (q : Block env α → Bool) :
    ∀ bs : List (Block env α),
      (Block.withNestedList bs).all q = (bs.all q && Block.everyListB (·.all q) bs)
  | [] => rfl
  | ⟨l, ps, ⟨instrs⟩, t, info⟩ :: bs => by
    rw [Block.withNestedList, Block.everyListB, List.all_cons, List.all_append, List.all_append,
      Instruction.nestedBlocksList_all q instrs, Terminator.nestedBlocks_all q t,
      Block.withNestedList_all q bs, List.all_cons]
    cases q ⟨l, ps, ⟨instrs⟩, t, info⟩ <;> cases List.all bs q <;>
      cases Instruction.everyListB (·.all q) instrs <;> cases t.everyB (·.all q) <;> rfl

/-- `q` holds of every block of the regions exactly when, in each body of the regions and each
body nested in them, `q` holds of every block. -/
private theorem Region.blocksList_all (q : Block env α → Bool) :
    ∀ rs : List (Region env α), (Region.blocksList rs).all q = Region.everyListB (·.all q) rs
  | [] => rfl
  | ⟨⟨blocks⟩⟩ :: rs => by
    rw [Region.blocksList, Region.everyListB, Region.everyB, List.all_append,
      Block.withNestedList_all q blocks, Region.blocksList_all q rs]

end

namespace Body

/-- No block of the body, nor of any body nested in it, is labelled `l` exactly when no block of
`Block.withNestedList` is. -/
public theorem every_not_label_iff (bs : List (Block env α)) (l : Label) :
    Every (fun bs => ∀ b ∈ bs, b.label ≠ l) bs ↔ l ∉ (Block.withNestedList bs).map (·.label) := by
  rw [← everyB_iff (p := fun bs => bs.all (·.label != l)) (fun bs => by simp) bs]
  unfold everyB
  rw [Region.everyB, ← Block.withNestedList_all]
  simp

/-- If `P` holds of every body, and some body nested in `bs` has a block labelled `l`, then some
body of which `P` holds has a block labelled `l`. -/
public theorem Every.exists_label {P : List (Block env α) → Prop} {bs : List (Block env α)} {l : Label}
    (hP : Every P bs) (hl : ¬ Every (fun bs => ∀ b ∈ bs, b.label ≠ l) bs) :
    ∃ bs', P bs' ∧ ∃ b ∈ bs', b.label = l := by
  induction hP with
  | @mk bs hPb _ ih =>
    by_cases hb : ∃ b ∈ bs, b.label = l
    · exact ⟨bs, hPb, hb⟩
    · have hno : ∀ b ∈ bs, b.label ≠ l := fun b hb' he => hb ⟨b, hb', he⟩
      obtain ⟨y, r, hr, hnot⟩ : ∃ y r, RegionAt bs y r ∧
          ¬ Every (fun bs => ∀ b ∈ bs, b.label ≠ l) r.blocks.toList :=
        Classical.byContradiction fun h => hl (.mk hno fun y r hr =>
          Classical.byContradiction fun hn => h ⟨y, r, hr, hn⟩)
      exact ih y r hr hnot

end Body

end

end Strata.Dyn
