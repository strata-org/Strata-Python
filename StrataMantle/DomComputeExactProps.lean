/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.DomComplete
public import StrataMantle.DomCompute
import all StrataMantle.DomCompute
import all StrataMantle.DomComputeProps
import all StrataMantle.DomProps
import all StrataMantle.DomComplete
import all StrataMantle.DomComputeExact
import all StrataMantle.Util.LabelMap
import all StrataMantle.Util.LabelMapProps

set_option autoImplicit false

/-!
# The computed tree is exact

`Body.exact_computeTree`: in an order where every block but the entry is entered from an
earlier block (`Body.EarlierPred`), the tree `Body.computeTree` gives is exact, its ancestors of
each reachable point being exactly the point's dominators, and every block is reachable.  The
position layer (`StrataMantle/DomComputeExact.lean`) proves it over any dominance relation with
`DomAx`; this module instantiates that with `Body.Dom` through `pt`, and carries the result from
positions to the tree `treeOf` gives.
-/

namespace Strata.Mantle

public section

variable {env : Env Unit} {α : Type}

/-- Every block but the entry is entered by a transfer from an earlier block. -/
@[expose] def Body.EarlierPred (bs : List (Block env α)) : Prop :=
  ∀ i ps, (i, ps) ∈ Body.predLists bs → ∃ u ∈ ps, u.1 < i

end

namespace Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)}

/-! ## Positions and points -/

/-- Under distinct labels, a position `positions` gives is a block's, with that label. -/
theorem positions_find?_eq (hn : (bs.map (·.label)).Nodup) {l : Label} {i : Nat}
    (h : (positions 0 bs ∅).find? l = some i) : ∃ v, bs[i]? = some v ∧ v.label = l := by
  by_cases hc : ∃ c ∈ bs, c.label = l
  · obtain ⟨c, hc, rfl⟩ := hc
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    have := positions_find?_of (k := 0) (m := ∅) hn hj
    rw [Nat.zero_add, h] at this
    cases this
    exact ⟨c, hj, rfl⟩
  · rw [positions_find?_notin (fun c hc' he => hc ⟨c, hc', he⟩), LabelMap.find?_empty] at h
    cases h

/-- Under distinct labels, distinct positions of blocks are distinct points. -/
theorem pt_injective (hn : (bs.map (·.label)).Nodup) {p q : Pos} (hp : p.1 < bs.length)
    (hq : q.1 < bs.length) (h : pt bs p = pt bs q) : p = q := by
  obtain ⟨b, hb⟩ := exists_block rfl hp
  obtain ⟨c, hc⟩ := exists_block rfl hq
  have hl : labelAt bs.toArray p.1 = labelAt bs.toArray q.1 := congrArg Point.label h
  rw [labelAt_of hb, labelAt_of hc] at hl
  have h₁ := positions_find?_of (k := 0) (m := ∅) hn hb
  rw [hl, positions_find?_of (k := 0) (m := ∅) hn hc] at h₁
  have h₂ : p.2 = q.2 := congrArg Point.count h
  have h₃ := Option.some.inj h₁
  exact Prod.ext (by omega) h₂

/-- The point at a valid position is a node. -/
theorem node_pt {q : Pos} (hq : Valid bs.length (sizeAt bs) q) : Node bs (pt bs q) := by
  obtain ⟨b, hb⟩ := exists_block rfl hq.1
  exact ⟨b, List.mem_of_getElem? hb, (labelAt_of hb).symm, by rw [← sizeAt_of hb]; exact hq.2⟩

/-- Every node is the point at some valid position. -/
theorem exists_pt {y : Point} (h : Node bs y) :
    ∃ q, Valid bs.length (sizeAt bs) q ∧ pt bs q = y := by
  obtain ⟨b, hb, hl, hk⟩ := h
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  refine ⟨(j, y.count), ⟨(List.getElem?_eq_some_iff.mp hj).1, by rw [sizeAt_of hj]; exact hk⟩, ?_⟩
  show (⟨labelAt bs.toArray j, y.count⟩ : Point) = y
  rw [labelAt_of hj, hl]

/-- The point at the entry's first position is the root. -/
theorem pt_root (e : Block env α) (rest : List (Block env α)) :
    pt (e :: rest) (0, 0) = root (e :: rest) := by
  show (⟨labelAt (e :: rest).toArray 0, 0⟩ : Point) = ⟨e.label, 0⟩
  rw [labelAt_of (show (e :: rest)[0]? = some e from rfl)]

/-- An instruction transfer `instrEdges` lists is a successor of the instruction at its count. -/
theorem mem_instrEdges_inv :
    ∀ {k₀ : Nat} {is : List (Instruction env α)} {k : Nat} {l : Label},
      (k, l) ∈ instrEdges k₀ is →
        ∃ i s, is[k - k₀]? = some i ∧ k₀ ≤ k ∧ s ∈ i.succs ∧ s.target = l
  | _, [], _, _, h => absurd h List.not_mem_nil
  | k₀, i :: is, k, l, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨s, hs, he⟩ := List.mem_map.mp h
      cases he
      exact ⟨i, s, by rw [Nat.sub_self]; rfl, Nat.le_refl _, Array.mem_toList_iff.mp hs, rfl⟩
    · obtain ⟨i₁, s, hi, hk, hs, hl⟩ := mem_instrEdges_inv h
      refine ⟨i₁, s, ?_, by omega, hs, hl⟩
      rw [show k - k₀ = (k - (k₀ + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hi

/-- A transfer `edges` lists is a jump. -/
theorem jump_of_mem_edges {b v : Block env α} {k : Nat} (hb : b ∈ bs) (hv : v ∈ bs)
    (h : (k, v.label) ∈ edges b) : Jump bs ⟨b.label, k⟩ v := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨i, s, hi, -, hs, hl⟩ := mem_instrEdges_inv h
    rw [Nat.sub_zero, Array.getElem?_toList] at hi
    exact .instr hb hi hs hv hl.symm
  · obtain ⟨s, hs, he⟩ := List.mem_map.mp h
    obtain ⟨hk, hl⟩ := Prod.mk.inj he
    subst hk
    exact .term hb (Array.mem_toList_iff.mp hs) hv hl.symm

/-- A point that `predLists` has jump to a block enters it. -/
theorem edge_of_mem_predLists (hn : (bs.map (·.label)).Nodup) {i : Nat} {ps : List Pos}
    {u : Pos} (h : (i, ps) ∈ predLists bs) (hu : u ∈ ps) :
    Edge bs (pt bs u) (pt bs (i, 0)) := by
  obtain ⟨i₁, hi₁, he⟩ := List.mem_map.mp h
  cases he
  have hi := List.mem_range'_1.mp hi₁
  obtain ⟨b, -, hb, l, hl, hp⟩ := mem_jumpsFrom ((mem_buckets (by omega)).mp hu)
  rw [Nat.sub_zero] at hb
  obtain ⟨v, hv, rfl⟩ := positions_find?_eq hn hp
  have hj := jump_of_mem_edges (List.mem_of_getElem? hb) (List.mem_of_getElem? hv) hl
  have h₁ : pt bs u = ⟨b.label, u.2⟩ := by
    show (⟨labelAt bs.toArray u.1, u.2⟩ : Point) = _
    rw [labelAt_of hb]
  have h₂ : pt bs (i, 0) = ⟨v.label, 0⟩ := by
    show (⟨labelAt bs.toArray i, 0⟩ : Point) = _
    rw [labelAt_of hv]
  rw [h₁, h₂]
  exact .jump hj

/-! ## Reachability -/

/-- In an order with earlier predecessors, every point is reachable. -/
theorem reach_pt (hn : (bs.map (·.label)).Nodup) (hc : EarlierPred bs) (hne : bs ≠ []) :
    ∀ q, Valid bs.length (sizeAt bs) q → Reach bs (pt bs q) := by
  intro q
  obtain ⟨i, k⟩ := q
  induction i using Nat.strongRecOn generalizing k with
  | _ i ihi =>
    induction k with
    | zero =>
      intro hq
      cases i with
      | zero =>
        cases bs with
        | nil => exact absurd rfl hne
        | cons e rest => exact (pt_root e rest).symm ▸ .root
      | succ i =>
        have hpm : (i + 1, (buckets bs.length (jumpsFrom (positions 0 bs ∅) 0 bs))[i + 1]?.getD [])
            ∈ predLists bs :=
          List.mem_map.mpr ⟨i + 1, List.mem_range'_1.mpr ⟨by omega, by have := hq.1; omega⟩, rfl⟩
        obtain ⟨u, hu, hlt⟩ := hc _ _ hpm
        obtain ⟨-, -, hval⟩ := predLists_ok bs _ _ hpm
        have hu₁ := hval u hu
        exact .step (ihi u.1 hlt u.2 hu₁) (edge_of_mem_predLists hn hpm hu)
    | succ k ihk =>
      intro hq
      obtain ⟨b, hb⟩ := exists_block rfl hq.1
      have hk : k < b.instrs.size := by have := hq.2; rw [sizeAt_of hb] at this; omega
      have he : Edge bs (pt bs (i, k)) (pt bs (i, k + 1)) := by
        simp only [pt, ptAt, labelAt_of hb]
        exact .fall (List.mem_of_getElem? hb) hk
      exact .step (ihk ⟨hq.1, Nat.le_of_succ_le hq.2⟩) he

/-- An empty body's tree is exact. -/
theorem exact_nil (t : Tree) : ∀ d y, Reach ([] : List (Block env α)) y →
    (Anc ([] : List (Block env α)) t d y ↔ Dom ([] : List (Block env α)) d y) := by
  intro d y hy
  have hy₁ : y = root ([] : List (Block env α)) := by
    cases hy with
    | root => rfl
    | step _ he =>
      cases he with
      | fall hb => exact absurd hb List.not_mem_nil
      | jump hj => cases hj <;> contradiction
  subst hy₁
  constructor
  · intro h
    exact h.dom (legal_nil t)
  · intro h
    by_cases hd : d = root ([] : List (Block env α))
    · subst hd
      exact .refl _
    · exact absurd (.root (Ne.symm hd)) h

/-! ## Exactness -/

/-- `Dom` through `pt` is a dominance relation over positions. -/
theorem domAx (hn : (bs.map (·.label)).Nodup) {e : Block env α} {rest : List (Block env α)}
    (hbs : bs = e :: rest) :
    DomAx bs.length (sizeAt bs) (fun d q => Dom bs (pt bs d) (pt bs q)) := by
  refine ⟨fun d i k hdv hq hD hne => ?_, fun d hdv hD => ?_⟩
  · have hne₁ : pt bs d ≠ pt bs (i, k + 1) := fun h => hne (pt_injective hn hdv.1 hq.1 h)
    exact Dom.of_fall (l := labelAt bs.toArray i) (node_pt hq) hD hne₁
  · have h₀ : pt bs (0, 0) = root bs := by subst hbs; exact pt_root e rest
    have hv₀ : (0 : Nat) < bs.length := by subst hbs; exact Nat.succ_pos _
    refine pt_injective hn hdv.1 hv₀ (Classical.byContradiction fun h => ?_)
    rw [h₀] at h hD
    exact hD (.root fun h₁ => h h₁.symm)

/-- In an order with earlier predecessors, the tree `computeTree` gives is exact: the ancestors
of each reachable point are its dominators.  And every block is reachable. -/
public theorem exact_computeTree {e : Block env α} {rest : List (Block env α)}
    (hn : ((e :: rest).map (·.label)).Nodup) (hc : EarlierPred (e :: rest)) :
    (∀ d y, Reach (e :: rest) y →
      (Anc (e :: rest) (computeTree (e :: rest)).find? d y ↔ Dom (e :: rest) d y)) ∧
    ∀ b ∈ e :: rest, Reach (e :: rest) ⟨b.label, 0⟩ := by
  have hL := legal_computeTree hn
  have hl := predLists_ok (e :: rest)
  have hI₀ := firstPass_inv (flat_valid e rest) rfl (start_inv (flat_valid e rest) rfl) hl
  obtain ⟨hI, -⟩ := settle_spec hl _ _ hI₀ rfl
  have hct : (computeTree (e :: rest)).find? = treeOf (e :: rest) (settle _ hl _ hI₀) := rfl
  have hA := domAx hn rfl
  -- The settled tree keeps `Under`, from the first pass on.
  have hPD : PredsDom (e :: rest).length (sizeAt (e :: rest))
      (fun d q => Dom (e :: rest) (pt (e :: rest) d) (pt (e :: rest) q)) (predLists (e :: rest)) :=
    fun i ps h u hu d hdv hne hD =>
      hD.of_edge (fun he => hne (pt_injective hn hdv.1 (hl i ps h).2.1 he))
        (edge_of_mem_predLists hn h hu)
  have hmem : ∀ i, 0 < i → i < (e :: rest).length →
      (i, (buckets (e :: rest).length
        (jumpsFrom (positions 0 (e :: rest) ∅) 0 (e :: rest)))[i]?.getD []) ∈
        predLists (e :: rest) := fun i h₀ h₁ =>
    List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨h₀, by omega⟩, rfl⟩
  have hU₀ := firstPass_underD (flat := (0, 0)) hA
    (fun i h₀ h₁ => (hl _ _ (hmem i h₀ h₁)).2.2) (fun i h₀ h₁ => hPD _ _ (hmem i h₀ h₁))
    (fun i h₀ h₁ => hc _ _ (hmem i h₀ h₁)) ((e :: rest).length - 1) 1 _
    (by simp only [List.length_cons]; omega) Nat.one_pos
    (start_inv (flat_valid e rest) rfl) (fun i r hi h => by
      rw [Nat.lt_one_iff] at hi
      subst hi
      rw [start_find?, if_neg (by simp)] at h
      cases h)
  have hU := settle_underD hA hl hPD _ _ hI₀ rfl hU₀
  rw [hct] at hL ⊢
  generalize settle _ hl _ hI₀ = par at hI hU hL ⊢
  refine ⟨fun d y hy => ⟨fun h => h.dom hL, fun hd => ?_⟩, fun b hb => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := exists_pt (hy.node (List.cons_ne_nil _ _))
    have hdn : Node (e :: rest) d := Classical.byContradiction fun h =>
      hd (hy.reachAvoid_of_not_node (List.cons_ne_nil _ _) h)
    obtain ⟨d₀, hd₀, rfl⟩ := exists_pt hdn
    exact (hU.anc hA hI q hq hq.1 d₀ hd₀ hd).lift rfl hn hI
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
    have := reach_pt hn hc (List.cons_ne_nil _ _) (j, 0)
      ⟨(List.getElem?_eq_some_iff.mp hj).1, Nat.zero_le _⟩
    rwa [pt, ptAt, labelAt_of hj] at this

end Body

end Strata.Mantle
