/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Dom
public import StrataMantle.DomCompute
import all StrataMantle.DomCompute
import all StrataMantle.DomProps
import all StrataMantle.Util.LabelMap
import all StrataMantle.Util.LabelMapProps

set_option autoImplicit false

/-!
# The computed tree is legal

## Main theorems

* `Body.legal_computeTree`: the tree `Body.computeTree` computes is legal, for blocks whose
  labels are distinct.

Everything else in the module is private.

When the passes settle, every block's parent is a common ancestor of the points that jump to it
(`pass_fixed`), which is (L3).  A parent lies in an earlier block (`Inv`), so every chain
reaches the entry.  The rest carries the tree from positions to labels.
-/

namespace Strata.Mantle

namespace Body

variable {env : Env Unit} {α : Type} {n : Nat} {size : Nat → Nat}

/-! ## The passes settle -/

/-- The passes settle on a tree that keeps the invariant and that a further pass leaves alone. -/
theorem settle_spec {l : List (Nat × List Pos)} (hl : PredsOK n size l) :
    ∀ (m : Nat) (par : NatTrie Pos) (hI : Inv n size par), Φ n par = m →
      Inv n size (settle l hl par hI) ∧ (pass l (settle l hl par hI)).1 = false := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro par hI hm
    rw [settle]
    by_cases h : (pass l par).1 = true
    · rw [dif_pos h]
      exact ih _ (hm ▸ (pass_Φ hI hl).2 h) _ _ rfl
    · rw [dif_neg h]
      exact ⟨hI, Bool.eq_false_iff.mpr h⟩

/-! ## Positions and labels -/

/-- `positions` leaves alone a label no block of the list has. -/
theorem positions_find?_notin {x : Label} : ∀ {k : Nat} {bs : List (Block env α)}
    {m : LabelMap Nat}, (∀ b ∈ bs, b.label ≠ x) → (positions k bs m).find? x = m.find? x
  | _, [], _, _ => rfl
  | k, b :: bs, m, h => by
    rw [positions, positions_find?_notin (fun c hc => h c (List.mem_cons_of_mem _ hc)),
      LabelMap.find?_insert, if_neg (Ne.symm (h b List.mem_cons_self))]

/-- Under distinct labels, `positions` maps each block's label to its position. -/
theorem positions_find?_of : ∀ {k : Nat} {bs : List (Block env α)} {m : LabelMap Nat}
    {i : Nat} {b : Block env α}, (bs.map (·.label)).Nodup → bs[i]? = some b →
      (positions k bs m).find? b.label = some (k + i)
  | _, [], _, _, _, _, h => by simp at h
  | k, c :: bs, m, 0, b, hn, h => by
    cases h
    have hc : ∀ d ∈ bs, d.label ≠ c.label := fun d hd he =>
      (List.nodup_cons.mp hn).1 (List.mem_map.mpr ⟨d, hd, he⟩)
    rw [positions, positions_find?_notin hc, LabelMap.find?_insert, if_pos rfl, Nat.add_zero]
  | k, c :: bs, m, i + 1, b, hn, h => by
    rw [positions, positions_find?_of (List.nodup_cons.mp hn).2 h]
    congr 1
    omega

/-- Every successor of an instruction is among `instrEdges`, at the instruction's count. -/
theorem mem_instrEdges_of : ∀ {k₀ : Nat} {is : List (Instruction env α)} {j : Nat}
    {i : Instruction env α} {s : BlockValue}, is[j]? = some i → s ∈ i.succs →
      (k₀ + j, s.target) ∈ instrEdges k₀ is
  | _, [], _, _, _, h, _ => by simp at h
  | k₀, i₁ :: is, 0, i, s, h, hs => by
    cases h
    exact List.mem_append_left _ (List.mem_map.mpr ⟨s, Array.mem_toList_iff.mpr hs, rfl⟩)
  | k₀, i₁ :: is, j + 1, i, s, h, hs => by
    rw [List.getElem?_cons_succ] at h
    have := mem_instrEdges_of (k₀ := k₀ + 1) (is := is) h hs
    rw [show k₀ + (j + 1) = k₀ + 1 + j by omega]
    exact List.mem_append_right _ this

/-- Every transfer of a block of the list is among `jumpsFrom`, from its point. -/
theorem mem_jumpsFrom_of {pos : LabelMap Nat} : ∀ {j₀ : Nat} {bs : List (Block env α)}
    {j k i : Nat} {b : Block env α} {l : Label}, bs[j]? = some b → (k, l) ∈ edges b →
      pos.find? l = some i → ((j₀ + j, k), i) ∈ jumpsFrom pos j₀ bs
  | _, [], _, _, _, _, _, h, _, _ => by simp at h
  | j₀, c :: bs, 0, k, i, b, l, h, he, hp => by
    cases h
    refine List.mem_append_left _ (List.mem_filterMap.mpr ⟨(k, l), he, ?_⟩)
    simp [hp]
  | j₀, c :: bs, j + 1, k, i, b, l, h, he, hp => by
    rw [List.getElem?_cons_succ] at h
    have := mem_jumpsFrom_of (j₀ := j₀ + 1) (bs := bs) h he hp
    rw [show j₀ + (j + 1) = j₀ + 1 + j by omega]
    exact List.mem_append_right _ this

/-! ## The tree out -/

/-- `labelAt` gives the label of the block at that position. -/
theorem labelAt_of {bs : List (Block env α)} {j : Nat} {b : Block env α} (h : bs[j]? = some b) :
    labelAt bs.toArray j = b.label := by
  simp [labelAt, h]

/-- `sizeAt` gives the instruction count of the block at that position. -/
theorem sizeAt_of {bs : List (Block env α)} {j : Nat} {b : Block env α} (h : bs[j]? = some b) :
    sizeAt bs j = b.instrs.size := by
  simp [sizeAt, h]

/-- The point of the blocks `bs` that `p` names. -/
def pt (bs : List (Block env α)) (p : Pos) : Point := ptAt bs.toArray p

/-- `assign` leaves alone a label no block of the list has. -/
theorem assign_find?_notin {all : Array (Block env α)} {par : NatTrie Pos} {l : Label} :
    ∀ {k : Nat} {bs : List (Block env α)} {m : LabelMap Point}, (∀ b ∈ bs, b.label ≠ l) →
      (assign all par k bs m).find? l = m.find? l
  | _, [], _, _ => rfl
  | k, b :: bs, m, h => by
    rw [assign, assign_find?_notin (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    split
    · rw [LabelMap.find?_insert, if_neg (Ne.symm (h b List.mem_cons_self))]
    · rfl

/-- Under distinct labels, `assign` gives the block at position `k + i` the point `par` gives
that position, if any. -/
theorem assign_find?_of {all : Array (Block env α)} {par : NatTrie Pos} :
    ∀ {k : Nat} {bs : List (Block env α)} {m : LabelMap Point} {i : Nat} {b : Block env α},
      (bs.map (·.label)).Nodup → bs[i]? = some b →
      (assign all par k bs m).find? b.label = ((par.find? (k + i)).map (ptAt all)).or
        (m.find? b.label)
  | _, [], _, _, _, _, h => by simp at h
  | k, c :: bs, m, 0, b, hn, h => by
    cases h
    have hc : ∀ d ∈ bs, d.label ≠ c.label := fun d hd he =>
      (List.nodup_cons.mp hn).1 (List.mem_map.mpr ⟨d, hd, he⟩)
    rw [assign, assign_find?_notin hc, Nat.add_zero]
    cases hr : par.find? k with
    | none => rfl
    | some r =>
      rw [LabelMap.find?_insert, if_pos rfl]
      rfl
  | k, c :: bs, m, i + 1, b, hn, h => by
    have hb : b ∈ bs := List.mem_of_getElem? (by simpa using h)
    have hne : b.label ≠ c.label := fun he =>
      (List.nodup_cons.mp hn).1 (List.mem_map.mpr ⟨b, hb, he⟩)
    rw [assign, assign_find?_of (List.nodup_cons.mp hn).2 h, show k + 1 + i = k + (i + 1) by omega]
    congr 1
    split
    · rw [LabelMap.find?_insert, if_neg hne]
    · rfl

/-- The tree `par` gives the blocks `bs`, as `computeTree` stores it. -/
def treeOf (bs : List (Block env α)) (par : NatTrie Pos) : Tree :=
  (assign bs.toArray par 0 bs ∅).find?

/-- Under distinct labels, `treeOf` gives the block at position `j` the point `par` gives `j`. -/
theorem treeOf_of {bs : List (Block env α)} {par : NatTrie Pos} (hn : (bs.map (·.label)).Nodup)
    {j : Nat} {b : Block env α} (hb : bs[j]? = some b) :
    treeOf bs par b.label = (par.find? j).map (pt bs) := by
  rw [treeOf, assign_find?_of hn hb, LabelMap.find?_empty, Option.or_none, Nat.zero_add]
  rfl

/-! ## Legality -/

section

variable {bs : List (Block env α)} {par : NatTrie Pos}

/-- Every block at a position below `n` has a block. -/
theorem exists_block (hn : n = bs.length) {i : Nat} (hi : i < n) : ∃ b, bs[i]? = some b :=
  ⟨bs[i]'(hn ▸ hi), List.getElem?_eq_getElem _⟩

/-- Ancestry in the tree by position is ancestry in the tree out. -/
theorem AncT.lift (hn : n = bs.length) (hd : (bs.map (·.label)).Nodup) (hI : Inv n size par)
    {p q : Pos} (h : AncT par p q) : Anc bs (treeOf bs par) (pt bs p) (pt bs q) := by
  induction h with
  | refl => exact .refl _
  | fall _ ih => exact .fall ih
  | @up r i _ hi ih =>
    obtain ⟨-, hin, -⟩ := hI.parent i r hi
    obtain ⟨b, hb⟩ := exists_block hn hin
    have := Anc.parent ih (List.mem_of_getElem? hb) (by rw [treeOf_of hd hb, hi]; rfl)
    show Anc _ _ _ ⟨labelAt bs.toArray i, 0⟩
    rwa [labelAt_of hb]

/-- Every point is below the start of the entry. -/
theorem AncT.root (hI : Inv n size par) : ∀ (i k : Nat), i < n → AncT par (0, 0) (i, k) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro k hi
    by_cases h₀ : i = 0
    · subst h₀; exact AncT.of_count_le 0 (Nat.zero_le k)
    · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hI.total i (by omega) hi)
      have hr₁ := hI.parent i r hr
      exact (ih r.1 hr₁.2.2.1 r.2 hr₁.2.2.2.1).trans (AncT.of_parent hr k)

end

/-- The tree `computeTree` computes is legal, for blocks whose labels are distinct. -/
public theorem legal_computeTree {bs : List (Block env α)} (hn : (bs.map (·.label)).Nodup) :
    Legal bs (computeTree bs).find? := by
  cases bs with
  | nil => exact legal_nil _
  | cons e rest =>
    -- The settled tree, and what it satisfies.
    have hl := predLists_ok (e :: rest)
    have hI₀ := firstPass_inv (flat_valid e rest) rfl (start_inv (flat_valid e rest) rfl) hl
    obtain ⟨hI, hfix⟩ := settle_spec hl _ _ hI₀ rfl
    show Legal (e :: rest) (treeOf (e :: rest) (settle _ hl _ hI₀))
    generalize settle _ hl _ hI₀ = par at hI hfix
    have hfix₁ := (pass_fixed hfix).2
    clear hfix hI₀
    have he : (e :: rest)[0]? = some e := rfl
    generalize e :: rest = bs at hn hl hI hfix₁ he ⊢
    refine ⟨hn, ?_, ?_, ?_, ?_⟩
    · intro e₁ h
      rw [List.head?_eq_getElem?, he] at h
      cases h
      rw [treeOf_of hn he, hI.find?_zero]
      rfl
    · intro b h
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
      rw [List.getElem?_tail] at hj
      have hjn : j + 1 < bs.length := (List.getElem?_eq_some_iff.mp hj).1
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hI.total (j + 1) (by omega) hjn)
      obtain ⟨-, -, -, hrv⟩ := hI.parent _ _ hr
      obtain ⟨c, hc⟩ := exists_block rfl hrv.1
      refine ⟨pt bs r, by rw [treeOf_of hn hj, hr]; rfl, c, List.mem_of_getElem? hc,
        (labelAt_of hc).symm, ?_⟩
      have := hrv.2
      rw [sizeAt_of hc] at this
      exact this
    · intro b hb
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
      have hroot : root bs = pt bs (0, 0) := by
        simp [root, pt, ptAt, labelAt_of he, List.head?_eq_getElem?, he]
      rw [hroot]
      have := (AncT.root hI j 0 (List.getElem?_eq_some_iff.mp hj).1).lift rfl hn hI
      simpa [pt, ptAt, labelAt_of hj] using this
    · intro u v p hj hp
      -- The jump leaves from the point `(j, k)` of a block of the body.
      obtain ⟨j, b, hb, k, hk, hu⟩ : ∃ j b, bs[j]? = some b ∧ ∃ k, (k, (v.label)) ∈ edges b ∧
          u = pt bs (j, k) := by
        cases hj with
        | @instr b v i k s hb₁ hk hs hv hl =>
          obtain ⟨j, hb⟩ := List.mem_iff_getElem?.mp hb₁
          refine ⟨j, b, hb, k, ?_, by simp [pt, ptAt, labelAt_of hb]⟩
          rw [hl]
          refine List.mem_append_left _ ?_
          simpa using mem_instrEdges_of (k₀ := 0) (is := b.instrs.toList)
            (by simpa [Array.getElem?_toList] using hk) hs
        | @term b v s hb₁ hs hv hl =>
          obtain ⟨j, hb⟩ := List.mem_iff_getElem?.mp hb₁
          refine ⟨j, b, hb, b.instrs.size, ?_, by simp [pt, ptAt, labelAt_of hb]⟩
          rw [hl]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨s, Array.mem_toList_iff.mpr hs, rfl⟩)
      have hv : v ∈ bs := by cases hj <;> assumption
      obtain ⟨i, hv₀⟩ := List.mem_iff_getElem?.mp hv
      rw [treeOf_of hn hv₀] at hp
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hp
      obtain ⟨hi₀, hin, -, hrv⟩ := hI.parent i r hr
      -- So it is among the points that jump to `i`.
      have hpos : (positions 0 bs ∅).find? v.label = some i := by
        simpa using positions_find?_of (k := 0) (m := ∅) hn hv₀
      have hjump : ((j, k), i) ∈ jumpsFrom (positions 0 bs ∅) 0 bs := by
        simpa using mem_jumpsFrom_of (j₀ := 0) hb hk hpos
      have hpred : (i, (buckets bs.length (jumpsFrom (positions 0 bs ∅) 0 bs))[i]?.getD []) ∈
          predLists bs :=
        List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨hi₀, by omega⟩, rfl⟩
      have hjk := (mem_buckets hin).mpr hjump
      obtain ⟨-, -, hps⟩ := hl i _ hpred
      have hanc := (ncaFold_spec hI hrv hps).2 _ hjk
      rw [hfix₁ i _ hpred r hr] at hanc
      rw [hu]
      exact hanc.lift rfl hn hI

/-! ## More blocks -/

section

variable {bs bs₁ : List (Block env α)} {t : Tree}

/-- Ancestry in a tree survives adding blocks. -/
theorem Anc.mono (h : ∀ b, b ∈ bs → b ∈ bs₁) {p q : Point} (ha : Anc bs t p q) :
    Anc bs₁ t p q := by
  induction ha with
  | refl => exact .refl _
  | fall _ ih => exact .fall ih
  | parent _ hb hi ih => exact .parent ih (h _ hb) hi

/-- A transfer survives adding blocks. -/
theorem Jump.mono (h : ∀ b, b ∈ bs → b ∈ bs₁) {u : Point} {v : Block env α} (hj : Jump bs u v) :
    Jump bs₁ u v := by
  cases hj with
  | instr hb hk hs hv hl => exact .instr (h _ hb) hk hs (h _ hv) hl
  | term hb hs hv hl => exact .term (h _ hb) hs (h _ hv) hl

end

end Body

end Strata.Mantle
