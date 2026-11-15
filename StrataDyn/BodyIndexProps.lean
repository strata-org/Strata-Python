/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.BodyIndex
import all StrataDyn.BodyIndex
import all StrataDyn.Loops
import all StrataDyn.LoopsProps
import all StrataDyn.LoopsFast
import all StrataDyn.DomCheck
import all StrataDyn.DomProps
import all StrataDyn.Util.LabelMapProps
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# A body's transfers and loops, by label, proved

## Main theorems

* `Body.Index.spec_of`: the index that `Body.Index.of` computes for a body with distinct labels
  holds `Body.Index.Spec`;
* `LabelMap.mem_listAt_groupBy`, `LabelMap.find?_setOf`, `LabelMap.mem_dedup`,
  `LabelMap.find?_dedup`: the maps and sets it is built from.
-/

namespace Strata.Dyn

/-! ## Lists with the same elements -/

/-- Two lists with the same elements give the same `all` of two predicates that agree. -/
public theorem all_eq_of_mem_iff {β : Type} {A B : List β} {p q : β → Bool}
    (hm : ∀ x, x ∈ A ↔ x ∈ B) (hp : ∀ x, p x = q x) : A.all p = B.all q := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun h x hx => hp x ▸ h x ((hm x).mpr hx), fun h x hx => (hp x).symm ▸ h x ((hm x).mp hx)⟩

/-- Two lists with the same elements give the same `any` of two predicates that agree. -/
public theorem any_eq_of_mem_iff {β : Type} {A B : List β} {p q : β → Bool}
    (hm : ∀ x, x ∈ A ↔ x ∈ B) (hp : ∀ x, p x = q x) : A.any p = B.any q := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, (hm x).mp hx, hp x ▸ h⟩,
    fun ⟨x, hx, h⟩ => ⟨x, (hm x).mpr hx, (hp x).symm ▸ h⟩⟩

/-! ## The maps -/

namespace LabelMap

variable {β γ : Type}

/-- `listAt` of `groupBy`, folded from `m`: the values `m` lists, and those of the elements whose
key is the label. -/
private theorem mem_listAt_foldl (key : γ → Label) (val : γ → β) (l : Label) (y : β) :
    ∀ (xs : List γ) (m : LabelMap (List β)),
      y ∈ listAt (xs.foldl (fun m x => m.update (key x) fun o => val x :: o.getD []) m) l ↔
        y ∈ listAt m l ∨ ∃ x ∈ xs, key x = l ∧ val x = y
  | [], m => by simp
  | x :: xs, m => by
    rw [List.foldl_cons, mem_listAt_foldl key val l y xs]
    simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
    unfold listAt
    rw [find?_update]
    by_cases hl : l = key x
    · subst hl
      rw [ite_eq_left rfl, Option.getD_some, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact .inr (.inl ⟨rfl, h.symm⟩)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | ⟨-, h⟩ | h)
        · exact .inl (.inr h)
        · exact .inl (.inl h.symm)
        · exact .inr h
    · rw [ite_eq_right hl]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | ⟨h, -⟩ | h)
        · exact .inl h
        · exact absurd h.symm hl
        · exact .inr h

/-- `groupBy key val xs` lists for `l` exactly `val x` of the elements `x` of `xs` whose key is
`l`. -/
public theorem mem_listAt_groupBy {key : γ → Label} {val : γ → β} {xs : List γ} {l : Label}
    {y : β} : y ∈ listAt (groupBy key val xs) l ↔ ∃ x ∈ xs, key x = l ∧ val x = y := by
  rw [groupBy, mem_listAt_foldl]
  simp [listAt]

/-- The step of `dedup` from a set `p.1` of the labels of `p.2` keeps the set the set of the
list's labels, and adds the labels of `ls` to it. -/
private theorem dedup_foldl :
    ∀ (ls : List Label) (p : LabelMap Unit × List Label),
      (∀ x, (p.1.find? x).isSome ↔ x ∈ p.2) →
      let q := ls.foldl (fun p l =>
        if (p.1.find? l).isSome then p else (p.1.insert l (), l :: p.2)) p
      (∀ x, (q.1.find? x).isSome ↔ x ∈ q.2) ∧ ∀ x, x ∈ q.2 ↔ x ∈ p.2 ∨ x ∈ ls
  | [], p, hp => ⟨hp, fun x => by simp⟩
  | l :: ls, p, hp => by
    dsimp only
    rw [List.foldl_cons]
    by_cases hl : (p.1.find? l).isSome = true
    · rw [ite_eq_left hl]
      refine ⟨(dedup_foldl ls p hp).1, fun x => ?_⟩
      rw [(dedup_foldl ls p hp).2 x, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl ((hp x).mp hl)
        · exact .inr h
    · rw [ite_eq_right hl]
      have hq : ∀ x, (((p.1.insert l ()).find? x).isSome ↔ x ∈ l :: p.2) := by
        intro x
        rw [find?_insert, List.mem_cons]
        by_cases hx : x = l
        · simp [hx]
        · simp [hx, hp x]
      refine ⟨(dedup_foldl ls _ hq).1, fun x => ?_⟩
      rw [(dedup_foldl ls _ hq).2 x, List.mem_cons, List.mem_cons]
      constructor
      · rintro ((rfl | h) | h)
        · exact .inr (.inl rfl)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr h

/-- The list of `dedup ls` holds exactly the labels of `ls`. -/
public theorem mem_dedup {ls : List Label} {x : Label} : x ∈ (dedup ls).2 ↔ x ∈ ls := by
  rw [dedup, ((dedup_foldl ls (∅, []) (fun x => by simp)).2 x)]
  simp

/-- The set of `dedup ls` holds exactly the labels of `ls`. -/
public theorem find?_dedup {ls : List Label} {x : Label} :
    ((dedup ls).1.find? x).isSome ↔ x ∈ ls := by
  rw [← mem_dedup, dedup]
  exact (dedup_foldl ls (∅, []) (fun x => by simp)).1 x

/-- The set of the labels `ls` holds exactly them. -/
public theorem find?_setOf {ls : List Label} {l : Label} :
    ((setOf ls).find? l).isSome ↔ l ∈ ls := by
  rw [setOf, isSome_find?_foldl_insert (fun l => l) (fun _ => ())]
  simp

end LabelMap

/-! ## The index -/

namespace Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)}

/-- A back edge is a transfer. -/
public theorem mem_transfers_of_backEdges {u : Point} {h : Label} (he : (u, h) ∈ backEdges bs) :
    (u, h) ∈ transfers bs := by
  simp only [backEdges, List.mem_eraseDups, List.mem_filter] at he
  exact he.1

/-- The loop of a back edge grows from `backSeed`'s seed. -/
theorem loopSeed_eq {u : Point} {h : Label} (he : (u, h) ∈ backEdges bs) :
    loopSeed bs u h = backSeed u h := by
  obtain ⟨b, hb, hbl, hk, -⟩ := mem_transfers.mp (mem_transfers_of_backEdges he)
  have hany : bs.any (fun b => b.label == u.label && decide (u.count ≤ b.instrs.size)) = true :=
    List.any_eq_true.mpr ⟨b, hb, by simp [hbl, hk]⟩
  unfold loopSeed backSeed
  rw [hany, Bool.and_true]

/-- For a back edge, the search of `loopSearch`, with the body's predecessor map and as many
steps as blocks, is that of `searchLoop`. -/
theorem loopSearch_eq {u : Point} {h : Label} (he : (u, h) ∈ backEdges bs) :
    loopSearch (predMap bs) bs.length u h = search (predMap bs) h bs.length
      ⟨loopSeed bs u h, (loopSeed bs u h).foldl (fun m l => m.insert l ()) ∅, loopSeed bs u h⟩ := by
  rw [loopSeed_eq he]
  rfl

/-- For a back edge, the search of `loopSearch` has found exactly the labels in its set. -/
theorem seen_loopSearch {u : Point} {h : Label} (he : (u, h) ∈ backEdges bs) (x : Label) :
    ((loopSearch (predMap bs) bs.length u h).seen.find? x).isSome ↔
      x ∈ (loopSearch (predMap bs) bs.length u h).found := by
  rw [loopSearch_eq he]
  obtain ⟨⟨_, hI⟩, -, -⟩ := search_spec (bs := bs)
    (Q := fun x => ∃ c ∈ bs, c.label = x ∧ x ≠ h ∧ PathAvoid bs ⟨h, 0⟩ ⟨x, 0⟩ u)
    (fun _ _ hx hp hph => loopInv_pred hx hp hph)
    (fun _ ⟨c, hc, hcl, _⟩ => List.mem_map.mpr ⟨c, hc, hcl⟩) bs.length _
    (searchStart_inv (loopSeed_inv u h).1 (loopSeed_inv u h).2)
  exact hI.seen x

/-- In a body with distinct labels, a label is in the natural loop of the back edge from `u` to
`h` exactly when it is the label of a block, and it is `h` or the search of `loopSearch` finds
it. -/
public theorem mem_loopBlocks_iff_found (ht : (tree? bs).isSome) {u : Point} {h x : Label}
    (he : (u, h) ∈ backEdges bs) :
    x ∈ loopBlocks bs u h ↔ (∃ b ∈ bs, b.label = x) ∧
      (x = h ∨ x ∈ (loopSearch (predMap bs) bs.length u h).found) := by
  rw [loopBlocks_eq_fast, loopBlocksFast, ite_eq_left ht]
  show x ∈ (bs.filter fun b => b.label == h || ((search (predMap bs) h bs.length
    ⟨loopSeed bs u h, (loopSeed bs u h).foldl (fun m l => m.insert l ()) ∅, loopSeed bs u h⟩).seen.find?
      b.label).isSome).map (·.label) ↔ _
  rw [← loopSearch_eq he]
  simp only [List.mem_map, List.mem_filter, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨b, ⟨hb, hh⟩, rfl⟩
    exact ⟨⟨b, hb, rfl⟩, hh.imp id (seen_loopSearch he b.label).mp⟩
  · rintro ⟨⟨b, hb, rfl⟩, hh⟩
    exact ⟨b, ⟨hb, hh.imp id (seen_loopSearch he b.label).mpr⟩, rfl⟩

/-- The head of a back edge is in the natural loop of the back edge. -/
public theorem mem_loopBlocks_self {u : Point} {h : Label} (he : (u, h) ∈ backEdges bs) :
    h ∈ loopBlocks bs u h := by
  obtain ⟨-, -, -, -, -, v, hv, hvl⟩ := mem_transfers.mp (mem_transfers_of_backEdges he)
  simp only [loopBlocks, List.mem_map, List.mem_filter, Bool.or_eq_true, beq_iff_eq]
  exact ⟨v, ⟨hv, .inl hvl⟩, hvl⟩

/-- `tree?`'s map gives the first block with a label: the block with that label. -/
theorem find?_tree {tm : LabelMap (Block env α)} (ht : tree? bs = some tm) (l : Label) :
    tm.find? l = bs.find? (·.label == l) := by
  have hT := (tree?_eq_some ht).2
  cases hf : bs.find? (·.label == l) with
  | some b =>
    exact (hT l b).mpr ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
  | none =>
    cases hm : tm.find? l with
    | none => rfl
    | some b =>
      obtain ⟨hb, hbl⟩ := (hT l b).mp hm
      exact absurd (List.find?_eq_none.mp hf b hb) (by simp [hbl])

/-- `tree?`'s map has exactly the labels of the body's blocks. -/
theorem isSome_find?_tree {tm : LabelMap (Block env α)} (ht : tree? bs = some tm) (l : Label) :
    (tm.find? l).isSome ↔ ∃ b ∈ bs, b.label = l := by
  rw [find?_tree ht]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    exact ⟨b, List.mem_of_find?_eq_some hb, by simpa using List.find?_some hb⟩
  · rintro ⟨b, hb, hbl⟩
    cases hf : bs.find? (·.label == l) with
    | some _ => rfl
    | none => exact absurd (List.find?_eq_none.mp hf b hb) (by simp [hbl])

/-- The loop data of a head lists exactly the labels of its loop, as a set and as a list. -/
private theorem loopData_spec {tm : LabelMap (Block env α)} (ht : tree? bs = some tm)
    {h : Label} (hh : ∃ u, (u, h) ∈ backEdges bs) (x : Label) :
    let d := loopData tm (predMap bs) bs.length h
      (LabelMap.listAt (LabelMap.groupBy (·.2) (·.1) (backEdges bs)) h)
    ((d.1.find? x).isSome ↔ ∃ u, (u, h) ∈ backEdges bs ∧ x ∈ loopBlocks bs u h) ∧
      (x ∈ d.2 ↔ ∃ u, (u, h) ∈ backEdges bs ∧ x ∈ loopBlocks bs u h) := by
  have hsome : (tree? bs).isSome := by rw [ht]; rfl
  have key : x ∈ (h :: (LabelMap.listAt (LabelMap.groupBy (·.2) (·.1) (backEdges bs)) h).flatMap
      fun u => (loopSearch (predMap bs) bs.length u h).found).filter
        (fun x => (tm.find? x).isSome) ↔ ∃ u, (u, h) ∈ backEdges bs ∧ x ∈ loopBlocks bs u h := by
    simp only [List.mem_filter, List.mem_cons, List.mem_flatMap, LabelMap.mem_listAt_groupBy,
      isSome_find?_tree ht]
    constructor
    · rintro ⟨rfl | ⟨u, ⟨⟨u', l⟩, he, rfl, rfl⟩, hx⟩, hb⟩
      · obtain ⟨u, hu⟩ := hh
        exact ⟨u, hu, mem_loopBlocks_self hu⟩
      · exact ⟨u', he, (mem_loopBlocks_iff_found hsome he).mpr ⟨hb, .inr hx⟩⟩
    · rintro ⟨u, hu, hx⟩
      obtain ⟨hb, rfl | hx⟩ := (mem_loopBlocks_iff_found hsome hu).mp hx
      · exact ⟨.inl rfl, hb⟩
      · exact ⟨.inr ⟨u, ⟨(u, h), hu, rfl, rfl⟩, hx⟩, hb⟩
  exact ⟨LabelMap.find?_dedup.trans key, LabelMap.mem_dedup.trans key⟩

/-- The index that `Index.of` computes for a body with distinct labels, whose blocks by label
`tree?` gives, holds what `Index.Spec` states of each of its fields. -/
public theorem Index.spec_of {tm : LabelMap (Block env α)} (ht : tree? bs = some tm)
    (ep : List Point) : (Index.of bs tm (domInfo bs) ep).Spec bs ep := by
  have hbe : backEdgesIn bs (transfers bs) (domInfo bs) = backEdges bs := by
    rw [backEdges_eq_fast]
    rfl
  have hpm : edgeMapIn (transfers bs) (·.2) (·.1.label) = predMap bs := rfl
  have hheads : ∀ h, h ∈ (LabelMap.dedup ((backEdges bs).map (·.2))).2 ↔
      ∃ u, (u, h) ∈ backEdges bs := by
    intro h
    rw [LabelMap.mem_dedup, List.mem_map]
    constructor
    · rintro ⟨⟨u, l⟩, he, rfl⟩
      exact ⟨u, he⟩
    · rintro ⟨u, he⟩
      exact ⟨(u, h), he, rfl⟩
  have hloops : ∀ h, (Index.of bs tm (domInfo bs) ep).loops.find? h =
      if h ∈ (LabelMap.dedup ((backEdges bs).map (·.2))).2 then
        some (loopData tm (predMap bs) bs.length h
          (LabelMap.listAt (LabelMap.groupBy (·.2) (·.1) (backEdges bs)) h)) else none := by
    intro h
    simp only [Index.of, hbe, hpm]
    rw [LabelMap.find?_foldl_insert_fun, LabelMap.find?_empty]
  have hlist : ∀ h x, x ∈ (Index.of bs tm (domInfo bs) ep).loopList h ↔
      ∃ u, (u, h) ∈ backEdges bs ∧ x ∈ loopBlocks bs u h := by
    intro h x
    simp only [Index.loopList, loopListIn, hloops]
    by_cases hh : h ∈ (LabelMap.dedup ((backEdges bs).map (·.2))).2
    · rw [ite_eq_left hh]
      exact (loopData_spec ht ((hheads h).mp hh) x).2
    · rw [ite_eq_right hh]
      simp only [List.not_mem_nil, false_iff]
      exact fun ⟨u, hu, _⟩ => hh ((hheads h).mpr ⟨u, hu⟩)
  refine ⟨rfl, rfl, rfl, hbe, find?_tree ht, fun l u => ?_, fun x t => ?_, rfl, fun h u => ?_,
    fun h => ?_, fun h => ?_, fun h x => ?_, hlist, fun x h => ?_, fun x => ?_⟩
  · simp only [Index.of, LabelMap.mem_listAt_groupBy]
    constructor
    · rintro ⟨⟨u', l'⟩, ht', rfl, rfl⟩
      exact ht'
    · exact fun h' => ⟨(u, l), h', rfl, rfl⟩
  · simp only [Index.of, LabelMap.mem_listAt_groupBy, id]
    constructor
    · rintro ⟨t', ht', hl, rfl⟩
      exact ⟨ht', hl⟩
    · exact fun ⟨ht', hl⟩ => ⟨t, ht', hl, rfl⟩
  · simp only [Index.of, hbe, LabelMap.mem_listAt_groupBy]
    constructor
    · rintro ⟨⟨u', l'⟩, ht', rfl, rfl⟩
      exact ht'
    · exact fun h' => ⟨(u, h), h', rfl, rfl⟩
  · simp only [Index.of, hbe]
    exact hheads h
  · rw [← hheads h]
    simp only [Index.isHead, hloops]
    by_cases hh : h ∈ (LabelMap.dedup ((backEdges bs).map (·.2))).2
    · simp [hh]
    · simp [hh]
  · simp only [Index.inLoop, hloops]
    by_cases hh : h ∈ (LabelMap.dedup ((backEdges bs).map (·.2))).2
    · rw [ite_eq_left hh]
      exact (loopData_spec ht ((hheads h).mp hh) x).1
    · rw [ite_eq_right hh]
      simp only [Bool.false_eq_true, false_iff]
      exact fun ⟨u, hu, _⟩ => hh ((hheads h).mpr ⟨u, hu⟩)
  · simp only [Index.of, hbe, hpm, LabelMap.mem_listAt_groupBy, List.mem_flatMap, List.mem_map]
    have hl := hlist h x
    simp only [Index.loopList, Index.of, hbe, hpm] at hl
    constructor
    · rintro ⟨_, ⟨h', -, x', hx', rfl⟩, rfl, rfl⟩
      exact hl.mp hx'
    · intro hx
      obtain ⟨u, hu, -⟩ := id hx
      exact ⟨(x, h), ⟨h, (hheads h).mpr ⟨u, hu⟩, x, hl.mpr hx, rfl⟩, rfl, rfl⟩
  · simp only [Index.of]
    rw [LabelMap.isSome_find?_foldl_insert]
    simp

end Body

end Strata.Dyn
