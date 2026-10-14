/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.DomCheck
import all StrataMantle.DomCheck
import all StrataMantle.Util.LabelMap
import all StrataMantle.Util.LabelMapProps
import all StrataMantle.Util.List

set_option autoImplicit false

/-!
# Scoping: the checker, and what it guarantees

This module proves that the checker (`StrataMantle/DomCheck.lean`) decides whether a given tree
scopes a body, and that every scopable function is dominance-correct.  It also proves the
checker's maps, for the decision of scoping (`StrataMantle/DomDecide.lean`), which checks uses
against the tree it computes.

## Main theorems

* `Body.checkScopedBy_iff`: the checker decides `Body.ScopedBy`;
* `Body.ancAt_iff`, `Body.scopeAt_iff`: under a legal tree, the ancestor map gives the ancestors,
  and the use check gives `InScope`;
* `Body.Anc.dom`: under a legal tree, every ancestor of a point dominates it;
* `Func.Scopable.domCorrect`: a scopable function is dominance-correct.
-/

namespace Strata.Mantle

/-- `Point.le` holds exactly for an earlier or equal point of the same block. -/
theorem Point.le_iff {p q : Point} : p.le q = true ↔ p.label = q.label ∧ p.count ≤ q.count := by
  simp only [Point.le, Bool.and_eq_true, decide_eq_true_eq]

namespace Body

variable {env : Env Unit} {α : Type} {t : Tree}

/-! ## The tree's map -/

/-- `tm` holds exactly the blocks of `bs`, by label. -/
def TreeOf (bs : List (Block env α)) (tm : LabelMap (Block env α)) : Prop :=
  ∀ l b, tm.find? l = some b ↔ b ∈ bs ∧ b.label = l

/-- One step of `tree?`. -/
abbrev treeStep (m : LabelMap (Block env α)) (b : Block env α) :
    Option (LabelMap (Block env α)) :=
  if (m.find? b.label).isSome then none else some (m.insert b.label b)

/-- Inserting a block with a new label extends the map to the blocks so far and that one. -/
theorem treeOf_insert {pre : List (Block env α)} {m : LabelMap (Block env α)}
    (hm : TreeOf pre m) {b : Block env α} (hb : m.find? b.label = none) :
    TreeOf (pre ++ [b]) (m.insert b.label b) := by
  intro l b₁
  rw [LabelMap.find?_insert]
  by_cases hl : l = b.label
  · subst hl
    rw [ite_eq_left rfl]
    refine ⟨fun h => ?_, fun ⟨hmem, hlab⟩ => ?_⟩
    · cases h; simp
    · rcases List.mem_append.mp hmem with h | h
      · exact absurd ((hm _ _).mpr ⟨h, hlab⟩) (by simp [hb])
      · simp_all
  · rw [ite_eq_right hl, hm]
    constructor
    · exact fun ⟨h₁, h₂⟩ => ⟨List.mem_append_left _ h₁, h₂⟩
    · rintro ⟨h₁, h₂⟩
      rcases List.mem_append.mp h₁ with h | h
      · exact ⟨h, h₂⟩
      · simp only [List.mem_singleton] at h; subst h; exact absurd h₂.symm hl

/-- Folding `treeStep` from a map of `pre` gives a map of `pre ++ rest`, whose labels are
distinct. -/
theorem foldlM_treeStep : ∀ (rest pre : List (Block env α)) (m : LabelMap (Block env α))
    (tm : LabelMap (Block env α)), TreeOf pre m → (pre.map (·.label)).Nodup →
    rest.foldlM treeStep m = some tm →
      ((pre ++ rest).map (·.label)).Nodup ∧ TreeOf (pre ++ rest) tm
  | [], pre, m, tm, hm, hn, h => by
    cases h; simpa using ⟨hn, hm⟩
  | b :: rest, pre, m, tm, hm, hn, h => by
    have hb : m.find? b.label = none := by
      cases hf : m.find? b.label with
      | none => rfl
      | some _ => simp [List.foldlM_cons, treeStep, hf] at h
    simp only [List.foldlM_cons, treeStep, hb, Option.isSome_none, Bool.false_eq_true,
      ite_false] at h
    have hn₁ : ((pre ++ [b]).map (·.label)).Nodup := by
      rw [List.map_append, List.nodup_append]
      refine ⟨hn, by simp, fun x hx y hy hxy => ?_⟩
      obtain ⟨b₁, hb₁, rfl⟩ := List.mem_map.mp hx
      have hy : y = b.label := by simpa using hy
      have := (hm _ _).mpr ⟨hb₁, hxy.trans hy⟩
      rw [hb] at this
      exact absurd this (by simp)
    simpa using foldlM_treeStep rest (pre ++ [b]) _ tm (treeOf_insert hm hb) hn₁ h

/-- Folding `treeStep` from a map of `pre` succeeds when the labels of `pre ++ rest` are
distinct. -/
theorem foldlM_treeStep_isSome : ∀ (rest pre : List (Block env α)) (m : LabelMap (Block env α)),
    TreeOf pre m → ((pre ++ rest).map (·.label)).Nodup →
    ∃ tm, rest.foldlM treeStep m = some tm
  | [], _, m, _, _ => ⟨m, rfl⟩
  | b :: rest, pre, m, hm, hn => by
    have hb : m.find? b.label = none := by
      cases h : m.find? b.label with
      | none => rfl
      | some b₁ =>
        obtain ⟨hb₁, hl⟩ := (hm _ _).mp h
        rw [List.map_append, List.nodup_append] at hn
        exact absurd rfl (hn.2.2 _ (List.mem_map.mpr ⟨b₁, hb₁, hl⟩) _ List.mem_cons_self)
    simp only [List.foldlM_cons, treeStep, hb, Option.isSome_none, Bool.false_eq_true,
      ite_false]
    exact foldlM_treeStep_isSome rest (pre ++ [b]) _ (treeOf_insert hm hb) (by simpa using hn)

/-- The empty map holds exactly the blocks of the empty body. -/
theorem treeOf_empty : TreeOf ([] : List (Block env α)) ∅ := by
  intro l b; simp

/-- What `tree?` gives holds the blocks, whose labels are distinct. -/
theorem tree?_eq_some {bs : List (Block env α)} {tm : LabelMap (Block env α)}
    (h : tree? bs = some tm) : (bs.map (·.label)).Nodup ∧ TreeOf bs tm := by
  simpa using foldlM_treeStep bs [] ∅ tm treeOf_empty List.nodup_nil h

/-- `tree?` succeeds when the labels are distinct. -/
theorem tree?_isSome {bs : List (Block env α)} (h : (bs.map (·.label)).Nodup) :
    ∃ tm, tree? bs = some tm :=
  foldlM_treeStep_isSome bs [] ∅ treeOf_empty (by simpa using h)

/-- Two blocks of a body whose labels are distinct are equal if their labels are. -/
theorem eq_of_label_eq {bs : List (Block env α)} (hn : (bs.map (·.label)).Nodup)
    {b b₁ : Block env α} (hb : b ∈ bs) (hb₁ : b₁ ∈ bs) (h : b.label = b₁.label) : b = b₁ := by
  obtain ⟨tm, ht⟩ := tree?_isSome hn
  have htr := (tree?_eq_some ht).2
  exact Option.some.inj (((htr _ _).mpr ⟨hb, h⟩).symm.trans ((htr _ _).mpr ⟨hb₁, rfl⟩))

/-! ## Ancestry -/

/-- Ancestry in a body's tree is transitive. -/
theorem Anc.trans {bs : List (Block env α)} {p q r : Point} (h₁ : Anc bs t p q)
    (h₂ : Anc bs t q r) : Anc bs t p r := by
  induction h₂ with
  | refl => exact h₁
  | fall _ ih => exact .fall ih
  | parent _ hb hi ih => exact .parent ih hb hi

/-- A point is above every later point of its block. -/
theorem Anc.of_count_le {bs : List (Block env α)} (l : Label) {j : Nat} :
    ∀ {k : Nat}, j ≤ k → Anc bs t ⟨l, j⟩ ⟨l, k⟩
  | 0, h => by cases Nat.le_zero.mp h; exact .refl _
  | k + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact .fall (Anc.of_count_le l (Nat.le_of_lt_succ h))
    · exact .refl _

/-- `Point.le` implies ancestry. -/
theorem Anc.of_le {bs : List (Block env α)} {p q : Point} (h : p.le q = true) :
    Anc bs t p q := by
  obtain ⟨h₁, h₂⟩ := Point.le_iff.mp h
  obtain ⟨l, j⟩ := p
  obtain ⟨_, k⟩ := q
  cases h₁
  exact Anc.of_count_le l h₂

/-- An ancestor of a point after an instruction is that point, or an ancestor of the point
before it. -/
theorem anc_succ_iff {bs : List (Block env α)} {d : Point} {l : Label} {k : Nat} :
    Anc bs t d ⟨l, k + 1⟩ ↔ d = ⟨l, k + 1⟩ ∨ Anc bs t d ⟨l, k⟩ := by
  constructor
  · intro h
    generalize hp : (⟨l, k + 1⟩ : Point) = p at h
    cases h with
    | refl => exact .inl rfl
    | fall h =>
      cases hp
      exact .inr h
    | parent _ _ _ => exact absurd (congrArg Point.count hp) (Nat.succ_ne_zero k)
  · rintro (rfl | h)
    · exact .refl _
    · exact .fall h

/-- An ancestor of the start of a block is that point, or an ancestor of the block's
parent. -/
theorem anc_zero_iff {bs : List (Block env α)} (hn : (bs.map (·.label)).Nodup)
    {b : Block env α} (hb : b ∈ bs) {d : Point} :
    Anc bs t d ⟨b.label, 0⟩ ↔ d = ⟨b.label, 0⟩ ∨ ∃ q, t b.label = some q ∧ Anc bs t d q := by
  constructor
  · intro h
    generalize hp : (⟨b.label, 0⟩ : Point) = p at h
    cases h with
    | refl => exact .inl rfl
    | fall _ => exact absurd (congrArg Point.count hp) (Nat.succ_ne_zero _).symm
    | parent h hb₁ hq =>
      cases eq_of_label_eq hn hb hb₁ (congrArg Point.label hp)
      exact .inr ⟨_, hq, h⟩
  · rintro (rfl | ⟨q, hq, h⟩)
    · exact .refl _
    · exact .parent h hb hq

/-- An ancestor of a point of block `b` is an earlier or equal point of `b`, or an ancestor of
`b`'s parent. -/
theorem anc_block_iff {bs : List (Block env α)} (hn : (bs.map (·.label)).Nodup)
    {b : Block env α} (hb : b ∈ bs) (d : Point) : ∀ k,
    Anc bs t d ⟨b.label, k⟩ ↔ d.le ⟨b.label, k⟩ = true ∨ ∃ q, t b.label = some q ∧ Anc bs t d q
  | 0 => by
    rw [anc_zero_iff hn hb, Point.le_iff, Nat.le_zero]
    obtain ⟨l, j⟩ := d
    rw [Point.mk.injEq]
  | k + 1 => by
    obtain ⟨l, j⟩ := d
    rw [anc_succ_iff, anc_block_iff hn hb _ k, Point.le_iff, Point.le_iff, Point.mk.injEq]
    dsimp only
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, hj⟩ | h)
      · exact .inl ⟨rfl, Nat.le_refl _⟩
      · exact .inl ⟨rfl, Nat.le_succ_of_le hj⟩
      · exact .inr h
    · rintro (⟨rfl, hj⟩ | h)
      · rcases Nat.lt_or_eq_of_le hj with hj | rfl
        · exact .inr (.inl ⟨rfl, Nat.le_of_lt_succ hj⟩)
        · exact .inl ⟨rfl, rfl⟩
      · exact .inr (.inr h)

/-! ## Walking up the tree -/

/-- The parent of `q`'s block in the tree `tm`. -/
def up (tm : LabelMap (Block env α)) (t : Tree) (q : Point) : Option Point :=
  (tm.find? q.label).bind fun b => t b.label

/-- Where `j` steps up from `q`'s block lead. -/
def walk (tm : LabelMap (Block env α)) (t : Tree) : Nat → Point → Option Point
  | 0, q => some q
  | j + 1, q => (up tm t q).bind (walk tm t j)

/-- Walking `i + m` steps up is walking `i` steps, then `m`. -/
theorem walk_add (tm : LabelMap (Block env α)) :
    ∀ (i m : Nat) (q : Point), walk tm t (i + m) q = (walk tm t i q).bind (walk tm t m)
  | 0, m, q => by simp [walk]
  | i + 1, m, q => by
    rw [Nat.add_right_comm, walk, walk, Option.bind_assoc]
    exact congrArg _ (funext fun r => walk_add tm i m r)

/-- An ancestor lies on the walk up. -/
theorem walk_of_anc {bs : List (Block env α)} {tm : LabelMap (Block env α)} (ht : TreeOf bs tm)
    {p q : Point} (h : Anc bs t p q) : ∃ j r, walk tm t j q = some r ∧ p.le r = true := by
  induction h with
  | refl => exact ⟨0, _, rfl, Point.le_iff.mpr ⟨rfl, Nat.le_refl _⟩⟩
  | @fall l k _ ih =>
    obtain ⟨_ | j, r, hw, hr⟩ := ih
    · cases hw
      exact ⟨0, _, rfl, Point.le_iff.mpr ⟨(Point.le_iff.mp hr).1, by
        have := (Point.le_iff.mp hr).2; simp only at this ⊢; omega⟩⟩
    · exact ⟨j + 1, r, hw, hr⟩
  | parent _ hb hi ih =>
    obtain ⟨j, r, hw, hr⟩ := ih
    exact ⟨j + 1, r, by simp [walk, up, (ht _ _).mpr ⟨hb, rfl⟩, hi, hw], hr⟩

/-- A walk that lasts `j` steps lasts every shorter number of steps. -/
theorem walk_ne_none_of_le {tm : LabelMap (Block env α)} {q : Point} {i j : Nat}
    (h : walk tm t j q ≠ none) (hij : i ≤ j) : walk tm t i q ≠ none := by
  intro hi
  apply h
  rw [show j = i + (j - i) by omega, walk_add, hi, Option.bind_none]

/-- After one step, the walk depends only on the starting block, not the count. -/
theorem walk_succ_congr (tm : LabelMap (Block env α)) {q q₁ : Point} (h : q.label = q₁.label)
    (j : Nat) : walk tm t (j + 1) q = walk tm t (j + 1) q₁ := by
  simp only [walk, up, h]

/-- Two points of the walk in the same block repeat it from there on. -/
theorem walk_periodic {tm : LabelMap (Block env α)} {q r₁ r₂ : Point} {a b : Nat}
    (ha : walk tm t a q = some r₁) (hb : walk tm t b q = some r₂) (h : r₁.label = r₂.label)
    (m : Nat) : walk tm t (a + (m + 1)) q = walk tm t (b + (m + 1)) q := by
  rw [walk_add, walk_add, ha, hb, Option.bind_some, Option.bind_some, walk_succ_congr tm h]

/-- In a legal tree, every parent is a node of the body. -/
theorem idom_node {bs : List (Block env α)} (hL : Legal bs t) {b : Block env α} (hb : b ∈ bs)
    {p : Point} (hp : t b.label = some p) : Node bs p := by
  cases bs with
  | nil => simp at hb
  | cons e rest =>
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [hL.entry b rfl] at hp
    · obtain ⟨p₁, hp₁, hn⟩ := hL.parent b hb
      exact (Option.some.inj (hp.symm.trans hp₁)) ▸ hn

/-- A node of the body names one of its blocks. -/
theorem label_mem_of_node {bs : List (Block env α)} {p : Point} (h : Node bs p) :
    p.label ∈ bs.map (·.label) := by
  obtain ⟨b, hb, hl, _⟩ := h
  exact List.mem_map.mpr ⟨b, hb, hl⟩

/-- In a legal tree, a walk up from a block of the body stays among its blocks. -/
theorem walk_label_mem {bs : List (Block env α)} {tm : LabelMap (Block env α)} (hL : Legal bs t)
    (ht : TreeOf bs tm) : ∀ (i : Nat) (q r : Point), q.label ∈ bs.map (·.label) →
      walk tm t i q = some r → r.label ∈ bs.map (·.label)
  | 0, _, _, hq, h => by cases h; exact hq
  | i + 1, q, r, _, h => by
    simp only [walk, up, Option.bind_eq_some_iff] at h
    obtain ⟨q₁, ⟨b, hb, hi⟩, h⟩ := h
    exact walk_label_mem hL ht i q₁ r
      (label_mem_of_node (idom_node hL ((ht _ _).mp hb).1 hi)) h

/-- In a legal tree, a walk up from a block of the body ends. -/
theorem walk_eventually_none {bs : List (Block env α)} {tm : LabelMap (Block env α)}
    (hL : Legal bs t) (ht : TreeOf bs tm) {q : Point} (hq : q.label ∈ bs.map (·.label)) :
    ∃ N, walk tm t N q = none := by
  obtain ⟨b, hb, hl⟩ := List.mem_map.mp hq
  obtain ⟨j, r, hw, hr⟩ := walk_of_anc ht (hL.rooted b hb)
  cases bs with
  | nil => simp at hb
  | cons e rest =>
    have hre : e.label = r.label := (Point.le_iff.mp hr).1
    have hup : up tm t r = none := by
      simp [up, ← hre, (ht _ _).mpr ⟨List.mem_cons_self, rfl⟩, hL.entry e rfl]
    refine ⟨j + 1, ?_⟩
    rw [walk_succ_congr tm (q₁ := ⟨b.label, 0⟩) hl.symm, walk_add, hw, Option.bind_some]
    simp [walk, hup]

/-- In a legal tree, the walk up from a block visits no label twice. -/
theorem walk_label_ne {bs : List (Block env α)} {tm : LabelMap (Block env α)} (hL : Legal bs t)
    (ht : TreeOf bs tm) {q : Point} (hq : q.label ∈ bs.map (·.label)) {a b : Nat}
    {r₁ r₂ : Point} (hab : a < b) (h₁ : walk tm t a q = some r₁) (h₂ : walk tm t b q = some r₂) :
    r₁.label ≠ r₂.label := by
  intro heq
  -- From `b` on, the walk repeats its steps from `a`, so it never ends; but it does.
  obtain ⟨N, hN⟩ := walk_eventually_none hL ht hq
  have : ∀ N, walk tm t N q ≠ none := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      by_cases hN : N ≤ b
      · exact walk_ne_none_of_le (by simp [h₂]) hN
      · obtain ⟨m, rfl⟩ : ∃ m, N = b + (m + 1) := ⟨N - b - 1, by omega⟩
        rw [← walk_periodic h₁ h₂ heq m]
        exact ih _ (by omega)
  exact this N hN

/-- In a legal tree, the walk up from a block leaves the body within its block count. -/
theorem walk_length {bs : List (Block env α)} {tm : LabelMap (Block env α)} (hL : Legal bs t)
    (ht : TreeOf bs tm) {q : Point} (hq : q.label ∈ bs.map (·.label)) :
    walk tm t bs.length q = none := by
  cases hn : walk tm t bs.length q with
  | none => rfl
  | some r₀ =>
    exfalso
    have hlast : walk tm t bs.length q ≠ none := by simp [hn]
    let f : Nat → Label := fun i => ((walk tm t i q).map (·.label)).getD default
    have hf : ∀ i ≤ bs.length, ∃ r, walk tm t i q = some r ∧ f i = r.label := fun i hi => by
      obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (walk_ne_none_of_le hlast hi)
      exact ⟨r, hr, by simp [f, hr]⟩
    -- `bs.length + 1` distinct labels, all of the body: too many.
    have hnodup : ((List.range (bs.length + 1)).map f).Nodup := by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      refine List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab => ?_
      simp only [List.mem_range] at ha hb
      obtain ⟨r₁, h₁, hf₁⟩ := hf a (by omega)
      obtain ⟨r₂, h₂, hf₂⟩ := hf b (by omega)
      rw [hf₁, hf₂]
      exact walk_label_ne hL ht hq hab h₁ h₂
    have hsub : (List.range (bs.length + 1)).map f ⊆ bs.map (·.label) := by
      intro l hl
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
      obtain ⟨r, hr, hfr⟩ := hf i (by have := List.mem_range.mp hi; omega)
      exact hfr ▸ walk_label_mem hL ht i q r hq hr
    have := List.length_le_of_nodup_subset hnodup hsub
    simp only [List.length_map, List.length_range] at this
    omega

/-! ## Chains -/

/-- Unfolding `chain` one step: the point, then the parent's chain. -/
theorem chain_succ (tm : LabelMap (Block env α)) (f : Nat) (b : Block env α) (k : Nat) :
    chain tm t (f + 1) b k = (b, k) ::
      match parent tm t b with
      | some (c, j) => chain tm t f c j
      | none => [] := rfl

/-- A block's parent in the map is a block of the body, at the point the tree gives it. -/
theorem parent_eq_some {bs : List (Block env α)} {tm : LabelMap (Block env α)}
    (ht : TreeOf bs tm) {b c : Block env α} {j : Nat} (h : parent tm t b = some (c, j)) :
    c ∈ bs ∧ t b.label = some ⟨c.label, j⟩ := by
  simp only [parent, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨l, k⟩, hp, c₁, hc₁, rfl, rfl⟩ := h
  obtain ⟨hc, hl⟩ := (ht _ _).mp hc₁
  exact ⟨hc, by rw [hp, hl]⟩

/-- The blocks of a chain from a block of the body are blocks of the body. -/
theorem mem_of_mem_chain {bs : List (Block env α)} {tm : LabelMap (Block env α)}
    (ht : TreeOf bs tm) : ∀ {f : Nat} {b c : Block env α} {k j : Nat}, b ∈ bs →
      (c, j) ∈ chain tm t f b k → c ∈ bs
  | 0, _, _, _, _, _, h => by simp [chain] at h
  | f + 1, b, c, k, j, hb, h => by
    rw [chain_succ, List.mem_cons] at h
    rcases h with h | h
    · cases h; exact hb
    · split at h
      next hp => exact mem_of_mem_chain ht (parent_eq_some ht hp).1 h
      next => simp at h

/-- What is above a chain's start is its ancestor. -/
theorem anc_of_above {bs : List (Block env α)} {tm : LabelMap (Block env α)} (ht : TreeOf bs tm)
    {p : Point} : ∀ {f : Nat} {b : Block env α} {k : Nat}, b ∈ bs →
      above (chain tm t f b k) p = true → Anc bs t p ⟨b.label, k⟩
  | 0, _, _, _, h => by simp [chain, above] at h
  | f + 1, b, k, hb, h => by
    rw [above, chain_succ, List.any_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Anc.of_le h
    · split at h
      next hp =>
        obtain ⟨hc, hi⟩ := parent_eq_some ht hp
        exact (Anc.parent (anc_of_above ht hc h) hb hi).trans (Anc.of_count_le _ (Nat.zero_le _))
      next => simp at h

/-- In a legal tree, every point of the walk up from a block, short of the fuel, is on the
block's chain. -/
theorem mem_chain_of_walk {bs : List (Block env α)} {tm : LabelMap (Block env α)} (hL : Legal bs t)
    (ht : TreeOf bs tm) : ∀ {j f : Nat} {b : Block env α} {k : Nat} {r : Point}, b ∈ bs →
      j < f → walk tm t j ⟨b.label, k⟩ = some r →
        ∃ c i, (c, i) ∈ chain tm t f b k ∧ r = ⟨c.label, i⟩
  | _, 0, _, _, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | 0, _ + 1, b, k, _, _, _, h => by
    cases h
    exact ⟨b, k, by simp [chain_succ], rfl⟩
  | j + 1, f + 1, b, k, r, hb, hj, h => by
    simp only [walk, up, (ht _ _).mpr ⟨hb, rfl⟩, Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨⟨l, i⟩, hi, hw⟩ := h
    obtain ⟨c, hc, hl, _⟩ := idom_node hL hb hi
    have hp : parent tm t b = some (c, i) := by simp [parent, hi, (ht _ _).mpr ⟨hc, hl⟩]
    -- `hl` is `c.label = ⟨l, i⟩.label`; reduce it to `c.label = l`.
    simp only at hl
    subst hl
    obtain ⟨c₁, i₁, hm, rfl⟩ := mem_chain_of_walk hL ht hc (Nat.lt_of_succ_lt_succ hj) hw
    exact ⟨c₁, i₁, by simp [chain_succ, hp, hm], rfl⟩

/-- In a legal tree, `above` along a block's chain, with the block count as fuel, finds every
ancestor of the chain's start. -/
theorem above_iff {bs : List (Block env α)} {tm : LabelMap (Block env α)} (hL : Legal bs t)
    (ht : TreeOf bs tm) {b : Block env α} (hb : b ∈ bs) (k : Nat) (p : Point) :
    above (chain tm t bs.length b k) p = true ↔ Anc bs t p ⟨b.label, k⟩ := by
  refine ⟨anc_of_above ht hb, fun h => ?_⟩
  obtain ⟨j, r, hw, hr⟩ := walk_of_anc ht h
  have hj : j < bs.length := by
    apply Nat.lt_of_not_le
    intro hj
    have := walk_length hL ht (q := ⟨b.label, k⟩) (List.mem_map.mpr ⟨b, hb, rfl⟩)
    rw [show j = bs.length + (j - bs.length) by omega, walk_add, this] at hw
    simp at hw
  obtain ⟨c, i, hm, rfl⟩ := mem_chain_of_walk hL ht hb hj hw
  exact List.any_eq_true.mpr ⟨(c, i), hm, hr⟩

/-! ## Legality -/

/-! ### Ancestor maps -/

/-- Every entry of the map `m` names exactly the points above the start of its block, other
than the start itself and the points before it. -/
def AncGood (bs : List (Block env α)) (t : Tree) (m : AncMap) : Prop :=
  ∀ b ∈ bs, ∀ a, m.find? b.label = some a → ∀ p,
    ((a.find? p.label).any (decide <| p.count ≤ ·) = true ↔ ∃ q, t b.label = some q ∧ Anc bs t p q)

/-- The empty map has no entries. -/
theorem ancGood_empty (bs : List (Block env α)) : AncGood bs t ∅ := by
  intro b _ a h
  simp at h

/-- Adding a good entry keeps the map good. -/
theorem ancGood_insert {bs : List (Block env α)} (hn : (bs.map (·.label)).Nodup) {m : AncMap}
    (hm : AncGood bs t m) {b : Block env α} (hb : b ∈ bs) {a : LabelMap Nat}
    (ha : ∀ p, ((a.find? p.label).any (decide <| p.count ≤ ·) = true ↔
      ∃ q, t b.label = some q ∧ Anc bs t p q)) :
    AncGood bs t (m.insert b.label a) := by
  intro b₁ hb₁ a₁ h
  rw [LabelMap.find?_insert] at h
  split at h
  next hl =>
    cases h
    cases eq_of_label_eq hn hb₁ hb hl
    exact ha
  next => exact hm b₁ hb₁ a₁ h

/-- The entry of a block whose parent is `p`, in block `c`, extends `c`'s by `p`. -/
theorem ancs_step {bs : List (Block env α)} (hn : (bs.map (·.label)).Nodup) {c : Block env α}
    (hc : c ∈ bs) {a : LabelMap Nat}
    (ha : ∀ p, ((a.find? p.label).any (decide <| p.count ≤ ·) = true ↔
      ∃ q, t c.label = some q ∧ Anc bs t p q))
    {p : Point} (hp : p.label = c.label) (p₁ : Point) :
    ((a.insert p.label (max p.count ((a.find? p.label).getD 0))).find? p₁.label).any
        (decide <| p₁.count ≤ ·) = true ↔ Anc bs t p₁ p := by
  obtain ⟨l, j⟩ := p
  simp only at hp
  subst hp
  rw [anc_block_iff hn hc p₁ j, ← ha p₁, Point.le_iff, LabelMap.find?_insert]
  dsimp only
  by_cases hl : p₁.label = c.label
  · rw [ite_eq_left hl, hl]
    cases a.find? c.label with
    | none => simp
    | some o =>
      simp only [Option.any_some, Option.getD_some, decide_eq_true_eq, true_and]
      omega
  · simp [hl]

/-- `addAncs` adds only good entries. -/
theorem addAncs_good {bs : List (Block env α)} {tm : LabelMap (Block env α)}
    (hn : (bs.map (·.label)).Nodup) (ht : TreeOf bs tm) :
    ∀ (f : Nat) (m : AncMap) (b : Block env α), b ∈ bs → AncGood bs t m →
      AncGood bs t (addAncs tm t f m b)
  | 0, _, _, _, hm => hm
  | f + 1, m, b, hb, hm => by
    rw [addAncs]
    by_cases hs : (m.find? b.label).isSome
    · rw [ite_eq_left hs]
      exact hm
    rw [ite_eq_right hs]
    cases hi : t b.label with
    | none => exact ancGood_insert hn hm hb fun p => by simp [hi]
    | some p =>
      dsimp only
      cases hc : tm.find? p.label with
      | none => exact hm
      | some c =>
        obtain ⟨hc₁, hl⟩ := (ht _ _).mp hc
        have hm₁ := addAncs_good hn ht f m c hc₁ hm
        dsimp only
        cases ha : (addAncs tm t f m c).find? p.label with
        | none => exact hm₁
        | some a =>
          refine ancGood_insert hn hm₁ hb fun p₁ => ?_
          rw [ancs_step hn hc₁ (hm₁ c hc₁ a (hl ▸ ha)) hl.symm p₁, hi]
          exact ⟨fun h => ⟨p, rfl, h⟩, fun ⟨_, hq, h⟩ => Option.some.inj hq ▸ h⟩

/-- Every entry of `ancs` is good. -/
theorem ancs_good {bs : List (Block env α)} {tm : LabelMap (Block env α)}
    (hn : (bs.map (·.label)).Nodup) (ht : TreeOf bs tm) : AncGood bs t (ancs tm t bs) := by
  have : ∀ (rest : List (Block env α)) (m : AncMap), (∀ b ∈ rest, b ∈ bs) → AncGood bs t m →
      AncGood bs t (rest.foldl (addAncs tm t bs.length) m) := by
    intro rest
    induction rest with
    | nil => exact fun _ _ hm => hm
    | cons b rest ih =>
      intro m hr hm
      exact ih _ (fun b₁ hb₁ => hr b₁ (List.mem_cons_of_mem _ hb₁))
        (addAncs_good hn ht _ m b (hr b List.mem_cons_self) hm)
  exact this bs ∅ (fun _ h => h) (ancGood_empty bs)

/-- What `ancAt` finds is an ancestor. -/
theorem ancAt_sound {bs : List (Block env α)} {tm : LabelMap (Block env α)} {m : AncMap}
    {n : Nat} (hn : (bs.map (·.label)).Nodup) (ht : TreeOf bs tm) (hm : AncGood bs t m)
    {b : Block env α} (hb : b ∈ bs) {k : Nat} {p : Point} (h : ancAt tm t n m b k p = true) :
    Anc bs t p ⟨b.label, k⟩ := by
  rw [ancAt] at h
  split at h
  next a ha =>
    rw [Bool.or_eq_true, hm b hb a ha p] at h
    exact (anc_block_iff hn hb p k).mpr h
  next => exact anc_of_above ht hb h

/-- In a legal tree, `ancAt` finds every ancestor. -/
theorem ancAt_iff {bs : List (Block env α)} {tm : LabelMap (Block env α)} {m : AncMap}
    (hL : Legal bs t) (ht : TreeOf bs tm) (hm : AncGood bs t m) {b : Block env α} (hb : b ∈ bs)
    (k : Nat) (p : Point) : ancAt tm t bs.length m b k p = true ↔ Anc bs t p ⟨b.label, k⟩ := by
  rw [ancAt]
  cases ha : m.find? b.label with
  | some a => rw [Bool.or_eq_true, hm b hb a ha p, anc_block_iff hL.distinct hb p k]
  | none => exact above_iff hL ht hb k p

/-! ### Legality -/

/-- `instrJumpsOK` holds exactly when each instruction's transfers are legal from its point. -/
theorem instrJumpsOK_iff (tm : LabelMap (Block env α)) (anc : Nat → Point → Bool) :
    ∀ (k : Nat) (is : List (Instruction env α)), instrJumpsOK tm t anc k is = true ↔
      ∀ j i, is[j]? = some i → ∀ s ∈ i.succs, jumpOK tm t (anc (k + j)) s = true
  | _, [] => by simp [instrJumpsOK]
  | k, i :: is => by
    simp only [instrJumpsOK, Bool.and_eq_true, List.all_eq_true, Array.mem_toList_iff,
      instrJumpsOK_iff tm anc (k + 1) is]
    constructor
    · rintro ⟨h₀, h⟩ (_ | j) i₁ hj
      · cases hj; exact h₀
      · simpa [Nat.add_assoc, Nat.add_comm 1] using h j i₁ hj
    · intro h
      exact ⟨h 0 i rfl, fun j i₁ hj => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using h (j + 1) i₁ hj⟩

/-- `jumpOK` holds exactly when `anc` holds of the target's parent. -/
theorem jumpOK_iff {bs : List (Block env α)} {tm : LabelMap (Block env α)} (ht : TreeOf bs tm)
    (anc : Point → Bool) (s : BlockValue) : jumpOK tm t anc s = true ↔
      ∀ v p, v ∈ bs → v.label = s.target → t v.label = some p → anc p = true := by
  simp only [jumpOK, Option.all_eq_true, Option.bind_eq_some_iff]
  constructor
  · exact fun h v p hv hl hp => h p ⟨v, (ht _ _).mpr ⟨hv, hl⟩, hp⟩
  · rintro h p ⟨v, hv, hp⟩
    exact h v p ((ht _ _).mp hv).1 ((ht _ _).mp hv).2 hp

/-- `node` decides `Node`. -/
theorem node_iff {bs : List (Block env α)} {tm : LabelMap (Block env α)} (ht : TreeOf bs tm)
    (p : Point) : node tm p = true ↔ Node bs p := by
  simp only [node, Option.any_eq_true, decide_eq_true_eq, Node]
  constructor
  · rintro ⟨b, hb, hc⟩
    exact ⟨b, ((ht _ _).mp hb).1, ((ht _ _).mp hb).2, hc⟩
  · rintro ⟨b, hb, hl, hc⟩
    exact ⟨b, (ht _ _).mpr ⟨hb, hl⟩, hc⟩

/-- A non-empty body's root is the start of its entry. -/
theorem root_cons (e : Block env α) (rest : List (Block env α)) :
    root (e :: rest) = ⟨e.label, 0⟩ := rfl

/-- Every tree of an empty body is legal. -/
theorem legal_nil (t : Tree) : Legal ([] : List (Block env α)) t :=
  ⟨List.nodup_nil, (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ _ _ h => by cases h <;> contradiction)⟩

/-- `legal` decides legality, the labels being distinct. -/
theorem legal_iff {bs : List (Block env α)} {tm : LabelMap (Block env α)} {m : AncMap}
    (hn : (bs.map (·.label)).Nodup) (ht : TreeOf bs tm) (hm : AncGood bs t m) :
    legal tm t m bs = true ↔ Legal bs t := by
  cases bs with
  | nil =>
    simp only [legal, true_iff]
    exact legal_nil t
  | cons e rest =>
    simp only [legal, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true,
      Option.any_eq_true, node_iff ht, blockOK, instrJumpsOK_iff, jumpOK_iff ht,
      Array.mem_toList_iff, Array.getElem?_toList, Nat.zero_add]
    constructor
    · rintro ⟨⟨he, hb⟩, hi⟩
      refine ⟨hn, fun e₁ h => by cases h; exact he, hi, fun b h => ?_, fun u v p h hp => ?_⟩
      · exact ancAt_sound hn ht hm h (hb b h).1.1
      · cases h with
        | instr hb₁ hk hs hv hl =>
          exact ancAt_sound hn ht hm hb₁ ((hb _ hb₁).1.2 _ _ hk _ hs v p hv hl hp)
        | term hb₁ hs hv hl => exact ancAt_sound hn ht hm hb₁ ((hb _ hb₁).2 _ hs v p hv hl hp)
    · intro hL
      refine ⟨⟨hL.entry e rfl, fun b hb => ⟨⟨?_, fun k i hk s hs v p hv hl hp => ?_⟩,
        fun s hs v p hv hl hp => ?_⟩⟩, hL.parent⟩
      · exact (ancAt_iff hL ht hm hb 0 _).mpr (hL.rooted b hb)
      · exact (ancAt_iff hL ht hm hb k p).mpr (hL.jump _ v p (.instr hb hk hs hv hl) hp)
      · exact (ancAt_iff hL ht hm hb _ p).mpr (hL.jump _ v p (.term hb hs hv hl) hp)

/-! ## Scope -/

/-- `x` is defined at `d` by block `b`: a parameter at its start, or an instruction's result
after the instruction. -/
def DefIn (b : Block env α) (x : ValId) (d : Point) : Prop :=
  (∃ v ∈ b.params.toList, v.id = x ∧ d = ⟨b.label, 0⟩) ∨
    ∃ k i, b.instrs[k]? = some i ∧ i.result.id = x ∧ d = ⟨b.label, k + 1⟩

/-- `x` is defined at `d` exactly when a block of the body defines it there. -/
theorem defAt_iff {bs : List (Block env α)} {x : ValId} {d : Point} :
    DefAt bs x d ↔ ∃ b ∈ bs, DefIn b x d := by
  constructor
  · rintro (⟨hb, hd, hx⟩ | ⟨hb, hi, hx⟩)
    · exact ⟨_, hb, .inl ⟨_, Array.mem_toList_iff.mpr hd, hx, rfl⟩⟩
    · exact ⟨_, hb, .inr ⟨_, _, hi, hx, rfl⟩⟩
  · rintro ⟨b, hb, ⟨v, hv, hx, rfl⟩ | ⟨k, i, hi, hx, rfl⟩⟩
    · exact .param hb (Array.mem_toList_iff.mp hv) hx
    · exact .result hb hi hx

/-- The empty map has no definitions. -/
theorem DefMap.get_leaf (x : ValId) : DefMap.get .leaf x = [] := by
  simp [DefMap.get]

/-- Adding `p` defining `y` adds it and keeps the rest. -/
theorem DefMap.mem_get_add (m : DefMap) (y : ValId) (p : Point) (x : ValId) (d : Point) :
    d ∈ (m.add y p).get x ↔ (x = y ∧ d = p) ∨ d ∈ m.get x := by
  by_cases h : x = y
  · subst h
    simp [DefMap.get, DefMap.add, NatTrie.find?_insert]
  · have hid : x.id ≠ y.id := fun e => h (by cases x; cases y; cases e; rfl)
    simp [DefMap.get, DefMap.add, NatTrie.find?_insert, hid, h]

/-- Adding the parameters `ds`, each defined at `q`. -/
theorem mem_get_foldl_params (q : Point) : ∀ (ds : List (ValDecl env)) (m : DefMap) (x : ValId)
    (d : Point), d ∈ (ds.foldl (fun m v => m.add v.id q) m).get x ↔
      (∃ v ∈ ds, v.id = x ∧ d = q) ∨ d ∈ m.get x
  | [], _, _, _ => by simp
  | v :: ds, m, x, d => by
    rw [List.foldl_cons, mem_get_foldl_params q ds, DefMap.mem_get_add]
    constructor
    · rintro (⟨v₁, hv₁, h⟩ | ⟨rfl, rfl⟩ | h)
      · exact .inl ⟨v₁, List.mem_cons_of_mem _ hv₁, h⟩
      · exact .inl ⟨v, List.mem_cons_self, rfl, rfl⟩
      · exact .inr h
    · rintro (⟨v₁, hv₁, h⟩ | h)
      · rcases List.mem_cons.mp hv₁ with rfl | hv₁
        · exact .inr (.inl ⟨h.1.symm, h.2⟩)
        · exact .inl ⟨v₁, hv₁, h⟩
      · exact .inr (.inr h)

/-- Adding the results of the instructions `is` of block `l`, the first at count `k`. -/
theorem mem_get_instrDefs (l : Label) : ∀ (is : List (Instruction env α)) (m : DefMap)
    (k : Nat) (x : ValId) (d : Point), d ∈ (instrDefs l m k is).get x ↔
      (∃ j i, is[j]? = some i ∧ i.result.id = x ∧ d = ⟨l, k + j + 1⟩) ∨ d ∈ m.get x
  | [], _, _, _, _ => by simp [instrDefs]
  | i :: is, m, k, x, d => by
    rw [instrDefs, mem_get_instrDefs l is, DefMap.mem_get_add]
    constructor
    · rintro (⟨j, i₁, hj, hx, rfl⟩ | ⟨rfl, rfl⟩ | h)
      · exact .inl ⟨j + 1, i₁, hj, hx, congrArg (Point.mk l) (by omega)⟩
      · exact .inl ⟨0, i, rfl, rfl, rfl⟩
      · exact .inr h
    · rintro (⟨_ | j, i₁, hj, hx, rfl⟩ | h)
      · cases hj
        exact .inr (.inl ⟨hx.symm, rfl⟩)
      · exact .inl ⟨j, i₁, hj, hx, congrArg (Point.mk l) (by omega)⟩
      · exact .inr (.inr h)

/-- Adding what block `b` defines. -/
theorem mem_get_blockDefs (m : DefMap) (b : Block env α) (x : ValId) (d : Point) :
    d ∈ (blockDefs m b).get x ↔ DefIn b x d ∨ d ∈ m.get x := by
  rw [blockDefs, mem_get_instrDefs, mem_get_foldl_params, DefIn]
  simp only [Nat.zero_add, Array.getElem?_toList]
  rw [or_left_comm, ← or_assoc]

/-- Adding what the blocks `rest` define. -/
theorem mem_get_foldl_blockDefs : ∀ (rest : List (Block env α)) (m : DefMap) (x : ValId)
    (d : Point), d ∈ (rest.foldl blockDefs m).get x ↔ (∃ b ∈ rest, DefIn b x d) ∨ d ∈ m.get x
  | [], _, _, _ => by simp
  | b :: rest, m, x, d => by
    rw [List.foldl_cons, mem_get_foldl_blockDefs rest, mem_get_blockDefs]
    constructor
    · rintro (⟨b₁, hb₁, h⟩ | h | h)
      · exact .inl ⟨b₁, List.mem_cons_of_mem _ hb₁, h⟩
      · exact .inl ⟨b, List.mem_cons_self, h⟩
      · exact .inr h
    · rintro (⟨b₁, hb₁, h⟩ | h)
      · rcases List.mem_cons.mp hb₁ with rfl | hb₁
        · exact .inr (.inl h)
        · exact .inl ⟨b₁, hb₁, h⟩
      · exact .inr (.inr h)

/-- `defs` has exactly the points that define each value. -/
theorem mem_defs {bs : List (Block env α)} (x : ValId) (d : Point) :
    d ∈ (defs bs).get x ↔ DefAt bs x d := by
  rw [defs, mem_get_foldl_blockDefs, DefMap.get_leaf, defAt_iff, List.mem_nil_iff, or_false]

/-- In a legal tree, `scopeAt`, with `Λ` visible on entry, is `InScope`. -/
theorem scopeAt_iff {bs : List (Block env α)} {tm : LabelMap (Block env α)} {m : AncMap}
    (hL : Legal bs t) (ht : TreeOf bs tm) (hm : AncGood bs t m) (Λ : ValId → Bool) {b : Block env α}
    (hb : b ∈ bs) (k : Nat) (x : ValId) :
    (scopeAt tm t bs.length m (defs bs) b k x || Λ x) = true ↔
      InScope bs t (Λ · = true) x ⟨b.label, k⟩ := by
  rw [scopeAt, Bool.or_eq_true, List.any_eq_true, InScope]
  simp only [mem_defs, ancAt_iff hL ht hm hb]

end Body

open Body

variable {env : Env Unit} {α : Type}

/-- `usesIn` holds exactly when every operand and successor argument satisfies `σ`. -/
theorem usesIn_iff (σ : ValId → Bool) (args : Array ValId) (succs : Array BlockValue) :
    usesIn σ args succs = true ↔ ∀ x, (x ∈ args ∨ ∃ s ∈ succs, x ∈ s.args) → σ x = true := by
  simp only [usesIn, Bool.and_eq_true, List.all_eq_true, Array.mem_toList_iff]
  constructor
  · rintro ⟨h₁, h₂⟩ x (hx | ⟨s, hs, hx⟩)
    · exact h₁ x hx
    · exact h₂ s hs x hx
  · exact fun h => ⟨fun x hx => h x (.inl hx), fun s hs x hx => h x (.inr ⟨s, hs, hx⟩)⟩

namespace Body

/-- `instrUsesOK` holds exactly when every instruction uses only what `σ` puts in scope at its
count. -/
theorem instrUsesOK_iff (σ : Nat → ValId → Bool) : ∀ (k : Nat) (is : List (Instruction env α)),
    instrUsesOK σ k is = true ↔ ∀ j i, is[j]? = some i → ∀ x, i.Uses x → σ (k + j) x = true
  | _, [] => by simp [instrUsesOK]
  | k, i :: is => by
    rw [instrUsesOK, Bool.and_eq_true, usesIn_iff, instrUsesOK_iff σ (k + 1) is]
    constructor
    · rintro ⟨h₀, h⟩ (_ | j) i₁ hj x hx
      · cases hj
        exact h₀ x hx
      · have := h j i₁ hj x hx
        rwa [Nat.add_right_comm, Nat.add_assoc] at this
    · intro h
      refine ⟨fun x hx => h 0 i rfl x hx, fun j i₁ hj x hx => ?_⟩
      have := h (j + 1) i₁ hj x hx
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this

/-- `usesOK` holds exactly when every block uses only what `σ` puts in scope at each count. -/
theorem usesOK_iff {bs : List (Block env α)} (σ : Block env α → Nat → ValId → Bool) :
    usesOK σ bs = true ↔ ∀ b ∈ bs,
      (∀ k i, b.instrs[k]? = some i → ∀ x, i.Uses x → σ b k x = true) ∧
        ∀ x, b.term.Uses x → σ b b.instrs.size x = true := by
  simp only [usesOK, List.all_eq_true, Bool.and_eq_true, instrUsesOK_iff, usesIn_iff,
    Nat.zero_add, Array.getElem?_toList, Instruction.Uses, Terminator.Uses]

/-- `checkScopedBy` decides `ScopedBy`. -/
public theorem checkScopedBy_iff (Λ : ValId → Bool) (bs : List (Block env α)) (t : Tree) :
    checkScopedBy Λ bs t = true ↔ ScopedBy bs (Λ · = true) t := by
  cases ht : tree? bs with
  | none =>
    simp only [checkScopedBy, ht, Bool.false_eq_true, false_iff]
    intro h
    obtain ⟨tm, htm⟩ := tree?_isSome h.legal.distinct
    rw [htm] at ht
    cases ht
  | some tm =>
    obtain ⟨hn, htr⟩ := tree?_eq_some ht
    have hm := ancs_good (t := t) hn htr
    simp only [checkScopedBy, ht]
    rw [Bool.and_eq_true, legal_iff hn htr hm, usesOK_iff]
    constructor
    · rintro ⟨hL, hu⟩
      refine ⟨hL, fun x y hy => ?_⟩
      cases hy with
      | instr hb hk hx => exact (scopeAt_iff hL htr hm Λ hb _ x).mp ((hu _ hb).1 _ _ hk x hx)
      | term hb hx => exact (scopeAt_iff hL htr hm Λ hb _ x).mp ((hu _ hb).2 x hx)
    · rintro ⟨hL, hu⟩
      exact ⟨hL, fun b hb => ⟨fun k i hk x hx =>
        (scopeAt_iff hL htr hm Λ hb k x).mpr (hu x _ (.instr hb hk hx)),
        fun x hx => (scopeAt_iff hL htr hm Λ hb _ x).mpr (hu x _ (.term hb hx))⟩⟩

end Body

/-! ## Ancestors dominate -/

namespace Body

/-- The last step of a path down the tree. -/
theorem Anc.eq_or_last_step {bs : List (Block env α)} {t : Tree} {p q : Point}
    (h : Anc bs t p q) :
    p = q ∨ (∃ k, q.count = k + 1 ∧ Anc bs t p ⟨q.label, k⟩) ∨
      (q.count = 0 ∧ ∃ b ∈ bs, b.label = q.label ∧ ∃ r, t b.label = some r ∧ Anc bs t p r) := by
  cases h with
  | refl => exact .inl rfl
  | fall h => exact .inr (.inl ⟨_, rfl, h⟩)
  | parent h hb hi => exact .inr (.inr ⟨rfl, _, hb, rfl, _, hi, h⟩)

/-- In a legal tree, a point's ancestor is on every path from the root to it. -/
theorem Anc.dom {bs : List (Block env α)} {t : Tree} (hL : Legal bs t) {d y : Point}
    (h : Anc bs t d y) : Dom bs d y := by
  intro hr
  -- Induct on a path that avoids `d`.  Its last step enters `y` from a point that `d` is still
  -- an ancestor of, by `Anc.eq_or_last_step` and (L3).
  induction hr with
  | root hne =>
    rcases h.eq_or_last_step with h | ⟨_, h, _⟩ | ⟨_, b, hb, hl, r, hi, _⟩
    · exact hne h.symm
    · simp [root] at h
    · cases bs with
      | nil => simp at hb
      | cons e rest =>
        have := eq_of_label_eq hL.distinct hb List.mem_cons_self hl
        simp [this, hL.entry e rfl] at hi
  | step _ he hne ih =>
    rcases h.eq_or_last_step with h₁ | ⟨k, hk, h₁⟩ | ⟨hk, b, hb, hl, r, hi, h₁⟩
    · exact hne h₁.symm
    · cases he with
      | fall => cases hk; exact ih h₁
      | jump => simp at hk
    · cases he with
      | fall => simp at hk
      | @jump _ v hj =>
        have hv : v ∈ bs := by cases hj <;> assumption
        cases eq_of_label_eq hL.distinct hb hv hl
        exact ih (h₁.trans (hL.jump _ _ r hj hi))

/-- Under a legal tree, what is in scope where `Λ` is visible is available where anything `Λ`
holds of is. -/
theorem InScope.avail {bs : List (Block env α)} {t : Tree} (hL : Legal bs t)
    {Λ Λ₁ : ValId → Prop} (hΛ : ∀ x, Λ x → Λ₁ x) {x : ValId} {y : Point}
    (h : InScope bs t Λ x y) : Avail bs Λ₁ x y :=
  h.elim (fun ⟨d, hd, ha⟩ => .inl ⟨d, hd, ha.dom hL⟩) (.inr ∘ hΛ x)

/-- A body that some tree scopes where `Λ` is visible is dominance-correct where anything `Λ`
holds of is available.  It is stated for any `Λ₁ ⊇ Λ` so that the induction can pass to
regions, whose `Λ` is an `InScope`. -/
theorem Scopable.domCorrect {Λ : ValId → Prop} {bs : List (Block env α)} (h : Scopable Λ bs) :
    ∀ {Λ₁ : ValId → Prop}, (∀ x, Λ x → Λ₁ x) → DomCorrect Λ₁ bs := by
  induction h with
  | mk t hs _ ih =>
    intro Λ₁ hΛ
    exact .mk (fun x y hy => (hs.uses x y hy).avail hs.legal hΛ)
      (fun y r hr => ih y r hr fun _ h => h.avail hs.legal hΛ)

end Body

/-- A scopable function is dominance-correct. -/
public theorem Func.Scopable.domCorrect {fn : Func env α} (h : fn.Scopable) : fn.DomCorrect :=
  Body.Scopable.domCorrect h fun _ => id

end Strata.Mantle
