/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.DomCompute
import all StrataMantle.DomCompute
import all StrataMantle.Util.LabelMap
import all StrataMantle.Util.LabelMapProps

set_option autoImplicit false

/-!
# The computed tree is exact: the position layer

The first half of the proof that `Body.computeTree` gives the immediate-dominator tree
(`Body.exact_computeTree`, `StrataMantle/DomComputeExactProps.lean`).  This module proves, over
positions:

* `AncT.cases_block`: an ancestor of a point is an earlier point of its block, or above
  the block's parent;
* `intersect_nearest`, `ncaFold_nearest`: `intersect` and `ncaFold` give the *nearest*
  common ancestor, not just a common one;
* `UnderD`, and over any relation `D` with the two axioms `DomAx` of a dominance relation,
  `UnderD.convex`, `UnderD.anc` and `UnderD.insert`: the invariant that every
  strict dominator of a block's start dominates its parent gives that every dominator is an
  ancestor, and survives a parent's move to a nearest common ancestor of points the block's
  strict dominators all dominate.
-/

namespace Strata.Mantle

namespace Body

variable {n : Nat} {size : Nat → Nat} {par : NatTrie Pos}

/-! ## Nearest common ancestors -/

/-- An ancestor of a point is an earlier point of its block, or is above the block's
parent. -/
theorem AncT.cases_block (hI : Inv n size par) {c : Pos} {i k : Nat} (h : AncT par c (i, k)) :
    (c.1 = i ∧ c.2 ≤ k) ∨ (c.1 < i ∧ ∃ r, par.find? i = some r ∧ AncT par c r) := by
  generalize hq : (i, k) = q at h
  induction h generalizing i k with
  | refl => cases hq; exact .inl ⟨rfl, Nat.le_refl _⟩
  | fall _ ih =>
    cases hq
    rcases ih rfl with ⟨h₁, h₂⟩ | h
    · exact .inl ⟨h₁, Nat.le_succ_of_le h₂⟩
    · exact .inr h
  | up h hi _ =>
    cases hq
    exact .inr ⟨Nat.lt_of_le_of_lt (h.pos_le hI) (hI.parent _ _ hi).2.2.1, _, hi, h⟩

/-- A point of a block is not above an earlier point of it. -/
theorem AncT.not_succ (hI : Inv n size par) {i k : Nat} (h : AncT par (i, k + 1) (i, k)) :
    False := by
  rcases h.cases_block hI with ⟨_, h⟩ | ⟨h, _⟩
  · exact Nat.not_succ_le_self k h
  · exact Nat.lt_irrefl i h

/-- `intersect` finds the nearest common ancestor of two valid points: every common
ancestor is above what it finds. -/
theorem intersect_nearest (hI : Inv n size par) :
    ∀ (f : Nat) (p q : Pos), Valid n size p → Valid n size q → p.1 + q.1 ≤ f →
      ∀ r, intersect par f p q = some r → ∀ c, AncT par c p → AncT par c q → AncT par c r
  | 0, (i, k), (j, l), _, _, hf, r, hr, c, hcp, hcq => by
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by simp only at hf; omega, by simp only at hf; omega⟩
    simp only [intersect, ↓reduceIte, Option.some.injEq] at hr
    subst hr
    rcases hcp.cases_block hI with ⟨h₁, h₂⟩ | ⟨h, _⟩
    · rcases hcq.cases_block hI with ⟨_, h₃⟩ | ⟨h, _⟩
      · obtain ⟨c₁, c₂⟩ := c
        dsimp only at h₁ h₂ h₃
        subst h₁
        exact AncT.of_count_le 0 (Nat.le_min.mpr ⟨h₂, h₃⟩)
      · exact absurd h (Nat.not_lt_zero _)
    · exact absurd h (Nat.not_lt_zero _)
  | f + 1, (i, k), (j, l), hp, hq, hf, r, hr, c, hcp, hcq => by
    simp only at hf
    by_cases hij : i = j
    · subst hij
      simp only [intersect, ↓reduceIte, Option.some.injEq] at hr
      subst hr
      rcases hcp.cases_block hI with ⟨h₁, h₂⟩ | ⟨_, r₀, hr₀, hc⟩
      · rcases hcq.cases_block hI with ⟨_, h₃⟩ | ⟨h, _⟩
        · obtain ⟨c₁, c₂⟩ := c
          dsimp only at h₁ h₂ h₃
          subst h₁
          exact AncT.of_count_le c₁ (Nat.le_min.mpr ⟨h₂, h₃⟩)
        · exact absurd h₁ (Nat.ne_of_lt h)
      · exact hc.trans (AncT.of_parent hr₀ _)
    · by_cases hji : j < i
      · simp only [intersect, if_neg hij, if_pos hji] at hr
        cases hr₀ : par.find? i with
        | none => simp only [hr₀, Option.bind_none, reduceCtorEq] at hr
        | some r₀ =>
          simp only [hr₀, Option.bind_some] at hr
          have hr₁ := hI.parent i r₀ hr₀
          rcases hcp.cases_block hI with ⟨h₁, _⟩ | ⟨_, r₂, hr₂, hc⟩
          · exact absurd (h₁ ▸ hcq.pos_le hI) (Nat.not_le_of_lt hji)
          · cases (hr₀.symm.trans hr₂ : some r₀ = some r₂)
            exact intersect_nearest hI f r₀ (j, l) hr₁.2.2.2 hq (by simp only; omega) r hr c hc hcq
      · simp only [intersect, if_neg hij, if_neg hji] at hr
        cases hr₀ : par.find? j with
        | none => simp only [hr₀, Option.bind_none, reduceCtorEq] at hr
        | some r₀ =>
          simp only [hr₀, Option.bind_some] at hr
          have hr₁ := hI.parent j r₀ hr₀
          rcases hcq.cases_block hI with ⟨h₁, _⟩ | ⟨_, r₂, hr₂, hc⟩
          · exact absurd (h₁ ▸ hcp.pos_le hI) (by omega)
          · cases (hr₀.symm.trans hr₂ : some r₀ = some r₂)
            exact intersect_nearest hI f (i, k) r₀ hp hr₁.2.2.2 (by simp only; omega) r hr c hcp hc

/-- `nca` is the nearest common ancestor of two valid points. -/
theorem nca_nearest (hI : Inv n size par) {p q c : Pos} (hp : Valid n size p)
    (hq : Valid n size q) (hcp : AncT par c p) (hcq : AncT par c q) : AncT par c (nca par p q) := by
  obtain ⟨r, hr, -, -⟩ := intersect_spec hI _ p q hp hq (Nat.le_refl _)
  simp only [nca, hr, Option.getD_some]
  exact intersect_nearest hI _ p q hp hq (Nat.le_refl _) r hr c hcp hcq

/-- `ncaFold` is the nearest common ancestor of the point and the list. -/
theorem ncaFold_nearest (hI : Inv n size par) :
    ∀ {p : Pos} {ps : List Pos}, Valid n size p → (∀ u ∈ ps, Valid n size u) →
      ∀ {c : Pos}, AncT par c p → (∀ u ∈ ps, AncT par c u) → AncT par c (ncaFold par p ps)
  | _, [], _, _, _, hc, _ => hc
  | p, u :: us, hp, hus, c, hc, hcs => by
    have hu := hus u List.mem_cons_self
    exact ncaFold_nearest (p := nca par p u) (ps := us) hI ((nca_spec hI hp hu).1.valid hI hp)
      (fun v hv => hus v (List.mem_cons_of_mem _ hv))
      (nca_nearest hI hp hu hc (hcs u List.mem_cons_self))
      (fun v hv => hcs v (List.mem_cons_of_mem _ hv))

/-! ## The invariant, over an abstract dominance relation

`D d q` reads "`d` dominates `q`".  The proofs need only that a strict dominator of a
point after an instruction dominates the point before it, and that only the root dominates the
root. -/

/-- What the proofs need of a dominance relation over the valid points of `n` blocks. -/
structure DomAx (n : Nat) (size : Nat → Nat) (D : Pos → Pos → Prop) : Prop where
  /-- A strict dominator of the point after an instruction dominates the point before it. -/
  fall : ∀ d i k, Valid n size d → Valid n size (i, k + 1) → D d (i, k + 1) → d ≠ (i, k + 1) →
    D d (i, k)
  /-- Only the root dominates the root. -/
  root : ∀ d, Valid n size d → D d (0, 0) → d = (0, 0)

/-- Every block before `lim` that has a parent has one that every strict dominator of the
block's start dominates. -/
def UnderD (n : Nat) (size : Nat → Nat) (D : Pos → Pos → Prop) (par : NatTrie Pos) (lim : Nat) :
    Prop :=
  ∀ i r, i < lim → par.find? i = some r →
    ∀ d, Valid n size d → d ≠ (i, 0) → D d (i, 0) → D d r

variable {D : Pos → Pos → Prop}

/-- On the way up from `q` to a dominator `d` of it, the chain stays among the points `d`
dominates. -/
theorem UnderD.convex (hA : DomAx n size D) (hI : Inv n size par) {lim : Nat}
    (hU : UnderD n size D par lim) {d z q : Pos} (hdv : Valid n size d) (hq : Valid n size q)
    (hql : q.1 < lim) (hd : D d q) (hdz : AncT par d z) (hzq : AncT par z q) : D d z := by
  induction hzq with
  | refl => exact hd
  | @fall i k h ih =>
    have hne : d ≠ (i, k + 1) := fun he => by
      subst he
      exact (hdz.trans h).not_succ hI
    exact ih ⟨hq.1, Nat.le_of_succ_le hq.2⟩ hql (hA.fall d i k hdv hq hd hne)
  | @up r i h hi ih =>
    have hr := hI.parent i r hi
    have hne : d ≠ (i, 0) := fun he => by
      have := (hdz.trans h).pos_le hI
      rw [he] at this
      exact Nat.not_le_of_lt hr.2.2.1 this
    exact ih hr.2.2.2 (Nat.lt_trans hr.2.2.1 hql) (hU i r hql hi d hdv hne hd)

/-- Every dominator of a valid point before `lim` is an ancestor of it. -/
theorem UnderD.anc (hA : DomAx n size D) (hI : Inv n size par) {lim : Nat}
    (hU : UnderD n size D par lim) :
    ∀ (q : Pos), Valid n size q → q.1 < lim → ∀ d, Valid n size d → D d q → AncT par d q := by
  intro q
  obtain ⟨i, k⟩ := q
  induction i using Nat.strongRecOn generalizing k with
  | _ i ihi =>
    induction k with
    | zero =>
      intro hq hql d hdv hd
      by_cases hdq : d = (i, 0)
      · subst hdq
        exact .refl _
      cases i with
      | zero => exact absurd (hA.root d hdv hd) hdq
      | succ i =>
        obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hI.total (i + 1) (Nat.succ_pos i) hq.1)
        have hr₁ := hI.parent _ r hr
        exact .up (ihi r.1 hr₁.2.2.1 r.2 hr₁.2.2.2 (Nat.lt_trans hr₁.2.2.1 hql) d hdv
          (hU _ r hql hr d hdv hdq hd)) hr
    | succ k ihk =>
      intro hq hql d hdv hd
      by_cases hdq : d = (i, k + 1)
      · subst hdq
        exact .refl _
      exact .fall (ihk ⟨hq.1, Nat.le_of_succ_le hq.2⟩ hql d hdv (hA.fall d i k hdv hq hd hdq))

/-- Moving block `i`'s parent to the nearest common ancestor of valid points before `lim`
that every strict dominator of the block's start dominates keeps the invariant, and extends it
to block `i`. -/
theorem UnderD.insert (hA : DomAx n size D) (hI : Inv n size par) {lim : Nat}
    (hU : UnderD n size D par lim) {i : Nat} (hil : i ≤ lim) {x₀ : Pos} {xs : List Pos}
    (hX : ∀ x ∈ x₀ :: xs, Valid n size x ∧ x.1 < lim ∧
      ∀ d, Valid n size d → d ≠ (i, 0) → D d (i, 0) → D d x) :
    UnderD n size D (par.insert i (ncaFold par x₀ xs)) (max lim (i + 1)) := by
  intro j r hj hr d hdv hdne hd
  rw [NatTrie.find?_insert] at hr
  by_cases hji : j = i
  · rw [if_pos hji] at hr
    cases hr
    subst hji
    have hx₀ := hX x₀ List.mem_cons_self
    have hxs : ∀ u ∈ xs, Valid n size u := fun u hu => (hX u (List.mem_cons_of_mem _ hu)).1
    -- `d` is above every point, so above their nearest common ancestor, which is above `x₀`.
    have hanc : ∀ x ∈ x₀ :: xs, AncT par d x := fun x hx =>
      let ⟨hv, hl, hD⟩ := hX x hx
      hU.anc hA hI x hv hl d hdv (hD d hdv hdne hd)
    have hnew := ncaFold_nearest hI hx₀.1 hxs (hanc x₀ List.mem_cons_self)
      (fun u hu => hanc u (List.mem_cons_of_mem _ hu))
    exact hU.convex hA hI hdv hx₀.1 hx₀.2.1 (hx₀.2.2 d hdv hdne hd) hnew
      (ncaFold_spec hI hx₀.1 hxs).1
  · rw [if_neg hji] at hr
    exact hU j r (by omega) hr d hdv hdne hd

/-- The invariant for fewer blocks. -/
theorem UnderD.mono {lim lim₁ : Nat} (h : UnderD n size D par lim₁) (hl : lim ≤ lim₁) :
    UnderD n size D par lim :=
  fun i r hi => h i r (Nat.lt_of_lt_of_le hi hl)

/-- What the proofs need of the points that jump to each block: they are valid, and every strict
dominator of the block's start dominates them. -/
def PredsDom (n : Nat) (size : Nat → Nat) (D : Pos → Pos → Prop) (l : List (Nat × List Pos)) :
    Prop :=
  ∀ i ps, (i, ps) ∈ l → ∀ u ∈ ps, ∀ d, Valid n size d → d ≠ (i, 0) → D d (i, 0) → D d u

/-- The first pass over the blocks from `m` on, each with predecessors as `PredsDom` has
them and one of them in an earlier block, extends the invariant to all `n` blocks. -/
theorem firstPass_underD (hA : DomAx n size D) {flat : Pos} {P : Nat → List Pos}
    (hl : ∀ i, 0 < i → i < n → ∀ u ∈ P i, Valid n size u)
    (hP : ∀ i, 0 < i → i < n → ∀ u ∈ P i, ∀ d, Valid n size d → d ≠ (i, 0) → D d (i, 0) →
      D d u)
    (hE : ∀ i, 0 < i → i < n → ∃ u ∈ P i, u.1 < i) :
    ∀ (k m : Nat) (par : NatTrie Pos), m + k = n → 0 < m → Inv n size par →
      UnderD n size D par m →
      UnderD n size D (firstPass flat ((List.range' m k).map fun i => (i, P i)) par) n
  | 0, m, par, hk, _, _, hU => by
    rw [Nat.add_zero] at hk
    subst hk
    exact hU
  | k + 1, m, par, hk, hm, hI, hU => by
    rw [List.range'_succ, List.map_cons, firstPass]
    have hmn : m < n := by omega
    obtain ⟨u₀, hu₀, hlt⟩ := hE m hm hmn
    cases hf : (P m).filter (·.1 < m) with
    | nil =>
      have := (List.mem_filter (p := fun x : Pos => decide (x.1 < m))).mpr
        ⟨hu₀, decide_eq_true hlt⟩
      rw [hf] at this
      exact absurd this List.not_mem_nil
    | cons u us =>
      have hX : ∀ x ∈ u :: us, Valid n size x ∧ x.1 < m ∧
          ∀ d, Valid n size d → d ≠ (m, 0) → D d (m, 0) → D d x := fun x hx => by
        have hx₁ := List.mem_filter.mp (hf ▸ hx)
        exact ⟨hl m hm hmn x hx₁.1, of_decide_eq_true hx₁.2, hP m hm hmn x hx₁.1⟩
      have hU₁ := hU.insert hA hI (Nat.le_refl m) hX
      rw [Nat.max_eq_right (Nat.le_succ m)] at hU₁
      have hu := hX u List.mem_cons_self
      have hanc := (ncaFold_spec hI hu.1 fun v hv => (hX v (List.mem_cons_of_mem _ hv)).1).1
      exact firstPass_underD hA hl hP hE k (m + 1) _ (by omega) (Nat.succ_pos m)
        (hI.insert hm hmn (hanc.valid hI hu.1) (Nat.lt_of_le_of_lt (hanc.pos_le hI) hu.2.1)) hU₁

/-- A later pass keeps the invariant for all `n` blocks. -/
theorem pass_underD (hA : DomAx n size D) :
    ∀ {l : List (Nat × List Pos)} {par : NatTrie Pos}, Inv n size par → PredsOK n size l →
      PredsDom n size D l → UnderD n size D par n → UnderD n size D (pass l par).2 n
  | [], _, _, _, _, hU => hU
  | (i, ps) :: l, par, hI, hl, hD, hU => by
    have hl₁ : PredsOK n size l := fun j qs h => hl j qs (List.mem_cons_of_mem _ h)
    have hD₁ : PredsDom n size D l := fun j qs h => hD j qs (List.mem_cons_of_mem _ h)
    obtain ⟨hi₀, hi, hps⟩ := hl i ps List.mem_cons_self
    cases hp : par.find? i with
    | none =>
      simp only [pass, hp]
      exact pass_underD hA hI hl₁ hD₁ hU
    | some p =>
      have hp₁ := hI.parent i p hp
      have hnew := (ncaFold_spec hI hp₁.2.2.2 hps).1
      simp only [pass, hp]
      by_cases hne : ncaFold par p ps = p
      · rw [if_pos hne]
        exact pass_underD hA hI hl₁ hD₁ hU
      · rw [if_neg hne]
        have hX : ∀ x ∈ p :: ps, Valid n size x ∧ x.1 < n ∧
            ∀ d, Valid n size d → d ≠ (i, 0) → D d (i, 0) → D d x := fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hp₁.2.2.2, hp₁.2.2.2.1, fun d hdv hdi hd => hU i x hi hp d hdv hdi hd⟩
          · exact ⟨hps x hx, (hps x hx).1, hD i ps List.mem_cons_self x hx⟩
        exact pass_underD hA (hI.insert hi₀ hi (hnew.valid hI hp₁.2.2.2)
          (Nat.lt_of_le_of_lt (hnew.pos_le hI) hp₁.2.2.1)) hl₁ hD₁
          ((hU.insert hA hI (Nat.le_of_lt hi) hX).mono (Nat.le_max_left _ _))

/-- Settling keeps the invariant. -/
theorem settle_underD (hA : DomAx n size D) {l : List (Nat × List Pos)}
    (hl : PredsOK n size l) (hD : PredsDom n size D l) :
    ∀ (m : Nat) (par : NatTrie Pos) (hI : Inv n size par), Φ n par = m →
      UnderD n size D par n → UnderD n size D (settle l hl par hI) n := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro par hI hm hU
    rw [settle]
    by_cases h : (pass l par).1 = true
    · rw [dif_pos h]
      exact ih _ (hm ▸ (pass_Φ hI hl).2 h) _ _ rfl (pass_underD hA hI hl hD hU)
    · rw [dif_neg h]
      exact hU

end Body

end Strata.Mantle
