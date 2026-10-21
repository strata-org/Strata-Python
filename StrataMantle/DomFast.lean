/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.DomComplete
public import StrataMantle.DomComputeExactProps
import all StrataMantle.DomCheck
import all StrataMantle.DomCompute
import all StrataMantle.DomComputeProps
import all StrataMantle.DomProps
import all StrataMantle.DomComplete
import all StrataMantle.DomComputeExactProps

set_option autoImplicit false

/-!
# The computed tree, checked

`Body.domTree?` computes a body's immediate-dominator tree the fast way, and checks the one thing
`Body.exact_computeTree` (`StrataMantle/DomComputeExactProps.lean`) needs that it cannot prove
of the depth-first search: that the search's order lists every block, the entry first, each
entered from an earlier one (`Body.EarlierPred`).  When the check passes, the tree is legal and
exact, and every block is reachable (`Body.domTree?_spec`).  When it fails, either a block is
unreachable or the search is wrong, and the caller falls back to the slow check.

Exactness needs every block reachable: an unreachable block has no immediate dominator, and its
transfers would pull up the parents of the blocks they enter.

`Body.Same` relates two bodies with the same blocks and the same entry: legality, dominance and
reachability are the same for both.
-/

namespace Strata.Mantle

public section

variable {env : Env Unit} {α : Type}

namespace Body

/-- The labels of the blocks the entry reaches, in the depth-first search's reverse postorder. -/
def rpoLabels (bs : List (Block env α)) : List Label :=
  let (kept, σ) := search bs.toArray
  (permute kept σ).toList.map (·.label)

/-- Whether every block but the entry is entered from an earlier block: `EarlierPred`, decided. -/
@[expose] def earlierPredB (bs : List (Block env α)) : Bool :=
  (predLists bs).all fun (i, ps) => ps.any (·.1 < i)

/-- The body's immediate-dominator tree, computed in the depth-first search's order, if that
order checks out: it lists every block of the body once, the entry first, each entered from an
earlier block. -/
def domTree? (bs : List (Block env α)) : Option Tree :=
  match tree? bs with
  | none => none
  | some tm =>
    let ord := (rpoLabels bs).filterMap tm.find?
    match tree? ord with
    | none => none
    | some t₂ =>
      if bs.all (fun b => (t₂.find? b.label).isSome) &&
          ord.head?.map (·.label) == bs.head?.map (·.label) && earlierPredB ord then
        some (computeTree ord).find?
      else none

/-- The two bodies have the same blocks and the same entry. -/
structure Same (X Y : List (Block env α)) : Prop where
  mem : ∀ b, b ∈ X ↔ b ∈ Y
  head : X.head? = Y.head?

end Body

end

namespace Body

variable {env : Env Unit} {α : Type}

/-- `earlierPredB` decides `EarlierPred`. -/
theorem earlierPredB_iff {bs : List (Block env α)} : earlierPredB bs = true ↔ EarlierPred bs := by
  simp only [earlierPredB, List.all_eq_true, List.any_eq_true, decide_eq_true_eq, EarlierPred]
  exact ⟨fun h i ps hm => h (i, ps) hm, fun h p hm => h p.1 p.2 hm⟩

/-! ## The same body in another order -/

section same

variable {X Y : List (Block env α)} {t : Tree}

/-- `Same` is symmetric. -/
theorem Same.symm (h : Same X Y) : Same Y X := ⟨fun b => (h.mem b).symm, h.head.symm⟩

/-- Bodies with the same blocks and entry have the same root. -/
theorem Same.root (h : Same X Y) : root X = root Y := by
  simp only [Body.root, h.head]

/-- An edge of one body is an edge of the same body in another order. -/
theorem Same.edge (h : Same X Y) {u w : Point} (he : Edge X u w) : Edge Y u w := by
  cases he with
  | fall hb hk => exact .fall ((h.mem _).mp hb) hk
  | jump hj => exact .jump (hj.mono fun b => (h.mem b).mp)

/-- A path avoiding `d` in one body is one in the same body in another order. -/
theorem Same.reachAvoid (h : Same X Y) {d y : Point} (hr : ReachAvoid X d y) :
    ReachAvoid Y d y := by
  induction hr with
  | root hne =>
    rw [h.root] at hne ⊢
    exact .root hne
  | step _ he hne ih => exact .step ih (h.edge he) hne

/-- Dominance is the same in the same body in another order. -/
theorem Same.dom_iff (h : Same X Y) {d y : Point} : Dom X d y ↔ Dom Y d y :=
  not_congr ⟨h.reachAvoid, h.symm.reachAvoid⟩

/-- A point reached in one body is reached in the same body in another order. -/
theorem Same.reach (h : Same X Y) {y : Point} (hr : Reach X y) : Reach Y y := by
  induction hr with
  | root =>
    rw [h.root]
    exact .root
  | step _ he ih => exact .step ih (h.edge he)

/-- Ancestry in a tree is the same in the same body in another order. -/
theorem Same.anc (h : Same X Y) {p q : Point} (ha : Anc X t p q) : Anc Y t p q :=
  ha.mono fun b => (h.mem b).mp

/-- Under distinct labels, a block other than the entry of one body is one of the other. -/
theorem Same.mem_tail (h : Same X Y) (hn : (Y.map (·.label)).Nodup) {b : Block env α}
    (hb : b ∈ Y.tail) : b ∈ X.tail := by
  cases Y with
  | nil => cases hb
  | cons y ys =>
    cases X with
    | nil => cases h.head
    | cons x xs =>
      cases (Option.some.inj h.head : x = y)
      rcases List.mem_cons.mp ((h.mem b).mpr (List.mem_cons_of_mem _ hb)) with rfl | hbx
      · exact absurd (List.mem_map_of_mem (f := fun c : Block env α => c.label) hb)
          (List.nodup_cons.mp hn).1
      · exact hbx

/-- Legality depends only on which blocks a body has and which is its entry. -/
theorem Same.legal (h : Same X Y) (hn : (Y.map (·.label)).Nodup) (hL : Legal X t) :
    Legal Y t where
  distinct := hn
  entry e he := hL.entry e (h.head ▸ he)
  parent b hb := by
    obtain ⟨p, hp, c, hc, hcl⟩ := hL.parent b (h.mem_tail hn hb)
    exact ⟨p, hp, c, (h.mem c).mp hc, hcl⟩
  rooted b hb := by
    rw [← h.root]
    exact h.anc (hL.rooted b ((h.mem b).mpr hb))
  jump u v p hj hv := h.anc (hL.jump u v p (hj.mono fun b => (h.mem b).mpr) hv)

end same

/-! ## The fast tree -/

/-- When `domTree?` gives a tree, it is legal and exact, and every block is reachable. -/
public theorem domTree?_spec {bs : List (Block env α)} {t : Tree} (h : domTree? bs = some t) :
    Legal bs t ∧ (∀ d y, Reach bs y → (Anc bs t d y ↔ Dom bs d y)) ∧
      ∀ b ∈ bs, Reach bs ⟨b.label, 0⟩ := by
  unfold domTree? at h
  cases ht : tree? bs with
  | none => simp only [ht, reduceCtorEq] at h
  | some tm =>
    obtain ⟨hn, htr⟩ := tree?_eq_some ht
    simp only [ht] at h
    generalize hord : (rpoLabels bs).filterMap tm.find? = ord at h
    cases ht₂ : tree? ord with
    | none => simp only [ht₂, reduceCtorEq] at h
    | some t₂ =>
      obtain ⟨hn₂, htr₂⟩ := tree?_eq_some ht₂
      simp only [ht₂] at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨hall, hhead⟩, hep⟩ := hc
        -- The order lists the body's blocks, the entry first.
        have hsub : ∀ b ∈ ord, b ∈ bs := fun b hb => by
          rw [← hord] at hb
          obtain ⟨l, -, hl⟩ := List.mem_filterMap.mp hb
          exact ((htr l b).mp hl).1
        have hsup : ∀ b ∈ bs, b ∈ ord := fun b hb => by
          obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hall b hb)
          obtain ⟨hc₁, hcl⟩ := (htr₂ _ _).mp hc
          rwa [eq_of_label_eq hn (hsub c hc₁) hb hcl] at hc₁
        have hh : ord.head? = bs.head? := by
          cases ho : ord with
          | nil =>
            cases hb : bs with
            | nil => rfl
            | cons e rest => exact absurd (hsup e (hb ▸ List.mem_cons_self)) (ho ▸ List.not_mem_nil)
          | cons o os =>
            cases hb : bs with
            | nil => exact absurd (hsub o (ho ▸ List.mem_cons_self)) (hb ▸ List.not_mem_nil)
            | cons e rest =>
              rw [ho, hb] at hhead
              have hl : o.label = e.label := Option.some.inj hhead
              rw [eq_of_label_eq hn (hsub o (ho ▸ List.mem_cons_self))
                (hb ▸ List.mem_cons_self) hl]
              rfl
        have hsame : Same ord bs := ⟨fun b => ⟨hsub b, hsup b⟩, hh⟩
        cases ho : ord with
        | nil =>
          subst ho
          cases bs with
          | nil => exact ⟨legal_nil _, exact_nil _, fun _ h => nomatch h⟩
          | cons e rest => exact absurd (hsup e List.mem_cons_self) List.not_mem_nil
        | cons e rest =>
          subst ho
          obtain ⟨hx, hr⟩ := exact_computeTree hn₂ (earlierPredB_iff.mp hep)
          refine ⟨hsame.legal hn (legal_computeTree hn₂), fun d y hy => ?_, fun b hb => ?_⟩
          · rw [← hsame.dom_iff]
            exact ⟨fun ha => (hx d y (hsame.symm.reach hy)).mp (hsame.symm.anc ha),
              fun hd => hsame.anc ((hx d y (hsame.symm.reach hy)).mpr hd)⟩
          · exact hsame.reach (hr b (hsup b hb))
      · cases h

end Body

end Strata.Mantle
