/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Dom
public import StrataMantle.Util.LabelMap
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataMantle.Env.WF
import Std.Data.HashMap
import all StrataMantle.Util.LabelMap
import all StrataMantle.Util.LabelMapProps

set_option autoImplicit false

/-!
# Computing the dominator tree

`Body.computeTree` computes a tree of a body (`Body.Tree`, `StrataMantle/Dom.lean`), giving
every block other than the entry a parent, the point `⟨l, k⟩` it is entered below.  The tree is
always legal, for blocks whose labels are distinct (`Body.legal_computeTree`,
`StrataMantle/DomComputeProps.lean`).  In an order where every block but the entry is entered
from an earlier block, such as reverse postorder from the entry, it is the immediate-dominator
tree (`Body.exact_computeTree`, `StrataMantle/DomComputeExactProps.lean`).
`StrataMantle/DomFast.lean` runs it in the order a depth-first search finds, and checks that
order.

`Body.dropUnreached` keeps the blocks of a body the entry reaches, by the same search, and drops
the rest.  The builder (`StrataMantle/Build.lean`) calls it on each body it finishes, regions
included, since `Func.WF` asks that every block be reachable.

The algorithm is Cooper, Harvey and Kennedy's ("A Simple, Fast Dominance Algorithm", 2001),
with points in place of blocks.  A transfer by instruction `k` of block `b` leaves from
`⟨b, k⟩`, and one by its terminator from `⟨b, n⟩`, as `Body.Jump` has it.

* The first pass gives each block the nearest common ancestor of the points that jump to it
  from earlier blocks, or the entry's start if there are none.  In reverse postorder, every
  block but the entry has such a point.
* Each later pass moves a block's parent up to the nearest common ancestor of the parent and
  every point that jumps to the block, and reports whether any parent moved.
* The passes stop when none moves.

A parent always lies in an earlier block (`Body.Inv`), and the passes only move parents up.  So
in an order where a block comes before its immediate dominator, or before every block that
jumps to it, the block may keep a parent above its immediate dominator.  Reverse postorder has
neither.

`intersect` walks up from the point in the later block, as Cooper, Harvey and Kennedy's does,
recursing on the sum of the two positions.  A pass that moves a parent shortens that block's
chain to the entry and the chains below it, so the passes terminate by the total length of the
chains, `Body.Φ`, which only the proof uses.

## Main theorems

* `intersect_spec`: the nearest common ancestor of two valid points is a common ancestor;
* `pass_Φ`: a pass that moves a parent decreases `Φ`, which terminates `settle`;
* `pass_fixed`: a pass that moves nothing leaves each parent a common ancestor of the points
  that jump to its block, which `StrataMantle/DomComputeProps.lean` turns into legality.
-/

namespace Strata.Mantle

public section

variable {env : Env Unit} {α : Type}

namespace Body

/-! ## Jumps, by position

Blocks are numbered by position in the body, the entry `0`, and a point is a position and a
count. -/

/-- A point by position: a block's position, and a count. -/
abbrev Pos := Nat × Nat

/-- The transfers of the instructions `is`, the first at count `k`: the count each leaves
from, and its target. -/
@[expose] def instrEdges : Nat → List (Instruction env α) → List (Nat × Label)
  | _, [] => []
  | k, i :: is => i.succs.toList.map (k, ·.target) ++ instrEdges (k + 1) is

/-- The transfers out of block `b`: the count each leaves from, and its target. -/
@[expose] def edges (b : Block env α) : List (Nat × Label) :=
  instrEdges 0 b.instrs.toList ++ b.term.succs.toList.map (b.instrs.size, ·.target)

/-- The positions of the blocks `bs`, the first at `i`, by label. -/
@[expose] def positions : Nat → List (Block env α) → LabelMap Nat → LabelMap Nat
  | _, [], m => m
  | i, b :: bs, m => positions (i + 1) bs (m.insert b.label i)

/-- The instruction count of the block at position `j`. -/
@[expose] def sizeAt (bs : List (Block env α)) (j : Nat) : Nat :=
  (bs[j]?.map (·.instrs.size)).getD 0

/-! ## The passes -/

/-- The nearest common ancestor of `p` and `q` in the tree `par`, walking up from the point in
the later block, in at most `f` steps.  A parent lies in an earlier block, so `f := p.1 + q.1`
is enough. -/
@[expose] def intersect (par : NatTrie Pos) : Nat → Pos → Pos → Option Pos
  | 0, p, q => if p.1 = q.1 then some (p.1, min p.2 q.2) else none
  | f + 1, p, q =>
    if p.1 = q.1 then some (p.1, min p.2 q.2)
    else if q.1 < p.1 then (par.find? p.1).bind (intersect par f · q)
    else (par.find? q.1).bind (intersect par f p ·)

/-- The nearest common ancestor of `p` and `q` in the tree `par`. -/
@[expose] def nca (par : NatTrie Pos) (p q : Pos) : Pos :=
  (intersect par (p.1 + q.1) p q).getD p

/-- The nearest common ancestor of `p` and the points `ps`. -/
@[expose] def ncaFold (par : NatTrie Pos) (p : Pos) (ps : List Pos) : Pos :=
  ps.foldl (nca par) p

/-- The first pass over the blocks `l`, each with the points that jump to it: a block gets the
nearest common ancestor of the points of earlier blocks, or `flat` if there are none. -/
@[expose] def firstPass (flat : Pos) : List (Nat × List Pos) → NatTrie Pos → NatTrie Pos
  | [], par => par
  | (i, ps) :: l, par =>
    let new := match ps.filter (·.1 < i) with
      | [] => flat
      | u :: us => ncaFold par u us
    firstPass flat l (par.insert i new)

/-- A later pass over the blocks `l`: each block's parent moves up to the nearest common
ancestor of the parent and the points that jump to it.  Returns whether any parent moved, and
the tree. -/
@[expose] def pass : List (Nat × List Pos) → NatTrie Pos → Bool × NatTrie Pos
  | [], par => (false, par)
  | (i, ps) :: l, par =>
    match par.find? i with
    | none => pass l par
    | some p =>
      let new := ncaFold par p ps
      if new = p then pass l par else (true, (pass l (par.insert i new)).2)

/-! ## What the tree satisfies

The invariant the passes keep, `Inv`, and ancestry in the tree, `AncT`, under which a nearest
common ancestor is a common ancestor. -/

/-- `p` is a point of one of `n` blocks, the block at position `j` having `size j`
instructions. -/
@[expose] def Valid (n : Nat) (size : Nat → Nat) (p : Pos) : Prop := p.1 < n ∧ p.2 ≤ size p.1

/-- Every block but the entry has a parent, and only those: a valid point of an earlier
block. -/
structure Inv (n : Nat) (size : Nat → Nat) (par : NatTrie Pos) : Prop where
  parent : ∀ i r, par.find? i = some r → 0 < i ∧ i < n ∧ r.1 < i ∧ Valid n size r
  total : ∀ i, 0 < i → i < n → (par.find? i).isSome

/-- The blocks `l` are blocks of the `n` but the entry, and the points that jump to them are
valid. -/
@[expose] def PredsOK (n : Nat) (size : Nat → Nat) (l : List (Nat × List Pos)) : Prop :=
  ∀ i ps, (i, ps) ∈ l → 0 < i ∧ i < n ∧ ∀ u ∈ ps, Valid n size u

/-- `p` is `q` or above it in the tree `par`. -/
inductive AncT (par : NatTrie Pos) : Pos → Pos → Prop
  | refl (p : Pos) : AncT par p p
  | fall {p : Pos} {i k : Nat} : AncT par p (i, k) → AncT par p (i, k + 1)
  | up {p r : Pos} {i : Nat} : AncT par p r → par.find? i = some r → AncT par p (i, 0)

variable {n : Nat} {size : Nat → Nat} {par : NatTrie Pos}

/-- Ancestry in the tree by position is transitive. -/
theorem AncT.trans {p q r : Pos} (h₁ : AncT par p q) (h₂ : AncT par q r) : AncT par p r := by
  induction h₂ with
  | refl => exact h₁
  | fall _ ih => exact .fall ih
  | up _ hi ih => exact .up ih hi

/-- A point is above every later point of its block. -/
theorem AncT.of_count_le (i : Nat) {j : Nat} : ∀ {k : Nat}, j ≤ k → AncT par (i, j) (i, k)
  | 0, h => by cases Nat.le_zero.mp h; exact .refl _
  | k + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact .fall (AncT.of_count_le i (Nat.le_of_lt_succ h))
    · exact .refl _

/-- A parent is above every point of its block. -/
theorem AncT.of_parent {i : Nat} {r : Pos} (h : par.find? i = some r) (k : Nat) :
    AncT par r (i, k) :=
  (AncT.up (.refl r) h).trans (AncT.of_count_le i (Nat.zero_le k))

/-- Ancestors lie in no later block. -/
theorem AncT.pos_le (hI : Inv n size par) {p q : Pos} (h : AncT par p q) : p.1 ≤ q.1 := by
  induction h with
  | refl => exact Nat.le_refl _
  | fall _ ih => exact ih
  | up _ hi ih => exact Nat.le_trans ih (Nat.le_of_lt (hI.parent _ _ hi).2.2.1)

/-- Ancestors of a valid point are valid. -/
theorem AncT.valid (hI : Inv n size par) {p q : Pos} (h : AncT par p q) (hq : Valid n size q) :
    Valid n size p := by
  induction h with
  | refl => exact hq
  | fall _ ih => exact ih ⟨hq.1, Nat.le_of_succ_le hq.2⟩
  | up _ hi ih => exact ih (hI.parent _ _ hi).2.2.2

/-- (a) `intersect` finds a common ancestor of two valid points, given enough steps. -/
theorem intersect_spec (hI : Inv n size par) :
    ∀ (f : Nat) (p q : Pos), Valid n size p → Valid n size q → p.1 + q.1 ≤ f →
      ∃ r, intersect par f p q = some r ∧ AncT par r p ∧ AncT par r q
  | 0, (i, k), (j, l), _, _, hf => by
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by simp only at hf; omega, by simp only at hf; omega⟩
    exact ⟨(0, min k l), ite_eq_left rfl, AncT.of_count_le 0 (Nat.min_le_left k l),
      AncT.of_count_le 0 (Nat.min_le_right k l)⟩
  | f + 1, (i, k), (j, l), hp, hq, hf => by
    by_cases hij : i = j
    · subst hij
      exact ⟨(i, min k l), ite_eq_left rfl, AncT.of_count_le i (Nat.min_le_left k l),
        AncT.of_count_le i (Nat.min_le_right k l)⟩
    · have hpi : i < n := hp.1
      have hqj : j < n := hq.1
      simp only at hf
      by_cases hji : j < i
      · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hI.total i (by omega) hpi)
        have hr₁ := hI.parent i r hr
        obtain ⟨s, hs, hsr, hsq⟩ := intersect_spec hI f r (j, l) hr₁.2.2.2 hq (by
          simp only; omega)
        refine ⟨s, ?_, hsr.trans (AncT.of_parent hr k), hsq⟩
        simp only [intersect, ite_eq_right hij, ite_eq_left hji, hr, Option.bind_some, hs]
      · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hI.total j (by omega) hqj)
        have hr₁ := hI.parent j r hr
        obtain ⟨s, hs, hsp, hsr⟩ := intersect_spec hI f (i, k) r hp hr₁.2.2.2 (by
          simp only; omega)
        refine ⟨s, ?_, hsp, hsr.trans (AncT.of_parent hr l)⟩
        simp only [intersect, ite_eq_right hij, ite_eq_right hji, hr, Option.bind_some, hs]

/-- `nca` is a common ancestor. -/
theorem nca_spec (hI : Inv n size par) {p q : Pos} (hp : Valid n size p) (hq : Valid n size q) :
    AncT par (nca par p q) p ∧ AncT par (nca par p q) q := by
  obtain ⟨r, hr, hrp, hrq⟩ := intersect_spec hI _ p q hp hq (Nat.le_refl _)
  simp only [nca, hr, Option.getD_some]
  exact ⟨hrp, hrq⟩

/-- `ncaFold` is a common ancestor of the point and of the list. -/
theorem ncaFold_spec (hI : Inv n size par) :
    ∀ {p : Pos} {ps : List Pos}, Valid n size p → (∀ u ∈ ps, Valid n size u) →
      AncT par (ncaFold par p ps) p ∧ ∀ u ∈ ps, AncT par (ncaFold par p ps) u
  | p, [], _, _ => ⟨.refl p, fun _ h => absurd h List.not_mem_nil⟩
  | p, u :: us, hp, hus => by
    have hu := hus u List.mem_cons_self
    obtain ⟨h₁, h₂⟩ := nca_spec hI hp hu
    obtain ⟨ih₁, ih₂⟩ := ncaFold_spec (p := nca par p u) (ps := us) hI
      (h₁.valid hI hp) (fun v hv => hus v (List.mem_cons_of_mem _ hv))
    refine ⟨ih₁.trans h₁, fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ih₁.trans h₂
    · exact ih₂ v hv

/-- Giving block `i` a valid parent in an earlier block keeps the invariant. -/
theorem Inv.insert (hI : Inv n size par) {i : Nat} {x : Pos} (hi₀ : 0 < i) (hi : i < n)
    (hx : Valid n size x) (hxi : x.1 < i) : Inv n size (par.insert i x) where
  parent j r h := by
    rw [NatTrie.find?_insert] at h
    by_cases hj : j = i
    · rw [ite_eq_left hj] at h
      cases h
      subst hj
      exact ⟨hi₀, hi, hxi, hx⟩
    · rw [ite_eq_right hj] at h
      exact hI.parent j r h
  total j h₀ h := by
    rw [NatTrie.find?_insert]
    by_cases hj : j = i
    · rw [ite_eq_left hj]; rfl
    · rw [ite_eq_right hj]; exact hI.total j h₀ h

/-- The first pass keeps every parent a valid point of an earlier block. -/
theorem firstPass_inv {flat : Pos} (hflat : Valid n size flat) (hflat₀ : flat.1 = 0) :
    ∀ {l : List (Nat × List Pos)} {par : NatTrie Pos}, Inv n size par → PredsOK n size l →
      Inv n size (firstPass flat l par)
  | [], _, hI, _ => hI
  | (i, ps) :: l, par, hI, hl => by
    obtain ⟨hi₀, hi, hps⟩ := hl i ps List.mem_cons_self
    have hl₁ : PredsOK n size l := fun j qs h => hl j qs (List.mem_cons_of_mem _ h)
    -- The new parent is `flat`, or a common ancestor of points of earlier blocks.
    cases hf : ps.filter (·.1 < i) with
    | nil =>
      simp only [firstPass, hf]
      exact firstPass_inv hflat hflat₀ (hI.insert hi₀ hi hflat (by omega)) hl₁
    | cons u us =>
      simp only [firstPass, hf]
      have hmem : ∀ v ∈ u :: us, v ∈ ps ∧ v.1 < i := fun v hv => by
        have := List.mem_filter.mp (hf ▸ hv)
        exact ⟨this.1, of_decide_eq_true this.2⟩
      have hu := hmem u List.mem_cons_self
      have hval := hps u hu.1
      have hanc := (ncaFold_spec hI hval
        (fun v hv => hps v (hmem v (List.mem_cons_of_mem _ hv)).1)).1
      exact firstPass_inv hflat hflat₀
        (hI.insert hi₀ hi (hanc.valid hI hval) (Nat.lt_of_le_of_lt (hanc.pos_le hI) hu.2)) hl₁

/-- A later pass keeps every parent a valid point of an earlier block. -/
theorem pass_inv : ∀ {l : List (Nat × List Pos)} {par : NatTrie Pos}, Inv n size par →
    PredsOK n size l → Inv n size (pass l par).2
  | [], _, hI, _ => hI
  | (i, ps) :: l, par, hI, hl => by
    have hl₁ : PredsOK n size l := fun j qs h => hl j qs (List.mem_cons_of_mem _ h)
    obtain ⟨hi₀, hi, hps⟩ := hl i ps List.mem_cons_self
    cases hp : par.find? i with
    | none =>
      simp only [pass, hp]
      exact pass_inv hI hl₁
    | some p =>
      have hp₁ := hI.parent i p hp
      have hnew := (ncaFold_spec hI hp₁.2.2.2 hps).1
      simp only [pass, hp]
      by_cases hne : ncaFold par p ps = p
      · rw [ite_eq_left hne]
        exact pass_inv hI hl₁
      · rw [ite_eq_right hne]
        exact pass_inv (hI.insert hi₀ hi (hnew.valid hI hp₁.2.2.2)
          (Nat.lt_of_le_of_lt (hnew.pos_le hI) hp₁.2.2.1)) hl₁

/-- A pass that moves nothing leaves the tree as it is, and every block's parent is then its
own nearest common ancestor with the points that jump to the block. -/
theorem pass_fixed : ∀ {l : List (Nat × List Pos)} {par : NatTrie Pos},
    (pass l par).1 = false → (pass l par).2 = par ∧
      ∀ i ps, (i, ps) ∈ l → ∀ p, par.find? i = some p → ncaFold par p ps = p
  | [], _, _ => ⟨rfl, fun _ _ h => absurd h List.not_mem_nil⟩
  | (i, ps) :: l, par, h => by
    cases hp₀ : par.find? i with
    | none =>
      simp only [pass, hp₀] at h ⊢
      obtain ⟨h₁, h₂⟩ := pass_fixed h
      refine ⟨h₁, fun j qs hm p hp => ?_⟩
      rcases List.mem_cons.mp hm with he | hm
      · cases he; rw [hp₀] at hp; cases hp
      · exact h₂ j qs hm p hp
    | some p₀ =>
      by_cases heq : ncaFold par p₀ ps = p₀
      · simp only [pass, hp₀, heq, ite_true] at h ⊢
        obtain ⟨h₁, h₂⟩ := pass_fixed h
        refine ⟨h₁, fun j qs hm p hp => ?_⟩
        rcases List.mem_cons.mp hm with he | hm
        · cases he; rw [hp₀] at hp; cases hp; exact heq
        · exact h₂ j qs hm p hp
      · simp only [pass, hp₀, heq, ite_false] at h
        cases h

/-! ## The measure

`sd par i` is the length of the chain from the start of block `i` to the root, a step for each
instruction passed and each parent taken.  `Φ n par` sums it over the `n` blocks. -/

/-- The length of the chain from the start of block `i`, in at most `f` parents. -/
@[expose] def sdF (par : NatTrie Pos) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, i =>
    match par.find? i with
    | some r => 1 + r.2 + sdF par f r.1
    | none => 0

/-- The length of the chain from the start of block `i`. -/
@[expose] def sd (par : NatTrie Pos) (i : Nat) : Nat := sdF par i i

/-- The length of the chain from `p`. -/
@[expose] def depth (par : NatTrie Pos) (p : Pos) : Nat := p.2 + sd par p.1

/-- The total length of the chains of the `n` blocks. -/
@[expose] def Φ (n : Nat) (par : NatTrie Pos) : Nat := ((List.range n).map (sd par)).sum

/-- Under the invariant, the entry, block `0`, has no parent. -/
theorem Inv.find?_zero (hI : Inv n size par) : par.find? 0 = none := by
  cases h : par.find? 0 with
  | none => rfl
  | some r => exact absurd (hI.parent 0 r h).1 (Nat.lt_irrefl 0)

/-- The chain length does not depend on the fuel, given at least the block's position. -/
theorem sdF_fuel (hI : Inv n size par) :
    ∀ (f g i : Nat), i ≤ f → i ≤ g → sdF par f i = sdF par g i
  | 0, 0, _, _, _ => rfl
  | 0, g + 1, i, hf, _ => by
    cases Nat.le_zero.mp hf
    simp only [sdF, hI.find?_zero]
  | f + 1, 0, i, _, hg => by
    cases Nat.le_zero.mp hg
    simp only [sdF, hI.find?_zero]
  | f + 1, g + 1, i, hf, hg => by
    cases hr : par.find? i with
    | none => simp only [sdF, hr]
    | some r =>
      have := (hI.parent i r hr).2.2.1
      simp only [sdF, hr, sdF_fuel hI f g r.1 (by omega) (by omega)]

/-- The chain from a block's start is one step longer than the chain from its parent. -/
theorem sd_parent (hI : Inv n size par) {i : Nat} {r : Pos} (h : par.find? i = some r) :
    sd par i = 1 + depth par r := by
  have hr := hI.parent i r h
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [sd, sdF, h, depth]
  rw [sdF_fuel hI j r.1 r.1 (by omega) (Nat.le_refl _)]
  omega

/-- A block with no parent has a chain of length zero. -/
theorem sd_none {i : Nat} (h : par.find? i = none) : sd par i = 0 := by
  cases i with
  | zero => rfl
  | succ j => simp only [sd, sdF, h]

/-- A proper ancestor has a shorter chain. -/
theorem AncT.depth_lt (hI : Inv n size par) {p q : Pos} (h : AncT par p q) :
    p = q ∨ depth par p < depth par q := by
  induction h with
  | refl => exact .inl rfl
  | @fall i k _ ih =>
    refine .inr ?_
    have : depth par (i, k + 1) = depth par (i, k) + 1 := by simp only [depth]; omega
    rcases ih with rfl | ih <;> omega
  | @up r i _ hi ih =>
    refine .inr ?_
    have : depth par (i, 0) = 1 + depth par r := by
      simp only [depth, sd_parent hI hi]; omega
    rcases ih with rfl | ih <;> omega

/-- (b) Moving block `i`'s parent from `p` up to a proper ancestor `x` lengthens no chain, and
shortens `i`'s. -/
theorem sd_insert (hI : Inv n size par) {i : Nat} {p x : Pos} (hp : par.find? i = some p)
    (hx : AncT par x p) (hne : x ≠ p) (hI₁ : Inv n size (par.insert i x)) :
    ∀ j, sd (par.insert i x) j ≤ sd par j ∧ (j = i → sd (par.insert i x) j < sd par j) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    cases h₁ : (par.insert i x).find? j with
    | none =>
      rw [sd_none h₁]
      refine ⟨Nat.zero_le _, fun hj => ?_⟩
      subst hj
      rw [NatTrie.find?_insert, ite_eq_left rfl] at h₁
      cases h₁
    | some r =>
      have hr := hI₁.parent j r h₁
      rw [sd_parent hI₁ h₁]
      have hle := (ih r.1 hr.2.2.1).1
      have hd : depth (par.insert i x) r ≤ depth par r := by simp only [depth]; omega
      by_cases hj : j = i
      · subst hj
        rw [NatTrie.find?_insert, ite_eq_left rfl] at h₁
        cases h₁
        rw [sd_parent hI hp]
        have hlt : depth par x < depth par p := (hx.depth_lt hI).resolve_left hne
        exact ⟨by omega, fun _ => by omega⟩
      · rw [NatTrie.find?_insert, ite_eq_right hj] at h₁
        rw [sd_parent hI h₁]
        exact ⟨by omega, fun h => absurd h hj⟩

/-- Summing over a list is monotone in the summand. -/
theorem sum_le_sum {f g : Nat → Nat} : ∀ {l : List Nat}, (∀ j ∈ l, f j ≤ g j) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl _
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := h a List.mem_cons_self
    have := sum_le_sum (l := l) (fun k hk => h k (List.mem_cons_of_mem _ hk))
    omega

/-- Summing over a list is strictly monotone when one summand grows strictly. -/
theorem sum_lt_sum {f g : Nat → Nat} : ∀ {l : List Nat}, (∀ j ∈ l, f j ≤ g j) →
    (∃ j ∈ l, f j < g j) → (l.map f).sum < (l.map g).sum
  | [], _, ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | a :: l, hle, ⟨j, hj, hlt⟩ => by
    simp only [List.map_cons, List.sum_cons]
    have hl := sum_le_sum (l := l) (fun k hk => hle k (List.mem_cons_of_mem _ hk))
    have ha := hle a List.mem_cons_self
    rcases List.mem_cons.mp hj with rfl | hj
    · omega
    · have := sum_lt_sum (fun k hk => hle k (List.mem_cons_of_mem _ hk)) ⟨j, hj, hlt⟩
      omega

/-- Moving one block's parent up to a proper ancestor shortens the total chain length. -/
theorem Φ_insert (hI : Inv n size par) {i : Nat} {p x : Pos} (hp : par.find? i = some p)
    (hx : AncT par x p) (hne : x ≠ p) (hI₁ : Inv n size (par.insert i x)) :
    Φ n (par.insert i x) < Φ n par :=
  sum_lt_sum (fun j _ => (sd_insert hI hp hx hne hI₁ j).1)
    ⟨i, List.mem_range.mpr (hI.parent i p hp).2.1, (sd_insert hI hp hx hne hI₁ i).2 rfl⟩

/-- (c) A pass lengthens no chain, and one that moves a parent shortens the chains. -/
theorem pass_Φ : ∀ {l : List (Nat × List Pos)} {par : NatTrie Pos}, Inv n size par →
    PredsOK n size l →
      Φ n (pass l par).2 ≤ Φ n par ∧ ((pass l par).1 = true → Φ n (pass l par).2 < Φ n par)
  | [], _, _, _ => ⟨Nat.le_refl _, fun h => by cases h⟩
  | (i, ps) :: l, par, hI, hl => by
    have hl₁ : PredsOK n size l := fun j qs h => hl j qs (List.mem_cons_of_mem _ h)
    obtain ⟨hi₀, hi, hps⟩ := hl i ps List.mem_cons_self
    cases hp : par.find? i with
    | none =>
      simp only [pass, hp]
      exact pass_Φ hI hl₁
    | some p =>
      have hp₁ := hI.parent i p hp
      have hnew := (ncaFold_spec hI hp₁.2.2.2 hps).1
      simp only [pass, hp]
      by_cases hne : ncaFold par p ps = p
      · rw [ite_eq_left hne]
        exact pass_Φ hI hl₁
      · simp only [ite_eq_right hne]
        have hI₁ := hI.insert hi₀ hi (hnew.valid hI hp₁.2.2.2)
          (Nat.lt_of_le_of_lt (hnew.pos_le hI) hp₁.2.2.1)
        have h₁ := Φ_insert hI hp hnew hne hI₁
        have h₂ := (pass_Φ hI₁ hl₁).1
        exact ⟨by omega, fun _ => by omega⟩

set_option linter.unusedVariables false in
/-- The passes after the first, until one moves nothing. -/
@[expose] def settle (l : List (Nat × List Pos)) (hl : PredsOK n size l) (par : NatTrie Pos)
    (hI : Inv n size par) : NatTrie Pos :=
  let r := pass l par
  if h : r.1 then settle l hl r.2 (pass_inv hI hl) else par
termination_by Φ n par
decreasing_by exact (pass_Φ hI hl).2 h

/-! ## The tree of a body -/

/-- The jumps out of the blocks `bs`, the first at position `j`: the point each leaves from, and
the target's position by `pos`. -/
@[expose] def jumpsFrom (pos : LabelMap Nat) : Nat → List (Block env α) → List (Pos × Nat)
  | _, [] => []
  | j, b :: bs =>
    (edges b).filterMap (fun (k, l) => (pos.find? l).map ((j, k), ·)) ++ jumpsFrom pos (j + 1) bs

/-- The jumps `js` into `n` blocks, bucketed by target: bucket `i` holds the points that jump
to block `i`. -/
@[expose] def buckets (n : Nat) (js : List (Pos × Nat)) : Array (List Pos) :=
  js.foldl (fun a (u, t) => a.modify t (u :: ·)) (Array.replicate n [])

/-- Each block but the entry, by position, with the points that jump to it. -/
@[expose] def predLists (bs : List (Block env α)) : List (Nat × List Pos) :=
  let a := buckets bs.length (jumpsFrom (positions 0 bs ∅) 0 bs)
  (List.range' 1 (bs.length - 1)).map fun i => (i, a[i]?.getD [])

/-- The tree every block but the entry starts with: `flat`. -/
@[expose] def start (bs : List (Block env α)) (flat : Pos) : NatTrie Pos :=
  (List.range' 1 (bs.length - 1)).foldl (fun m i => m.insert i flat) .leaf

/-- The block at position `j`'s label. -/
@[expose] def labelAt (bs : Array (Block env α)) (j : Nat) : Label :=
  (bs[j]?.map (·.label)).getD default

/-- The point of the blocks `all` that the position `p` names. -/
@[expose] def ptAt (all : Array (Block env α)) (p : Pos) : Point := ⟨labelAt all p.1, p.2⟩

/-- `m`, with each of the blocks `bs`, the first at position `i`, given the point `par` gives
its position, as a point of the blocks `all`. -/
@[expose] def assign (all : Array (Block env α)) (par : NatTrie Pos) :
    Nat → List (Block env α) → LabelMap Point → LabelMap Point
  | _, [], m => m
  | i, b :: bs, m =>
    assign all par (i + 1) bs
      (match par.find? i with
       | some r => m.insert b.label (ptAt all r)
       | none => m)

/-- An instruction's transfer leaves from a count among the instructions listed. -/
theorem mem_instrEdges : ∀ {k₀ : Nat} {is : List (Instruction env α)} {k : Nat} {l : Label},
    (k, l) ∈ instrEdges k₀ is → k₀ ≤ k ∧ k < k₀ + is.length
  | _, [], _, _, h => absurd h List.not_mem_nil
  | k₀, i :: is, k, l, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨_, _, he⟩ := List.mem_map.mp h
      cases he
      simp only [List.length_cons]
      omega
    · have := mem_instrEdges h
      simp only [List.length_cons]
      omega

/-- A jump leaves from a point of its block. -/
theorem le_of_mem_edges {b : Block env α} {k : Nat} {l : Label} (h : (k, l) ∈ edges b) :
    k ≤ b.instrs.size := by
  rcases List.mem_append.mp h with h | h
  · have := mem_instrEdges h
    simp only [Array.length_toList] at this
    omega
  · obtain ⟨_, _, he⟩ := List.mem_map.mp h
    cases he
    exact Nat.le_refl _

/-- A position `positions` gives is one of the blocks', or was in the map already. -/
theorem positions_find? : ∀ {k : Nat} {bs : List (Block env α)} {m : LabelMap Nat} {l : Label}
    {i : Nat}, (positions k bs m).find? l = some i →
      (k ≤ i ∧ i < k + bs.length) ∨ m.find? l = some i
  | _, [], _, _, _, h => .inr h
  | k, b :: bs, m, l, i, h => by
    rw [positions] at h
    rcases positions_find? h with h | h
    · simp only [List.length_cons]
      exact .inl (by omega)
    · rw [LabelMap.find?_insert] at h
      split at h
      · cases h
        simp only [List.length_cons]
        exact .inl (by omega)
      · exact .inr h

/-- A jump `jumpsFrom` lists leaves a block of the list, by one of its transfers. -/
theorem mem_jumpsFrom {pos : LabelMap Nat} :
    ∀ {j₀ : Nat} {bs : List (Block env α)} {u : Pos} {i : Nat}, (u, i) ∈ jumpsFrom pos j₀ bs →
      ∃ b, j₀ ≤ u.1 ∧ bs[u.1 - j₀]? = some b ∧ ∃ l, (u.2, l) ∈ edges b ∧ pos.find? l = some i
  | _, [], _, _, h => absurd h List.not_mem_nil
  | j₀, b :: bs, u, i, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨⟨k, l⟩, hk, he⟩ := List.mem_filterMap.mp h
      obtain ⟨i₁, hi₁, he⟩ := Option.map_eq_some_iff.mp he
      cases he
      exact ⟨b, Nat.le_refl _, by simp, l, hk, hi₁⟩
    · obtain ⟨b₁, hle, hb₁, rest⟩ := mem_jumpsFrom h
      refine ⟨b₁, by omega, ?_, rest⟩
      rw [show u.1 - j₀ = (u.1 - (j₀ + 1)) + 1 by omega]
      exact hb₁

/-- The starting tree gives the flat parent to exactly the blocks after the entry. -/
theorem start_find? {bs : List (Block env α)} {flat : Pos} (i : Nat) :
    (start bs flat).find? i = if i ∈ List.range' 1 (bs.length - 1) then some flat else none := by
  suffices h : ∀ (l : List Nat) (m : NatTrie Pos) (j : Nat),
      (l.foldl (fun m i => m.insert i flat) m).find? j = if j ∈ l then some flat else m.find? j by
    rw [start, h]
    split <;> simp
  intro l
  induction l with
  | nil => intro m j; simp
  | cons a l ih =>
    intro m j
    rw [List.foldl_cons, ih, NatTrie.find?_insert]
    by_cases hj : j ∈ l
    · rw [ite_eq_left hj, ite_eq_left (List.mem_cons_of_mem _ hj)]
    · rw [ite_eq_right hj]
      by_cases ha : j = a
      · rw [ite_eq_left ha, ite_eq_left (ha ▸ List.mem_cons_self)]
      · rw [ite_eq_right ha, ite_eq_right (fun h => (List.mem_cons.mp h).elim ha hj)]

/-- The starting tree gives every parent as a valid point of an earlier block. -/
theorem start_inv {bs : List (Block env α)} {flat : Pos} (hflat : Valid bs.length (sizeAt bs) flat)
    (hflat₀ : flat.1 = 0) : Inv bs.length (sizeAt bs) (start bs flat) where
  parent i r h := by
    rw [start_find?] at h
    split at h
    next hi =>
      cases h
      have := List.mem_range'_1.mp hi
      exact ⟨by omega, by omega, by omega, hflat⟩
    next => cases h
  total i h₀ h := by
    rw [start_find?, ite_eq_left (List.mem_range'_1.mpr ⟨h₀, by omega⟩)]
    rfl

/-- Bucketing keeps the jumps already in the buckets, and adds those of `js`. -/
theorem mem_foldl_modify {i : Nat} {u : Pos} : ∀ {js : List (Pos × Nat)} {a : Array (List Pos)},
    i < a.size → (u ∈ (js.foldl (fun a (u, t) => a.modify t (u :: ·)) a)[i]?.getD [] ↔
      u ∈ a[i]?.getD [] ∨ (u, i) ∈ js)
  | [], a, _ => by simp
  | (v, t) :: js, a, hi => by
    have hi₁ : i < (a.modify t (v :: ·)).size := by rw [Array.size_modify]; exact hi
    refine (mem_foldl_modify (js := js) hi₁).trans ?_
    rw [Array.getElem?_modify, List.mem_cons]
    by_cases ht : t = i
    · subst ht
      rw [ite_eq_left rfl, Array.getElem?_eq_getElem hi]
      simp only [Option.map_some, Option.getD_some, List.mem_cons, Prod.mk.injEq, and_true]
      constructor
      · rintro ((rfl | h) | h)
        · exact .inr (.inl rfl)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr h
    · have hit : i ≠ t := Ne.symm ht
      rw [ite_eq_right ht]
      simp only [Prod.mk.injEq, hit, and_false, false_or]

/-- A point is in bucket `i` exactly when it jumps to block `i`. -/
theorem mem_buckets {n i : Nat} {js : List (Pos × Nat)} {u : Pos} (hi : i < n) :
    u ∈ (buckets n js)[i]?.getD [] ↔ (u, i) ∈ js := by
  rw [buckets, mem_foldl_modify (by simpa using hi)]
  simp [hi]

/-- The predecessor lists name blocks after the entry, and only valid points. -/
theorem predLists_ok (bs : List (Block env α)) :
    PredsOK bs.length (sizeAt bs) (predLists bs) := by
  intro i ps h
  obtain ⟨i₁, hi₁, he⟩ := List.mem_map.mp h
  cases he
  have hi := List.mem_range'_1.mp hi₁
  refine ⟨by omega, by omega, fun u hu => ?_⟩
  obtain ⟨b, -, hb, l, hl, -⟩ := mem_jumpsFrom ((mem_buckets (by omega)).mp hu)
  rw [Nat.sub_zero] at hb
  refine ⟨(List.getElem?_eq_some_iff.mp hb).1, ?_⟩
  simp only [sizeAt, hb, Option.map_some, Option.getD_some]
  exact le_of_mem_edges hl

/-- The entry's start is a valid point. -/
theorem flat_valid (e : Block env α) (rest : List (Block env α)) :
    Valid (e :: rest).length (sizeAt (e :: rest)) (0, 0) :=
  ⟨by simp, Nat.zero_le _⟩

/-- A tree of the blocks, the first the entry, as a map that gives every block but the entry a
dominator, and the entry none.  The dominator is the immediate one when every block but the
entry is entered from an earlier block.  The tree is the map's `find?`; it is a map, not a
function, so that it is computed once. -/
@[expose] def computeTree : List (Block env α) → LabelMap Point
  | [] => ∅
  | e :: rest =>
    let bs := e :: rest
    let flat : Pos := (0, 0)
    let l := predLists bs
    let par := settle l (predLists_ok bs) (firstPass flat l (start bs flat))
      (firstPass_inv (flat_valid e rest) rfl (start_inv (flat_valid e rest) rfl) (predLists_ok bs))
    assign bs.toArray par 0 bs ∅

/-- The blocks of `bs` the entry, the first, reaches, in their order, and their positions in
that list in reverse postorder from the entry, by a depth-first search. -/
private def search (bs : Array (Block env α)) : Array (Block env α) × Array Nat := Id.run do
  if bs.isEmpty then return (#[], #[])
  let pos : Std.HashMap Label Nat := bs.zipIdx.foldl (fun m (b, i) => m.insert b.label i) {}
  let succs : Array (Array Nat) := bs.map fun b => ((edges b).filterMap (pos.get? ·.2)).toArray
  let mut seen := (Array.replicate bs.size false).setIfInBounds 0 true
  let mut post : Array Nat := #[]
  -- Each frame is a block and how many of its successors it has passed.  A round finishes a
  -- block or passes a successor, so `bs.size` rounds and one per transfer suffice.
  let mut stack : Array (Nat × Nat) := #[(0, 0)]
  for _ in [0:succs.foldl (· + ·.size) (bs.size + 1)] do
    let some (i, k) := stack.back? | break
    match (succs[i]?.getD #[])[k]? with
    | none =>
      post := post.push i
      stack := stack.pop
    | some t =>
      stack := stack.pop.push (i, k + 1)
      if seen[t]? == some false then
        seen := seen.setIfInBounds t true
        stack := stack.push (t, 0)
  -- A block is kept when the block its label names is reached.
  let mut kept : Array (Block env α) := #[]
  let mut slot : Array Nat := Array.replicate bs.size 0
  for (b, i) in bs.zipIdx do
    if ((pos.get? b.label).bind (seen[·]?)) == some true then
      slot := slot.setIfInBounds i kept.size
      kept := kept.push b
  return (kept, post.reverse.map (slot[·]?.getD 0))

/-- The elements of `a` at the positions `σ`. -/
private def permute {β : Type} (a : Array β) (σ : Array Nat) : Array β := σ.filterMap (a[·]?)

/-- The blocks of `bs` the entry, the first, reaches, in their order.  A block the entry does
not reach is dropped, with its transfers. -/
def dropUnreached (bs : List (Block env α)) : List (Block env α) :=
  (search bs.toArray).1.toList

end Body

end

end Strata.Mantle
