/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Loops
public import StrataDyn.DomFast
import all StrataDyn.Loops
import all StrataDyn.LoopsProps
import all StrataDyn.Dom
import all StrataDyn.DomCheck
import all StrataDyn.DomComplete
import all StrataDyn.DomDecide
import all StrataDyn.DomFast
import all StrataDyn.DomProps
import all StrataDyn.Util.List
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Loops, the fast way

`Body.backEdges` and `Body.loopBlocks` (`StrataDyn/Loops.lean`) decide every path with the
cubic search.  This module computes the same lists faster, and proves them equal, so that
`@[csimp]` runs the fast versions and every proof stays about the simple ones.

* `Body.backEdgesFast` decides dominance with the immediate-dominator tree that `Body.domTree?`
  computes and checks (`StrataDyn/DomFast.lean`), and the ancestor map of
  `StrataDyn/DomCheck.lean`.  If there is no such tree, it falls back to the search.
* `Body.loopBlocksFast` grows the loop backwards from the block of the back edge's source, one
  block at a time, never through the head.  If the labels are not distinct, it falls back to
  `Body.loopBlocks`.  Each step scans the body and checks membership in the loop so far by a list
  scan, so a loop of `m` blocks costs about `m²` times the size of the body.  That is fast on the
  translator's functions, and slow on a loop of hundreds of blocks: a predecessor map and a
  worklist would make it linear.

The `@[csimp]` lemmas replace the simple versions only in modules that import this one, so code
that runs loop finding imports `StrataDyn.LoopsFast`.  The fast definitions and their
equalities are in one module, as in `StrataDyn/DomFast.lean`, so that importing the fast
versions also brings the lemmas that make them run.

## Main theorems

* `Body.backEdges_eq_fast`, `Body.loopBlocks_eq_fast`: the two equalities, both `@[csimp]`.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

namespace Body

variable (bs : List (Block env α))

/-- What `domWith` decides dominance with: the blocks by label, the immediate-dominator tree, its
ancestor map and the block count, if `tree?` and `domTree?` succeed.  It is data, so it is
computed once per body. -/
@[expose] def domInfo : Option (LabelMap (Block env α) × Tree × AncMap × Nat) :=
  match tree? bs, domTree? bs with
  | some tm, some t => some (tm, t, ancs tm t bs, bs.length)
  | _, _ => none

/-- Whether the start of the block `l` dominates `u`: an ancestor of `u` in the tree of `info`,
or else as the search decides. -/
@[expose] def domWith (info : Option (LabelMap (Block env α) × Tree × AncMap × Nat))
    (u : Point) (l : Label) : Bool :=
  match info with
  | some (tm, t, m, n) =>
    match tm.find? u.label with
    | some b => ancAt tm t n m b u.count ⟨l, 0⟩
    | none => !reachAvoidB bs ⟨l, 0⟩ u
  | none => !reachAvoidB bs ⟨l, 0⟩ u

/-- `backEdges`, deciding dominance with `domWith`. -/
@[expose] def backEdgesFast : List (Point × Label) :=
  let info := domInfo bs
  ((transfers bs).filter fun (u, l) => domWith bs info u l).eraseDups

/-- Whether block `b` transfers, from any count, to a block whose label is in `S`. -/
@[expose] def entersAny (S : List Label) (b : Block env α) : Bool :=
  (List.range (b.instrs.size + 1)).any fun k => (targets b k).any S.contains

/-- `S`, grown by blocks other than `h` that transfer into it, one at a time, at most `fuel` of
them. -/
@[expose] def growLoop (h : Label) : (fuel : Nat) → List Label → List Label
  | 0, S => S
  | f + 1, S =>
    match bs.find? fun b => b.label != h && !S.contains b.label && entersAny S b with
    | none => S
    | some b => growLoop h f (b.label :: S)

/-- Where the loop of the back edge from `u` to `h` grows from: `u`'s block, unless it is `h` or
`u` is not a point of the body. -/
@[expose] def loopSeed (u : Point) (h : Label) : List Label :=
  if u.label != h && bs.any (fun b => b.label == u.label && decide (u.count ≤ b.instrs.size))
  then [u.label] else []

/-- `loopBlocks`, by growing the loop backwards. -/
@[expose] def loopBlocksFast (u : Point) (h : Label) : List Label :=
  if (tree? bs).isSome then
    let S := growLoop bs h bs.length (loopSeed bs u h)
    (bs.filter fun b => b.label == h || S.contains b.label).map (·.label)
  else loopBlocks bs u h

end Body

end

/-! ## Back edges -/

namespace Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)}

/-- On every transfer of the body, `domWith` with the body's `domInfo` gives what the cubic search
`reachAvoidB` gives: whether the target's start dominates the transfer's point. -/
theorem domWith_eq {u : Point} {l : Label} (h : (u, l) ∈ transfers bs) :
    domWith bs (domInfo bs) u l = !reachAvoidB bs ⟨l, 0⟩ u := by
  unfold domInfo
  cases htm : tree? bs with
  | none => rfl
  | some tm =>
    cases ht : domTree? bs with
    | none => rfl
    | some t =>
      dsimp only [domWith]
      obtain ⟨hn, htr⟩ := tree?_eq_some htm
      obtain ⟨hL, hex, hre⟩ := domTree?_spec ht
      obtain ⟨b, hb, hbl, hk, -⟩ := mem_transfers.mp h
      have hf : tm.find? u.label = some b := (htr _ _).mpr ⟨hb, hbl⟩
      simp only [hf]
      have hne : bs ≠ [] := List.ne_nil_of_mem hb
      have hreach : Reach bs u := by
        have := reach_count hb (hre b hb) hk
        rwa [hbl] at this
      have hanc := ancAt_iff hL htr (ancs_good hn htr) hb u.count ⟨l, 0⟩
      rw [hbl] at hanc
      apply Bool.eq_iff_iff.mpr
      rw [hanc, (hex _ _ hreach), Bool.not_eq_true', ← Bool.not_eq_true,
        reachAvoidB_iff hne hn]
      rfl

/-- `backEdgesFast` is `backEdges`. -/
@[csimp] public theorem backEdges_eq_fast : @backEdges = @backEdgesFast := by
  funext env α bs
  unfold backEdges backEdgesFast
  congr 1
  exact (List.filter_congr fun p hp => (domWith_eq hp).symm)

/-! ## Natural loops -/

/-- The invariant of the loop's growth `S`: it has no duplicates, and each of its labels is the
label of a block other than `h` whose start reaches `u` without passing through `h`'s start. -/
def LoopInv (u : Point) (h : Label) (S : List Label) : Prop :=
  S.Nodup ∧ ∀ l ∈ S, ∃ c ∈ bs, c.label = l ∧ l ≠ h ∧ PathAvoid bs ⟨h, 0⟩ ⟨l, 0⟩ u

/-- `loopSeed bs u h`, where the loop of the back edge from `u` to `h` grows from, satisfies
`LoopInv u h`. -/
theorem loopSeed_inv (u : Point) (h : Label) : LoopInv (bs := bs) u h (loopSeed bs u h) := by
  unfold loopSeed
  split
  next hc =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hc
    obtain ⟨hne, b, hb, hbl, hk⟩ := hc
    refine ⟨by simp, fun l hl => ?_⟩
    rw [List.mem_singleton] at hl
    subst hl
    refine ⟨b, hb, hbl, hne, ?_⟩
    have := PathAvoid.fall (bs := bs) (d := ⟨h, 0⟩) hb (by rw [hbl]; exact hne) hk
    rwa [hbl] at this
  next => exact ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- Adding to `S` the label of a block other than `h`, not in `S`, that transfers into `S`, keeps
`LoopInv u h`. -/
theorem LoopInv.cons {u : Point} {h : Label} {S : List Label} (hI : LoopInv (bs := bs) u h S)
    {b : Block env α} (hb : b ∈ bs) (hbh : b.label ≠ h) (hbS : b.label ∉ S)
    (he : entersAny S b = true) : LoopInv (bs := bs) u h (b.label :: S) := by
  refine ⟨List.nodup_cons.mpr ⟨hbS, hI.1⟩, fun l hl => ?_⟩
  rcases List.mem_cons.mp hl with rfl | hl
  · refine ⟨b, hb, rfl, hbh, ?_⟩
    simp only [entersAny, List.any_eq_true, List.mem_range, List.contains_iff_mem] at he
    obtain ⟨k, hk, l₁, hl₁, hS⟩ := he
    obtain ⟨c, hc, hcl, hch, hp⟩ := hI.2 l₁ hS
    have hj : Jump bs ⟨b.label, k⟩ c := jump_of_targets hb hc (hcl ▸ hl₁)
    have hcd : (⟨c.label, 0⟩ : Point) ≠ ⟨h, 0⟩ := fun he =>
      hch (by rw [← hcl]; exact congrArg Point.label he)
    have hstep := PathAvoid.step (PathAvoid.fall (d := ⟨h, 0⟩) hb hbh (Nat.le_of_lt_succ hk))
      (.jump hj) hcd
    exact hstep.trans (hcl ▸ hp)
  · exact hI.2 l hl

/-- `growLoop` keeps the invariant, keeps what it started with, and stops either with no block
left to add or after adding `fuel` labels. -/
theorem growLoop_spec {u : Point} {h : Label} :
    ∀ (f : Nat) {S : List Label}, LoopInv (bs := bs) u h S →
      LoopInv (bs := bs) u h (growLoop bs h f S) ∧ (∀ l ∈ S, l ∈ growLoop bs h f S) ∧
        ((bs.find? fun b => b.label != h && !(growLoop bs h f S).contains b.label &&
            entersAny (growLoop bs h f S) b) = none ∨ S.length + f ≤ (growLoop bs h f S).length)
  | 0, S, hI => ⟨hI, fun _ h => h, .inr (Nat.le_refl _)⟩
  | f + 1, S, hI => by
    unfold growLoop
    split
    next hf => exact ⟨hI, fun _ h => h, .inl hf⟩
    next b hf =>
      have hb := List.mem_of_find?_eq_some hf
      have hc := List.find?_some hf
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', Bool.eq_false_iff,
        List.contains_iff_mem] at hc
      obtain ⟨⟨hbh, hbS⟩, he⟩ := hc
      obtain ⟨hI', hsub, hdone⟩ := growLoop_spec f (hI.cons hb hbh hbS he)
      refine ⟨hI', fun l hl => hsub l (List.mem_cons_of_mem _ hl), ?_⟩
      rcases hdone with hdone | hdone
      · exact .inl hdone
      · exact .inr (by simp only [List.length_cons] at hdone; omega)

/-- If no block other than `h` outside `S` transfers into `S`, then a path that starts outside
`h`, avoids `h`'s start and ends in `S`, starts in `S`. -/
theorem PathAvoid.mem_of_closed {h : Label} {S : List Label}
    (hcl : (bs.find? fun c => c.label != h && !S.contains c.label && entersAny S c) = none)
    {x y : Point} (hp : PathAvoid bs ⟨h, 0⟩ x y) (hx : x.label ≠ h) (hy : y.label ∈ S) :
    x.label ∈ S := by
  induction hp with
  | refl => exact hy
  | step hp₁ he _ ih =>
    apply ih
    cases he with
    | fall => exact hy
    | @jump u' v hj =>
      obtain ⟨c, hc, hcl', ht⟩ := targets_of_jump hj
      rw [← hcl']
      apply Classical.byContradiction
      intro hcS
      have hch : c.label ≠ h := hcl' ▸ hp₁.label_ne hx
      have := List.find?_eq_none.mp hcl c hc
      apply this
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', Bool.eq_false_iff,
        List.contains_iff_mem, entersAny, List.any_eq_true, List.mem_range,
        List.contains_iff_mem]
      exact ⟨⟨hch, hcS⟩, _, Nat.lt_succ_of_le (le_of_mem_targets ht), v.label, ht, hy⟩

/-- The grown loop holds every block other than `h` whose start reaches `u` avoiding `h`'s
start. -/
theorem growLoop_complete {u : Point} {h : Label}
    {b : Block env α} (hb : b ∈ bs) (hbh : b.label ≠ h)
    (hp : PathAvoid bs ⟨h, 0⟩ ⟨b.label, 0⟩ u) :
    b.label ∈ growLoop bs h bs.length (loopSeed bs u h) := by
  obtain ⟨hI, hseed, hdone⟩ := growLoop_spec (bs := bs) bs.length (loopSeed_inv u h)
  generalize growLoop bs h bs.length (loopSeed bs u h) = S at hI hseed hdone
  apply Classical.byContradiction
  intro hbS
  -- `S` misses `b.label`, so it holds fewer labels than the body has, and the growth stopped
  -- with nothing left to add.
  have hcl : (bs.find? fun c => c.label != h && !S.contains c.label && entersAny S c) = none := by
    rcases hdone with hdone | hdone
    · exact hdone
    · exfalso
      have hmem : b.label ∈ bs.map (·.label) := List.mem_map.mpr ⟨b, hb, rfl⟩
      have hsub : S ⊆ (bs.map (·.label)).erase b.label := fun l hl => by
        obtain ⟨c, hc, hcl, -, -⟩ := hI.2 l hl
        exact (List.mem_erase_of_ne fun (he : l = b.label) => hbS (he ▸ hl)).mpr
          (List.mem_map.mpr ⟨c, hc, hcl⟩)
      have hle := List.length_le_of_nodup_subset hI.1 hsub
      rw [List.length_erase_of_mem hmem, List.length_map] at hle
      have := List.length_pos_of_mem hb
      omega
  -- The path ends at `u`, a point of the body outside `h`, so `u`'s block is the seed.
  have hu : u.label ∈ loopSeed bs u h := by
    obtain ⟨c, hc, hcl, hk⟩ := hp.node ⟨b, hb, rfl, Nat.zero_le _⟩
    have huh : u.label ≠ h := hp.label_ne hbh
    unfold loopSeed
    rw [ite_eq_left]
    · exact List.mem_singleton_self _
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      exact ⟨huh, c, hc, hcl, hk⟩
  exact hbS (hp.mem_of_closed hcl hbh (hseed _ hu))

/-- `loopBlocksFast` is `loopBlocks`. -/
@[csimp] public theorem loopBlocks_eq_fast : @loopBlocks = @loopBlocksFast := by
  funext env α bs u h
  unfold loopBlocksFast
  split
  next ht =>
    obtain ⟨tm, htm⟩ := Option.isSome_iff_exists.mp ht
    have hn := (tree?_eq_some htm).1
    unfold loopBlocks
    congr 1
    apply List.filter_congr
    intro b hb
    by_cases hbh : b.label = h
    · rw [show (b.label == h) = true from beq_iff_eq.mpr hbh, Bool.true_or, Bool.true_or]
    · rw [show (b.label == h) = false from beq_false_of_ne hbh, Bool.false_or, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      rw [reachAvoidB_enteredAt_iff hn hb, List.contains_iff_mem]
      constructor
      · exact growLoop_complete hb hbh
      · intro hS
        obtain ⟨c, -, -, -, hp⟩ := (growLoop_spec (bs := bs) bs.length (loopSeed_inv u h)).1.2 _ hS
        exact hp
  next => rfl

end Body

end Strata.Dyn
