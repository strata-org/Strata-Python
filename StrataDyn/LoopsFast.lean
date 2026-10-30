/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Loops
public import StrataDyn.DomFast
public import StrataDyn.ContractRegion
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

* `Body.transfersFast` checks each transfer's target against a set of the body's labels, where
  `Body.transfers` scans the body for it.
* `Body.backEdgesFast` decides dominance with the immediate-dominator tree that `Body.domTree?`
  computes and checks (`StrataDyn/DomFast.lean`), and the ancestor map of
  `StrataDyn/DomCheck.lean`.  If there is no such tree, it falls back to the search.
* `Body.loopBlocksFast` searches backwards from the block of the back edge's source, never
  through the head.  A map from each block to the blocks that transfer to it is built once, and
  the blocks found are kept in a label map, so the search visits each block and each transfer at
  most once.  If the labels are not distinct, it falls back to `Body.loopBlocks`.
  `Body.loopsOfFast` builds the predecessor map once for all the loops it searches.

The `@[csimp]` lemmas replace the simple versions only in modules that import this one, so code
that runs loop finding imports `StrataDyn.LoopsFast`.  The fast definitions and their
equalities are in one module, as in `StrataDyn/DomFast.lean`, so that importing the fast
versions also brings the lemmas that make them run.

## Main theorems

* `Body.transfers_eq_fast`, `Body.backEdges_eq_fast`, `Body.loopBlocks_eq_fast`,
  `Body.loopsOf_eq_fast`: the equalities, all `@[csimp]`.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

namespace Body

variable (bs : List (Block env α))

/-- `transfers`, checking each target against `labelSet` instead of scanning the body. -/
@[expose] def transfersFast : List (Point × Label) :=
  let set := labelSet bs
  bs.flatMap fun b => (List.range (b.instrs.size + 1)).flatMap fun k =>
    (targets b k).filterMap fun l =>
      if (set.find? l).isSome then some (⟨b.label, k⟩, l) else none

end Body

end

namespace Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)}

/-- `labelSet` holds exactly the labels of the body's blocks. -/
theorem labelSet_find? (l : Label) : ((labelSet bs).find? l).isSome = bs.any (·.label == l) := by
  unfold labelSet
  suffices ∀ (cs : List (Block env α)) (m : LabelMap Unit),
      ((cs.foldl (fun m b => m.insert b.label ()) m).find? l).isSome =
        ((m.find? l).isSome || cs.any (·.label == l)) by
    rw [this]; simp
  intro cs
  induction cs with
  | nil => intro m; simp
  | cons c cs ih =>
    intro m
    rw [List.foldl_cons, ih, LabelMap.find?_insert]
    by_cases hl : l = c.label
    · subst hl; simp
    · have hc : (c.label == l) = false := beq_false_of_ne (Ne.symm hl)
      simp [hl, hc]

/-- `transfersFast` is `transfers`.  It comes before `backEdgesFast` and `predMap`, which use
`transfers`, because a `@[csimp]` lemma replaces a definition only in code compiled after it. -/
@[csimp] public theorem transfers_eq_fast : @transfers = @transfersFast := by
  funext env α bs
  unfold transfers transfersFast
  simp only [labelSet_find?]

end Body

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

/-- For each block, by label, the labels of the blocks that transfer to it. -/
@[expose] def predMap : LabelMap (List Label) :=
  (transfers bs).foldl (init := ∅) fun m p => m.insert p.2 (p.1.label :: (m.find? p.2).getD [])

/-- The labels of the blocks that transfer to `l`, as the predecessor map `pm` has them. -/
@[expose] def predsIn (pm : LabelMap (List Label)) (l : Label) : List Label :=
  (pm.find? l).getD []

/-- The state of the search for a loop: the labels still to visit, and the labels found, as a
set for lookups and as a list. -/
structure Search where
  todo : List Label
  seen : LabelMap Unit
  found : List Label

/-- The search with `p` found and to visit, unless it is `h` or found already. -/
@[expose] def Search.add (h : Label) (s : Search) (p : Label) : Search :=
  if p == h || (s.seen.find? p).isSome then s
  else ⟨p :: s.todo, s.seen.insert p (), p :: s.found⟩

/-- The search, at most `fuel` steps: each takes a label to visit and adds its predecessors. -/
@[expose] def search (pm : LabelMap (List Label)) (h : Label) :
    (fuel : Nat) → Search → Search
  | 0, s => s
  | f + 1, s =>
    match s.todo with
    | [] => s
    | l :: todo => search pm h f ((predsIn pm l).foldl (Search.add h) { s with todo })

/-- Where the loop of the back edge from `u` to `h` grows from: `u`'s block, unless it is `h` or
`u` is not a point of the body. -/
@[expose] def loopSeed (u : Point) (h : Label) : List Label :=
  if u.label != h && bs.any (fun b => b.label == u.label && decide (u.count ≤ b.instrs.size))
  then [u.label] else []

/-- The labels of the natural loop of the back edge from `u` to `h`, by a search backwards from
`u`'s block, with the predecessor map `pm`, that never passes the head. -/
@[expose] def searchLoop (pm : LabelMap (List Label)) (u : Point) (h : Label) : List Label :=
  let seed := loopSeed bs u h
  let start : Search := ⟨seed, seed.foldl (fun m l => m.insert l ()) ∅, seed⟩
  let s := search pm h bs.length start
  (bs.filter fun b => b.label == h || (s.seen.find? b.label).isSome).map (·.label)

/-- `loopBlocks`, by `searchLoop`. -/
@[expose] def loopBlocksFast (u : Point) (h : Label) : List Label :=
  if (tree? bs).isSome then searchLoop bs (predMap bs) u h else loopBlocks bs u h

/-- `loopsOf`, by `searchLoop`, with one predecessor map for all the loops. -/
@[expose] def loopsOfFast (es : List (Point × Label)) : List (List Label) :=
  if (tree? bs).isSome then
    let pm := predMap bs
    es.map fun e => searchLoop bs pm e.1 e.2
  else loopsOf bs es

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

/-- `predMap` lists, for each label, the labels of the blocks with a transfer to it. -/
theorem mem_predsIn_predMap {l x : Label} :
    x ∈ predsIn (predMap bs) l ↔ ∃ u, (u, l) ∈ transfers bs ∧ u.label = x := by
  unfold predsIn predMap
  suffices ∀ (ts : List (Point × Label)) (m : LabelMap (List Label)),
      x ∈ ((ts.foldl (fun m p => m.insert p.2 (p.1.label :: (m.find? p.2).getD [])) m).find?
        l).getD [] ↔ x ∈ (m.find? l).getD [] ∨ ∃ u, (u, l) ∈ ts ∧ u.label = x by
    rw [this]
    simp
  intro ts
  induction ts with
  | nil => intro m; simp
  | cons t ts ih =>
    intro m
    rw [List.foldl_cons, ih, LabelMap.find?_insert]
    obtain ⟨u, l'⟩ := t
    by_cases hl : l = l'
    · subst hl
      simp only [↓reduceIte, Option.getD_some, List.mem_cons, Prod.mk.injEq, and_true]
      constructor
      · rintro ((rfl | hx) | ⟨w, hw, rfl⟩)
        · exact .inr ⟨u, .inl rfl, rfl⟩
        · exact .inl hx
        · exact .inr ⟨w, .inr hw, rfl⟩
      · rintro (hx | ⟨w, (rfl | hw), rfl⟩)
        · exact .inl (.inr hx)
        · exact .inl (.inl rfl)
        · exact .inr ⟨w, hw, rfl⟩
    · simp only [hl, ↓reduceIte, List.mem_cons, Prod.mk.injEq, and_false, false_or]

/-- What the search keeps true, with `F` its remaining fuel: the set and the list of found labels
agree, the found labels satisfy `LoopInv`, the labels to visit are found, a found label that is
not to visit has all its predecessors other than `h` (in `predMap bs`) found, except perhaps `l`,
and there is fuel for every label left to visit. -/
structure SearchInv (u : Point) (h : Label) (l : Option Label) (F : Nat) (s : Search) : Prop where
  seen : ∀ x, (s.seen.find? x).isSome ↔ x ∈ s.found
  inv : LoopInv (bs := bs) u h s.found
  todo : s.todo ⊆ s.found
  closed : ∀ x ∈ s.found, x ∉ s.todo → some x ≠ l →
    ∀ p ∈ predsIn (predMap bs) x, p ≠ h → p ∈ s.found
  count : s.todo.length + bs.length ≤ F + s.found.length

/-- A label other than `h` with a transfer to a found label can be found: it is the label of a
block of the body, whose start reaches `u` avoiding `h`'s start. -/
theorem LoopInv.pred {u : Point} {h : Label} {S : List Label} (hI : LoopInv (bs := bs) u h S)
    {l p : Label} (hl : l ∈ S) (hp : p ∈ predsIn (predMap bs) l) (hph : p ≠ h) (hpS : p ∉ S) :
    LoopInv (bs := bs) u h (p :: S) := by
  refine ⟨List.nodup_cons.mpr ⟨hpS, hI.1⟩, fun x hx => ?_⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · obtain ⟨w, hw, rfl⟩ := mem_predsIn_predMap.mp hp
    obtain ⟨b, hb, hbl, hk, ht, v, hv, hvl⟩ := mem_transfers.mp hw
    obtain ⟨-, -, -, hlh, hpath⟩ := hI.2 l hl
    refine ⟨b, hb, hbl, hph, ?_⟩
    have hj : Jump bs ⟨b.label, w.count⟩ v := jump_of_targets hb hv (hvl ▸ ht)
    have hvd : (⟨v.label, 0⟩ : Point) ≠ ⟨h, 0⟩ := fun he =>
      hlh (by rw [← hvl]; exact congrArg Point.label he)
    have hbh : b.label ≠ h := by rw [hbl]; exact hph
    have hstep := PathAvoid.step (PathAvoid.fall (d := ⟨h, 0⟩) hb hbh hk) (.jump hj) hvd
    rw [hbl] at hstep
    exact hstep.trans (hvl ▸ hpath)
  · exact hI.2 x hx

/-- Adding the predecessors `ps` of the found label `l`, which is not to visit, keeps the
invariant, finds every one of them other than `h`, and keeps what was found. -/
theorem foldl_add {u : Point} {h l : Label} {F : Nat} :
    ∀ (ps : List Label) (s : Search), (∀ p ∈ ps, p ∈ predsIn (predMap bs) l) → l ∈ s.found →
      SearchInv (bs := bs) u h (some l) F s →
      SearchInv (bs := bs) u h (some l) F (ps.foldl (Search.add h) s) ∧
        (∀ p ∈ ps, p ≠ h → p ∈ (ps.foldl (Search.add h) s).found) ∧
        (∀ x ∈ s.found, x ∈ (ps.foldl (Search.add h) s).found)
  | [], s, _, _, hI => ⟨hI, nofun, fun _ h => h⟩
  | p :: ps, s, hps, hl, hI => by
    rw [List.foldl_cons]
    have hp := hps p List.mem_cons_self
    -- One step, then the rest.
    have step : SearchInv (bs := bs) u h (some l) F (Search.add h s p) ∧
        (p ≠ h → p ∈ (Search.add h s p).found) ∧
        (∀ x ∈ s.found, x ∈ (Search.add h s p).found) := by
      unfold Search.add
      by_cases hc : (p == h || (s.seen.find? p).isSome) = true
      · rw [ite_eq_left hc]
        refine ⟨hI, fun hph => ?_, fun _ h => h⟩
        rcases Bool.or_eq_true _ _ |>.mp hc with he | hs
        · exact absurd (beq_iff_eq.mp he) hph
        · exact (hI.seen p).mp hs
      · rw [ite_eq_right hc]
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hc
        obtain ⟨hph, hns⟩ := hc
        have hpS : p ∉ s.found := fun hm => hns ((hI.seen p).mpr hm)
        refine ⟨⟨fun x => ?_, hI.inv.pred hl hp hph hpS, ?_, ?_, ?_⟩,
          fun _ => List.mem_cons_self, fun x hx => List.mem_cons_of_mem _ hx⟩
        · rw [LabelMap.find?_insert]
          by_cases hx : x = p
          · subst hx; simp
          · simp [hx, hI.seen x]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hI.todo hx)
        · intro x hx hxt hxl q hq hqh
          rcases List.mem_cons.mp hx with rfl | hx
          · exact absurd List.mem_cons_self hxt
          · exact List.mem_cons_of_mem _
              (hI.closed x hx (fun hm => hxt (List.mem_cons_of_mem _ hm)) hxl q hq hqh)
        · have hc := hI.count
          simp only [List.length_cons]
          omega
    obtain ⟨hI₁, hp₁, hsub₁⟩ := step
    obtain ⟨hI₂, hps₂, hsub₂⟩ := foldl_add ps (Search.add h s p)
      (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (hsub₁ l hl) hI₁
    refine ⟨hI₂, fun q hq hqh => ?_, fun x hx => hsub₂ x (hsub₁ x hx)⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hsub₂ _ (hp₁ hqh)
    · exact hps₂ q hq hqh

/-- The search keeps the invariant, with some fuel, keeps what it has found, and ends with nothing
left to visit: the fuel the invariant counts is enough. -/
theorem search_spec {u : Point} {h : Label} :
    ∀ (F : Nat) (s : Search), SearchInv (bs := bs) u h none F s →
      (∃ F', SearchInv (bs := bs) u h none F' (search (predMap bs) h F s)) ∧
        (search (predMap bs) h F s).todo = [] ∧
        ∀ x ∈ s.found, x ∈ (search (predMap bs) h F s).found
  | 0, s, hI => by
    refine ⟨⟨0, hI⟩, ?_, fun _ h => h⟩
    -- No fuel is left, so nothing is left to visit.
    have hc := hI.count
    have hsub : s.found ⊆ bs.map (·.label) := fun x hx => by
      obtain ⟨c, hc, hcl, -, -⟩ := hI.inv.2 x hx
      exact List.mem_map.mpr ⟨c, hc, hcl⟩
    have hle := List.length_le_of_nodup_subset hI.inv.1 hsub
    rw [List.length_map] at hle
    exact List.eq_nil_of_length_eq_zero (by simp only [search]; omega)
  | F + 1, s, hI => by
    unfold search
    split
    next ht => exact ⟨⟨F + 1, hI⟩, ht, fun _ h => h⟩
    next l todo ht =>
      have hl : l ∈ s.found := hI.todo (ht ▸ List.mem_cons_self)
      let s₀ : Search := { s with todo }
      have hI₀ : SearchInv (bs := bs) u h (some l) F s₀ := by
        refine ⟨hI.seen, hI.inv, fun x hx => hI.todo (ht ▸ List.mem_cons_of_mem _ hx),
          fun x hx hxt hxl => ?_, ?_⟩
        · refine hI.closed x hx (fun hm => ?_) (by simp)
          rw [ht] at hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact hxl rfl
          · exact hxt hm
        · have hc := hI.count
          rw [ht] at hc
          simp only [List.length_cons] at hc
          show todo.length + bs.length ≤ F + s.found.length
          omega
      obtain ⟨hI₁, hall, hsub⟩ := foldl_add (predsIn (predMap bs) l) s₀
        (fun _ h => h) hl hI₀
      have hI₂ : SearchInv (bs := bs) u h none F (List.foldl (Search.add h) s₀
          (predsIn (predMap bs) l)) := by
        refine ⟨hI₁.seen, hI₁.inv, hI₁.todo, fun x hx hxt _ => ?_, hI₁.count⟩
        by_cases hxl : x = l
        · subst hxl
          exact hall
        · exact hI₁.closed x hx hxt (by simp [hxl])
      obtain ⟨hI₃, hdone, hsub₃⟩ := search_spec F _ hI₂
      exact ⟨hI₃, hdone, fun x hx => hsub₃ x (hsub x hx)⟩

/-- If no found label has a predecessor other than `h` outside the found labels, then a path that
starts outside `h`, avoids `h`'s start and ends in a found label, starts in one. -/
theorem PathAvoid.mem_of_closed {h : Label} {S : List Label}
    (hcl : ∀ x ∈ S, ∀ p ∈ predsIn (predMap bs) x, p ≠ h → p ∈ S)
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
      exact hcl _ hy _ (mem_predsIn_predMap.mpr ⟨_, mem_transfers.mpr
          ⟨c, hc, hcl', le_of_mem_targets ht, ht, v, hj.mem, rfl⟩, rfl⟩) (hp₁.label_ne hx)

/-- The search's start, from the seed `S`, satisfies the invariant. -/
theorem searchStart_inv {u : Point} {h : Label} {S : List Label}
    (hI : LoopInv (bs := bs) u h S) :
    SearchInv (bs := bs) u h none bs.length ⟨S, S.foldl (fun m l => m.insert l ()) ∅, S⟩ := by
  refine ⟨fun x => ?_, hI, fun _ h => h, fun x hx hxt => absurd hx hxt, by simp only; omega⟩
  suffices ∀ (T : List Label) (m : LabelMap Unit), ((T.foldl (fun m l => m.insert l ()) m).find?
      x).isSome ↔ x ∈ T ∨ (m.find? x).isSome by
    rw [this]; simp
  intro T
  induction T with
  | nil => intro m; simp
  | cons t T ih =>
    intro m
    rw [List.foldl_cons, ih, LabelMap.find?_insert]
    by_cases hx : x = t
    · subst hx; simp
    · simp [hx]

/-- `loopBlocksFast` is `loopBlocks`. -/
@[csimp] public theorem loopBlocks_eq_fast : @loopBlocks = @loopBlocksFast := by
  funext env α bs u h
  unfold loopBlocksFast
  split
  next ht =>
    obtain ⟨tm, htm⟩ := Option.isSome_iff_exists.mp ht
    have hn := (tree?_eq_some htm).1
    unfold searchLoop
    dsimp only
    obtain ⟨⟨_, hI⟩, hdone, hseed⟩ := search_spec (bs := bs) (u := u) (h := h) bs.length _
      (searchStart_inv (loopSeed_inv u h))
    generalize search (predMap bs) h bs.length ⟨loopSeed bs u h,
      (loopSeed bs u h).foldl (fun m l => m.insert l ()) ∅, loopSeed bs u h⟩ = s at hI hdone hseed ⊢
    have hcl : ∀ x ∈ s.found, ∀ p ∈ predsIn (predMap bs) x, p ≠ h → p ∈ s.found :=
      fun x hx => hI.closed x hx (by rw [hdone]; exact List.not_mem_nil) (by simp)
    unfold loopBlocks
    congr 1
    apply List.filter_congr
    intro b hb
    by_cases hbh : b.label = h
    · rw [show (b.label == h) = true from beq_iff_eq.mpr hbh, Bool.true_or, Bool.true_or]
    · rw [show (b.label == h) = false from beq_false_of_ne hbh, Bool.false_or, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      rw [reachAvoidB_enteredAt_iff hn hb, hI.seen]
      constructor
      · intro hp
        -- The path ends at `u`, a point of the body outside `h`, so `u`'s block is the seed.
        have hu : u.label ∈ s.found := by
          obtain ⟨c, hc, hcl', hk⟩ := hp.node ⟨b, hb, rfl, Nat.zero_le _⟩
          apply hseed
          unfold loopSeed
          rw [ite_eq_left]
          · exact List.mem_singleton_self _
          · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, beq_iff_eq,
              decide_eq_true_eq]
            exact ⟨hp.label_ne hbh, c, hc, hcl', hk⟩
        exact hp.mem_of_closed hcl hbh hu
      · intro hS
        obtain ⟨c, -, -, -, hp⟩ := hI.inv.2 _ hS
        exact hp
  next => rfl

/-- `loopsOfFast` is `loopsOf`. -/
@[csimp] public theorem loopsOf_eq_fast : @loopsOf = @loopsOfFast := by
  funext env α bs es
  unfold loopsOfFast
  split
  next ht =>
    unfold loopsOf
    apply List.map_congr_left
    intro e _
    rw [loopBlocks_eq_fast]
    unfold loopBlocksFast
    rw [ite_eq_left ht]
  next => rfl

end Body

end Strata.Dyn
