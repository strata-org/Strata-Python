/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Dom
public import StrataMantle.DomCheck
import all StrataMantle.DomCheck
import all StrataMantle.DomProps

set_option autoImplicit false

/-!
# Scopability is dominance-correctness

`Body.Scopable` (`StrataMantle/Dom.lean`) asks that some legal tree of each body put every use
in scope.  Every such tree makes the body dominance-correct (`Body.Scopable.domCorrect`,
`StrataMantle/DomProps.lean`).  This module proves the converse for a body that is reachable,
every block reached from its entry, and whose labels are distinct, at every region depth: it
has a legal tree whose ancestors are exactly the dominators (`Body.exists_exact`), which puts in
scope everything any legal tree does (`Body.anc_exact_of_legal`), and so every available use.
So for such a function scopability is dominance-correctness (`Func.scopable_iff_domCorrect`).

Reachability is needed.  A block nothing reaches still constrains a legal tree, through (L3),
but not dominance: a transfer from it pulls up the parent of the block it enters, and two such
transfers may pull up the parents of two blocks whose uses need definitions that no one chain
of parents holds.

A use that is not available is refuted by a path from the entry to it that avoids each of its
value's definitions (`Body.not_scopable_of_refutes`), which `Body.pathB` checks.

## Main theorems

* `Body.exists_exact`: a reachable body with distinct labels has a legal tree whose ancestors
  are its dominators;
* `Body.anc_exact_of_legal`: that tree is maximal, putting in scope what any legal tree does;
* `Body.Shaped.scopable_iff`, `Func.scopable_iff_domCorrect`: for a reachable body with
  distinct labels, some tree scopes it exactly when it is dominance-correct;
* `Func.reachable_scopable_iff`: so a function is reachable and scopable exactly when it is
  shaped, reachable with distinct labels, and dominance-correct, which
  `StrataMantle/DomDecide.lean` decides;
* `Body.not_scopable_of_refutes`: a checked avoiding path refutes every tree.
-/

namespace Strata.Mantle

public section

variable {env : Env Unit} {α : Type}

namespace Body

/-- Every body has distinct labels, at every region depth. -/
inductive Distinct : List (Block env α) → Prop
  | mk {bs : List (Block env α)} : (bs.map (·.label)).Nodup →
      (∀ y r, RegionAt bs y r → Distinct r.blocks.toList) → Distinct bs

/-- The body's labels are distinct and its entry reaches every block, and so for each of its
regions. -/
inductive Shaped : List (Block env α) → Prop
  | mk {bs : List (Block env α)} : (bs.map (·.label)).Nodup →
      (∀ b ∈ bs, Reach bs ⟨b.label, 0⟩) →
      (∀ y r, RegionAt bs y r → Shaped r.blocks.toList) → Shaped bs

/-! ## Checking a path -/

/-- The labels the instruction or terminator at count `k` of block `b` transfers to. -/
@[expose] def targets (b : Block env α) (k : Nat) : List Label :=
  ((b.instrs[k]?.map fun i => i.succs.toList.map (·.target)).getD []) ++
    if k = b.instrs.size then b.term.succs.toList.map (·.target) else []

/-- Whether control may pass from `u` to `w`: `Edge`, checked. -/
@[expose] def edgeB (bs : List (Block env α)) (u w : Point) : Bool :=
  bs.any fun b => b.label == u.label &&
    ((w == ⟨u.label, u.count + 1⟩ && decide (u.count < b.instrs.size)) ||
      (w.count == 0 && bs.any (·.label == w.label) && (targets b u.count).contains w.label))

/-- Whether the points `ps`, after `u`, are a path from `u` to `y` that avoids `d`. -/
@[expose] def pathFrom (bs : List (Block env α)) (d y : Point) : Point → List Point → Bool
  | u, [] => u == y
  | u, w :: ps => edgeB bs u w && w != d && pathFrom bs d y w ps

/-- Whether the points `ps`, after the root, are a path from the root to `y` that avoids `d`. -/
@[expose] def pathB (bs : List (Block env α)) (d y : Point) (ps : List Point) : Bool :=
  root bs != d && pathFrom bs d y (root bs) ps

/-- Whether `find d` is, for every definition `d` of `x`, a path from the root to `y` that
avoids `d`. -/
@[expose] def refutes (find : Point → List Point) (bs : List (Block env α)) (x : ValId)
    (y : Point) : Bool :=
  ((defs bs).get x).all fun d => pathB bs d y (find d)


end Body

/-- Every body of the function has distinct labels and its entry reaches each of its blocks. -/
@[expose] def Func.Shaped (fn : Func env α) : Prop := Body.Shaped fn.blocks.toList

end

namespace Body

variable {env : Env Unit} {α : Type}

/-! ## Shapes -/

section shape

variable {bs : List (Block env α)}

/-- A shaped body is reachable. -/
theorem Shaped.reachable (h : Shaped bs) : Reachable bs := by
  induction h with
  | mk _ hr _ ih => exact .mk hr ih

/-- A reachable body with distinct labels at every depth is shaped. -/
theorem Reachable.shaped (hr : Reachable bs) : Distinct bs → Shaped bs := by
  induction hr with
  | mk hr _ ih =>
    intro hd
    cases hd with
    | mk hn hdr => exact .mk hn hr fun y r h => ih y r h (hdr y r h)

/-- A scopable body has distinct labels at every depth, which its trees' legality asks. -/
theorem Scopable.distinct {Λ : ValId → Prop} (h : Scopable Λ bs) : Distinct bs := by
  induction h with
  | mk _ hs _ ih => exact .mk hs.legal.distinct ih

end shape

/-! ## Dominance -/

section dom

variable {bs : List (Block env α)}

/-- A point reached avoiding `d` is not `d`. -/
theorem ReachAvoid.ne {d w : Point} (h : ReachAvoid bs d w) : w ≠ d := by
  cases h with
  | root h => exact h
  | step _ _ h => exact h

/-- If a path from the root avoids `d`, the root is not `d`. -/
theorem ReachAvoid.root_ne {d w : Point} (h : ReachAvoid bs d w) : Body.root bs ≠ d := by
  induction h with
  | root h => exact h
  | step _ _ _ ih => exact ih

/-- A point reached avoiding `d` is reached. -/
theorem ReachAvoid.reach {d w : Point} (h : ReachAvoid bs d w) : Reach bs w := by
  induction h with
  | root => exact .root
  | step _ he _ ih => exact .step ih he

/-- Every point dominates itself. -/
theorem dom_refl (d : Point) : Dom bs d d := fun h => h.ne rfl

/-- The root dominates every point. -/
theorem dom_root (y : Point) : Dom bs (root bs) y := fun h => h.root_ne rfl

/-- A strict dominator of a point dominates every point that enters it. -/
theorem Dom.of_edge {d u w : Point} (h : Dom bs d w) (hne : d ≠ w) (he : Edge bs u w) :
    Dom bs d u :=
  fun hu => h (.step hu he (Ne.symm hne))

/-- Dominance is transitive. -/
theorem Dom.trans {a b c : Point} (h₁ : Dom bs a b) (h₂ : Dom bs b c) : Dom bs a c := by
  intro hc
  refine h₂ ?_
  clear h₂
  -- A path that avoids `a` avoids `b`, or it would reach `b` without `a`.
  induction hc with
  | root hne => exact .root fun h => h₁ (h ▸ .root hne)
  | step hu he hne ih => exact .step ih he fun h => h₁ (h ▸ .step hu he hne)

/-- The dominators of a reachable point are ordered by dominance. -/
theorem Dom.total {a b y : Point} (hy : Reach bs y) (ha : Dom bs a y) (hb : Dom bs b y) :
    Dom bs a b ∨ Dom bs b a := by
  by_cases hab : Dom bs a b
  · exact .inl hab
  refine .inr fun hba => ?_
  have hab : ReachAvoid bs a b := Classical.not_not.mp hab
  -- Every reachable point is reached avoiding `a` or avoiding `b`: switch to the path to `b`
  -- avoiding `a` on reaching `b`, and to the one to `a` avoiding `b` on reaching `a`.
  have key : ∀ w, Reach bs w → ReachAvoid bs a w ∨ ReachAvoid bs b w := by
    intro w hw
    induction hw with
    | root => exact .inl (.root hab.root_ne)
    | @step u w _ he ih =>
      by_cases hwa : w = a
      · exact .inr (hwa ▸ hba)
      by_cases hwb : w = b
      · exact .inl (hwb ▸ hab)
      exact ih.elim (fun h => .inl (.step h he hwa)) (fun h => .inr (.step h he hwb))
  exact (key y hy).elim ha hb

/-- Some path from the root of `n` edges reaches the point. -/
inductive ReachN (bs : List (Block env α)) : Nat → Point → Prop
  | root : ReachN bs 0 (root bs)
  | step {n : Nat} {u w : Point} : ReachN bs n u → Edge bs u w → ReachN bs (n + 1) w

/-- A reached point is reached by a path of some number of edges. -/
theorem Reach.reachN {y : Point} (h : Reach bs y) : ∃ n, ReachN bs n y := by
  induction h with
  | root => exact ⟨0, .root⟩
  | step _ he ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .step hn he⟩

/-- A point reached by a path of `n` edges is reached. -/
theorem ReachN.reach {n : Nat} {y : Point} (h : ReachN bs n y) : Reach bs y := by
  induction h with
  | root => exact .root
  | step _ he ih => exact .step ih he

/-- A strict dominator is reached by a shorter path. -/
theorem ReachN.dom_lt {n : Nat} {w b : Point} (h : ReachN bs n w) (hb : Dom bs b w)
    (hne : b ≠ w) : ∃ m < n, ReachN bs m b := by
  induction h with
  | root => exact absurd (.root (Ne.symm hne)) hb
  | @step n u w hu he ih =>
    by_cases hbu : b = u
    · subst hbu
      exact ⟨n, Nat.lt_succ_self n, hu⟩
    · obtain ⟨m, hm, hm₁⟩ := ih (hb.of_edge hne he) hbu
      exact ⟨m, Nat.lt_succ_of_lt hm, hm₁⟩

/-- A reachable point is a node. -/
theorem Reach.node {y : Point} (hne : bs ≠ []) (h : Reach bs y) : Node bs y := by
  induction h with
  | root =>
    cases bs with
    | nil => exact absurd rfl hne
    | cons e _ => exact ⟨e, List.mem_cons_self, rfl, Nat.zero_le _⟩
  | step _ he _ =>
    cases he with
    | fall hb hk => exact ⟨_, hb, rfl, hk⟩
    | jump hj =>
      cases hj with
      | instr _ _ _ hv _ | term _ _ hv _ => exact ⟨_, hv, rfl, Nat.zero_le _⟩

/-- A point that is not a node dominates no reachable point. -/
theorem Reach.reachAvoid_of_not_node {d y : Point} (hne : bs ≠ []) (h : Reach bs y)
    (hd : ¬ Node bs d) : ReachAvoid bs d y := by
  induction h with
  | root => exact .root fun h => hd (h ▸ Reach.node hne .root)
  | step hu he ih => exact .step ih he fun h => hd (h ▸ (Reach.step hu he).node hne)

/-- Every point of a reached block is reached. -/
theorem reach_count {b : Block env α} (hb : b ∈ bs) (h : Reach bs ⟨b.label, 0⟩) :
    ∀ {k : Nat}, k ≤ b.instrs.size → Reach bs ⟨b.label, k⟩
  | 0, _ => h
  | _ + 1, hk => .step (reach_count hb h (Nat.le_of_succ_le hk)) (.fall hb hk)

/-- Every node of a body whose entry reaches its blocks is reached. -/
theorem Node.reach {p : Point} (hr : ∀ b ∈ bs, Reach bs ⟨b.label, 0⟩) (h : Node bs p) :
    Reach bs p := by
  obtain ⟨l, k⟩ := p
  obtain ⟨b, hb, hl, hk⟩ := h
  dsimp only at hl hk
  subst hl
  exact reach_count hb (hr b hb) hk

/-- A point that uses a value is a node. -/
theorem UseAt.node {x : ValId} {y : Point} (h : UseAt bs x y) : Node bs y := by
  cases h with
  | instr hb hk _ => exact ⟨_, hb, rfl, Nat.le_of_lt (Array.getElem?_eq_some_iff.mp hk).1⟩
  | term hb _ => exact ⟨_, hb, rfl, Nat.le_refl _⟩

/-- A point whose instruction or terminator owns a region is a node. -/
theorem RegionAt.node {y : Point} {r : Region env α} (h : RegionAt bs y r) : Node bs y := by
  cases h with
  | instr hb hk _ => exact ⟨_, hb, rfl, Nat.le_of_lt (Array.getElem?_eq_some_iff.mp hk).1⟩
  | term hb _ => exact ⟨_, hb, rfl, Nat.le_refl _⟩

/-- The point a jump leaves from is a node. -/
theorem Jump.node {u : Point} {v : Block env α} (h : Jump bs u v) : Node bs u := by
  cases h with
  | instr hb hk _ _ _ => exact ⟨_, hb, rfl, Nat.le_of_lt (Array.getElem?_eq_some_iff.mp hk).1⟩
  | term hb _ _ _ => exact ⟨_, hb, rfl, Nat.le_refl _⟩

/-- The point before an instruction dominates the point after it. -/
theorem dom_fall {l : Label} {k : Nat} : Dom bs ⟨l, k⟩ ⟨l, k + 1⟩ := by
  intro h
  generalize hy : (⟨l, k + 1⟩ : Point) = y at h
  cases h with
  | root _ => exact Nat.succ_ne_zero k (congrArg Point.count hy)
  | step hu he _ =>
    cases he with
    | fall _ _ =>
      cases hy
      exact hu.ne rfl
    | jump _ => exact Nat.succ_ne_zero k (congrArg Point.count hy)

/-- A strict dominator of the point after an instruction dominates the point before it. -/
theorem Dom.of_fall {d : Point} {l : Label} {k : Nat} (hn : Node bs ⟨l, k + 1⟩)
    (h : Dom bs d ⟨l, k + 1⟩) (hne : d ≠ ⟨l, k + 1⟩) : Dom bs d ⟨l, k⟩ := by
  obtain ⟨b, hb, hl, hk⟩ := hn
  dsimp only at hl hk
  subst hl
  exact h.of_edge hne (.fall hb hk)

end dom

/-! ## The exact tree -/

/-- Among the elements of `l` that satisfy `S`, totally preordered by `R` there, some one is
above all the others. -/
theorem exists_max {β : Type} (R : β → β → Prop) (S : β → Prop)
    (htrans : ∀ a b c, R a b → R b c → R a c) (htot : ∀ a b, S a → S b → R a b ∨ R b a)
    (hrefl : ∀ a, R a a) : ∀ l : List β, (∃ x ∈ l, S x) → ∃ m, S m ∧ ∀ x ∈ l, S x → R x m
  | [], ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | a :: l, ⟨x, hx, hS⟩ => by
    simp only [List.forall_mem_cons]
    by_cases hl : ∃ x ∈ l, S x
    · obtain ⟨m, hm, hmax⟩ := exists_max R S htrans htot hrefl l hl
      by_cases ha : S a
      · rcases htot a m ha hm with h | h
        · exact ⟨m, hm, fun _ => h, hmax⟩
        · exact ⟨a, ha, fun _ => hrefl a, fun x hx hSx => htrans _ _ _ (hmax x hx hSx) h⟩
      · exact ⟨m, hm, fun h => absurd h ha, hmax⟩
    · -- Only `a` satisfies `S`.
      have ha : S a := (List.mem_cons.mp hx).elim (· ▸ hS) fun hx => absurd ⟨x, hx, hS⟩ hl
      exact ⟨a, ha, fun _ => hrefl a, fun x hx hSx => absurd ⟨x, hx, hSx⟩ hl⟩

/-- The nodes of the body. -/
def nodes (bs : List (Block env α)) : List Point :=
  bs.flatMap fun b => (List.range (b.instrs.size + 1)).map (⟨b.label, ·⟩)

/-- Every node is in `nodes`. -/
theorem mem_nodes {bs : List (Block env α)} {p : Point} (h : Node bs p) : p ∈ nodes bs := by
  obtain ⟨b, hb, hl, hk⟩ := h
  exact List.mem_flatMap.mpr
    ⟨b, hb, List.mem_map.mpr ⟨p.count, List.mem_range.mpr (Nat.lt_succ_of_le hk), by rw [hl]⟩⟩

/-- `m` is the immediate dominator of the start of block `v`: a strict dominator that every
strict dominator dominates. -/
def IsIdom (bs : List (Block env α)) (v : Block env α) (m : Point) : Prop :=
  (Dom bs m ⟨v.label, 0⟩ ∧ m ≠ ⟨v.label, 0⟩) ∧
    ∀ q, Dom bs q ⟨v.label, 0⟩ → q ≠ ⟨v.label, 0⟩ → Dom bs q m

/-- A reachable block other than the root has an immediate dominator. -/
theorem exists_idom {bs : List (Block env α)} {v : Block env α} (hne : bs ≠ [])
    (hv : Reach bs ⟨v.label, 0⟩) (hroot : root bs ≠ ⟨v.label, 0⟩) : ∃ m, IsIdom bs v m := by
  obtain ⟨m, ⟨hm, hmne⟩, hmax⟩ := exists_max (Dom bs)
    (fun q => Dom bs q ⟨v.label, 0⟩ ∧ q ≠ ⟨v.label, 0⟩) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun _ _ ha hb => Dom.total hv ha.1 hb.1) dom_refl (nodes bs)
    ⟨root bs, mem_nodes (Reach.node hne .root), dom_root _, hroot⟩
  refine ⟨m, ⟨hm, hmne⟩, fun q hq hqne => hmax q (mem_nodes ?_) ⟨hq, hqne⟩⟩
  exact Classical.byContradiction fun hn => hq (hv.reachAvoid_of_not_node hne hn)


/-- A body whose labels are distinct and whose entry reaches every block has a legal tree whose
ancestors of each reachable point are exactly its dominators: the immediate-dominator tree. -/
public theorem exists_exact {e : Block env α} {rest : List (Block env α)}
    (hn : ((e :: rest).map (·.label)).Nodup)
    (hr : ∀ b ∈ e :: rest, Reach (e :: rest) ⟨b.label, 0⟩) :
    ∃ t : Tree, Legal (e :: rest) t ∧
      ∀ d y, Reach (e :: rest) y → (Anc (e :: rest) t d y ↔ Dom (e :: rest) d y) := by
  generalize hbs : e :: rest = bs at hn hr
  have hne : bs ≠ [] := hbs ▸ List.cons_ne_nil e rest
  have hroot : root bs = ⟨e.label, 0⟩ := by rw [← hbs]; rfl
  have hspec : ∀ l : Label, ∃ o : Option Point, (l = e.label → o = none) ∧
      (∀ v ∈ bs, v.label = l → l ≠ e.label → ∃ m, o = some m ∧ IsIdom bs v m) := by
    intro l
    by_cases hex : ∃ v ∈ bs, v.label = l ∧ l ≠ e.label
    · obtain ⟨v, hv, rfl, hve⟩ := hex
      obtain ⟨m, hm⟩ := exists_idom hne (hr v hv)
        (fun h => hve (congrArg Point.label (hroot.symm.trans h)).symm)
      refine ⟨some m, fun h => absurd h hve, fun v₁ hv₁ hl _ => ⟨m, rfl, ?_⟩⟩
      rwa [eq_of_label_eq hn hv₁ hv hl]
    · exact ⟨none, fun _ => rfl, fun v hv hl hle => absurd ⟨v, hv, hl, hle⟩ hex⟩
  obtain ⟨t, ht⟩ := Classical.axiomOfChoice hspec
  -- Every dominator of a reachable point is an ancestor, by induction on the length of a path
  -- to it: the point's parent, before an instruction or the block's immediate dominator, is
  -- reached by a shorter one.
  have anc : ∀ n y, ReachN bs n y → ∀ d, Dom bs d y → Anc bs t d y := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro y hy d hd
      by_cases hdy : d = y
      · subst hdy
        exact .refl _
      obtain ⟨l, k⟩ := y
      cases k with
      | succ j =>
        have hfall : Dom bs ⟨l, j⟩ ⟨l, j + 1⟩ := dom_fall
        obtain ⟨m, hm, hmr⟩ :=
          hy.dom_lt hfall fun h => Nat.succ_ne_self j (congrArg Point.count h).symm
        exact .fall (ih m hm _ hmr d (hd.of_fall (hy.reach.node hne) hdy))
      | zero =>
        obtain ⟨v, hv, hl, -⟩ := hy.reach.node hne
        dsimp only at hl
        subst hl
        by_cases hve : v.label = e.label
        · have hr₁ : root bs = ⟨v.label, 0⟩ := hroot.trans (by rw [hve])
          exact absurd (hr₁ ▸ ReachAvoid.root fun h => hdy (h.symm.trans hr₁)) hd
        obtain ⟨m, htv, ⟨hm, hmne⟩, hmax⟩ := (ht v.label).2 v hv rfl hve
        obtain ⟨n₁, hn₁, hmr⟩ := hy.dom_lt hm hmne
        exact .parent (ih n₁ hn₁ m hmr d (hmax d hd hdy)) hv htv
  have anc₁ : ∀ d y, Reach bs y → Dom bs d y → Anc bs t d y := fun d y hy hd =>
    let ⟨n, hn⟩ := hy.reachN
    anc n y hn d hd
  have hnot : ∀ v ∈ rest, v.label ≠ e.label := fun v hv h => by
    subst hbs
    exact (List.nodup_cons.mp hn).1 (List.mem_map.mpr ⟨v, hv, h⟩)
  have hL : Legal bs t := by
    refine ⟨hn, ?_, ?_, ?_, ?_⟩
    · intro e₁ he₁
      subst hbs
      cases he₁
      exact (ht e.label).1 rfl
    · intro b hb
      subst hbs
      obtain ⟨m, htv, ⟨hm, _⟩, _⟩ :=
        (ht b.label).2 b (List.mem_cons_of_mem _ hb) rfl (hnot b hb)
      refine ⟨m, htv, ?_⟩
      exact Classical.byContradiction fun h =>
        hm ((hr b (List.mem_cons_of_mem _ hb)).reachAvoid_of_not_node (List.cons_ne_nil _ _) h)
    · intro b hb
      exact anc₁ _ _ (hr b hb) (dom_root _)
    · intro u v p hj hp
      have hv : v ∈ bs := by cases hj <;> assumption
      by_cases hve : v.label = e.label
      · exact absurd ((ht v.label).1 hve ▸ hp : (none : Option Point) = some p) nofun
      obtain ⟨m, htv, ⟨hm, hmne⟩, _⟩ := (ht v.label).2 v hv rfl hve
      cases (Option.some.inj (htv.symm.trans hp) : m = p)
      exact anc₁ _ _ (hj.node.reach hr) (hm.of_edge hmne (.jump hj))
  subst hbs
  exact ⟨t, hL, fun d y hy => ⟨fun h => h.dom hL, anc₁ d y hy⟩⟩

/-- The exact tree is maximal: whatever a legal tree puts above a reachable point, it does. -/
public theorem anc_exact_of_legal {bs : List (Block env α)} {t t₁ : Tree}
    (hx : ∀ d y, Reach bs y → (Anc bs t d y ↔ Dom bs d y))
    (hL : Legal bs t₁) {d y : Point} (hy : Reach bs y) (h : Anc bs t₁ d y) : Anc bs t d y :=
  (hx d y hy).mpr (h.dom hL)

/-- A shaped body that is dominance-correct where `Λ` is available is scopable where anything
`Λ` holds of is visible. -/
public theorem Shaped.scopable {bs : List (Block env α)} (hs : Shaped bs) :
    ∀ {Λ Λ₁ : ValId → Prop}, (∀ x, Λ x → Λ₁ x) → DomCorrect Λ bs → Scopable Λ₁ bs := by
  induction hs with
  | @mk bs hn hr _ ih =>
    intro Λ Λ₁ hΛ hd
    obtain ⟨hu, hreg⟩ := hd
    cases bs with
    | nil =>
      refine .mk (fun _ => none) ⟨legal_nil _, fun _ _ h => ?_⟩ (fun _ _ h => ?_) <;>
        cases h <;> contradiction
    | cons e rest =>
      obtain ⟨t, hL, hx⟩ := exists_exact hn hr
      have avail : ∀ x y, Node (e :: rest) y → Avail (e :: rest) Λ x y →
          InScope (e :: rest) t Λ₁ x y := fun x y hy h =>
        h.elim (fun ⟨d, hd, hdom⟩ => .inl ⟨d, hd, (hx d y (hy.reach hr)).mpr hdom⟩)
          (.inr ∘ hΛ x)
      exact .mk t ⟨hL, fun x y h => avail x y h.node (hu x y h)⟩
        (fun y r h => ih y r h (avail · y h.node) (hreg y r h))

/-- For a shaped body, some tree scopes it exactly when it is dominance-correct. -/
public theorem Shaped.scopable_iff {Λ : ValId → Prop} {bs : List (Block env α)}
    (hs : Shaped bs) : Scopable Λ bs ↔ DomCorrect Λ bs :=
  ⟨fun h => h.domCorrect fun _ => id, hs.scopable fun _ => id⟩

/-! ## Refuting a use -/

section refute

variable {bs : List (Block env α)}

/-- `edgeB` holds only of an edge. -/
theorem edgeB_sound {u w : Point} (h : edgeB bs u w = true) : Edge bs u w := by
  obtain ⟨l, k⟩ := u
  simp only [edgeB, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨b, hb, hl, ⟨rfl, hk⟩ | ⟨⟨hw, v, hv, hvl⟩, ht⟩⟩ := h
  · subst hl
    exact .fall hb hk
  · obtain ⟨l₁, k₁⟩ := w
    dsimp only at hl hw hvl ht
    subst hl hw hvl
    unfold targets at ht
    rcases List.mem_append.mp ht with ht | ht
    · cases hi : b.instrs[k]? with
      | none => simp only [hi, Option.map_none, Option.getD_none, List.not_mem_nil] at ht
      | some i =>
        simp only [hi, Option.map_some, Option.getD_some, List.mem_map] at ht
        obtain ⟨s, hs, hst⟩ := ht
        exact .jump (.instr hb hi (Array.mem_toList_iff.mp hs) hv hst.symm)
    · by_cases hk : k = b.instrs.size
      · rw [if_pos hk, List.mem_map] at ht
        obtain ⟨s, hs, hst⟩ := ht
        subst hk
        exact .jump (.term hb (Array.mem_toList_iff.mp hs) hv hst.symm)
      · simp only [if_neg hk, List.not_mem_nil] at ht

/-- A path `pathFrom` accepts, from a point reached avoiding `d`, reaches its end avoiding `d`. -/
theorem pathFrom_sound {d y : Point} :
    ∀ {u : Point} {ps : List Point}, ReachAvoid bs d u → pathFrom bs d y u ps = true →
      ReachAvoid bs d y
  | u, [], hu, h => by
    simp only [pathFrom, beq_iff_eq] at h
    exact h ▸ hu
  | u, w :: ps, hu, h => by
    simp only [pathFrom, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact pathFrom_sound (.step hu (edgeB_sound h.1.1) h.1.2) h.2

/-- A checked path reaches its end avoiding `d`. -/
public theorem pathB_sound {d y : Point} {ps : List Point} (h : pathB bs d y ps = true) :
    ReachAvoid bs d y := by
  simp only [pathB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact pathFrom_sound (.root h.1) h.2

/-- A use that a checked path avoids every definition of, and that is not visible on entry,
refutes every tree. -/
public theorem not_scopable_of_refutes {Λ : ValId → Prop} {x : ValId} {y : Point}
    {find : Point → List Point} (hu : UseAt bs x y) (hΛ : ¬ Λ x)
    (h : refutes find bs x y = true) : ¬ Scopable Λ bs := by
  intro hs
  obtain ⟨hav, -⟩ := hs.domCorrect (Λ₁ := Λ) fun _ => id
  rcases hav x y hu with ⟨d, hd, hdom⟩ | hx
  · exact hdom (pathB_sound (List.all_eq_true.mp h d ((mem_defs x d).mpr hd)))
  · exact hΛ hx

end refute

end Body

/-- For a function whose bodies are reachable and have distinct labels, some tree per body
scopes it exactly when it is dominance-correct. -/
public theorem Func.scopable_iff_domCorrect {env : Env Unit} {α : Type} {fn : Func env α}
    (hr : fn.Reachable) (hd : Body.Distinct fn.blocks.toList) : fn.Scopable ↔ fn.DomCorrect :=
  (hr.shaped hd).scopable_iff

/-- A function is reachable and scopable exactly when it is shaped and dominance-correct. -/
public theorem Func.reachable_scopable_iff {env : Env Unit} {α : Type} {fn : Func env α} :
    fn.Reachable ∧ fn.Scopable ↔ fn.Shaped ∧ fn.DomCorrect := by
  constructor
  · rintro ⟨hr, hs⟩
    have hsh := hr.shaped hs.distinct
    exact ⟨hsh, (hsh.scopable_iff).mp hs⟩
  · rintro ⟨hsh, hd⟩
    exact ⟨hsh.reachable, (hsh.scopable_iff).mpr hd⟩

/-- A use of a value at the top level of the function, with a checked path from the entry
avoiding each of its definitions, refutes every tree. -/
public theorem Func.not_scopable_of_refutes {env : Env Unit} {α : Type} {fn : Func env α}
    {x : ValId} {y : Point} {find : Point → List Point} (hu : Body.UseAt fn.blocks.toList x y)
    (h : Body.refutes find fn.blocks.toList x y = true) : ¬ fn.Scopable :=
  Body.not_scopable_of_refutes hu id h

end Strata.Mantle
