/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.DomComplete
public import StrataMantle.DomFast
import all StrataMantle.DomCheck
import all StrataMantle.DomFast
import all StrataMantle.DomProps
import all StrataMantle.DomComplete
import all StrataMantle.Util.List

set_option autoImplicit false

/-!
# Deciding scopability

`Func.checkDom` decides whether a function is shaped, reachable with distinct labels in every
body, and dominance-correct, and so, by `Func.reachable_scopable_iff`
(`StrataMantle/DomComplete.lean`), whether it is reachable and some tree per body scopes it.
That gives `Decidable (fn.Reachable ∧ fn.Scopable)`, which `Func.WF`'s instance uses.  The
statement names no algorithm: this module computes the tree and proves the computation
correct, so the algorithm is verified rather than trusted.

Per body it takes one of three ways:

* the fast way, when `Body.domTree?` (`StrataMantle/DomFast.lean`) gives the computed tree,
  which is then exact: it checks each use against that tree with the ancestor and definition
  maps of `StrataMantle/DomCheck.lean`, so it rejects a use out of scope as fast as it accepts
  one in scope;
* the cheap rejection, when the depth-first search's labels are closed under transfers but miss
  a block (`Body.unreachedB`): the block is unreachable, so the body is not shaped;
* otherwise, which happens only if the search is wrong, the slow way.  `Body.reachAvoidB`
  decides `Body.ReachAvoid`, and so dominance, for a body whose labels are distinct, by the
  labels whose start a path from the root reaches avoiding `d`, grown one label at a time.  Each
  round scans every transfer of the blocks reached so far, so it is cubic.

## Main theorems

* `Body.reachAvoidB_iff`, `Body.reachB_iff`: the slow search decides `ReachAvoid` and `Reach`;
* `Body.not_shaped_of_unreachedB`: the cheap rejection is sound;
* `Func.checkDom_iff`: `checkDom` decides shaped dominance-correctness.
-/

namespace Strata.Mantle

public section

variable {env : Env Unit} {α : Type}

namespace Body

/-- The last count of block `b` that a path entering it at its start reaches without passing
`d`, or `none` if its start is `d`. -/
@[expose] def lim (d : Point) (b : Block env α) : Option Nat :=
  if b.label = d.label then (if d.count = 0 then none else some (min (d.count - 1) b.instrs.size))
  else some b.instrs.size

/-- The labels that block `b`, entered at its start, transfers to before passing `d`. -/
@[expose] def exits (d : Point) (b : Block env α) : List Label :=
  match lim d b with
  | none => []
  | some m => (List.range (m + 1)).flatMap (targets b)

/-- A label a path from the starts of the blocks `S` enters next while avoiding `d`, if there
is one not in `S`. -/
@[expose] def nextLabel (bs : List (Block env α)) (d : Point) (S : List Label) : Option Label :=
  ((bs.filter (S.contains ·.label)).flatMap (exits d)).find? fun l =>
    !S.contains l && bs.any (·.label == l) && (⟨l, 0⟩ : Point) != d

/-- `S`, with labels `nextLabel` gives added, at most `fuel` of them. -/
@[expose] def grow (bs : List (Block env α)) (d : Point) : (fuel : Nat) → List Label → List Label
  | 0, S => S
  | f + 1, S =>
    match nextLabel bs d S with
    | none => S
    | some l => grow bs d f (l :: S)

/-- The labels whose start a path from the root reaches avoiding `d`. -/
@[expose] def reached (bs : List (Block env α)) (d : Point) : List Label :=
  if root bs = d then [] else grow bs d bs.length [(root bs).label]

/-- Whether a path from the root reaches `y` avoiding `d`: `ReachAvoid`, decided. -/
@[expose] def reachAvoidB (bs : List (Block env α)) (d y : Point) : Bool :=
  (bs.find? (·.label == y.label)).any fun b =>
    (reached bs d).contains y.label && (lim d b).any (y.count ≤ ·)

/-- A point that is not a node of the body: past the end of its first block. -/
@[expose] def outside (bs : List (Block env α)) : Point :=
  ⟨(root bs).label, (bs.map (·.instrs.size)).foldl max 0 + 1⟩

/-- Whether a path from the root reaches `y`: `Reach`, decided. -/
@[expose] def reachB (bs : List (Block env α)) (y : Point) : Bool := reachAvoidB bs (outside bs) y

/-- Whether `x` is available at count `k` of block `b` of the body, entered where `Λ` is: defined
at a point no path from the root to there avoids, or in `Λ`. -/
@[expose] def availB (bs : List (Block env α)) (Λ : ValId → Bool) (b : Block env α) (k : Nat)
    (x : ValId) : Bool :=
  ((defs bs).get x).any (fun d => !reachAvoidB bs d ⟨b.label, k⟩) || Λ x

/-- Whether the labels the depth-first search reaches are closed under transfers, include the
entry's, and miss some block's: a certificate that a block is unreachable. -/
def unreachedB (bs : List (Block env α)) : Bool :=
  match tree? bs with
  | none => false
  | some t =>
    let S : LabelMap Unit := (rpoLabels bs).foldl (fun m l => m.insert l ()) ∅
    let inS (l : Label) : Bool := (S.find? l).isSome
    (bs.head?.all fun e => inS e.label) &&
      bs.all (fun b => !inS b.label || (List.range (b.instrs.size + 1)).all fun k =>
        (targets b k).all fun l => inS l || (t.find? l).isNone) &&
      bs.any (fun b => !inS b.label)

/-- Whether the body's labels are distinct and its entry reaches every block. -/
@[expose] def shapeB (bs : List (Block env α)) : Bool :=
  (tree? bs).isSome && bs.all fun b => reachB bs ⟨b.label, 0⟩

end Body

mutual

/-- The instruction uses only what `σ` makes available, and its regions are shaped and
dominance-correct. -/
@[expose] def Instruction.domOK (σ : ValId → Bool) : Instruction env α → Bool
  | .const .. => true
  | .apply _ _ _ _ args succs ⟨regions⟩ => usesIn σ args succs && Region.domOKList σ regions

/-- `Instruction.domOK` of each, the first at count `k`, with `σ` at its count. -/
@[expose] def Instruction.domOKList (σ : Nat → ValId → Bool) :
    Nat → List (Instruction env α) → Bool
  | _, [] => true
  | k, i :: is => i.domOK (σ k) && Instruction.domOKList σ (k + 1) is

/-- The terminator uses only what `σ` makes available, and its regions are shaped and
dominance-correct. -/
@[expose] def Terminator.domOK (σ : ValId → Bool) : Terminator env α → Bool
  | .apply _ _ _ args succs ⟨regions⟩ => usesIn σ args succs && Region.domOKList σ regions

/-- Each block uses only what `σ b k` makes available at its count `k`, and its regions are
shaped and dominance-correct. -/
@[expose] def Block.domOKList (σ : Block env α → Nat → ValId → Bool) :
    List (Block env α) → Bool
  | [] => true
  | (b@⟨_, _, ⟨instrs⟩, term, _⟩) :: bs =>
    Instruction.domOKList (σ b) 0 instrs && term.domOK (σ b instrs.length) &&
      Block.domOKList σ bs

/-- The region is shaped and dominance-correct, entered where `Λ` is available.  When the
computed tree checks out, it checks each use against that tree; otherwise it checks the body
the slow way. -/
@[expose] def Region.domOK (Λ : ValId → Bool) : Region env α → Bool
  | ⟨⟨bs⟩⟩ =>
    match Body.domTree? bs with
    | some t =>
      match Body.tree? bs with
      | none => false
      | some tm =>
        let n := bs.length
        let m := Body.ancs tm t bs
        let dm := Body.defs bs
        Block.domOKList (fun b k x => Body.scopeAt tm t n m dm b k x || Λ x) bs
    | none =>
      !Body.unreachedB bs && Body.shapeB bs && Block.domOKList (Body.availB bs Λ) bs

/-- `Region.domOK` of each. -/
@[expose] def Region.domOKList (Λ : ValId → Bool) : List (Region env α) → Bool
  | [] => true
  | r :: rs => r.domOK Λ && Region.domOKList Λ rs

end

/-- Whether the function is shaped and dominance-correct, the slow way. -/
@[expose] def Func.checkDom (fn : Func env α) : Bool := Region.domOK (fun _ => false) ⟨fn.blocks⟩

end

namespace Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)}

/-! ## Transfers -/

/-- A block jumps to every block of the body that `targets` lists. -/
theorem jump_of_targets {b v : Block env α} {k : Nat} (hb : b ∈ bs) (hv : v ∈ bs)
    (h : v.label ∈ targets b k) : Jump bs ⟨b.label, k⟩ v := by
  unfold targets at h
  rcases List.mem_append.mp h with h | h
  · cases hi : b.instrs[k]? with
    | none => simp only [hi, Option.map_none, Option.getD_none, List.not_mem_nil] at h
    | some i =>
      simp only [hi, Option.map_some, Option.getD_some, List.mem_map] at h
      obtain ⟨s, hs, hst⟩ := h
      exact .instr hb hi (Array.mem_toList_iff.mp hs) hv hst.symm
  · by_cases hk : k = b.instrs.size
    · rw [ite_eq_left hk, List.mem_map] at h
      obtain ⟨s, hs, hst⟩ := h
      subst hk
      exact .term hb (Array.mem_toList_iff.mp hs) hv hst.symm
    · simp only [ite_eq_right hk, List.not_mem_nil] at h

/-- Every jump is from a block whose `targets` at its count lists the target. -/
theorem targets_of_jump {u : Point} {v : Block env α} (h : Jump bs u v) :
    ∃ b ∈ bs, b.label = u.label ∧ v.label ∈ targets b u.count := by
  cases h with
  | @instr b _ i k s hb hk hs _ hl =>
    refine ⟨b, hb, rfl, List.mem_append_left _ ?_⟩
    simp only [hk, Option.map_some, Option.getD_some, List.mem_map]
    exact ⟨s, Array.mem_toList_iff.mpr hs, hl.symm⟩
  | @term b _ s hb hs _ hl =>
    refine ⟨b, hb, rfl, List.mem_append_right _ ?_⟩
    rw [ite_eq_left rfl, List.mem_map]
    exact ⟨s, Array.mem_toList_iff.mpr hs, hl.symm⟩

/-! ## The reach of a block -/

/-- `lim d b` is `none` exactly when `d` is the start of `b`. -/
theorem lim_eq_none {d : Point} {b : Block env α} :
    lim d b = none ↔ (⟨b.label, 0⟩ : Point) = d := by
  obtain ⟨l, c⟩ := d
  simp only [lim]
  by_cases hl : b.label = l
  · rw [ite_eq_left hl]
    by_cases hc : c = 0
    · rw [ite_eq_left hc, hl, hc]
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    · rw [ite_eq_right hc]
      exact ⟨nofun, fun h => (hc (congrArg Point.count h).symm).elim⟩
  · rw [ite_eq_right hl]
    exact ⟨nofun, fun h => (hl (congrArg Point.label h)).elim⟩

/-- `lim d b` is a count of `b`, and no count up to it is `d`. -/
theorem lim_spec {d : Point} {b : Block env α} {m : Nat} (h : lim d b = some m) :
    m ≤ b.instrs.size ∧ ∀ j ≤ m, (⟨b.label, j⟩ : Point) ≠ d := by
  obtain ⟨l, c⟩ := d
  simp only [lim] at h
  by_cases hl : b.label = l
  · rw [ite_eq_left hl] at h
    by_cases hc : c = 0
    · rw [ite_eq_left hc] at h
      exact absurd h nofun
    · rw [ite_eq_right hc] at h
      cases h
      refine ⟨Nat.min_le_right _ _, fun j hj he => ?_⟩
      have := congrArg Point.count he
      dsimp only at this
      omega
  · rw [ite_eq_right hl] at h
    cases h
    exact ⟨Nat.le_refl _, fun _ _ he => hl (congrArg Point.label he)⟩

/-- A block entered at its start avoiding `d` is passed through avoiding `d` up to `lim`. -/
theorem reachAvoid_count {d : Point} {b : Block env α} {m : Nat} (hb : b ∈ bs)
    (h : ReachAvoid bs d ⟨b.label, 0⟩) (hm : lim d b = some m) :
    ∀ {k : Nat}, k ≤ m → ReachAvoid bs d ⟨b.label, k⟩
  | 0, _ => h
  | _ + 1, hk =>
    .step (reachAvoid_count hb h hm (Nat.le_of_succ_le hk))
      (.fall hb (Nat.lt_of_lt_of_le hk (lim_spec hm).1)) ((lim_spec hm).2 _ hk)

/-! ## Growing the reached labels -/

/-- What `grow` keeps true of the labels reached: each names a block of the body whose start a
path from the root reaches avoiding `d`, and none twice. -/
def GrowInv (bs : List (Block env α)) (d : Point) (S : List Label) : Prop :=
  (∀ l ∈ S, ∃ b ∈ bs, b.label = l ∧ ReachAvoid bs d ⟨l, 0⟩) ∧ S.Nodup

/-- A label `nextLabel` gives is new, names a block, does not start at `d`, and is an exit of a
block in `S`. -/
theorem nextLabel_some {d : Point} {S : List Label} {l : Label} (h : nextLabel bs d S = some l) :
    l ∉ S ∧ (∃ v ∈ bs, v.label = l) ∧ (⟨l, 0⟩ : Point) ≠ d ∧
      ∃ b ∈ bs, b.label ∈ S ∧ l ∈ exits d b := by
  have hp := List.find?_some h
  have hm := List.mem_of_find?_eq_some h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at hp
  obtain ⟨⟨hS, hv⟩, hd⟩ := hp
  obtain ⟨b, hb, hl⟩ := List.mem_flatMap.mp hm
  obtain ⟨hb, hbS⟩ := List.mem_filter.mp hb
  refine ⟨fun h => ?_, hv, hd, b, hb, List.contains_iff_mem.mp hbS, hl⟩
  rw [List.contains_iff_mem.mpr h] at hS
  exact Bool.false_ne_true hS.symm

/-- When `nextLabel` gives nothing, every exit of a block in `S` that names a block and does not
start at `d` is in `S`. -/
theorem nextLabel_none {d : Point} {S : List Label} (h : nextLabel bs d S = none) :
    ∀ b ∈ bs, b.label ∈ S → ∀ l ∈ exits d b, (∃ v ∈ bs, v.label = l) →
      (⟨l, 0⟩ : Point) ≠ d → l ∈ S := by
  intro b hb hbS l hl hv hd
  have := List.find?_eq_none.mp h l
    (List.mem_flatMap.mpr ⟨b, List.mem_filter.mpr ⟨hb, List.contains_iff_mem.mpr hbS⟩, hl⟩)
  refine Classical.byContradiction fun hS => this ?_
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq]
  exact ⟨⟨Bool.eq_false_iff.mpr fun h => hS (List.contains_iff_mem.mp h), hv⟩, hd⟩

/-- Adding the label `nextLabel` gives keeps `GrowInv`. -/
theorem GrowInv.next {d : Point} {S : List Label} {l : Label} (hI : GrowInv bs d S)
    (h : nextLabel bs d S = some l) : GrowInv bs d (l :: S) := by
  obtain ⟨hS, ⟨v, hv, hvl⟩, hd, b, hb, hbS, hl⟩ := nextLabel_some h
  refine ⟨fun l₁ hl₁ => ?_, List.nodup_cons.mpr ⟨hS, hI.2⟩⟩
  rcases List.mem_cons.mp hl₁ with rfl | hl₁
  · refine ⟨v, hv, hvl, ?_⟩
    obtain ⟨b₁, hb₁, hbl, hr⟩ := hI.1 _ hbS
    unfold exits at hl
    cases hm : lim d b with
    | none => simp only [hm, List.not_mem_nil] at hl
    | some m =>
      simp only [hm, List.mem_flatMap, List.mem_range] at hl
      obtain ⟨k, hk, ht⟩ := hl
      subst hvl
      have hr₁ : ReachAvoid bs d ⟨b.label, k⟩ :=
        reachAvoid_count hb (hbl ▸ hr) hm (Nat.le_of_lt_succ hk)
      exact .step hr₁ (.jump (jump_of_targets hb hv ht)) hd
  · exact hI.1 _ hl₁

/-- `grow` keeps `GrowInv` and the labels it starts with, and stops either with nothing left to add
or after adding `f` labels. -/
theorem grow_spec {d : Point} :
    ∀ (f : Nat) {S : List Label}, GrowInv bs d S →
      GrowInv bs d (grow bs d f S) ∧ (∀ l ∈ S, l ∈ grow bs d f S) ∧
        (nextLabel bs d (grow bs d f S) = none ∨ S.length + f ≤ (grow bs d f S).length)
  | 0, S, hI => ⟨hI, fun _ h => h, .inr (Nat.le_refl _)⟩
  | f + 1, S, hI => by
    cases h : nextLabel bs d S with
    | none =>
      have hg : grow bs d (f + 1) S = S := by rw [grow, h]
      rw [hg]
      exact ⟨hI, fun _ h => h, .inl h⟩
    | some l =>
      have hg : grow bs d (f + 1) S = grow bs d f (l :: S) := by rw [grow, h]
      rw [hg]
      obtain ⟨hI₁, hsub, hdone⟩ := grow_spec f (hI.next h)
      refine ⟨hI₁, fun l₁ hl₁ => hsub l₁ (List.mem_cons_of_mem _ hl₁), ?_⟩
      rcases hdone with hdone | hdone
      · exact .inl hdone
      · refine .inr ?_
        simp only [List.length_cons] at hdone
        omega

/-- The labels reached are closed under `nextLabel`, and satisfy `GrowInv`. -/
theorem reached_spec {d : Point} (hbs : bs ≠ []) (hne : root bs ≠ d) :
    GrowInv bs d (reached bs d) ∧ (root bs).label ∈ reached bs d ∧
      nextLabel bs d (reached bs d) = none := by
  cases bs with
  | nil => exact absurd rfl hbs
  | cons e rest =>
    have hI₀ : GrowInv (e :: rest) d [(root (e :: rest)).label] :=
      ⟨fun l hl => by
        rw [List.mem_singleton.mp hl]
        exact ⟨e, List.mem_cons_self, rfl, .root hne⟩,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩
    obtain ⟨hI, hsub, hdone⟩ := grow_spec (e :: rest).length hI₀
    have hr : reached (e :: rest) d =
        grow (e :: rest) d (e :: rest).length [(root (e :: rest)).label] :=
      ite_eq_right hne
    rw [hr]
    refine ⟨hI, hsub _ (List.mem_singleton_self _), hdone.resolve_right fun h => ?_⟩
    have hle := List.length_le_of_nodup_subset (m := (e :: rest).map (·.label)) hI.2 fun l hl =>
      let ⟨b, hb, hbl, _⟩ := hI.1 l hl
      hbl ▸ List.mem_map_of_mem hb
    simp only [List.length_map, List.length_cons] at hle h
    omega

/-- Every point a path reaches avoiding `d` is, by `lim`, in a block whose label is reached. -/
theorem reached_complete {d w : Point} (hbs : bs ≠ []) (hn : (bs.map (·.label)).Nodup)
    (h : ReachAvoid bs d w) :
    ∃ b ∈ bs, b.label = w.label ∧ w.label ∈ reached bs d ∧ ∃ m, lim d b = some m ∧ w.count ≤ m := by
  obtain ⟨hI, hroot, hdone⟩ := reached_spec hbs h.root_ne
  have somelim : ∀ b : Block env α, (⟨b.label, 0⟩ : Point) ≠ d → ∃ m, lim d b = some m :=
    fun b hb => Option.ne_none_iff_exists'.mp fun h => hb (lim_eq_none.mp h)
  induction h with
  | root hne =>
    cases bs with
    | nil => exact absurd rfl hbs
    | cons e rest =>
      obtain ⟨m, hm⟩ := somelim e hne
      exact ⟨e, List.mem_cons_self, rfl, hroot, m, hm, Nat.zero_le _⟩
  | step _ he hne ih =>
    obtain ⟨b, hb, hbl, hbS, m, hm, hk⟩ := ih
    cases he with
    | @fall b₁ k hb₁ hk₁ =>
      cases eq_of_label_eq hn hb hb₁ hbl
      refine ⟨b, hb, rfl, hbS, m, hm, ?_⟩
      have hlim := lim_spec hm
      dsimp only at hk ⊢
      unfold lim at hm
      by_cases hl : b.label = d.label
      · by_cases hc : d.count = 0
        · simp only [ite_eq_left hl, ite_eq_left hc, reduceCtorEq] at hm
        · simp only [ite_eq_left hl, ite_eq_right hc, Option.some.injEq] at hm
          have : k + 1 ≠ d.count := fun h => hne (by rw [hl, h])
          omega
      · simp only [ite_eq_right hl, Option.some.injEq] at hm
        omega
    | @jump _ v hj =>
      obtain ⟨b₁, hb₁, hbl₁, ht⟩ := targets_of_jump hj
      cases eq_of_label_eq hn hb hb₁ (hbl.trans hbl₁.symm)
      have hx : v.label ∈ exits d b := by
        unfold exits
        rw [hm]
        exact List.mem_flatMap.mpr ⟨_, List.mem_range.mpr (Nat.lt_succ_of_le hk), ht⟩
      have hv : v ∈ bs := by cases hj <;> assumption
      obtain ⟨m₁, hm₁⟩ := somelim v hne
      exact ⟨v, hv, rfl,
        nextLabel_none hdone b hb (by rw [hbl]; exact hbS) _ hx ⟨v, hv, rfl⟩ hne, m₁, hm₁,
        Nat.zero_le _⟩

/-- `reachAvoidB` decides `ReachAvoid`, for a body whose labels are distinct. -/
public theorem reachAvoidB_iff (hbs : bs ≠ []) (hn : (bs.map (·.label)).Nodup) {d y : Point} :
    reachAvoidB bs d y = true ↔ ReachAvoid bs d y := by
  unfold reachAvoidB
  constructor
  · intro h
    cases hf : bs.find? (·.label == y.label) with
    | none => simp only [hf, Option.any_none, Bool.false_eq_true] at h
    | some b =>
      simp only [hf, Option.any_some, Bool.and_eq_true, List.contains_iff_mem] at h
      obtain ⟨hS, hl⟩ := h
      have hb := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      have hbl : b.label = y.label := beq_iff_eq.mp hp
      by_cases hne : root bs = d
      · simp only [reached, ite_eq_left hne, List.not_mem_nil] at hS
      obtain ⟨hI, -, -⟩ := reached_spec hbs hne
      obtain ⟨b₁, hb₁, hbl₁, hr⟩ := hI.1 _ hS
      cases eq_of_label_eq hn hb hb₁ (hbl.trans hbl₁.symm)
      cases hm : lim d b with
      | none => simp only [hm, Option.any_none, Bool.false_eq_true] at hl
      | some m =>
        simp only [hm, Option.any_some, decide_eq_true_eq] at hl
        obtain ⟨l, k⟩ := y
        dsimp only at hbl hl
        subst hbl
        exact reachAvoid_count hb hr hm hl
  · intro h
    obtain ⟨b, hb, hbl, hS, m, hm, hk⟩ := reached_complete hbs hn h
    obtain ⟨b₁, hf⟩ := Option.isSome_iff_exists.mp
      ((List.find?_isSome (p := fun x : Block env α => x.label == y.label)).mpr
        ⟨b, hb, by simp only [hbl, beq_self_eq_true]⟩)
    have hp := List.find?_some hf
    cases eq_of_label_eq hn (List.mem_of_find?_eq_some hf) hb ((beq_iff_eq.mp hp).trans hbl.symm)
    simp only [hf, Option.any_some, Bool.and_eq_true, List.contains_iff_mem, hm,
      decide_eq_true_eq]
    exact ⟨hS, hk⟩

/-- `outside` is not a node. -/
theorem outside_not_node : ¬ Node bs (outside bs) := by
  rintro ⟨b, hb, -, hk⟩
  have hle : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a := fun l => by
    induction l with
    | nil => exact fun a => Nat.le_refl a
    | cons x l ih => exact fun a => Nat.le_trans (Nat.le_max_left a x) (ih _)
  have hmem : ∀ (l : List Nat) (a x : Nat), x ∈ l → x ≤ l.foldl max a := fun l => by
    induction l with
    | nil => exact fun _ _ h => absurd h List.not_mem_nil
    | cons y l ih =>
      intro a x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_trans (Nat.le_max_right a x) (hle l _)
      · exact ih _ x hx
  have := hmem _ 0 _ (List.mem_map_of_mem (f := fun b : Block env α => b.instrs.size) hb)
  simp only [outside] at hk
  omega

/-- `reachB` decides `Reach`, for a body whose labels are distinct. -/
public theorem reachB_iff (hbs : bs ≠ []) (hn : (bs.map (·.label)).Nodup) {y : Point} :
    reachB bs y = true ↔ Reach bs y := by
  rw [reachB, reachAvoidB_iff hbs hn]
  exact ⟨ReachAvoid.reach, fun h => h.reachAvoid_of_not_node hbs outside_not_node⟩

/-- `shapeB` decides `Shaped`'s two conditions on the body itself. -/
theorem shapeB_iff : shapeB bs = true ↔
    (bs.map (·.label)).Nodup ∧ ∀ b ∈ bs, Reach bs ⟨b.label, 0⟩ := by
  rw [shapeB, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨ht, hr⟩
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ht
    have hn := (tree?_eq_some ht).1
    exact ⟨hn, fun b hb => (reachB_iff (List.ne_nil_of_mem hb) hn).mp (hr b hb)⟩
  · rintro ⟨hn, hr⟩
    obtain ⟨t, ht⟩ := tree?_isSome hn
    exact ⟨by rw [ht]; rfl, fun b hb => (reachB_iff (List.ne_nil_of_mem hb) hn).mpr (hr b hb)⟩

/-- `availB` decides `Avail`, for a body whose labels are distinct. -/
theorem availB_iff (hbs : bs ≠ []) (hn : (bs.map (·.label)).Nodup) (Λ : ValId → Bool)
    (b : Block env α) (k : Nat) (x : ValId) :
    availB bs Λ b k x = true ↔ Avail bs (Λ · = true) x ⟨b.label, k⟩ := by
  rw [availB, Bool.or_eq_true, List.any_eq_true, Avail]
  simp only [mem_defs, Bool.not_eq_true', Dom]
  refine or_congr (exists_congr fun d => and_congr_right fun _ => ?_) Iff.rfl
  rw [← reachAvoidB_iff hbs hn, Bool.eq_false_iff]

/-- `availB` decides `Avail`, as an equation of predicates, for a body whose labels are distinct. -/
theorem availB_eq (hbs : bs ≠ []) (hn : (bs.map (·.label)).Nodup) (Λ : ValId → Bool)
    (b : Block env α) (k : Nat) :
    (fun x => availB bs Λ b k x = true) = (Avail bs (Λ · = true) · ⟨b.label, k⟩) :=
  funext fun x => propext (availB_iff hbs hn Λ b k x)

/-- A block outside a set of labels that holds the entry's and is closed under transfers is
unreachable, so the body is not shaped. -/
theorem not_shaped_of_unreachedB (h : unreachedB bs = true) : ¬ Shaped bs := by
  unfold unreachedB at h
  cases ht : tree? bs with
  | none => simp only [ht, Bool.false_eq_true] at h
  | some t =>
    obtain ⟨hn, htr⟩ := tree?_eq_some ht
    simp only [ht, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    generalize ((rpoLabels bs).foldl (fun m l => m.insert l ()) (∅ : LabelMap Unit)) = S at h
    obtain ⟨⟨hentry, hclosed⟩, b, hb, hbS⟩ := h
    -- Every reachable point is in a block whose label is in `S`.
    have key : ∀ y, Reach bs y → (S.find? y.label).isSome = true := by
      intro y hy
      induction hy with
      | root =>
        cases bs with
        | nil => exact absurd hb List.not_mem_nil
        | cons e rest => exact hentry
      | @step u₁ _ _ he ih =>
        cases he with
        | fall _ _ => exact ih
        | @jump _ v hj =>
          obtain ⟨c, hc, hcl, hvt⟩ := targets_of_jump hj
          have hk : u₁.count ≤ c.instrs.size := by
            obtain ⟨c₁, hc₁, hcl₁, hk⟩ := hj.node
            rwa [eq_of_label_eq hn hc₁ hc (hcl₁.trans hcl.symm)] at hk
          rcases hclosed c hc with hc₂ | hc₂
          · rw [hcl, ih] at hc₂
            cases hc₂
          · rcases hc₂ _ (List.mem_range.mpr (Nat.lt_succ_of_le hk)) _ hvt with h | h
            · exact h
            · have hv : v ∈ bs := by cases hj <;> assumption
              rw [(htr _ _).mpr ⟨hv, rfl⟩] at h
              cases h
    intro hs
    cases hs with
    | mk _ hr _ =>
      have := key _ (hr b hb)
      rw [this] at hbS
      cases hbS

end Body

open Body

variable {env : Env Unit} {α : Type}

/-- What the checker asks of an instruction, with `S` available. -/
def InstrDomOK (S : ValId → Prop) (i : Instruction env α) : Prop :=
  (∀ x, i.Uses x → S x) ∧ ∀ r ∈ i.regions, Shaped r.blocks.toList ∧ DomCorrect S r.blocks.toList

/-- What the checker asks of a terminator, with `S` available. -/
def TermDomOK (S : ValId → Prop) (t : Terminator env α) : Prop :=
  (∀ x, t.Uses x → S x) ∧ ∀ r ∈ t.regions, Shaped r.blocks.toList ∧ DomCorrect S r.blocks.toList

/-- What the checker asks of a block, with `σ b k` available at its count `k`. -/
def BlockDomOK (σ : Block env α → Nat → ValId → Bool) (b : Block env α) : Prop :=
  (∀ k i, b.instrs[k]? = some i → InstrDomOK (σ b k · = true) i) ∧
    TermDomOK (σ b b.instrs.size · = true) b.term

/-- `σ b k` is what is available at count `k` of each block `b` of the body. -/
def SigmaOK (bs : List (Block env α)) (Λ : ValId → Bool) (σ : Block env α → Nat → ValId → Bool) :
    Prop :=
  ∀ b ∈ bs, ∀ k ≤ b.instrs.size, ∀ x, σ b k x = true ↔ Avail bs (Λ · = true) x ⟨b.label, k⟩

/-- Under `SigmaOK`, `σ b k` is `Avail` at each count `k` of each block `b`, as an equation of
predicates. -/
theorem SigmaOK.eq {bs : List (Block env α)} {Λ : ValId → Bool}
    {σ : Block env α → Nat → ValId → Bool} (h : SigmaOK bs Λ σ) {b : Block env α} (hb : b ∈ bs)
    {k : Nat} (hk : k ≤ b.instrs.size) :
    (fun x => σ b k x = true) = (Avail bs (Λ · = true) · ⟨b.label, k⟩) :=
  funext fun x => propext (h b hb k hk x)

/-- The count of an instruction is a count of its block. -/
theorem lt_of_getElem? {b : Block env α} {k : Nat} {i : Instruction env α}
    (h : b.instrs[k]? = some i) : k ≤ b.instrs.size :=
  Nat.le_of_lt (Array.getElem?_eq_some_iff.mp h).1

/-- A body with distinct labels whose entry reaches every block, each of whose blocks the checker
accepts, is shaped and dominance-correct. -/
theorem shaped_domCorrect_of_blockOK {bs : List (Block env α)} {Λ : ValId → Bool}
    {σ : Block env α → Nat → ValId → Bool}
    (hn : (bs.map (·.label)).Nodup) (hr : ∀ b ∈ bs, Reach bs ⟨b.label, 0⟩) (hσ : SigmaOK bs Λ σ)
    (h : ∀ b ∈ bs, BlockDomOK σ b) :
    Shaped bs ∧ DomCorrect (Λ · = true) bs := by
  refine ⟨.mk hn hr fun y r hr₁ => ?_, .mk (fun x y hu => ?_) (fun y r hr₁ => ?_)⟩
  · cases hr₁ with
    | instr hb hk hr₁ => exact (((h _ hb).1 _ _ hk).2 r hr₁).1
    | term hb hr₁ => exact ((h _ hb).2.2 r hr₁).1
  · cases hu with
    | instr hb hk hu => exact (hσ _ hb _ (lt_of_getElem? hk) x).mp (((h _ hb).1 _ _ hk).1 x hu)
    | term hb hu => exact (hσ _ hb _ (Nat.le_refl _) x).mp ((h _ hb).2.1 x hu)
  · cases hr₁ with
    | instr hb hk hr₁ => exact hσ.eq hb (lt_of_getElem? hk) ▸ (((h _ hb).1 _ _ hk).2 r hr₁).2
    | term hb hr₁ => exact hσ.eq hb (Nat.le_refl _) ▸ ((h _ hb).2.2 r hr₁).2

/-- The checker accepts every block of a shaped, dominance-correct body. -/
theorem blockOK_of_shaped_domCorrect {bs : List (Block env α)} {Λ : ValId → Bool}
    {σ : Block env α → Nat → ValId → Bool} (hσ : SigmaOK bs Λ σ)
    (hs : Shaped bs) (hd : DomCorrect (Λ · = true) bs) :
    ∀ b ∈ bs, BlockDomOK σ b := by
  rcases hs with ⟨_, _, hsr⟩
  rcases hd with ⟨hu, hdr⟩
  intro b hb
  refine ⟨fun k i hk => ⟨fun x hx => ?_, fun r hr₁ => ⟨hsr _ r (.instr hb hk hr₁), ?_⟩⟩,
    fun x hx => ?_, fun r hr₁ => ⟨hsr _ r (.term hb hr₁), ?_⟩⟩
  · exact (hσ b hb k (lt_of_getElem? hk) x).mpr (hu x _ (.instr hb hk hx))
  · exact (hσ.eq hb (lt_of_getElem? hk)).symm ▸ hdr _ r (.instr hb hk hr₁)
  · exact (hσ b hb _ (Nat.le_refl _) x).mpr (hu x _ (.term hb hx))
  · exact (hσ.eq hb (Nat.le_refl _)).symm ▸ hdr _ r (.term hb hr₁)

/-- The slow check's availability is `Avail`. -/
theorem sigmaOK_availB {bs : List (Block env α)} (hn : (bs.map (·.label)).Nodup)
    (Λ : ValId → Bool) : SigmaOK bs Λ (availB bs Λ) :=
  fun b hb k _ x => availB_iff (List.ne_nil_of_mem hb) hn Λ b k x

/-- Under the fast tree, the fast check's availability is `Avail`. -/
theorem sigmaOK_fast {bs : List (Block env α)} {t : Tree} (h : domTree? bs = some t)
    {tm : LabelMap (Block env α)} (ht : tree? bs = some tm) (Λ : ValId → Bool) :
    SigmaOK bs Λ (fun b k x => scopeAt tm t bs.length (ancs tm t bs) (defs bs) b k x || Λ x) := by
  obtain ⟨hL, hx, hr⟩ := domTree?_spec h
  obtain ⟨hn, htr⟩ := tree?_eq_some ht
  intro b hb k hk x
  rw [scopeAt_iff hL htr (ancs_good hn htr) Λ hb k x]
  constructor
  · rintro (⟨d, hd, ha⟩ | hΛ)
    · exact .inl ⟨d, hd, ha.dom hL⟩
    · exact .inr hΛ
  · rintro (⟨d, hd, hdom⟩ | hΛ)
    · exact .inl ⟨d, hd, (hx d _ (reach_count hb (hr b hb) hk)).mpr hdom⟩
    · exact .inr hΛ

mutual

/-- `Instruction.domOK` decides `InstrDomOK`. -/
theorem Instruction.domOK_iff : ∀ (i : Instruction env α) (σ : ValId → Bool),
    i.domOK σ = true ↔ InstrDomOK (σ · = true) i
  | .const .., σ => by
    simp [Instruction.domOK, InstrDomOK, Instruction.Uses, Instruction.args, Instruction.succs,
      Instruction.regions]
  | .apply _ _ _ _ args succs ⟨regions⟩, σ => by
    rw [Instruction.domOK, Bool.and_eq_true, usesIn_iff, Region.domOKList_iff regions σ]
    simp only [InstrDomOK, Instruction.Uses, Instruction.args, Instruction.succs,
      Instruction.regions, Array.mem_def]

/-- `Instruction.domOKList` decides `InstrDomOK` of each instruction, at its count. -/
theorem Instruction.domOKList_iff : ∀ (is : List (Instruction env α)) (σ : Nat → ValId → Bool)
    (k : Nat), Instruction.domOKList σ k is = true ↔
      ∀ j i, is[j]? = some i → InstrDomOK (σ (k + j) · = true) i
  | [], _, _ => by simp [Instruction.domOKList]
  | i :: is, σ, k => by
    rw [Instruction.domOKList, Bool.and_eq_true, Instruction.domOK_iff i (σ k),
      Instruction.domOKList_iff is σ (k + 1)]
    constructor
    · rintro ⟨h₀, h⟩ (_ | j) i₁ hj
      · cases hj
        exact h₀
      · have := h j i₁ hj
        rwa [Nat.add_right_comm, Nat.add_assoc] at this
    · intro h
      refine ⟨h 0 i rfl, fun j i₁ hj => ?_⟩
      have := h (j + 1) i₁ hj
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this

/-- `Terminator.domOK` decides `TermDomOK`. -/
theorem Terminator.domOK_iff : ∀ (t : Terminator env α) (σ : ValId → Bool),
    t.domOK σ = true ↔ TermDomOK (σ · = true) t
  | .apply _ _ _ args succs ⟨regions⟩, σ => by
    rw [Terminator.domOK, Bool.and_eq_true, usesIn_iff, Region.domOKList_iff regions]
    simp only [TermDomOK, Terminator.Uses, Terminator.args, Terminator.succs, Terminator.regions,
      Array.mem_def]

/-- `Block.domOKList` decides `BlockDomOK` of each block. -/
theorem Block.domOKList_iff : ∀ (bs : List (Block env α))
    (σ : Block env α → Nat → ValId → Bool),
    Block.domOKList σ bs = true ↔ ∀ b ∈ bs, BlockDomOK σ b
  | [], _ => by simp [Block.domOKList]
  | ⟨l, ps, ⟨instrs⟩, term, info⟩ :: bs, σ => by
    rw [Block.domOKList, Bool.and_eq_true, Bool.and_eq_true, Instruction.domOKList_iff instrs,
      Terminator.domOK_iff term, Block.domOKList_iff bs σ, List.forall_mem_cons]
    simp only [BlockDomOK, List.getElem?_toArray, List.size_toArray, Nat.zero_add, and_assoc]

/-- `Region.domOK` decides whether the region is shaped and dominance-correct. -/
theorem Region.domOK_iff : ∀ (r : Region env α) (Λ : ValId → Bool),
    r.domOK Λ = true ↔ Shaped r.blocks.toList ∧ DomCorrect (Λ · = true) r.blocks.toList
  | ⟨⟨bs⟩⟩, Λ => by
    rw [Region.domOK]
    cases hf : domTree? bs with
    | some t =>
      obtain ⟨hL, -, hr⟩ := domTree?_spec hf
      obtain ⟨tm, ht⟩ := tree?_isSome hL.distinct
      simp only [ht]
      have hσ := sigmaOK_fast hf ht Λ
      rw [Block.domOKList_iff]
      exact ⟨shaped_domCorrect_of_blockOK hL.distinct hr hσ,
        fun ⟨hs, hd⟩ => blockOK_of_shaped_domCorrect hσ hs hd⟩
    | none =>
      simp only
      by_cases hu : unreachedB bs = true
      · rw [hu]
        exact ⟨nofun, fun ⟨hs, _⟩ => (not_shaped_of_unreachedB hu hs).elim⟩
      rw [Bool.eq_false_iff.mpr hu, Bool.not_false, Bool.true_and, Bool.and_eq_true, shapeB_iff,
        Block.domOKList_iff]
      constructor
      · rintro ⟨⟨hn, hr⟩, h⟩
        exact shaped_domCorrect_of_blockOK hn hr (sigmaOK_availB hn Λ) h
      · rintro ⟨hs, hd⟩
        have ⟨hn, hr, _⟩ := hs
        exact ⟨⟨hn, hr⟩, blockOK_of_shaped_domCorrect (sigmaOK_availB hn Λ) hs hd⟩

/-- `Region.domOKList` decides whether each region is shaped and dominance-correct. -/
theorem Region.domOKList_iff : ∀ (rs : List (Region env α)) (Λ : ValId → Bool),
    Region.domOKList Λ rs = true ↔
      ∀ r ∈ rs, Shaped r.blocks.toList ∧ DomCorrect (Λ · = true) r.blocks.toList
  | [], _ => by simp [Region.domOKList]
  | r :: rs, Λ => by
    rw [Region.domOKList, Bool.and_eq_true, Region.domOK_iff r Λ, Region.domOKList_iff rs Λ,
      List.forall_mem_cons]

end

/-- `Func.checkDom` decides whether the function is shaped and dominance-correct. -/
public theorem Func.checkDom_iff (fn : Func env α) :
    fn.checkDom = true ↔ fn.Shaped ∧ fn.DomCorrect := by
  have hΛ : (fun x : ValId => (fun _ => false) x = true) = fun _ => False := by
    funext x
    simp
  rw [Func.checkDom, Region.domOK_iff, hΛ]
  rfl

/-- `Func.checkDom` decides whether a function is reachable and scopable. -/
public instance (fn : Func env α) : Decidable (fn.Reachable ∧ fn.Scopable) :=
  decidable_of_iff _ ((Func.checkDom_iff fn).trans Func.reachable_scopable_iff.symm)

end Strata.Mantle
