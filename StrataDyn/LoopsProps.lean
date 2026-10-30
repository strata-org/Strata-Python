/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Loops
import all StrataDyn.Loops
import all StrataDyn.Dom
import all StrataDyn.DomComplete
import all StrataDyn.DomComputeProps
import all StrataDyn.DomDecide
import all StrataDyn.DomProps

set_option autoImplicit false

/-!
# Loops, proved

`StrataDyn/Loops.lean` computes a body's back edges and natural loops.  This module proves
that the computations give what the statements say, for a body whose labels are distinct, as
`Func.WF` asks.

## Main theorems

* `Body.mem_backEdges_iff`: `Body.backEdges` lists exactly the back edges;
* `Body.mem_loopBlocks_iff`: `Body.loopBlocks` lists exactly the labels of a natural loop.
-/

namespace Strata.Dyn

namespace Body

variable {env : Env Unit} {α : Type} {bs bs₁ : List (Block env α)}

/-- An edge of a body is an edge of any body that has all its blocks. -/
theorem Edge.mono (h : ∀ b, b ∈ bs → b ∈ bs₁) {u w : Point} (he : Edge bs u w) :
    Edge bs₁ u w := by
  cases he with
  | fall hb hk => exact .fall (h _ hb) hk
  | jump hj => exact .jump (hj.mono h)

/-- A path of a body that avoids `d` is one of any body that has all its blocks. -/
theorem PathAvoid.mono (h : ∀ b, b ∈ bs → b ∈ bs₁) {d x y : Point}
    (hp : PathAvoid bs d x y) : PathAvoid bs₁ d x y := by
  induction hp with
  | refl hx => exact .refl hx
  | step _ he hw ih => exact .step ih (Edge.mono h he) hw

/-- A path from the root that avoids `d` is a path that starts at the root and avoids `d`. -/
theorem reachAvoid_iff_pathAvoid {d y : Point} :
    ReachAvoid bs d y ↔ PathAvoid bs d (root bs) y := by
  constructor
  · intro h
    induction h with
    | root hne => exact .refl hne
    | step _ he hw ih => exact .step ih he hw
  · intro h
    suffices ∀ {x y : Point}, PathAvoid bs d x y → x = root bs → ReachAvoid bs d y from this h rfl
    intro x y hp
    induction hp with
    | refl hx =>
      intro hxr
      subst hxr
      exact .root hx
    | step _ he hw ih => exact fun hxr => .step (ih hxr) he hw

/-- The body entered at one of its blocks has the same blocks, if its labels are distinct. -/
theorem mem_enteredAt (hn : (bs.map (·.label)).Nodup) {b c : Block env α} (hb : b ∈ bs) :
    c ∈ enteredAt bs b ↔ c ∈ bs := by
  simp only [enteredAt, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq]
  constructor
  · rintro (rfl | ⟨hc, -⟩) <;> assumption
  · intro hc
    by_cases hl : c.label = b.label
    · exact .inl (eq_of_label_eq hn hc hb hl)
    · exact .inr ⟨hc, hl⟩

/-- The body entered at a block has distinct labels if the body has. -/
theorem nodup_enteredAt (hn : (bs.map (·.label)).Nodup) (b : Block env α) :
    ((enteredAt bs b).map (·.label)).Nodup := by
  simp only [enteredAt, List.map_cons, List.nodup_cons]
  refine ⟨?_, List.Nodup.sublist (List.filter_sublist.map _) hn⟩
  simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq, not_exists, not_and]
  exact fun c hc heq => hc.2 heq

/-- Within a body with distinct labels, the search from the start of `b` decides whether a path
from there reaches `y` avoiding `d`. -/
theorem reachAvoidB_enteredAt_iff (hn : (bs.map (·.label)).Nodup) {b : Block env α}
    (hb : b ∈ bs) {d y : Point} :
    reachAvoidB (enteredAt bs b) d y = true ↔ PathAvoid bs d ⟨b.label, 0⟩ y := by
  rw [reachAvoidB_iff (bs := enteredAt bs b) (List.cons_ne_nil _ _) (nodup_enteredAt hn b),
    reachAvoid_iff_pathAvoid]
  exact ⟨PathAvoid.mono fun c hc => (mem_enteredAt hn hb).mp hc,
    PathAvoid.mono fun c hc => (mem_enteredAt hn hb).mpr hc⟩

/-- A block transfers only from a count no greater than its instruction count. -/
theorem le_of_mem_targets {b : Block env α} {k : Nat} {l : Label} (h : l ∈ targets b k) :
    k ≤ b.instrs.size := by
  unfold targets at h
  rcases List.mem_append.mp h with h | h
  · cases hi : b.instrs[k]? with
    | none => simp only [hi, Option.map_none, Option.getD_none, List.not_mem_nil] at h
    | some i =>
      obtain ⟨hk, -⟩ := Array.getElem?_eq_some_iff.mp hi
      exact Nat.le_of_lt hk
  · by_cases hk : k = b.instrs.size
    · exact Nat.le_of_eq hk
    · simp only [ite_eq_right hk, List.not_mem_nil] at h

/-- The target of a transfer is a block of the body. -/
theorem Jump.mem {u : Point} {v : Block env α} (h : Jump bs u v) : v ∈ bs := by
  cases h <;> assumption

/-- A path that avoids `d` extends by one that starts where it ends. -/
theorem PathAvoid.trans {d x y z : Point} (h₁ : PathAvoid bs d x y) (h₂ : PathAvoid bs d y z) :
    PathAvoid bs d x z := by
  induction h₂ with
  | refl => exact h₁
  | step _ he hw ih => exact .step ih he hw

/-- Within a block other than `d`'s, a path falls from the start to any count. -/
theorem PathAvoid.fall {d : Point} {b : Block env α} (hb : b ∈ bs) (hd : b.label ≠ d.label) :
    ∀ {k : Nat}, k ≤ b.instrs.size → PathAvoid bs d ⟨b.label, 0⟩ ⟨b.label, k⟩
  | 0, _ => .refl fun he => hd (congrArg Point.label he)
  | _ + 1, hk => .step (PathAvoid.fall hb hd (Nat.le_of_succ_le hk)) (.fall hb hk)
      fun he => hd (congrArg Point.label he)

/-- A path that starts outside the block `h` and avoids its start never enters it. -/
theorem PathAvoid.label_ne {h : Label} {x y : Point} (hp : PathAvoid bs ⟨h, 0⟩ x y)
    (hx : x.label ≠ h) : y.label ≠ h := by
  induction hp with
  | refl => exact hx
  | step _ he hw ih =>
    cases he with
    | fall => exact ih
    | @jump _ v _ => exact fun hv => hw (by simp only [← hv])

/-- A path ends at a point of the body: a block of it, at a count no greater than its
instruction count. -/
theorem PathAvoid.node {d x y : Point} (hp : PathAvoid bs d x y) (hx : Node bs x) :
    Node bs y := by
  induction hp with
  | refl => exact hx
  | step _ he _ _ =>
    cases he with
    | fall hb hk => exact ⟨_, hb, rfl, hk⟩
    | jump hj => exact ⟨_, hj.mem, rfl, Nat.zero_le _⟩

/-- The transfers are the transfers to blocks of the body, from counts no greater than the
source block's instruction count. -/
theorem mem_transfers {u : Point} {l : Label} :
    (u, l) ∈ transfers bs ↔ ∃ b ∈ bs, b.label = u.label ∧ u.count ≤ b.instrs.size ∧
      l ∈ targets b u.count ∧ ∃ v ∈ bs, v.label = l := by
  simp only [transfers, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, k, hk, l₁, hl, he⟩
    by_cases hc : bs.any (·.label == l₁) = true
    · rw [ite_eq_left hc, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [List.any_eq_true, beq_iff_eq] at hc
      exact ⟨b, hb, rfl, Nat.le_of_lt_succ hk, hl, hc⟩
    · rw [ite_eq_right hc] at he
      exact absurd he (by simp)
  · rintro ⟨b, hb, hbl, hk, hl, v, hv, hvl⟩
    refine ⟨b, hb, u.count, Nat.lt_succ_of_le hk, l, hl, ?_⟩
    have hc : bs.any (·.label == l) = true := by
      simp only [List.any_eq_true, beq_iff_eq]
      exact ⟨v, hv, hvl⟩
    rw [ite_eq_left hc, hbl]

/-- In a body with distinct labels, `backEdges` lists exactly the back edges. -/
public theorem mem_backEdges_iff (hn : (bs.map (·.label)).Nodup) {u : Point} {h : Label} :
    (u, h) ∈ backEdges bs ↔ IsBackEdge bs u h := by
  simp only [backEdges, List.mem_eraseDups, List.mem_filter, mem_transfers, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨b, hb, hbl, -, hl, v, hv, hvl⟩, hra⟩
    have hne : bs ≠ [] := List.ne_nil_of_mem hb
    refine ⟨v, ?_, hvl, fun hr => ?_⟩
    · have hj := jump_of_targets hb hv (k := u.count) (hvl ▸ hl)
      rwa [hbl] at hj
    · have hrt := (reachAvoidB_iff hne hn).mpr hr
      rw [hra] at hrt
      exact Bool.false_ne_true hrt
  · rintro ⟨v, hj, rfl, hd⟩
    obtain ⟨b, hb, hbl, ht⟩ := targets_of_jump hj
    have hne : bs ≠ [] := List.ne_nil_of_mem hb
    refine ⟨⟨b, hb, hbl, le_of_mem_targets ht, ht, v, hj.mem, rfl⟩, ?_⟩
    cases hr : reachAvoidB bs ⟨v.label, 0⟩ u with
    | false => rfl
    | true => exact absurd ((reachAvoidB_iff hne hn).mp hr) hd

/-- In a body with distinct labels, `loopBlocks` lists exactly the labels of the natural loop
of the back edge from `u` to `h`. -/
public theorem mem_loopBlocks_iff (hn : (bs.map (·.label)).Nodup) {u : Point} {h l : Label} :
    l ∈ loopBlocks bs u h ↔ ∃ b, b.label = l ∧ InLoop bs u h b := by
  simp only [loopBlocks, List.mem_map, List.mem_filter, Bool.or_eq_true, beq_iff_eq, InLoop]
  constructor
  · rintro ⟨b, ⟨hb, hc⟩, rfl⟩
    exact ⟨b, rfl, hb, hc.imp_right (reachAvoidB_enteredAt_iff hn hb).mp⟩
  · rintro ⟨b, rfl, hb, hc⟩
    exact ⟨b, ⟨hb, hc.imp_right (reachAvoidB_enteredAt_iff hn hb).mpr⟩, rfl⟩

end Body

end Strata.Dyn
