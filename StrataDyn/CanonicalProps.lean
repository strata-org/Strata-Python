/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Canonical
public import StrataDyn.EveryBodyProps
public import StrataDyn.WF
import all StrataDyn.Canonical
import all StrataDyn.Loops
import all StrataDyn.LoopsProps
import all StrataDyn.DomComplete
import all StrataDyn.DomDecide
import all StrataDyn.DomProps

set_option autoImplicit false

/-!
# The canonical form, decided

`StrataDyn/Canonical.lean` states the canonical form and computes its check.  This module
proves that the check decides the form, for a function whose bodies have distinct labels, which
every well-formed function's do.

## Main theorems

* `Func.checkCanonicalCFG_iff`: `Func.checkCanonicalCFG` decides `Func.CanonicalCFG`.

## Main definitions

* `Func.decCanonicalCFG`: the decision of `Func.CanonicalCFG` for a well-formed function.
-/

namespace Strata.Dyn

namespace Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)}

/-! ## Transfers, heads and loops -/

/-- A transfer to a block is one that `transfers` lists. -/
theorem transfer_iff {u : Point} {l : Label} : Transfer bs u l ↔ (u, l) ∈ transfers bs := by
  rw [mem_transfers]
  constructor
  · rintro ⟨v, hj, rfl⟩
    obtain ⟨b, hb, hbl, ht⟩ := targets_of_jump hj
    exact ⟨b, hb, hbl, le_of_mem_targets ht, ht, v, hj.mem, rfl⟩
  · rintro ⟨b, hb, hbl, -, hl, v, hv, rfl⟩
    refine ⟨v, ?_, rfl⟩
    have hj := jump_of_targets hb hv (k := u.count) hl
    rwa [hbl] at hj

/-- In a body with distinct labels, `heads` lists exactly the heads of loops. -/
theorem mem_heads_iff (hn : (bs.map (·.label)).Nodup) {h : Label} :
    h ∈ heads bs ↔ IsHead bs h := by
  simp only [heads, List.mem_eraseDups, List.mem_map, IsHead]
  constructor
  · rintro ⟨⟨u, h'⟩, he, rfl⟩
    exact ⟨u, (mem_backEdges_iff hn).mp he⟩
  · rintro ⟨u, hu⟩
    exact ⟨(u, h), (mem_backEdges_iff hn).mpr hu, rfl⟩

/-- In a body with distinct labels, `loopOf bs h` lists exactly the labels of the loop of `h`. -/
theorem mem_loopOf_iff (hn : (bs.map (·.label)).Nodup) {h l : Label} :
    l ∈ loopOf bs h ↔ ∃ b, b.label = l ∧ InLoopOf bs h b := by
  simp only [loopOf, List.mem_flatMap, List.mem_filter, beq_iff_eq, InLoopOf]
  constructor
  · rintro ⟨⟨u, h'⟩, ⟨he, rfl⟩, hl⟩
    obtain ⟨b, hbl, hin⟩ := (mem_loopBlocks_iff hn).mp hl
    exact ⟨b, hbl, u, (mem_backEdges_iff hn).mp he, hin⟩
  · rintro ⟨b, hbl, u, hbe, hin⟩
    exact ⟨(u, h), ⟨(mem_backEdges_iff hn).mpr hbe, rfl⟩,
      (mem_loopBlocks_iff hn).mpr ⟨b, hbl, hin⟩⟩

/-- In a body with distinct labels, a point is in the loop of `h` exactly when its label is in
`loopOf bs h`. -/
theorem atLoop_iff (hn : (bs.map (·.label)).Nodup) {h : Label} {u : Point} :
    AtLoop bs h u ↔ u.label ∈ loopOf bs h :=
  (mem_loopOf_iff hn).symm

/-- A block of the loop of `h` is a block of the body. -/
theorem InLoopOf.mem {h : Label} {b : Block env α} (hb : InLoopOf bs h b) : b ∈ bs := by
  obtain ⟨_, _, hin, _⟩ := hb
  exact hin

/-- In a body with distinct labels, the end of a block is in the loop of `h` exactly when the
block is. -/
theorem atLoop_endOf_iff (hn : (bs.map (·.label)).Nodup) {h : Label} {b : Block env α}
    (hb : b ∈ bs) : AtLoop bs h (endOf b) ↔ InLoopOf bs h b := by
  constructor
  · rintro ⟨c, hcl, hc⟩
    rwa [eq_of_label_eq hn hc.mem hb hcl] at hc
  · exact fun hc => ⟨b, rfl, hc⟩

/-! ## Blocks by label -/

/-- In a body with distinct labels, `blockAt?` finds the block with a label, if there is one. -/
theorem blockAt?_eq_some (hn : (bs.map (·.label)).Nodup) {l : Label} {b : Block env α} :
    blockAt? bs l = some b ↔ b ∈ bs ∧ b.label = l := by
  unfold blockAt?
  constructor
  · intro h
    exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
  · rintro ⟨hb, rfl⟩
    cases hf : bs.find? (·.label == b.label) with
    | none => exact absurd (List.find?_eq_none.mp hf b hb) (by simp)
    | some c =>
      have hcl : c.label = b.label := by simpa using List.find?_some hf
      rw [eq_of_label_eq hn (List.mem_of_find?_eq_some hf) hb hcl]

/-- In a body with distinct labels, `endsAtB u l` holds exactly when `u` is the end of a block
that ends in a plain jump to `l`. -/
theorem endsAtB_iff (hn : (bs.map (·.label)).Nodup) {u : Point} {l : Label} :
    endsAtB bs u l = true ↔ ∃ b ∈ bs, u = endOf b ∧ EndsIn b l := by
  unfold endsAtB
  cases hf : blockAt? bs u.label with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro b hb hu _
    have hsome := (blockAt?_eq_some hn (l := u.label)).mpr ⟨hb, by subst hu; rfl⟩
    rw [hf] at hsome
    exact absurd hsome (by simp)
  | some b =>
    obtain ⟨hb, hbl⟩ := (blockAt?_eq_some hn).mp hf
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem,
      Array.isEmpty_iff, EndsIn]
    constructor
    · rintro ⟨⟨⟨hk, hname⟩, hreg⟩, hs⟩
      refine ⟨b, hb, ?_, hname, hreg, fun s hs' => by simpa using hs s hs'⟩
      obtain ⟨ul, uk⟩ := u
      simp only [endOf] at hbl hk ⊢
      rw [hbl, hk]
    · rintro ⟨c, hc, rfl, hname, hreg, hend⟩
      have hcb : c = b := eq_of_label_eq hn hc hb hbl.symm
      subst hcb
      exact ⟨⟨⟨rfl, hname⟩, hreg⟩, fun s hs' => by simpa using hend s hs'⟩

/-- `theOneB E p` holds exactly when some point of `E` is the only one, and `p` holds of it. -/
theorem theOneB_iff {E : List Point} {p : Point → Bool} :
    theOneB E p = true ↔ ∃ u ∈ E, (∀ w ∈ E, w = u) ∧ p u = true := by
  unfold theOneB
  cases E with
  | nil => simp
  | cons u us =>
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨hall, hp⟩
      exact ⟨u, .inl rfl, ⟨rfl, hall⟩, hp⟩
    · rintro ⟨v, -, ⟨huv, hall⟩, hp⟩
      subst huv
      exact ⟨hall, hp⟩

/-! ## The loop properties -/

/-- In a body with distinct labels, `entriesFrom` lists the points outside the loop of `h` that
transfer to `h`. -/
theorem mem_entriesFrom (hn : (bs.map (·.label)).Nodup) {h : Label} {w : Point} :
    w ∈ entriesFrom bs (loopOf bs h) h ↔ Transfer bs w h ∧ ¬ AtLoop bs h w := by
  simp only [entriesFrom, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem, transfer_iff,
    atLoop_iff hn]
  constructor
  · rintro ⟨⟨w', l⟩, ⟨hw, rfl, hL⟩, rfl⟩
    exact ⟨hw, hL⟩
  · rintro ⟨hw, hL⟩
    exact ⟨(w, h), ⟨hw, rfl, hL⟩, rfl⟩

/-- In a body with distinct labels, `preheaderB` decides whether the loop of `h` has a
preheader. -/
theorem preheaderB_iff (hn : (bs.map (·.label)).Nodup) {h : Label} :
    preheaderB bs (loopOf bs h) h = true ↔ ∃ pre, Preheader bs h pre := by
  rw [preheaderB, theOneB_iff]
  constructor
  · rintro ⟨u, hu, hall, hend⟩
    obtain ⟨b, hb, rfl, hends⟩ := (endsAtB_iff hn).mp hend
    obtain ⟨htr, hout⟩ := (mem_entriesFrom hn).mp hu
    refine ⟨b, ⟨hb, fun hin => hout ((atLoop_endOf_iff hn hb).mpr hin), hends, htr,
      fun w hw hwo => hall w ((mem_entriesFrom hn).mpr ⟨hw, hwo⟩)⟩⟩
  · rintro ⟨pre, hpre⟩
    have hin : endOf pre ∈ entriesFrom bs (loopOf bs h) h :=
      (mem_entriesFrom hn).mpr ⟨hpre.enters, fun hat =>
        hpre.outside ((atLoop_endOf_iff hn hpre.mem).mp hat)⟩
    refine ⟨endOf pre, hin, fun w hw => ?_, (endsAtB_iff hn).mpr ⟨pre, hpre.mem, rfl, hpre.endsIn⟩⟩
    obtain ⟨htr, hout⟩ := (mem_entriesFrom hn).mp hw
    exact hpre.entries w htr hout

/-- In a body with distinct labels, `backFrom` lists the points that back edges to `h` leave
from. -/
theorem mem_backFrom (hn : (bs.map (·.label)).Nodup) {h : Label} {w : Point} :
    w ∈ backFrom bs h ↔ IsBackEdge bs w h := by
  simp only [backFrom, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨w', h'⟩, ⟨he, rfl⟩, rfl⟩
    exact (mem_backEdges_iff hn).mp he
  · intro hw
    exact ⟨(w, h), ⟨(mem_backEdges_iff hn).mpr hw, rfl⟩, rfl⟩

/-- In a body with distinct labels, `latchB` decides whether the loop of the head `h` has a
latch. -/
theorem latchB_iff (hn : (bs.map (·.label)).Nodup) {h : Label} (hh : IsHead bs h) :
    latchB bs h = true ↔ ∃ latch, Latch bs h latch := by
  rw [latchB, theOneB_iff]
  constructor
  · rintro ⟨u, -, hall, hend⟩
    obtain ⟨b, hb, rfl, hends⟩ := (endsAtB_iff hn).mp hend
    exact ⟨b, hb, hends, fun w hw => hall w ((mem_backFrom hn).mpr hw)⟩
  · rintro ⟨latch, hl⟩
    obtain ⟨u, hu⟩ := hh
    have hin : endOf latch ∈ backFrom bs h := hl.back u hu ▸ (mem_backFrom hn).mpr hu
    exact ⟨endOf latch, hin, fun w hw => hl.back w ((mem_backFrom hn).mp hw),
      (endsAtB_iff hn).mpr ⟨latch, hl.mem, rfl, hl.endsIn⟩⟩

/-- In a body with distinct labels, `exitTargets` lists the labels of the blocks that a transfer
leaves the loop of `h` for. -/
theorem mem_exitTargets (hn : (bs.map (·.label)).Nodup) {h l : Label} :
    l ∈ exitTargets bs (loopOf bs h) ↔
      ∃ u, Transfer bs u l ∧ AtLoop bs h u ∧ ¬ AtLoop bs h ⟨l, 0⟩ := by
  simp only [exitTargets, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, List.contains_iff_mem, transfer_iff, atLoop_iff hn]
  constructor
  · rintro ⟨⟨u, l'⟩, ⟨hu, hL, hl⟩, rfl⟩
    exact ⟨u, hu, hL, hl⟩
  · rintro ⟨u, hu, hL, hl⟩
    exact ⟨(u, l), ⟨hu, hL, hl⟩, rfl⟩

/-- `exitPoints` lists the points that transfer to the body's exit. -/
theorem mem_exitPoints {u : Point} : u ∈ exitPoints bs ↔ Leaves bs u := by
  unfold Leaves
  simp only [exitPoints, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, k, -, he⟩
    by_cases hc : (targets b k).contains Label.exit = true
    · rw [ite_eq_left hc, Option.some.injEq] at he
      subst he
      exact ⟨b, hb, rfl, List.contains_iff_mem.mp hc⟩
    · rw [ite_eq_right hc] at he
      exact absurd he (by simp)
  · rintro ⟨b, hb, hbl, ht⟩
    refine ⟨b, hb, u.count, Nat.lt_succ_of_le (le_of_mem_targets ht), ?_⟩
    rw [ite_eq_left (List.contains_iff_mem.mpr ht), hbl]

/-- In a body with distinct labels, `exitsB` decides whether the loop of `h` has dedicated
exits. -/
theorem exitsB_iff (hn : (bs.map (·.label)).Nodup) {h : Label} :
    exitsB bs (loopOf bs h) = true ↔ DedicatedExits bs h := by
  simp only [exitsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, List.contains_iff_mem, DedicatedExits]
  refine and_congr ⟨fun hall u l hu hat hl w hw => ?_, fun hded p hp => ?_⟩
    ⟨fun hall u hat hl => hall u (mem_exitPoints.mpr hl) ((atLoop_iff hn).mp hat),
      fun hall u hu hL => hall u ((atLoop_iff hn).mpr hL) (mem_exitPoints.mp hu)⟩
  · rcases hall (w, l) (transfer_iff.mp hw) with hne | hwL
    · exact absurd ((mem_exitTargets hn).mpr ⟨u, hu, hat, hl⟩) hne
    · exact (atLoop_iff hn).mpr hwL
  · obtain ⟨w, l⟩ := p
    by_cases hx : l ∈ exitTargets bs (loopOf bs h)
    · obtain ⟨u, hu, hat, hl⟩ := (mem_exitTargets hn).mp hx
      exact .inr ((atLoop_iff hn).mp (hded u l hu hat hl w (transfer_iff.mpr hp)))
    · exact .inl hx

/-- In a body with distinct labels, `loopsSimplifiedB` decides whether every loop has a
preheader, a latch and dedicated exits. -/
theorem loopsSimplifiedB_iff (hn : (bs.map (·.label)).Nodup) :
    loopsSimplifiedB bs = true ↔ LoopsSimplified bs := by
  simp only [loopsSimplifiedB, List.all_eq_true, Bool.and_eq_true, LoopsSimplified,
    LoopSimplified]
  constructor
  · intro hall h hh
    obtain ⟨⟨hp, hl⟩, he⟩ := hall h ((mem_heads_iff hn).mpr hh)
    exact ⟨(preheaderB_iff hn).mp hp, (latchB_iff hn hh).mp hl, (exitsB_iff hn).mp he⟩
  · intro hall h hh
    have hh' := (mem_heads_iff hn).mp hh
    obtain ⟨hp, hl, he⟩ := hall h hh'
    exact ⟨⟨(preheaderB_iff hn).mpr hp, (latchB_iff hn hh').mpr hl⟩, (exitsB_iff hn).mpr he⟩

/-- In a body with distinct labels, `oneExitB` decides `OneExit`. -/
theorem oneExitB_iff (hn : (bs.map (·.label)).Nodup) : oneExitB bs = true ↔ OneExit bs := by
  rw [oneExitB, Bool.or_eq_true, theOneB_iff, List.isEmpty_iff, OneExit]
  constructor
  · rintro (hE | ⟨u, -, hall, hend⟩)
    · refine .inl fun u hu => ?_
      have hmem := mem_exitPoints.mpr hu
      rw [hE] at hmem
      exact List.not_mem_nil hmem
    · obtain ⟨b, hb, rfl, hends⟩ := (endsAtB_iff hn).mp hend
      exact .inr ⟨b, hb, hends, fun w hw => hall w (mem_exitPoints.mpr hw)⟩
  · rintro (hno | ⟨post, hpost⟩)
    · refine .inl (List.eq_nil_iff_forall_not_mem.mpr fun u hu => hno u (mem_exitPoints.mp hu))
    · cases hE : exitPoints bs with
      | nil => exact .inl rfl
      | cons u us =>
        refine .inr ?_
        rw [← hE]
        have hu : u ∈ exitPoints bs := hE ▸ List.mem_cons_self
        have hend : endOf post ∈ exitPoints bs := hpost.exits u (mem_exitPoints.mp hu) ▸ hu
        exact ⟨endOf post, hend, fun w hw => hpost.exits w (mem_exitPoints.mp hw),
          (endsAtB_iff hn).mpr ⟨post, hpost.mem, rfl, hpost.endsIn⟩⟩

end Body

/-! ## The function -/

variable {env : Env Unit} {α : Type}

/-- For a function whose bodies have distinct labels, `checkCanonicalCFG` holds exactly when the
function is canonical: every loop of every body has a preheader, a latch and dedicated exits,
and its own body leaves through its exit from at most one block. -/
public theorem Func.checkCanonicalCFG_iff (fn : Func env α)
    (hd : Body.Distinct fn.blocks.toList) :
    fn.checkCanonicalCFG = true ↔ fn.CanonicalCFG := by
  have hn : (fn.blocks.toList.map (·.label)).Nodup := by
    cases hd with
    | mk hn _ => exact hn
  rw [Func.checkCanonicalCFG, Bool.and_eq_true,
    Body.everyB_iff_of (Q := fun bs => (bs.map (·.label)).Nodup)
      (fun _ hn => Body.loopsSimplifiedB_iff hn) ((Body.distinct_iff_every _).mp hd),
    Body.oneExitB_iff hn]
  rfl

/-- Whether a well-formed function is canonical is decided, by `Func.checkCanonicalCFG`. -/
public def Func.decCanonicalCFG [base ≼ env] (fn : Func env α) (h : fn.WF) :
    Decidable fn.CanonicalCFG :=
  decidable_of_iff _ (fn.checkCanonicalCFG_iff h.distinct)

end Strata.Dyn
