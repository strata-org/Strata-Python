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

* `Func.checkCanonicalCFG_iff`: `Func.checkCanonicalCFG` decides `Func.CanonicalCFG`;
* `Body.reducible_of_reducibleB`, `Func.reducible_of_everyB`: the check of one entry per loop,
  against a depth-first order, establishes `Body.Reducible` and `Func.Reducible` when it holds;
* `Body.Reducible.no_forward_cycle`: then no cycle of blocks avoids the back edges;
* `Func.of_loopsCheck`: `Canonicalize.run`'s check establishes the form and one entry per loop;
* `Body.mem_loopRoles`, `Body.loopRoles_complete`, `Func.loopRoles_spec`: in a body whose loops
  have preheaders and latches, and so in a canonical function, `Body.loopRoles` names each loop's
  head, preheader and latch.

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
  unfold endsAtB Block.endsAtB
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

/-- `theOne? E` is `u` exactly when `u` is in `E` and every point of `E` is `u`. -/
public theorem theOne?_eq_some {E : List Point} {u : Point} :
    theOne? E = some u ↔ u ∈ E ∧ ∀ w ∈ E, w = u := by
  unfold theOne?
  cases E with
  | nil => simp
  | cons v vs =>
    simp only [List.mem_cons, forall_eq_or_imp]
    split
    · rename_i hall
      simp only [List.all_eq_true, beq_iff_eq] at hall
      constructor
      · rintro ⟨⟩
        exact ⟨.inl rfl, rfl, hall⟩
      · rintro ⟨-, rfl, -⟩
        rfl
    · rename_i hall
      simp only [List.all_eq_true, beq_iff_eq] at hall
      simp only [reduceCtorEq, false_iff, not_and]
      rintro - rfl hrest
      exact hall hrest

/-- In a body with distinct labels whose loops have preheaders and latches, each entry of
`loopRoles` names the head of a loop, its preheader and its latch. -/
public theorem mem_loopRoles (hn : (bs.map (·.label)).Nodup) (hs : LoopsSimplified bs) {r : LoopRoles}
    (hr : r ∈ loopRoles bs) :
    IsHead bs r.head ∧ (∃ pre, pre.label = r.preheader ∧ Preheader bs r.head pre) ∧
      ∃ latch, latch.label = r.latch ∧ Latch bs r.head latch := by
  obtain ⟨h, hh, hm⟩ := List.mem_filterMap.mp hr
  split at hm
  · rename_i u v hu hv
    cases hm
    have hhead := (mem_heads_iff hn).mp hh
    obtain ⟨⟨pre, hpre⟩, ⟨latch, hlat⟩, -⟩ := hs h hhead
    obtain ⟨-, hu⟩ := theOne?_eq_some.mp hu
    obtain ⟨-, hv⟩ := theOne?_eq_some.mp hv
    have hpu : endOf pre = u := hu _ ((mem_entriesFrom hn).mpr ⟨hpre.enters, fun hat =>
      hpre.outside ((atLoop_endOf_iff hn hpre.mem).mp hat)⟩)
    obtain ⟨w, hw⟩ := hhead
    have hlv : endOf latch = v := hv _ (hlat.back w hw ▸ (mem_backFrom hn).mpr hw)
    exact ⟨⟨w, hw⟩, ⟨pre, by rw [← hpu]; rfl, hpre⟩, ⟨latch, by rw [← hlv]; rfl, hlat⟩⟩
  · cases hm

/-- In a body with distinct labels whose loops have preheaders and latches, every loop has an
entry in `loopRoles`. -/
public theorem loopRoles_complete (hn : (bs.map (·.label)).Nodup) (hs : LoopsSimplified bs) {h : Label}
    (hh : IsHead bs h) : ∃ r ∈ loopRoles bs, r.head = h := by
  obtain ⟨⟨pre, hpre⟩, ⟨latch, hlat⟩, -⟩ := hs h hh
  have hp : theOne? (entriesFrom bs (loopOf bs h) h) = some (endOf pre) := by
    refine theOne?_eq_some.mpr ⟨(mem_entriesFrom hn).mpr ⟨hpre.enters, fun hat =>
      hpre.outside ((atLoop_endOf_iff hn hpre.mem).mp hat)⟩, fun w hw => ?_⟩
    obtain ⟨htr, hout⟩ := (mem_entriesFrom hn).mp hw
    exact hpre.entries w htr hout
  have hl : theOne? (backFrom bs h) = some (endOf latch) := by
    obtain ⟨u, hu⟩ := hh
    exact theOne?_eq_some.mpr ⟨hlat.back u hu ▸ (mem_backFrom hn).mpr hu,
      fun w hw => hlat.back w ((mem_backFrom hn).mp hw)⟩
  refine ⟨⟨h, (endOf pre).label, (endOf latch).label⟩, List.mem_filterMap.mpr
    ⟨h, (mem_heads_iff hn).mpr hh, ?_⟩, rfl⟩
  simp only [hp, hl]

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

/-! ## One entry per loop -/

/-- `backBy` lists, for each label, the points that the back edges `be` to it leave from. -/
theorem mem_backBy {be : List (Point × Label)} {u : Point} {l : Label} :
    u ∈ ((backBy be).find? l).getD [] ↔ (u, l) ∈ be := by
  unfold backBy
  suffices ∀ (es : List (Point × Label)) (m : LabelMap (List Point)),
      u ∈ ((es.foldl (fun m e => m.insert e.2 (e.1 :: (m.find? e.2).getD [])) m).find?
        l).getD [] ↔ u ∈ (m.find? l).getD [] ∨ (u, l) ∈ es by
    rw [this]
    simp
  intro es
  induction es with
  | nil => intro m; simp
  | cons e es ih =>
    intro m
    rw [List.foldl_cons, ih, LabelMap.find?_insert]
    obtain ⟨w, l'⟩ := e
    by_cases hl : l = l'
    · subst hl
      simp only [↓reduceIte, Option.getD_some, List.mem_cons, Prod.mk.injEq, and_true]
      constructor
      · rintro ((rfl | hu) | hu)
        · exact .inr (.inl rfl)
        · exact .inl hu
        · exact .inr (.inr hu)
      · rintro (hu | (rfl | hu))
        · exact .inl (.inr hu)
        · exact .inl (.inl rfl)
        · exact .inr hu
    · simp only [hl, ↓reduceIte, List.mem_cons, Prod.mk.injEq, and_false, false_or]

/-- In a body with distinct labels, if every transfer that is not a back edge goes up in the
order `ord`, every loop has one entry. -/
public theorem reducible_of_reducibleWithB (hn : (bs.map (·.label)).Nodup) {ord : List Label}
    (h : reducibleWithB bs ord = true) : Reducible bs := by
  refine ⟨fun x => ((rankIn ord).find? x).getD 0, fun u l ht hb => ?_⟩
  simp only [reducibleWithB, reducibleIn, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem, decide_eq_true_eq] at h
  rcases h (u, l) (transfer_iff.mp ht) with hback | hlt
  · exact absurd ((mem_backEdges_iff hn).mp (mem_backBy.mp hback)) hb
  · exact hlt

/-- In a body with distinct labels, if the check against the depth-first order (`reducibleB`)
holds, every loop has one entry. -/
public theorem reducible_of_reducibleB (hn : (bs.map (·.label)).Nodup)
    (h : reducibleB bs = true) : Reducible bs :=
  reducible_of_reducibleWithB hn h

/-- In a body where every loop has one entry, no cycle of blocks avoids the back edges: there is
no chain of transfers that are not back edges from a block back to itself. -/
public theorem Reducible.no_forward_cycle (h : Reducible bs) (l : Label) :
    ¬ Relation.TransGen (FwdStep bs) l l := by
  obtain ⟨rank, hr⟩ := h
  have hlt : ∀ a b, Relation.TransGen (FwdStep bs) a b → rank a < rank b := by
    intro a b hab
    induction hab with
    | single hs =>
      obtain ⟨u, rfl, ht, hb⟩ := hs
      exact hr u _ ht hb
    | tail _ hs ih =>
      obtain ⟨u, hu, ht, hb⟩ := hs
      have h1 := hr u _ ht hb
      rw [hu] at h1
      omega
  exact fun hc => Nat.lt_irrefl _ (hlt l l hc)

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

/-- If the check against the depth-first order (`reducibleB`) holds of every body of a function
whose bodies have distinct labels, every loop in it has one entry. -/
public theorem Func.reducible_of_everyB {fn : Func env α} (hd : Body.Distinct fn.blocks.toList)
    (h : Body.everyB Body.reducibleB fn.blocks.toList = true) : fn.Reducible := by
  have hd' := (Body.distinct_iff_every _).mp hd
  have he := (Body.everyB_iff (P := (Body.reducibleB · = true)) (fun _ => Iff.rfl) _).mp h
  exact Body.Every.imp (fun _ hn hr => Body.reducible_of_reducibleB hn hr) hd' he

/-- In a canonical function whose bodies have distinct labels, in its own body and in every
region's body, each entry of `loopRoles` names the head of a loop, its preheader and its latch,
and every loop has an entry. -/
public theorem Func.loopRoles_spec {fn : Func env α} (hd : Body.Distinct fn.blocks.toList)
    (hc : fn.CanonicalCFG) :
    Body.Every (fun bs =>
      (∀ r ∈ Body.loopRoles bs, Body.IsHead bs r.head ∧
        (∃ pre, pre.label = r.preheader ∧ Body.Preheader bs r.head pre) ∧
        ∃ latch, latch.label = r.latch ∧ Body.Latch bs r.head latch) ∧
      ∀ h, Body.IsHead bs h → ∃ r ∈ Body.loopRoles bs, r.head = h) fn.blocks.toList :=
  Body.Every.imp (fun _ hn hs => ⟨fun _ hr => Body.mem_loopRoles hn hs hr,
    fun _ hh => Body.loopRoles_complete hn hs hh⟩) ((Body.distinct_iff_every _).mp hd) hc.1

/-- If `Canonicalize.run`'s per-body check holds of every body of a function whose bodies have
distinct labels, and its own body leaves through at most one block, the function is canonical
and every loop in it has one entry. -/
public theorem Func.of_loopsCheck {fn : Func env α} (hd : Body.Distinct fn.blocks.toList)
    (h : Body.everyB Body.loopsCheckB fn.blocks.toList = true)
    (ho : Body.oneExitB fn.blocks.toList = true) : fn.CanonicalCFG ∧ fn.Reducible := by
  have hd' := (Body.distinct_iff_every _).mp hd
  have he := (Body.everyB_iff (P := (Body.loopsCheckB · = true)) (fun _ => Iff.rfl) _).mp h
  have hn : (fn.blocks.toList.map (·.label)).Nodup := by
    cases hd with
    | mk hn _ => exact hn
  refine ⟨⟨Body.Every.imp (fun _ hn hc => ?_) hd' he, (Body.oneExitB_iff hn).mp ho⟩,
    Body.Every.imp (fun _ hn hc => ?_) hd' he⟩
  · simp only [Body.loopsCheckB, Bool.and_eq_true] at hc
    exact (Body.loopsSimplifiedB_iff hn).mp hc.1
  · simp only [Body.loopsCheckB, Bool.and_eq_true] at hc
    exact Body.reducible_of_reducibleB hn hc.2

/-- Whether a well-formed function is canonical is decided, by `Func.checkCanonicalCFG`. -/
public def Func.decCanonicalCFG [base ≼ env] (fn : Func env α) (h : fn.WF) :
    Decidable fn.CanonicalCFG :=
  decidable_of_iff _ (fn.checkCanonicalCFG_iff h.distinct)

end Strata.Dyn
