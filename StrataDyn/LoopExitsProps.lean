/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.LoopExits
public import StrataDyn.CanonicalProps
import all StrataDyn.Canonical
import all StrataDyn.CanonicalProps
import all StrataDyn.LoopExits
import all StrataDyn.Loops
import all StrataDyn.LoopsProps
import all StrataDyn.LoopsFast
import all StrataDyn.DomDecide

set_option autoImplicit false

/-!
# Reason-carrying loop exits and the preamble, decided

`StrataDyn/LoopExits.lean` states P4, P7 and F1 and computes their checks.  This module proves
that the checks decide them, for a function whose bodies have distinct labels, which every
well-formed function's do.

## Main theorems

* `Func.checkLoopExits_iff`: `Func.checkLoopExits` decides `Func.LoopExits`;
* `Func.checkPreamble_iff`: `Func.checkPreamble` decides `Func.Preamble`, for every function;
* `CanonicalSpec.holds_of_check`: the check of a `CanonicalSpec` proves the properties that it asks for.
-/

namespace Strata.Dyn

namespace Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)}

/-! ## Scopes and exits -/

/-- A label is in the loop of `h` only if some back edge enters `h`. -/
private theorem isHead_of_mem_loopOf (hn : (bs.map (·.label)).Nodup) {h l : Label}
    (hl : l ∈ loopOf bs h) : IsHead bs h := by
  obtain ⟨_, -, u, hu, -⟩ := (mem_loopOf_iff hn).mp hl
  exact ⟨u, hu⟩

/-- The head of a loop is in its loop. -/
private theorem mem_loopOf_self (hn : (bs.map (·.label)).Nodup) {h : Label} (hh : IsHead bs h) :
    h ∈ loopOf bs h := by
  obtain ⟨u, v, hj, hvl, hd⟩ := hh
  exact (mem_loopOf_iff hn).mpr ⟨v, hvl, u, ⟨v, hj, hvl, hd⟩, hj.mem, .inl hvl⟩

/-- In a body with distinct labels, a point is in the scope of `h` exactly when its label is in
`scopeIn (loopOf bs) h`. -/
theorem inLoopScope_iff (hn : (bs.map (·.label)).Nodup) {h : Label} {u : Point} :
    InLoopScope bs h u ↔ u.label ∈ scopeIn (loopOf bs) h := by
  unfold InLoopScope scopeIn
  rw [atLoop_iff hn]
  split
  · rename_i hL
    simp only [hL, List.not_mem_nil, false_or, List.mem_singleton]
    exact ⟨fun ⟨_, h'⟩ => h', fun h' => ⟨fun hh => by
      have hself := mem_loopOf_self hn hh
      rw [hL] at hself
      exact List.not_mem_nil hself, h'⟩⟩
  · rename_i L hL
    have hh : IsHead bs h := by
      cases hc : loopOf bs h with
      | nil => exact absurd hc hL
      | cons l _ => exact isHead_of_mem_loopOf hn (l := l) (by rw [hc]; exact List.mem_cons_self)
    exact ⟨fun h' => h'.elim id fun ⟨hnh, _⟩ => absurd hh hnh, .inl⟩

/-- In a body with distinct labels, `exitsIn` of the scope of `h` lists the blocks that a
transfer leaves the scope for. -/
theorem mem_exitsIn_iff (hn : (bs.map (·.label)).Nodup) {h x : Label} :
    x ∈ exitsIn (transfers bs) (scopeIn (loopOf bs) h) ↔ ExitOf bs h x := by
  simp only [exitsIn, ExitOf, List.mem_eraseDups, List.mem_map, List.mem_filter,
    Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem,
    transfer_iff, inLoopScope_iff hn]
  constructor
  · rintro ⟨⟨u, l'⟩, ⟨hu, hL, hl⟩, rfl⟩
    exact ⟨u, hu, hL, hl⟩
  · rintro ⟨u, hu, hL, hl⟩
    exact ⟨(u, x), ⟨hu, hL, hl⟩, rfl⟩

/-- A block that a transfer leaves the scope of `h` for is a block of the body. -/
private theorem ExitOf.block {h x : Label} (hx : ExitOf bs h x) : ∃ xb ∈ bs, xb.label = x := by
  obtain ⟨_, ⟨v, hj, rfl⟩, -⟩ := hx
  exact ⟨v, hj.mem, rfl⟩

/-! ## Reachability from a block -/

/-- In a body with distinct labels, `unreachableB` decides `Unreachable`. -/
theorem unreachableB_iff (hn : (bs.map (·.label)).Nodup) {l : Label} :
    unreachableB bs l = true ↔ Unreachable bs l := by
  unfold unreachableB Block.unreachableB Unreachable
  cases hf : blockAt? bs l with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro b hb hbl _
    rw [(blockAt?_eq_some hn).mpr ⟨hb, hbl⟩] at hf
    exact absurd hf (by simp)
  | some b =>
    obtain ⟨hb, hbl⟩ := (blockAt?_eq_some hn).mp hf
    simp only [Option.any_some, Bool.and_eq_true, Array.isEmpty_iff, beq_iff_eq]
    constructor
    · exact fun ⟨he, ht⟩ => ⟨b, hb, hbl, he, ht⟩
    · rintro ⟨c, hc, hcl, he, ht⟩
      rw [eq_of_label_eq hn hc hb (hcl.trans hbl.symm)] at he ht
      exact ⟨he, ht⟩

/-- In a body with distinct labels, `avoidsFromB` from a block of the body decides whether a
path from its start reaches `u` avoiding `d`. -/
theorem avoidsFromB_iff (hn : (bs.map (·.label)).Nodup) {d x : Label} {u : Point}
    (hx : ∃ xb ∈ bs, xb.label = x) :
    avoidsFromB bs d x u = true ↔ PathAvoid bs ⟨d, 0⟩ ⟨x, 0⟩ u := by
  obtain ⟨xb, hxb, rfl⟩ := hx
  unfold avoidsFromB
  rw [(blockAt?_eq_some hn).mpr ⟨hxb, rfl⟩, Option.any_some]
  exact reachAvoidB_enteredAt_iff hn hxb

/-- In a body with distinct labels, `pastExitB` from the exits of the scope of `h` decides
`PastExit`. -/
theorem pastExitB_iff (hn : (bs.map (·.label)).Nodup) {h d : Label} {u : Point} :
    pastExitB bs (exitsIn (transfers bs) (scopeIn (loopOf bs) h)) d u = true ↔
      PastExit bs h d u := by
  unfold pastExitB PastExit
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hp⟩
    have he := (mem_exitsIn_iff hn).mp hx
    exact ⟨x, he, (avoidsFromB_iff hn he.block).mp hp⟩
  · rintro ⟨x, he, hp⟩
    exact ⟨x, (mem_exitsIn_iff hn).mpr he, (avoidsFromB_iff hn he.block).mpr hp⟩

/-- In a body with distinct labels, `reachesB` from a block of the body decides `Reaches`. -/
theorem reachesB_iff (hn : (bs.map (·.label)).Nodup) {x d : Label}
    (hx : ∃ xb ∈ bs, xb.label = x) : reachesB bs (transfers bs) x d = true ↔ Reaches bs x d := by
  unfold reachesB Reaches
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true, Prod.exists]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨y, l, hy, rfl, hp⟩
    exact ⟨y, (avoidsFromB_iff hn hx).mp hp, transfer_iff.mpr hy⟩
  · rintro ⟨y, hp, ht⟩
    exact ⟨y, d, transfer_iff.mp ht, rfl, (avoidsFromB_iff hn hx).mpr hp⟩

/-- In a body with distinct labels, the body entered at one of its blocks has the same block for
each label. -/
theorem blockAt?_enteredAt (hn : (bs.map (·.label)).Nodup) {xb : Block env α} (hxb : xb ∈ bs)
    (l : Label) : blockAt? (enteredAt bs xb) l = blockAt? bs l := by
  apply Option.ext
  intro b
  rw [blockAt?_eq_some (nodup_enteredAt hn xb), blockAt?_eq_some hn, mem_enteredAt hn hxb]

/-- In a body with distinct labels, the search from the root of the body entered at `xb` reaches
the start of `l` avoiding the start of `d` exactly when, in the body, a path from the start of
`xb` does. -/
theorem mem_reached_enteredAt (hn : (bs.map (·.label)).Nodup) {xb : Block env α} (hxb : xb ∈ bs)
    {d l : Label} : l ∈ reached (enteredAt bs xb) ⟨d, 0⟩ ↔
      ∃ c ∈ bs, c.label = l ∧ PathAvoid bs ⟨d, 0⟩ ⟨xb.label, 0⟩ ⟨l, 0⟩ := by
  have hne : enteredAt bs xb ≠ [] := List.cons_ne_nil _ _
  have hn' := nodup_enteredAt hn xb
  have hroot : root (enteredAt bs xb) = ⟨xb.label, 0⟩ := rfl
  have hmono₁ := fun {x y : Point} (hp : PathAvoid (enteredAt bs xb) ⟨d, 0⟩ x y) =>
    hp.mono fun c hc => (mem_enteredAt hn hxb).mp hc
  have hmono₂ := fun {x y : Point} (hp : PathAvoid bs ⟨d, 0⟩ x y) =>
    hp.mono fun c hc => (mem_enteredAt (c := c) hn hxb).mpr hc
  by_cases hrd : root (enteredAt bs xb) = ⟨d, 0⟩
  · simp only [reached, ite_eq_left hrd, List.not_mem_nil, false_iff, not_exists, not_and]
    exact fun _ _ _ hp => hp.start_ne (hroot ▸ hrd)
  · constructor
    · intro hl
      obtain ⟨⟨hgrow, -⟩, -, -⟩ := reached_spec hne hrd
      obtain ⟨c, hc, hcl, hra⟩ := hgrow l hl
      exact ⟨c, (mem_enteredAt hn hxb).mp hc, hcl,
        hroot ▸ hmono₁ (reachAvoid_iff_pathAvoid.mp hra)⟩
    · rintro ⟨c, -, -, hp⟩
      obtain ⟨-, -, -, hmem, -⟩ := reached_complete hne hn'
        (reachAvoid_iff_pathAvoid.mpr (hroot ▸ hmono₂ hp))
      exact hmem

/-- In a body with distinct labels, a region, computed once for `x` with the body's successor map,
gives the same answer as the search from `x`. -/
theorem inRegionB_regionOf (hn : (bs.map (·.label)).Nodup) {d x : Label} {u : Point} :
    inRegionB bs d (regionOf bs (succMap bs) d x) u = avoidsFromB bs d x u := by
  unfold avoidsFromB regionOf
  cases hxb : blockAt? bs x with
  | none =>
    have hno : bs.any (·.label == x) = false := by
      rw [Bool.eq_false_iff]
      intro ha
      obtain ⟨b, hb, hbl⟩ := List.any_eq_true.mp ha
      rw [(blockAt?_eq_some hn).mpr ⟨hb, beq_iff_eq.mp hbl⟩] at hxb
      exact absurd hxb (by simp)
    simp [hno, inRegionB]
  | some xb =>
    obtain ⟨hxb', hxbl⟩ := (blockAt?_eq_some hn).mp hxb
    have hany : bs.any (·.label == x) = true :=
      List.any_eq_true.mpr ⟨xb, hxb', beq_iff_eq.mpr hxbl⟩
    rw [ite_eq_left hany, Option.any_some]
    unfold inRegionB reachAvoidB
    rw [show (enteredAt bs xb).find? (·.label == u.label) = blockAt? bs u.label from
      blockAt?_enteredAt hn hxb' u.label]
    congr 1
    funext b
    congr 1
    apply Bool.eq_iff_iff.mpr
    rw [found_searchFrom_iff ⟨xb, hxb', hxbl⟩, List.contains_iff_mem, mem_reached_enteredAt hn hxb',
      hxbl]

/-- The regions of the blocks of `X` give the same answer as `pastExitB`. -/
theorem inRegionsB_regionsOf (hn : (bs.map (·.label)).Nodup) {d : Label} {X : List Label}
    {u : Point} : inRegionsB bs d (regionsOf bs (succMap bs) d X) u = pastExitB bs X d u := by
  simp only [inRegionsB, regionsOf, pastExitB, List.any_map]
  exact congrArg _ (funext fun x => inRegionB_regionOf hn)

/-- `reachesInB` with the region of `x` is `reachesB`. -/
theorem reachesInB_regionOf (hn : (bs.map (·.label)).Nodup) {tr : List (Point × Label)}
    {x d : Label} : reachesInB bs tr x d (regionOf bs (succMap bs) d x) = reachesB bs tr x d := by
  simp only [reachesInB, reachesB, inRegionB_regionOf hn]

/-- A test of every region of `X` is a test of every block of `X` with its region. -/
theorem all_regionsOf {sm : LabelMap (List Label)} {d : Label} {X : List Label}
    {f : Label × LabelMap Unit → Bool} :
    (regionsOf bs sm d X).all f = X.all fun x => f (x, regionOf bs sm d x) := by
  simp only [regionsOf, List.all_map]
  rfl

/-- In a nonempty body with distinct labels, `d` dominates `y` exactly when no path from the root
reaches `y` without passing `d`. -/
theorem not_reachAvoidB_iff (hbs : bs ≠ []) (hn : (bs.map (·.label)).Nodup) {d y : Point} :
    (!reachAvoidB bs d y) = true ↔ Dom bs d y := by
  rw [Bool.not_eq_true', Bool.eq_false_iff, Dom, ne_eq, reachAvoidB_iff hbs hn]

/-! ## P4 -/

/-- In a body with distinct labels, `doneB` decides `Done`. -/
theorem doneB_iff (hn : (bs.map (·.label)).Nodup) {s : CompletionShape env} {h d : Label} :
    doneB bs (transfers bs) (exitPoints bs) (heads bs) (loopOf bs) s h d
        (regionsOf bs (succMap bs) d (exitsIn (transfers bs) (scopeIn (loopOf bs) h))) = true ↔
      Done bs s h d := by
  unfold doneB
  simp only [all_regionsOf, reachesInB_regionOf hn, inRegionsB_regionsOf hn, List.all_filter,
    List.all_map]
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true,
    Bool.eq_false_iff, ne_eq, List.contains_iff_mem, Bool.not_and, bne_iff_ne,
    Function.comp, Classical.not_not]
  constructor
  · rintro ⟨⟨⟨⟨⟨hb, hout⟩, hstay⟩, hreach⟩, hret⟩, hhead⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · cases hf : blockAt? bs d with
      | none => rw [hf] at hb; exact absurd hb (by simp)
      | some b =>
        rw [hf, Option.any_some, decide_eq_true_iff] at hb
        obtain ⟨hbm, hbl⟩ := (blockAt?_eq_some hn).mp hf
        exact ⟨b, hbm, hbl, hb⟩
    · exact fun hin => hout ((inLoopScope_iff hn).mp hin)
    · intro u hu hl
      exact hstay u (mem_exitPoints.mpr hl) ((inLoopScope_iff hn).mp hu)
    · intro x hx hu
      rcases hreach x ((mem_exitsIn_iff hn).mpr hx) with hu' | hr
      · exact absurd ((unreachableB_iff hn).mp hu') hu
      · exact (reachesB_iff hn hx.block).mp hr
    · intro u hp hl
      exact hret u (mem_exitPoints.mpr hl) ((pastExitB_iff hn).mpr hp)
    · intro h' hh' hne ⟨b, hbl, hin⟩ hp
      rcases hhead h' ((mem_heads_iff hn).mpr hh') with (heq | hnot) | hnp
      · exact hne heq
      · exact hnot ((mem_loopOf_iff hn).mpr ⟨b, hbl, hin⟩)
      · exact hnp ((pastExitB_iff hn).mpr hp)
  · intro hD
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · obtain ⟨b, hbm, hbl, hty⟩ := hD.block
      rw [(blockAt?_eq_some hn).mpr ⟨hbm, hbl⟩, Option.any_some, decide_eq_true_iff]
      exact hty
    · exact fun hin => hD.outside ((inLoopScope_iff hn).mpr hin)
    · intro u hu hin
      exact hD.stays u ((inLoopScope_iff hn).mpr hin) (mem_exitPoints.mp hu)
    · intro x hx
      have he := (mem_exitsIn_iff hn).mp hx
      by_cases hu : Unreachable bs x
      · exact .inl ((unreachableB_iff hn).mpr hu)
      · exact .inr ((reachesB_iff hn he.block).mpr (hD.reaches x he hu))
    · intro u hu hp
      exact hD.noReturn u ((pastExitB_iff hn).mp hp) (mem_exitPoints.mp hu)
    · intro h' hh'
      by_cases heq : h' = h
      · exact .inl (.inl heq)
      · by_cases hin : h ∈ loopOf bs h'
        · refine .inr fun hp => ?_
          exact hD.noOuterHead h' ((mem_heads_iff hn).mp hh') heq
            ((mem_loopOf_iff hn).mp hin) ((pastExitB_iff hn).mp hp)
        · exact .inl (.inr hin)

/-! ## P7 -/

/-- In a body with distinct labels, `armOutB` of the scope of `h` and its exits decides
`ArmOut`. -/
theorem armOutB_iff (hn : (bs.map (·.label)).Nodup) {h d t : Label} :
    armOutB bs (scopeIn (loopOf bs) h)
        (regionsOf bs (succMap bs) d (exitsIn (transfers bs) (scopeIn (loopOf bs) h))) d t =
        true ↔
      ArmOut bs h d t := by
  unfold armOutB ArmOut
  simp only [inRegionsB_regionsOf hn, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq,
    List.contains_iff_mem, bne_iff_ne, unreachableB_iff hn, ← inLoopScope_iff hn (u := ⟨t, 0⟩),
    pastExitB_iff hn]
  exact or_congr Iff.rfl ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

/-- In a body with distinct labels, `enclosesB` decides `Encloses`. -/
theorem enclosesB_iff (hn : (bs.map (·.label)).Nodup) {r r' : LoopRecord} :
    enclosesB (loopOf bs) r r' = true ↔ Encloses bs r r' := by
  unfold enclosesB Encloses
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem,
    ← inLoopScope_iff hn (u := ⟨r.head, 0⟩)]

/-- In a body with distinct labels, `jumpsToB` decides whether the block `t` is empty and ends in
a plain jump to `h`. -/
theorem jumpsToB_iff (hn : (bs.map (·.label)).Nodup) {t h : Label} :
    jumpsToB bs t h = true ↔ ∃ b ∈ bs, b.label = t ∧ b.instrs = #[] ∧ EndsIn b h := by
  unfold jumpsToB
  cases hf : blockAt? bs t with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro b hb hbl _
    rw [(blockAt?_eq_some hn).mpr ⟨hb, hbl⟩] at hf
    exact absurd hf (by simp)
  | some b =>
    obtain ⟨hb, hbl⟩ := (blockAt?_eq_some hn).mp hf
    rw [Option.any_some, Bool.and_eq_true, Array.isEmpty_iff, endsAtB_iff hn]
    constructor
    · rintro ⟨hi, c, hc, hcb, he⟩
      have hcl : c.label = b.label := congrArg Point.label hcb.symm
      rw [eq_of_label_eq hn hc hb hcl] at he
      exact ⟨b, hb, hbl, hi, he⟩
    · rintro ⟨c, hc, hcl, hi, he⟩
      rw [eq_of_label_eq hn hc hb (hcl.trans hbl.symm)] at he hi
      exact ⟨hi, b, hb, rfl, he⟩

/-- In a body with distinct labels, `toOuterDoneB` decides `ToOuterDone`. -/
theorem toOuterDoneB_iff (hn : (bs.map (·.label)).Nodup) {recs : List LoopRecord}
    {r : LoopRecord} {t : Label} :
    toOuterDoneB bs (loopOf bs) recs r t = true ↔ ToOuterDone bs recs r t := by
  unfold toOuterDoneB ToOuterDone
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    unreachableB_iff hn, enclosesB_iff hn, Option.any_eq_true, jumpsToB_iff hn]

/-- In a body with distinct labels, `toOuterLoopB` decides `ToOuterLoop`. -/
theorem toOuterLoopB_iff (hn : (bs.map (·.label)).Nodup) {recs : List LoopRecord}
    {r : LoopRecord} {t : Label} :
    toOuterLoopB bs (loopOf bs) recs r t = true ↔ ToOuterLoop bs recs r t := by
  unfold toOuterLoopB ToOuterLoop
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    toOuterDoneB_iff hn, enclosesB_iff hn, jumpsToB_iff hn, List.contains_iff_mem,
    ← inLoopScope_iff hn (u := ⟨t, 0⟩)]
  refine or_congr Iff.rfl (exists_congr fun r' => and_congr Iff.rfl (and_congr Iff.rfl ?_))
  refine or_congr ⟨fun h => h.symm, fun h => h.symm⟩ ?_
  exact ⟨fun ⟨⟨b, hb, hbl, hi, he⟩, hin⟩ => ⟨b, hb, hbl, hi, he, hin⟩,
    fun ⟨b, hb, hbl, hi, he, hin⟩ => ⟨⟨b, hb, hbl, hi, he⟩, hin⟩⟩

/-- In a body with distinct labels, `labelArmB` decides `LabelArm`, given checks that decide
`own` and `other`. -/
theorem labelArmB_iff (hn : (bs.map (·.label)).Nodup) {lt : Name} {n : Int}
    {own other : Label → Prop} {ownB otherB : Label → Bool}
    (hown : ∀ l, ownB l = true ↔ own l) (hother : ∀ l, otherB l = true ↔ other l) {t : Label} :
    labelArmB bs lt n ownB otherB t = true ↔ LabelArm bs lt n own other t := by
  unfold labelArmB Block.labelArmB LabelArm
  cases hf : blockAt? bs t with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro b hb hbl
    rw [(blockAt?_eq_some hn).mpr ⟨hb, hbl⟩] at hf
    exact absurd hf (by simp)
  | some b =>
    obtain ⟨hb, hbl⟩ := (blockAt?_eq_some hn).mp hf
    rw [Option.any_some]
    constructor
    · intro hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hname, hrest⟩ := hc
      refine ⟨b, hb, hbl, hname, ?_⟩
      split at hrest
      · rename_i p x v s₁ s₂ hp ha hs
        simp only [Bool.and_eq_true, beq_iff_eq, ← Array.any_toList, List.any_eq_true,
          Array.mem_toList_iff] at hrest
        obtain ⟨⟨⟨hx, i, hi, hiv⟩, ho⟩, hot⟩ := hrest
        refine ⟨p, v, s₁, s₂, hp, ?_, ⟨i, hi, hiv⟩, ?_, (hown _).mp ho, (hother _).mp hot⟩
        · rw [← Array.toList_inj, ha, hx]
        · rw [← Array.toList_inj, hs]
      · exact absurd hrest (by simp)
    · rintro ⟨c, hc, hcl, hname, p, v, s₁, s₂, hp, ha, ⟨i, hi, hiv⟩, hs, ho, hot⟩
      have hcb := eq_of_label_eq hn hc hb (hcl.trans hbl.symm)
      subst hcb
      simp only [Bool.and_eq_true, beq_iff_eq, hname, true_and]
      rw [hp, ha, hs]
      simp only [Bool.and_eq_true, beq_iff_eq, ← Array.any_toList, List.any_eq_true,
        Array.mem_toList_iff]
      exact ⟨⟨⟨by simp, i, hi, hiv⟩, (hown _).mpr ho⟩, (hother _).mpr hot⟩

/-- In a body with distinct labels, `armOkB` decides `ArmOk`. -/
theorem armOkB_iff (hn : (bs.map (·.label)).Nodup) {s : CompletionShape env} {ro : Roles}
    {recs : List LoopRecord} {r : LoopRecord} {d : Label} {i : Nat} {t : Label} :
    armOkB bs (loopOf bs) (scopeIn (loopOf bs) r.head)
        (regionsOf bs (succMap bs) d (exitsIn (transfers bs) (scopeIn (loopOf bs) r.head))) s ro
        recs r d i t =
        true ↔
      ArmOk bs s ro recs r d i t := by
  unfold armOkB ArmOk
  have hu := fun l => unreachableB_iff hn (bs := bs) (l := l)
  have ho := fun l => armOutB_iff hn (bs := bs) (h := r.head) (d := d) (t := l)
  have hd := fun l => toOuterDoneB_iff hn (bs := bs) (recs := recs) (r := r) (t := l)
  have hl := fun l => toOuterLoopB_iff hn (bs := bs) (recs := recs) (r := r) (t := l)
  split
  · split
    · exact hu t
    · exact ho t
  · split
    · rw [Bool.or_eq_true, hu t, labelArmB_iff hn hu hl]
    · split
      · exact labelArmB_iff hn ho hd
      · exact ho t
  · simp

/-- In a body with distinct labels, `absorbsB` decides `Absorbs`. -/
theorem absorbsB_iff (hn : (bs.map (·.label)).Nodup) {s : CompletionShape env} {ro : Roles}
    {recs : List LoopRecord} {r : LoopRecord} {d : Label} :
    absorbsB bs (loopOf bs) s ro recs r d
        (regionsOf bs (succMap bs) d (exitsIn (transfers bs) (scopeIn (loopOf bs) r.head))) =
      true ↔ Absorbs bs s ro recs r d := by
  unfold absorbsB Block.absorbsB Absorbs
  cases hf : blockAt? bs d with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro b hb hbl
    rw [(blockAt?_eq_some hn).mpr ⟨hb, hbl⟩] at hf
    exact absurd hf (by simp)
  | some b =>
    obtain ⟨hb, hbl⟩ := (blockAt?_eq_some hn).mp hf
    rw [Option.any_some]
    have harms : ((List.range b.term.succs.size).all fun i =>
          (b.term.succs[i]?).all fun sv =>
            armOkB bs (loopOf bs) (scopeIn (loopOf bs) r.head)
              (regionsOf bs (succMap bs) d (exitsIn (transfers bs) (scopeIn (loopOf bs) r.head)))
              s ro recs r d
              i sv.label) =
          true ↔
        ∀ (i : Nat) (sv : Target.Raw), b.term.succs[i]? = some sv →
          ArmOk bs s ro recs r d i sv.label := by
      simp only [List.all_eq_true, List.mem_range]
      constructor
      · intro hall i sv hi
        have hlt : i < b.term.succs.size := (Array.getElem?_eq_some_iff.mp hi).1
        have hai := hall i hlt
        rw [hi, Option.all_some] at hai
        exact (armOkB_iff hn).mp hai
      · intro hall i _
        cases hi : b.term.succs[i]? with
        | none => rfl
        | some sv => exact (armOkB_iff hn).mpr (hall i sv hi)
    simp only [Bool.and_eq_true, beq_iff_eq, harms, Option.any_eq_true]
    constructor
    · rintro ⟨⟨⟨hname, hargs⟩, hsize⟩, hall⟩
      exact ⟨b, hb, hbl, hname, hargs, hsize, hall⟩
    · rintro ⟨c, hc, hcl, hname, hargs, hsize, hall⟩
      have hcb := eq_of_label_eq hn hc hb (hcl.trans hbl.symm)
      subst hcb
      exact ⟨⟨⟨hname, hargs⟩, hsize⟩, hall⟩

/-! ## A body -/

/-- In a body with distinct labels, every exit of the scope of `h` is unreachable exactly when
every block that a transfer leaves the scope for is. -/
theorem exitsIn_all_unreachable_iff (hn : (bs.map (·.label)).Nodup) {h : Label} :
    (exitsIn (transfers bs) (scopeIn (loopOf bs) h)).all (unreachableB bs) = true ↔
      ∀ x, ExitOf bs h x → Unreachable bs x := by
  rw [List.all_eq_true]
  exact forall_congr' fun x =>
    imp_congr (mem_exitsIn_iff hn) (unreachableB_iff hn)

/-- In a body with distinct labels, `recordHoldsB` decides `RecordHolds`. -/
theorem recordHoldsB_iff (hbs : bs ≠ []) (hn : (bs.map (·.label)).Nodup)
    {s : CompletionShape env} {ro : Roles} {recs : List LoopRecord} {r : LoopRecord} :
    recordHoldsB bs (transfers bs) (exitPoints bs) (heads bs) (loopOf bs) (domInfo bs)
        (succMap bs) s ro recs r = true ↔
      RecordHolds bs s ro recs r := by
  unfold recordHoldsB headDominatesB RecordHolds
  rw [Bool.and_eq_true, Bool.and_eq_true, preheaderB_iff hn, and_assoc]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · simp only [Bool.or_eq_true, List.contains_iff_mem, mem_heads_iff hn, Bool.and_eq_true,
      Option.all_eq_true, List.all_eq_true, domWith_start, not_reachAvoidB_iff hbs hn]
    constructor
    · rintro (hh | ⟨hd, hx⟩) hnh
      · exact absurd hh hnh
      · exact ⟨hd, fun x hx' => hx x ((mem_exitsIn_iff hn).mpr hx')⟩
    · intro h
      by_cases hh : IsHead bs r.head
      · exact .inl hh
      · obtain ⟨hd, hx⟩ := h hh
        exact .inr ⟨hd, fun x hx' => hx x ((mem_exitsIn_iff hn).mp hx')⟩
  cases r.done with
  | none =>
    rw [Bool.and_eq_true, exitsIn_all_unreachable_iff hn]
    refine and_congr Iff.rfl ?_
    simp only [List.all_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      List.contains_iff_mem]
    exact ⟨fun h u hin hl => h u (mem_exitPoints.mpr hl) ((inLoopScope_iff hn).mp hin),
      fun h u hu hin => h u ((inLoopScope_iff hn).mpr hin) (mem_exitPoints.mp hu)⟩
  | some d =>
    rw [Bool.and_eq_true, doneB_iff hn, absorbsB_iff hn]

/-- In a body with distinct labels, `loopExitsB` decides `LoopExits`. -/
theorem loopExitsB_iff (hn : (bs.map (·.label)).Nodup) {s : CompletionShape env} {ro : Roles}
    {recs : List LoopRecord} : loopExitsB bs s ro recs = true ↔ LoopExits bs s ro recs := by
  by_cases hbs : bs = []
  · subst hbs
    refine ⟨fun _ => ⟨fun h ⟨_, v, hj, _⟩ => absurd hj.mem (List.not_mem_nil), ?_⟩, fun _ => ?_⟩
    · exact fun r _ ⟨b, hb, _⟩ => absurd hb (List.not_mem_nil)
    · simp [loopExitsB, loopExitsWith, tableOf, backEdges, transfers, loopsOf]
  unfold loopExitsB
  simp only [lookupLoop_table, table_heads]
  unfold loopExitsWith
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, recordHoldsB_iff hbs hn]
  constructor
  · rintro ⟨hrec, heach⟩
    refine ⟨fun h hh => hrec h ((mem_heads_iff hn).mpr hh), fun r hr ⟨b, hb, hbl⟩ => ?_⟩
    rcases heach r hr with hno | hok
    · exact absurd ⟨b, hb, by rw [hbl]⟩ hno
    · exact hok
  · intro hL
    refine ⟨fun h hh => hL.recorded h ((mem_heads_iff hn).mp hh), fun r hr => ?_⟩
    by_cases hin : ∃ b ∈ bs, (b.label == r.head) = true
    · obtain ⟨b, hb, hbl⟩ := hin
      exact .inr (hL.each r hr ⟨b, hb, beq_iff_eq.mp hbl⟩)
    · exact .inl fun ⟨b, hb, hbl⟩ => hin ⟨b, hb, by simpa using hbl⟩

end Body

/-! ## The function -/

variable {env : Env Unit} {α : Type}

/-- For a function whose bodies have distinct labels, `checkLoopExits` holds exactly when the
shape is well formed, every body states P4 and P7 truly for the records, and the records name
each head and each `done` once, at blocks of the function. -/
public theorem Func.checkLoopExits_iff (fn : Func env α) (hd : Body.Distinct fn.blocks.toList)
    {s : CompletionShape env} {recs : List LoopRecord} :
    fn.checkLoopExits s recs = true ↔ fn.LoopExits s recs := by
  rw [Func.checkLoopExits, Func.LoopExits]
  cases hr : s.roles? with
  | none => simp
  | some ro =>
    simp only [Option.some.injEq, exists_eq_left', Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.contains_iff_mem]
    rw [Body.everyB_iff_of (Q := fun bs => (bs.map (·.label)).Nodup)
      (fun _ hn => Body.loopExitsB_iff hn) ((Body.distinct_iff_every _).mp hd)]
    exact ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨⟨a, b⟩, c⟩, d⟩⟩

/-- `checkPreamble` holds exactly when the function's entry block ends in a plain jump to a block
that nothing else enters, or in `base.unreachable`. -/
public theorem Func.checkPreamble_iff (fn : Func env α) :
    fn.checkPreamble = true ↔ fn.Preamble := by
  unfold Func.checkPreamble Func.Preamble
  cases he : fn.blocks[0]? with
  | none => simp
  | some e =>
    simp only [Option.all_some, Option.some.injEq, forall_eq', Bool.or_eq_true]
    refine or_congr (by simp [Bool.and_eq_true, Array.isEmpty_iff]) ?_
    have hsz : ∀ sv, e.term.succs.toList = [sv] → e.term.succs.size = 1 := fun sv h => by
      rw [← Array.length_toList, h]; rfl
    constructor
    · intro hc
      simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at hc
      obtain ⟨⟨hj, hr⟩, hm⟩ := hc
      split at hm
      · rename_i sv hsv
        simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, List.all_eq_true,
          Bool.or_eq_true, bne_iff_ne, ne_eq, Prod.forall] at hm
        obtain ⟨⟨b, hb, hbl⟩, hall⟩ := hm
        refine ⟨b, hb, ⟨hj, hr, fun t ht => ?_⟩, hsz sv hsv, fun u hu => ?_⟩
        · rw [← Array.mem_toList_iff, hsv, List.mem_singleton] at ht
          rw [ht, hbl]
        · rcases hall u b.label (Body.transfer_iff.mp hu) with hne | heq
          · exact absurd hbl hne
          · exact heq
      · exact absurd hm (by simp)
    · rintro ⟨b, hb, ⟨hj, hr, hall⟩, hs, hin⟩
      simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff, hj, hr, true_and]
      obtain ⟨sv, hsv⟩ : ∃ sv, e.term.succs.toList = [sv] := by
        cases h : e.term.succs.toList with
        | nil => rw [← Array.length_toList, h] at hs; exact absurd hs (by simp)
        | cons sv t =>
          cases t with
          | nil => exact ⟨sv, rfl⟩
          | cons _ _ => rw [← Array.length_toList, h] at hs; exact absurd hs (by simp)
      have hst : sv.label = b.label :=
        hall sv (Array.mem_toList_iff.mp (by rw [hsv]; exact List.mem_singleton_self _))
      rw [hsv]
      simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, List.all_eq_true,
        Bool.or_eq_true, bne_iff_ne, ne_eq, Prod.forall]
      refine ⟨⟨b, hb, hst.symm⟩, fun u l hul => ?_⟩
      by_cases hl : l = sv.label
      · subst hl
        rw [hst] at hul
        exact .inr (hin u (Body.transfer_iff.mpr hul))
      · exact .inl hl

/-- For a function whose bodies have distinct labels, `spec.check` proves the properties that
`spec` asks for. -/
public theorem CanonicalSpec.holds_of_check {spec : CanonicalSpec env α} {g : Func env α}
    (hd : Body.Distinct g.blocks.toList) (h : spec.check g = true) : spec.Holds g := by
  simp only [CanonicalSpec.check, Bool.and_eq_true, Option.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  refine ⟨fun s hs => (g.checkLoopExits_iff hd).mp (h.1 s hs), fun hp => ?_⟩
  rcases h.2 with hf | hc
  · rw [hp] at hf; cases hf
  · exact (g.checkPreamble_iff).mp hc

end Strata.Dyn
