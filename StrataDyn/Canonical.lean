/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.EveryBody
public import StrataDyn.LoopsFast
public import StrataDyn.BodyIndexProps
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The canonical form of loops and returns

A contract obligation must be placed at one block, so that every path that should meet it does.
The canonical form gives each class of obligation such a block.  For each loop:

* (P1) a *preheader*: a block outside the loop, through whose end every entry into the loop
  passes.  The base case of the invariant is asserted there, and the loop's writes are havocked;
* (P2) a *latch*: a block from whose end every back edge leaves.  The step case of the invariant
  and the decrease of the variant are asserted there;
* (P3) *dedicated exits*: every block that a transfer leaves the loop for is entered only from
  the loop.  What holds when the loop ends is asserted in those blocks.  No point of the loop
  leaves the body, so every path out of the loop passes through one of them.

And for the function:

* (F2) one block from whose end every return leaves.  The postcondition is asserted there.

A stage that asserts the invariant at the end of the preheader and of the latch may assume it at
the head's start: a run reaches the head's start only by a transfer (`Body.Preheader.root_ne`),
and every transfer to the head leaves from one of the two (`Body.Preheader.transfer_head_latch`).
And the writes it havocs at the preheader are those of the loop's blocks, the regions their
instructions run and the code they call included: a path that comes back to the head without
passing the end of the preheader stays in the loop (`Body.Preheader.atLoop_of_path_head`).  For a
recorded loop that no back edge enters, every transfer to the head leaves from the end of its
preheader (`Body.Preheader.transfer_head_of_not_isHead`), so the base case alone suffices.

The loop of a head `h` is the union of the natural loops of its back edges
(`StrataDyn/Loops.lean`), as in LLVM.  Its code that cannot repeat the loop, such as the code
after a `break`, is not in it.  The loop properties hold in every body of the function, its own
and each region's, but not its contract's clauses (`Body.Every`); F2 holds in its own body.  The
form does not ask for the loops to be reducible: a cycle with no back edge has no head, so no
loop property mentions it.
`Body.Reducible` asks it separately: every cycle passes through a back edge, so every cycle lies
in the loop of some head.  Neither says anything about an operation that runs a region again and
again: such a loop has no back edge.

The preheader, the latch and the exit block end in the base's plain `jump`, so that an obligation
placed before that jump holds where control arrives.

`Func.CanonicalCFG` states the form.  `Func.checkCanonicalCFG` decides it for a function whose
bodies have distinct labels, as `Func.WF` asks; `StrataDyn/CanonicalProps.lean` proves it.

## Main definitions

* `Body.Preheader`, `Body.Latch`, `Body.DedicatedExits`, `Body.LoopsSimplified`, `Body.OneExit`:
  the properties;
* `Func.CanonicalCFG`: the form;
* `Func.checkCanonicalCFG`: its decision;
* `Body.Reducible`, `Func.Reducible`: one entry per loop, and `Body.reducibleB`, its check
  against a depth-first order;
* `Body.FwdStep`: a transfer between blocks that is not a back edge;
* `Body.loopsCheckB`: the per-body check that `Canonicalize.run` makes, of both;
* `Body.loopRoles`: each loop's head, preheader and latch, by name, the loops that a front end
  records but no back edge enters included.

`Body.loopsSimplifiedFastB` and `Body.loopsCheckFastB` read each loop's blocks and the transfers
into and out of them from the body's index (`Body.Index`, `StrataDyn/BodyIndex.lean`), computed
once, so that a check of a loop costs what its blocks and their transfers cost, not what the
whole body costs.  `Body.loopsSimplifiedB_eq_fast` and `Body.loopsCheckB_eq_fast`, proved here so
that the code below and `Canonicalize.run` use them, make them run in place of
`Body.loopsSimplifiedB` and `Body.loopsCheckB`.  `Body.loopRoles_eq_fast` does the same for
`Body.loopRoles`, so the lemmas about `theOne?` that it needs are here too.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

/-- The name of the terminal operation the terminator applies. -/
@[expose] def Terminator.name : Terminator env α → Name
  | .apply _ r .. => r.name

/-- A loop's blocks by their role in the canonical form: its head, its preheader and, if a back
edge enters its head, its latch.  A recorded loop that no back edge enters, such as
`while c: return x`, has no latch. -/
structure LoopRoles where
  head : Label
  preheader : Label
  latch : Option Label
deriving DecidableEq

namespace Body

variable (bs : List (Block env α))

/-! ## The properties -/

/-- A transfer from the point `u` to the block labelled `l`. -/
@[expose] def Transfer (u : Point) (l : Label) : Prop :=
  ∃ v, Jump bs u v ∧ v.label = l

/-- The block `h` heads a loop: some back edge goes to it. -/
@[expose] def IsHead (h : Label) : Prop :=
  ∃ u, IsBackEdge bs u h

/-- The block `b` is in the loop of `h`: in the natural loop of some back edge to `h`. -/
@[expose] def InLoopOf (h : Label) (b : Block env α) : Prop :=
  ∃ u, IsBackEdge bs u h ∧ InLoop bs u h b

/-- The point `u` is in a block of the loop of `h`. -/
@[expose] def AtLoop (h : Label) (u : Point) : Prop :=
  ∃ b, b.label = u.label ∧ InLoopOf bs h b

/-- The point of the terminator of `b`. -/
@[expose] def endOf (b : Block env α) : Point := ⟨b.label, b.instrs.size⟩

/-- The block `b` ends in a plain jump to `l`: its terminator is the base's `jump`, it has no
regions, and its successors name `l`.  So nothing runs between the end of `b` and `l`. -/
@[expose] def EndsIn (b : Block env α) (l : Label) : Prop :=
  b.term.name = bn "jump" ∧ b.term.regions = #[] ∧ ∀ s ∈ b.term.succs, s.label = l

/-- The point `u` transfers to the body's exit. -/
@[expose] def Leaves (u : Point) : Prop :=
  ∃ b ∈ bs, b.label = u.label ∧ Label.exit ∈ targets b u.count

/-- (P1) `pre` is the preheader of the loop of `h`: it is outside the loop, it ends in a plain
jump to `h`, and every transfer to `h` from outside the loop leaves from
its end. -/
structure Preheader (h : Label) (pre : Block env α) : Prop where
  mem : pre ∈ bs
  outside : ¬ InLoopOf bs h pre
  endsIn : EndsIn pre h
  enters : Transfer bs (endOf pre) h
  entries : ∀ u, Transfer bs u h → ¬ AtLoop bs h u → u = endOf pre

/-- (P2) `latch` is the latch of the loop of `h`: it ends in a plain jump to `h`, and every back
edge to `h` leaves from its end. -/
structure Latch (h : Label) (latch : Block env α) : Prop where
  mem : latch ∈ bs
  endsIn : EndsIn latch h
  back : ∀ u, IsBackEdge bs u h → u = endOf latch

/-- (P3) Every block that a transfer leaves the loop of `h` for is entered only from the loop, and
no point of the loop leaves the body.  So every path out of the loop passes through such a
block. -/
@[expose] def DedicatedExits (h : Label) : Prop :=
  (∀ u l, Transfer bs u l → AtLoop bs h u → ¬ AtLoop bs h ⟨l, 0⟩ →
    ∀ w, Transfer bs w l → AtLoop bs h w) ∧
  ∀ u, AtLoop bs h u → ¬ Leaves bs u

/-- The loop of `h` has a preheader, a latch and dedicated exits. -/
@[expose] def LoopSimplified (h : Label) : Prop :=
  (∃ pre, Preheader bs h pre) ∧ (∃ latch, Latch bs h latch) ∧ DedicatedExits bs h

/-- Every loop of the body has a preheader, a latch and dedicated exits. -/
@[expose] def LoopsSimplified : Prop :=
  ∀ h, IsHead bs h → LoopSimplified bs h

/-- (F2) `post` is the body's exit block: it ends in a plain jump to the body's exit, and every
point that leaves the body is its end. -/
structure ExitBlock (post : Block env α) : Prop where
  mem : post ∈ bs
  endsIn : EndsIn post Label.exit
  exits : ∀ u, Leaves bs u → u = endOf post

/-- (F2) The body never leaves through its exit, or it has an exit block. -/
@[expose] def OneExit : Prop :=
  (∀ u, ¬ Leaves bs u) ∨ ∃ post, ExitBlock bs post

/-! ## Their decisions -/

/-- The heads of the body's loops, each once. -/
@[expose] def heads : List Label :=
  ((backEdges bs).map (·.2)).eraseDups

/-- A label is among the heads exactly when some back edge enters it. -/
theorem mem_heads {h : Label} : h ∈ heads bs ↔ ∃ u, (u, h) ∈ backEdges bs := by
  rw [heads, List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨⟨u, l⟩, he, rfl⟩
    exact ⟨u, he⟩
  · rintro ⟨u, he⟩
    exact ⟨(u, h), he, rfl⟩

/-- The labels of the loop of `h`. -/
@[expose] def loopOf (h : Label) : List Label :=
  ((backEdges bs).filter (·.2 == h)).flatMap fun e => loopBlocks bs e.1 h

/-- The block labelled `l`. -/
@[expose] def blockAt? (l : Label) : Option (Block env α) :=
  bs.find? (·.label == l)

/-- Whether `k` is the number of instructions of the block `b`, and `b` ends in a plain jump to
`l`. -/
@[expose] def _root_.Strata.Dyn.Block.endsAtB (b : Block env α) (k : Nat) (l : Label) : Bool :=
  k == b.instrs.size && b.term.name == bn "jump" && b.term.regions.isEmpty &&
    b.term.succs.all (·.label == l)

/-- Whether `u` is the end of a block that ends in a plain jump to `l`. -/
@[expose] def endsAtB (u : Point) (l : Label) : Bool :=
  (blockAt? bs u.label).any (·.endsAtB u.count l)

/-- Whether `E` holds a single point, perhaps several times, and `p` holds of it. -/
@[expose] def theOneB (E : List Point) (p : Point → Bool) : Bool :=
  match E with
  | [] => false
  | u :: us => us.all (· == u) && p u

/-- The points from outside the loop whose labels are `L` that transfer to its head `h`. -/
@[expose] def entriesFrom (L : List Label) (h : Label) : List Point :=
  ((transfers bs).filter fun (u, l) => l == h && !L.contains u.label).map (·.1)

/-- The points that back edges to `h` leave from. -/
@[expose] def backFrom (h : Label) : List Point :=
  ((backEdges bs).filter (·.2 == h)).map (·.1)

/-- The labels of the blocks that a transfer leaves the loop whose labels are `L` for. -/
@[expose] def exitTargets (L : List Label) : List Label :=
  ((transfers bs).filter fun (u, l) => L.contains u.label && !L.contains l).map (·.2)

/-- Whether the loop of `h`, whose labels are `L`, has a preheader. -/
@[expose] def preheaderB (L : List Label) (h : Label) : Bool :=
  theOneB (entriesFrom bs L h) (endsAtB bs · h)

/-- Whether the loop of `h` has a latch. -/
@[expose] def latchB (h : Label) : Bool :=
  theOneB (backFrom bs h) (endsAtB bs · h)

/-- The points that transfer to the body's exit. -/
@[expose] def exitPoints : List Point :=
  bs.flatMap fun b => (List.range (b.instrs.size + 1)).filterMap fun k =>
    if (targets b k).contains Label.exit then some ⟨b.label, k⟩ else none

/-- Whether the loop whose labels are `L` has dedicated exits. -/
@[expose] def exitsB (L : List Label) : Bool :=
  let exits := exitTargets bs L
  ((transfers bs).all fun (w, l) => !exits.contains l || L.contains w.label) &&
    (exitPoints bs).all fun u => !L.contains u.label

/-- Whether every loop of the body has a preheader, a latch and dedicated exits. -/
@[expose] def loopsSimplifiedB : Bool :=
  (heads bs).all fun h =>
    let L := loopOf bs h
    preheaderB bs L h && latchB bs h && exitsB bs L

/-- Each head of the back edges `es` with the labels of its loop, given `ls`, the natural loop of
each back edge of `es`. -/
@[expose] def tableOf (es : List (Point × Label)) (ls : List (List Label)) :
    List (Label × List Label) :=
  (es.map (·.2)).eraseDups.map fun h => (h, ((es.zip ls).filter (·.1.2 == h)).flatMap (·.2))

/-- `tableOf` of a list `es` and of `f` of each of its elements pairs each second component `h`
with the union of `f e` over the elements `e` whose second component is `h`. -/
private theorem tableOf_map (es : List (Point × Label)) (f : Point × Label → List Label) :
    tableOf es (es.map f) =
      (es.map (·.2)).eraseDups.map fun h => (h, (es.filter (·.2 == h)).flatMap f) := by
  unfold tableOf
  congr 1
  funext h
  congr 1
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases he : (e.2 == h) = true
    · simp [List.zip_cons_cons, he, ih]
    · simp [List.zip_cons_cons, he, ih]

/-- Two functions that agree on a list's elements give the same `flatMap`. -/
private theorem flatMap_congr {β γ : Type} {l : List β} {f g : β → List γ}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- Each back edge's loop, collected by head, is the loop of that head. -/
theorem tableOf_loopsOf (bs : List (Block env α)) :
    tableOf (backEdges bs) (loopsOf bs (backEdges bs)) =
      (heads bs).map fun h => (h, loopOf bs h) := by
  simp only [loopsOf, tableOf_map, heads]
  congr 1
  funext h
  congr 1
  unfold loopOf
  apply flatMap_congr
  intro e he
  rw [(beq_iff_eq.mp (List.mem_filter.mp he).2)]

/-! ## The checks with an index

`Body.Index` (`StrataDyn/BodyIndex.lean`) holds, for each label, the transfers into it and out of
its block, and each loop's labels as a set and as a list.  The checks below read them from it, so
that the check of a loop reads only its blocks, its head's incoming transfers, and the transfers
into and out of its blocks, where the simple checks scan the body's transfers for each loop. -/

namespace Index

variable (ix : Index env α)

/-- `endsAtB`, with the index's blocks by label. -/
@[expose] def endsAtB (u : Point) (l : Label) : Bool :=
  (ix.blocks.find? u.label).any (·.endsAtB u.count l)

/-- `preheaderB` of the loop of `h`, with the index. -/
@[expose] def preheaderB (h : Label) : Bool :=
  theOneB ((LabelMap.listAt ix.into h).filter fun u => !ix.inLoop h u.label) (ix.endsAtB · h)

/-- `latchB`, with the index. -/
@[expose] def latchB (h : Label) : Bool :=
  theOneB (LabelMap.listAt ix.backInto h) (ix.endsAtB · h)

/-- The labels, each once, of the blocks that a transfer leaves the labels `F` for, given
`inF`, which tells the labels of `F`. -/
@[expose] def exitsOf (F : List Label) (inF : Label → Bool) : List Label :=
  (LabelMap.dedup (F.flatMap fun x =>
    ((LabelMap.listAt ix.outOf x).filter fun t => !inF t.2).map (·.2))).2

/-- `exitsB` of the loop of `h`, with the index: every block that a transfer leaves the loop for
is entered only from the loop, and no block of the loop leaves the body. -/
@[expose] def exitsB (h : Label) : Bool :=
  (ix.exitsOf (ix.loopList h) (ix.inLoop h)).all (fun l =>
    (LabelMap.listAt ix.into l).all fun w => ix.inLoop h w.label) &&
    (ix.loopList h).all fun x => !(ix.exitAt.find? x).isSome

/-- `loopsSimplifiedB`, with the index. -/
@[expose] def loopsSimplifiedB : Bool :=
  ix.heads.all fun h => ix.preheaderB h && ix.latchB h && ix.exitsB h

end Index

/-- `loopsSimplifiedB`, with the body's index if its labels are distinct, and as defined if
not. -/
@[expose] def loopsSimplifiedFastB : Bool :=
  match tree? bs with
  | some tm => (Index.of bs tm (domInfo bs) (exitPoints bs)).loopsSimplifiedB
  | none => loopsSimplifiedB bs

end Body

end

namespace Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)} {ep : List Point}
  {ix : Index env α}

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

/-- `theOneB` gives the same answer on two lists with the same points, and two predicates that
agree. -/
private theorem theOneB_congr {E E' : List Point} {p q : Point → Bool}
    (hE : ∀ u, u ∈ E ↔ u ∈ E') (hp : ∀ u, p u = q u) : theOneB E p = theOneB E' q := by
  apply Bool.eq_iff_iff.mpr
  rw [theOneB_iff, theOneB_iff]
  constructor
  · rintro ⟨u, hu, hall, hpu⟩
    exact ⟨u, (hE u).mp hu, fun w hw => hall w ((hE w).mpr hw), hp u ▸ hpu⟩
  · rintro ⟨u, hu, hall, hpu⟩
    exact ⟨u, (hE u).mpr hu, fun w hw => hall w ((hE w).mp hw), (hp u).symm ▸ hpu⟩

/-- A label is in the loop of `h` exactly when it is in the natural loop of some back edge to
`h`. -/
public theorem mem_loopOf {h x : Label} :
    x ∈ loopOf bs h ↔ ∃ u, (u, h) ∈ backEdges bs ∧ x ∈ loopBlocks bs u h := by
  simp only [loopOf, List.mem_flatMap, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨u, l⟩, ⟨he, rfl⟩, hx⟩
    exact ⟨u, he, hx⟩
  · rintro ⟨u, he, hx⟩
    exact ⟨(u, h), ⟨he, rfl⟩, hx⟩

/-- The index tells the labels of each loop as `loopOf` lists them. -/
public theorem Index.inLoop_eq (hs : ix.Spec bs ep) (h x : Label) :
    ix.inLoop h x = (loopOf bs h).contains x := by
  apply Bool.eq_iff_iff.mpr
  rw [hs.inLoop, List.contains_iff_mem, mem_loopOf]

/-- The index lists the labels of each loop as `loopOf` does. -/
public theorem Index.mem_loopList (hs : ix.Spec bs ep) {h x : Label} :
    x ∈ ix.loopList h ↔ x ∈ loopOf bs h := by
  rw [hs.loopList, mem_loopOf]

/-- `exitsOf F inF` lists the labels of the blocks that a transfer from a label of `F` goes to,
when that label is not one of `F`, given `inF`, which tells the labels of `F`. -/
public theorem Index.mem_exitsOf (hs : ix.Spec bs ep) {F : List Label} {inF : Label → Bool}
    (hF : ∀ x, x ∈ F ↔ inF x = true) {l : Label} :
    l ∈ ix.exitsOf F inF ↔ ∃ u, (u, l) ∈ transfers bs ∧ inF u.label = true ∧ inF l = false := by
  simp only [Index.exitsOf, LabelMap.mem_dedup, List.mem_flatMap, List.mem_map, List.mem_filter,
    hs.outOf, Bool.not_eq_true']
  constructor
  · rintro ⟨x, hx, ⟨u, l'⟩, ⟨⟨ht, rfl⟩, hl⟩, rfl⟩
    exact ⟨u, ht, (hF _).mp hx, hl⟩
  · rintro ⟨u, ht, hu, hl⟩
    exact ⟨u.label, (hF _).mpr hu, (u, l), ⟨⟨ht, rfl⟩, hl⟩, rfl⟩

/-- The index's `endsAtB` is `endsAtB`. -/
public theorem Index.endsAtB_eq (hs : ix.Spec bs ep) (u : Point) (l : Label) :
    ix.endsAtB u l = Body.endsAtB bs u l := by
  rw [Index.endsAtB, Body.endsAtB, blockAt?, hs.blocks]

/-- The index's `preheaderB` is `preheaderB` of the loop of `h`. -/
public theorem Index.preheaderB_eq (hs : ix.Spec bs ep) (h : Label) :
    ix.preheaderB h = Body.preheaderB bs (loopOf bs h) h := by
  unfold Index.preheaderB Body.preheaderB entriesFrom
  apply theOneB_congr _ (fun u => Index.endsAtB_eq hs u h)
  intro u
  simp only [List.mem_filter, List.mem_map, hs.into, Index.inLoop_eq hs, Bool.and_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨ht, hL⟩
    exact ⟨(u, h), ⟨ht, rfl, hL⟩, rfl⟩
  · rintro ⟨⟨u', l⟩, ⟨ht, rfl, hL⟩, rfl⟩
    exact ⟨ht, hL⟩

/-- The index's `latchB` is `latchB`. -/
public theorem Index.latchB_eq (hs : ix.Spec bs ep) (h : Label) :
    ix.latchB h = Body.latchB bs h := by
  unfold Index.latchB Body.latchB backFrom
  apply theOneB_congr _ (fun u => Index.endsAtB_eq hs u h)
  intro u
  simp only [List.mem_map, List.mem_filter, hs.backInto, beq_iff_eq]
  constructor
  · exact fun he => ⟨(u, h), ⟨he, rfl⟩, rfl⟩
  · rintro ⟨⟨u', l⟩, ⟨he, rfl⟩, rfl⟩
    exact he

/-- The index's `exitsB` is `exitsB` of the loop of `h`, with the points `ep` that leave the
body. -/
private theorem Index.exitsB_eq (hs : ix.Spec bs (exitPoints bs)) (h : Label) :
    ix.exitsB h = Body.exitsB bs (loopOf bs h) := by
  have hF : ∀ x, x ∈ ix.loopList h ↔ ix.inLoop h x = true := fun x => by
    rw [Index.mem_loopList hs, Index.inLoop_eq hs, List.contains_iff_mem]
  have hexits : ∀ l, l ∈ exitTargets bs (loopOf bs h) ↔
      l ∈ ix.exitsOf (ix.loopList h) (ix.inLoop h) := by
    intro l
    rw [Index.mem_exitsOf hs hF]
    simp only [exitTargets, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
      Index.inLoop_eq hs]
    constructor
    · rintro ⟨⟨u, l'⟩, ⟨ht, hu, hl⟩, rfl⟩
      exact ⟨u, ht, hu, hl⟩
    · rintro ⟨u, ht, hu, hl⟩
      exact ⟨(u, l), ⟨ht, hu, hl⟩, rfl⟩
  have h₁ : (ix.exitsOf (ix.loopList h) (ix.inLoop h)).all (fun l =>
      (LabelMap.listAt ix.into l).all fun w => ix.inLoop h w.label) =
      (transfers bs).all fun p =>
        !(exitTargets bs (loopOf bs h)).contains p.2 || (loopOf bs h).contains p.1.label := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hall
      apply List.all_eq_true.mpr
      intro ⟨w, l⟩ hw
      cases hc : (exitTargets bs (loopOf bs h)).contains l
      · rfl
      · have hl := (hexits l).mp (List.contains_iff_mem.mp hc)
        have hw' := List.all_eq_true.mp (List.all_eq_true.mp hall l hl) w ((hs.into l w).mpr hw)
        rw [Index.inLoop_eq hs] at hw'
        rw [hw']
        rfl
    · intro hall
      apply List.all_eq_true.mpr
      intro l hl
      apply List.all_eq_true.mpr
      intro w hw
      have hw' := List.all_eq_true.mp hall (w, l) ((hs.into l w).mp hw)
      have hc : l ∈ exitTargets bs (loopOf bs h) := (hexits l).mpr hl
      rw [Index.inLoop_eq hs]
      simpa [hc] using hw'
  have h₂ : ((ix.loopList h).all fun x => !(ix.exitAt.find? x).isSome) =
      (exitPoints bs).all fun u => !(loopOf bs h).contains u.label := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hall
      apply List.all_eq_true.mpr
      intro u hu
      cases hc : (loopOf bs h).contains u.label
      · rfl
      · have hx := (Index.mem_loopList hs).mpr (List.contains_iff_mem.mp hc)
        have hu' := List.all_eq_true.mp hall u.label hx
        have he : (ix.exitAt.find? u.label).isSome = true := (hs.exitAt u.label).mpr ⟨u, hu, rfl⟩
        simp [he] at hu'
    · intro hall
      apply List.all_eq_true.mpr
      intro x hx
      cases hc : (ix.exitAt.find? x).isSome
      · rfl
      · obtain ⟨u, hu, rfl⟩ := (hs.exitAt _).mp hc
        have hu' := List.all_eq_true.mp hall u hu
        exact absurd ((Index.mem_loopList hs).mp hx) (by simpa using hu')
  unfold Index.exitsB Body.exitsB
  rw [h₁, h₂]

/-- The index's `loopsSimplifiedB` is `loopsSimplifiedB`. -/
private theorem Index.loopsSimplifiedB_eq (hs : ix.Spec bs (exitPoints bs)) :
    ix.loopsSimplifiedB = Body.loopsSimplifiedB bs := by
  unfold Index.loopsSimplifiedB Body.loopsSimplifiedB
  refine all_eq_of_mem_iff (fun h => ?_) (fun h => ?_)
  · rw [hs.heads, Body.mem_heads]
  · rw [Index.preheaderB_eq hs, Index.latchB_eq hs, Index.exitsB_eq hs]

/-- The fast check gives the same answer as `loopsSimplifiedB` on every body.  It is proved here,
before `Func.checkCanonicalCFG` uses the check, because a `@[csimp]` lemma replaces a definition
only in code compiled after it. -/
@[csimp] public theorem loopsSimplifiedB_eq_fast :
    @loopsSimplifiedB = @loopsSimplifiedFastB := by
  funext env α bs
  unfold loopsSimplifiedFastB
  split
  next tm ht => exact (Index.loopsSimplifiedB_eq (Index.spec_of ht _)).symm
  next => rfl

end Body

public section

variable {env : Env Unit} {α : Type}

namespace Body

variable (bs : List (Block env α))

/-- Whether the body never leaves through its exit, or has an exit block. -/
@[expose] def oneExitB : Bool :=
  (exitPoints bs).isEmpty || theOneB (exitPoints bs) (endsAtB bs · Label.exit)

/-! ## Each loop's blocks by role -/

/-- The one point of `E`, if `E` holds a single point, perhaps several times. -/
@[expose] def theOne? (E : List Point) : Option Point :=
  match E with
  | [] => none
  | u :: us => if us.all (· == u) then some u else none

/-- The roles of the loop at the block labelled `h`, given `isRec`, which tells the heads that a
front end records.  If `h` heads a loop of the CFG, its preheader is the block of the one point
outside the loop that transfers to `h`, and its latch the block of the one point that a back edge
to `h` leaves from.  If no back edge enters `h` and `isRec h` holds, its preheader is the block of
the one point that transfers to `h`, and it has no latch.  Each block it names must end in a plain
jump to `h`; otherwise there are none. -/
@[expose] def rolesAt (isRec : Label → Bool) (h : Label) : Option LoopRoles :=
  if (heads bs).contains h then
    match theOne? (entriesFrom bs (loopOf bs h) h), theOne? (backFrom bs h) with
    | some pre, some latch =>
      if endsAtB bs pre h && endsAtB bs latch h then some ⟨h, pre.label, some latch.label⟩
      else none
    | _, _ => none
  else if isRec h then
    match theOne? (entriesFrom bs (loopOf bs h) h) with
    | some pre => if endsAtB bs pre h then some ⟨h, pre.label, none⟩ else none
    | none => none
  else none

/-- Each loop of the body, in the order of its heads' blocks, with its preheader and its latch
(`rolesAt`): every loop of the CFG, and every loop at a head that `isRec` tells, the heads that a
front end records, that no back edge enters.  A loop whose blocks do not have these roles is left
out.  Each entry names the right blocks (`Body.mem_loopRoles`), and in a body whose loops have a
preheader and a latch every loop of the CFG has its entry (`Body.loopRoles_complete`), and so has
every recorded head that has a preheader, as the head of every record that the loop exits check
accepts does (`Body.loopRoles_complete_record`).  So a stage that places obligations reads each
block by its role.  `isRec` should cost one lookup, such as a label set built once per
function. -/
@[expose] def loopRoles (isRec : Label → Bool) : List LoopRoles :=
  bs.filterMap fun b => rolesAt bs isRec b.label

namespace Index

variable (ix : Index env α)

/-- `rolesAt`, with the index. -/
@[expose] def rolesAt (isRec : Label → Bool) (h : Label) : Option LoopRoles :=
  if ix.isHead h then
    match theOne? ((LabelMap.listAt ix.into h).filter fun u => !ix.inLoop h u.label),
        theOne? (LabelMap.listAt ix.backInto h) with
    | some pre, some latch =>
      if ix.endsAtB pre h && ix.endsAtB latch h then some ⟨h, pre.label, some latch.label⟩
      else none
    | _, _ => none
  else if isRec h then
    match theOne? (LabelMap.listAt ix.into h) with
    | some pre => if ix.endsAtB pre h then some ⟨h, pre.label, none⟩ else none
    | none => none
  else none

end Index

/-- `loopRoles`, read from the body's index, so that each block costs what the transfers into it
cost; as defined when two blocks share a label. -/
@[expose] def loopRolesFastB (isRec : Label → Bool) : List LoopRoles :=
  match tree? bs with
  | some tm =>
    let ix := Index.of bs tm (domInfo bs) (exitPoints bs)
    bs.filterMap fun b => ix.rolesAt isRec b.label
  | none => loopRoles bs isRec

end Body

end

namespace Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)} {ep : List Point}
  {ix : Index env α}

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

/-- `theOne?` gives the same answer on two lists with the same points. -/
private theorem theOne?_congr {E E' : List Point} (hE : ∀ u, u ∈ E ↔ u ∈ E') :
    theOne? E = theOne? E' := by
  cases h : theOne? E' with
  | none =>
    cases h' : theOne? E with
    | none => rfl
    | some u =>
      obtain ⟨hu, hall⟩ := theOne?_eq_some.mp h'
      exact absurd (theOne?_eq_some.mpr ⟨(hE u).mp hu, fun w hw => hall w ((hE w).mpr hw)⟩)
        (by rw [h]; simp)
  | some u =>
    obtain ⟨hu, hall⟩ := theOne?_eq_some.mp h
    exact theOne?_eq_some.mpr ⟨(hE u).mpr hu, fun w hw => hall w ((hE w).mp hw)⟩

/-- The index's `rolesAt` is `rolesAt`. -/
private theorem Index.rolesAt_eq (hs : ix.Spec bs ep) (isRec : Label → Bool) (h : Label) :
    ix.rolesAt isRec h = Body.rolesAt bs isRec h := by
  have hhead : ix.isHead h = (Body.heads bs).contains h := by
    apply Bool.eq_iff_iff.mpr
    rw [hs.isHead, List.contains_iff_mem, mem_heads]
  have hentries : theOne? ((LabelMap.listAt ix.into h).filter fun u => !ix.inLoop h u.label) =
      theOne? (entriesFrom bs (loopOf bs h) h) := by
    apply theOne?_congr
    intro u
    simp only [entriesFrom, List.mem_filter, List.mem_map, hs.into, Index.inLoop_eq hs,
      Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨ht, hL⟩
      exact ⟨(u, h), ⟨ht, rfl, hL⟩, rfl⟩
    · rintro ⟨⟨u', l⟩, ⟨ht, rfl, hL⟩, rfl⟩
      exact ⟨ht, hL⟩
  have hback : theOne? (LabelMap.listAt ix.backInto h) = theOne? (backFrom bs h) := by
    apply theOne?_congr
    intro u
    simp only [backFrom, List.mem_map, List.mem_filter, hs.backInto, beq_iff_eq]
    constructor
    · exact fun he => ⟨(u, h), ⟨he, rfl⟩, rfl⟩
    · rintro ⟨⟨u', l⟩, ⟨he, rfl⟩, rfl⟩
      exact he
  unfold Index.rolesAt Body.rolesAt
  rw [hhead, hentries, hback]
  split
  · simp only [Index.endsAtB_eq hs]
  · rename_i hnh
    have hall : theOne? (LabelMap.listAt ix.into h) = theOne? (entriesFrom bs (loopOf bs h) h) := by
      rw [← hentries]
      congr 1
      symm
      apply List.filter_eq_self.mpr
      intro u _
      have hno : ix.inLoop h u.label = false := by
        cases hl : ix.inLoop h u.label with
        | false => rfl
        | true =>
          obtain ⟨w, hw, -⟩ := (hs.inLoop h u.label).mp hl
          exact absurd (List.contains_iff_mem.mpr ((mem_heads bs).mpr ⟨w, hw⟩)) hnh
      simp [hno]
    rw [hall]
    split <;> simp only [Index.endsAtB_eq hs]

/-- The fast version gives the same list as `loopRoles` on every body, so that it runs in its
place. -/
@[csimp] public theorem loopRoles_eq_fast : @loopRoles = @loopRolesFastB := by
  funext env α bs isRec
  unfold loopRolesFastB
  split
  next tm ht =>
    have hs := Index.spec_of ht (exitPoints bs)
    unfold loopRoles
    congr 1
    funext b
    exact (Index.rolesAt_eq hs isRec b.label).symm
  next => rfl

end Body

public section

variable {env : Env Unit} {α : Type}

namespace Body

variable (bs : List (Block env α))

/-! ## One entry per loop -/

/-- Every loop of the body has one entry: some rank of the labels goes up along every transfer
that is not a back edge.  So every cycle of the body passes through a back edge, and a loop is
entered only through its head. -/
@[expose] def Reducible : Prop :=
  ∃ rank : Label → Nat, ∀ u l, Transfer bs u l → ¬ IsBackEdge bs u l → rank u.label < rank l

/-- The position of each label of `ord`. -/
@[expose] def rankIn (ord : List Label) : LabelMap Nat :=
  ord.zipIdx.foldl (init := ∅) fun m p => m.insert p.1 p.2

/-- The points that back edges leave from, by the label of their target. -/
@[expose] def backBy (be : List (Point × Label)) : LabelMap (List Point) :=
  be.foldl (init := ∅) fun m e => m.insert e.2 (e.1 :: (m.find? e.2).getD [])

/-- Whether every transfer of `tr` that is not one of the back edges `be` goes up in the order
`ord`. -/
@[expose] def reducibleIn (be tr : List (Point × Label)) (ord : List Label) : Bool :=
  let rank := rankIn ord
  let back := backBy be
  tr.all fun (u, l) =>
    ((back.find? l).getD []).contains u ||
      decide ((rank.find? u.label).getD 0 < (rank.find? l).getD 0)

/-- Whether every transfer that is not a back edge goes up in the order `ord`. -/
@[expose] def reducibleWithB (ord : List Label) : Bool :=
  reducibleIn (backEdges bs) (transfers bs) ord

/-- Whether every loop of the body has one entry, checked against the order of the depth-first
search, which is not trusted: the check confirms it. -/
@[expose] def reducibleB : Bool :=
  reducibleWithB bs (rpoLabels bs)

/-- A transfer from block `a` to block `b` that is not a back edge. -/
@[expose] def FwdStep (a b : Label) : Prop :=
  ∃ u : Point, u.label = a ∧ Transfer bs u b ∧ ¬ IsBackEdge bs u b

/-- Whether every loop of the body has a preheader, a latch and dedicated exits, and one entry:
the per-body check of `Canonicalize.run`. -/
@[expose] def loopsCheckB : Bool :=
  loopsSimplifiedB bs && reducibleB bs

/-- `loopsCheckB`, with the body's index if its labels are distinct, so that the back edges and
the transfers are computed once for both checks, and as defined if not. -/
@[expose] def loopsCheckFastB : Bool :=
  match tree? bs with
  | some tm =>
    let ix := Index.of bs tm (domInfo bs) (exitPoints bs)
    ix.loopsSimplifiedB && reducibleIn ix.be ix.tr (rpoLabels bs)
  | none => loopsCheckB bs

/-- The fast check gives the same answer as `loopsCheckB` on every body.  It is proved here, before
any code uses the check, because a `@[csimp]` lemma replaces a definition only in code compiled
after it. -/
@[csimp] theorem loopsCheckB_eq_fast : @loopsCheckB = @loopsCheckFastB := by
  funext env α bs
  unfold loopsCheckFastB
  split
  next tm ht =>
    have hs := Index.spec_of ht (exitPoints bs)
    dsimp only
    rw [loopsCheckB, Index.loopsSimplifiedB_eq hs, reducibleB, reducibleWithB, hs.tr, hs.be]
  next => rfl

end Body

/-- Every loop in every body of the function has one entry. -/
@[expose] def Func.Reducible (fn : Func env α) : Prop :=
  Body.Every Body.Reducible fn.blocks.toList

/-- The function is canonical: in each of its bodies every loop has a preheader, a latch and
dedicated exits, and its own body leaves through its exit from at most one block. -/
@[expose] def Func.CanonicalCFG (fn : Func env α) : Prop :=
  Body.Every Body.LoopsSimplified fn.blocks.toList ∧ Body.OneExit fn.blocks.toList

/-- Whether the function is canonical, for a function whose bodies have distinct labels. -/
@[expose] def Func.checkCanonicalCFG (fn : Func env α) : Bool :=
  Body.everyB Body.loopsSimplifiedB fn.blocks.toList && Body.oneExitB fn.blocks.toList

end

end Strata.Dyn
