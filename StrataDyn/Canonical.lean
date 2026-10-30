/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.EveryBody
public import StrataDyn.LoopsFast
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

The loop of a head `h` is the union of the natural loops of its back edges
(`StrataDyn/Loops.lean`), as in LLVM.  Its code that cannot repeat the loop, such as the code
after a `break`, is not in it.  The loop properties hold in every body of the function, its own
and each region's (`Body.Every`); F2 holds in its own body.  The form does not ask for the loops
to be reducible: a cycle with no back edge has no head, so no loop property mentions it.
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
* `Body.loopRoles`: each loop's head, preheader and latch, by name.

`Body.loopsSimplifiedFastB` and `Body.loopsCheckFastB` compute each body's loops, transfers and
back edges once.  `Body.loopsSimplifiedB_eq_fast` and `Body.loopsCheckB_eq_fast`, proved here so
that the code below and `Canonicalize.run` use them, make them run in place of
`Body.loopsSimplifiedB` and `Body.loopsCheckB`.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

/-- The name of the terminal operation the terminator applies. -/
@[expose] def Terminator.name : Terminator env α → Name
  | .apply _ r .. => r.name

/-- A loop's blocks by their role in the canonical form: its head, its preheader and its
latch. -/
structure LoopRoles where
  head : Label
  preheader : Label
  latch : Label
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

/-- The labels of the loop of `h`. -/
@[expose] def loopOf (h : Label) : List Label :=
  ((backEdges bs).filter (·.2 == h)).flatMap fun e => loopBlocks bs e.1 h

/-- The block labelled `l`. -/
@[expose] def blockAt? (l : Label) : Option (Block env α) :=
  bs.find? (·.label == l)

/-- Whether `u` is the end of a block that ends in a plain jump to `l`. -/
@[expose] def endsAtB (u : Point) (l : Label) : Bool :=
  (blockAt? bs u.label).any fun b =>
    u.count == b.instrs.size && b.term.name == bn "jump" && b.term.regions.isEmpty &&
      b.term.succs.all (·.label == l)

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

/-- `loopsSimplifiedB`, given the body's back edges `be`, transfers `tr` and exit points `ep`. -/
@[expose] def loopsSimplifiedWith (be : List (Point × Label)) (tr : List (Point × Label))
    (ep : List Point) : Bool :=
  (tableOf be (loopsOf bs be)).all fun (h, L) =>
    theOneB ((tr.filter fun (u, l) => l == h && !L.contains u.label).map (·.1))
        (endsAtB bs · h) &&
      theOneB ((be.filter (·.2 == h)).map (·.1)) (endsAtB bs · h) &&
      (let exits := (tr.filter fun (u, l) => L.contains u.label && !L.contains l).map (·.2)
       (tr.all fun (w, l) => !exits.contains l || L.contains w.label) &&
         ep.all fun u => !L.contains u.label)

/-- `loopsSimplifiedB`, with the back edges, the transfers, the exit points and every loop
computed once for the body. -/
@[expose] def loopsSimplifiedFastB : Bool :=
  loopsSimplifiedWith bs (backEdges bs) (transfers bs) (exitPoints bs)

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

/-- The fast check gives the same answer as `loopsSimplifiedB` on every body.  It is proved here,
before `Func.checkCanonicalCFG` uses the check, because a `@[csimp]` lemma replaces a definition
only in code compiled after it. -/
@[csimp] theorem loopsSimplifiedB_eq_fast :
    @loopsSimplifiedB = @loopsSimplifiedFastB := by
  funext env α bs
  unfold loopsSimplifiedB loopsSimplifiedFastB loopsSimplifiedWith
  simp only [tableOf_loopsOf, List.all_map]
  rfl

/-- Whether the body never leaves through its exit, or has an exit block. -/
@[expose] def oneExitB : Bool :=
  (exitPoints bs).isEmpty || theOneB (exitPoints bs) (endsAtB bs · Label.exit)

/-! ## Each loop's blocks by role -/

/-- The one point of `E`, if `E` holds a single point, perhaps several times. -/
@[expose] def theOne? (E : List Point) : Option Point :=
  match E with
  | [] => none
  | u :: us => if us.all (· == u) then some u else none

/-- Each loop of the body, with its preheader and its latch, in the order of `heads`: the block of
the one point outside the loop that transfers to the head, and the block of the one point that a
back edge to it leaves from.  A loop without such single points is left out.  In a body whose
loops have a preheader and a latch, every loop has its entry, and each entry names them
(`Body.mem_loopRoles`, `Body.loopRoles_complete`), so a stage that places obligations reads each
block by its role. -/
@[expose] def loopRoles : List LoopRoles :=
  (heads bs).filterMap fun h =>
    match theOne? (entriesFrom bs (loopOf bs h) h), theOne? (backFrom bs h) with
    | some pre, some latch => some ⟨h, pre.label, latch.label⟩
    | _, _ => none

/-- `loopRoles`, given the body's back edges `be` and transfers `tr`, with every loop computed
once from them. -/
@[expose] def loopRolesWith (be tr : List (Point × Label)) : List LoopRoles :=
  (tableOf be (loopsOf bs be)).filterMap fun (h, L) =>
    match theOne? ((tr.filter fun (u, l) => l == h && !L.contains u.label).map (·.1)),
        theOne? ((be.filter (·.2 == h)).map (·.1)) with
    | some pre, some latch => some ⟨h, pre.label, latch.label⟩
    | _, _ => none

/-- `loopRoles`, with the back edges, the transfers and every loop computed once for the body. -/
@[expose] def loopRolesFastB : List LoopRoles :=
  loopRolesWith bs (backEdges bs) (transfers bs)

/-- The fast version gives the same list as `loopRoles` on every body, so that it runs in its
place. -/
@[csimp] theorem loopRoles_eq_fast : @loopRoles = @loopRolesFastB := by
  funext env α bs
  unfold loopRoles loopRolesFastB loopRolesWith
  simp only [tableOf_loopsOf, List.filterMap_map]
  rfl

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

/-- `loopsCheckB`, with the back edges and the transfers computed once for both checks. -/
@[expose] def loopsCheckFastB : Bool :=
  let be := backEdges bs
  let tr := transfers bs
  loopsSimplifiedWith bs be tr (exitPoints bs) && reducibleIn be tr (rpoLabels bs)

/-- The fast check gives the same answer as `loopsCheckB` on every body.  It is proved here, before
any code uses the check, because a `@[csimp]` lemma replaces a definition only in code compiled
after it. -/
@[csimp] theorem loopsCheckB_eq_fast : @loopsCheckB = @loopsCheckFastB := by
  funext env α bs
  simp only [loopsCheckB, loopsCheckFastB, loopsSimplifiedB_eq_fast, loopsSimplifiedFastB,
    reducibleB, reducibleWithB]

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
