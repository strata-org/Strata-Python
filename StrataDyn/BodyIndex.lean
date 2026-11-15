/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.LoopsFast
import all StrataDyn.Loops
import all StrataDyn.LoopsProps
import all StrataDyn.LoopsFast
import all StrataDyn.DomCheck
import all StrataDyn.DomProps
import all StrataDyn.Util.LabelMapProps
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# A body's transfers and loops, by label

The checks of the canonical form (`StrataDyn/Canonical.lean`, `StrataDyn/LoopExits.lean`) ask,
for each loop, about the transfers into its head, out of its blocks, and into the blocks it leaves
for.  Their simple definitions scan the body's whole list of transfers for each loop.  A
`Body.Index` holds, computed once per body, a map from each label to each of those kinds of
transfers, and the labels of each loop as a set and as a list.  So a fast check of a loop reads
only the blocks of the loop and the transfers into and out of them.

`Body.Index.Spec` states what each field holds, in terms of the body's `transfers`, `backEdges`
and `loopBlocks` (`StrataDyn/Loops.lean`).  The fast checks are proved equal to the simple ones
from it alone.

## Main definitions

* `LabelMap.groupBy`, `LabelMap.listAt`: the values of a list, grouped under a label;
* `LabelMap.setOf`, `LabelMap.dedup`: the labels of a list as a set, and each once, as a set and
  as a list;
* `Body.Index`, `Body.Index.of`: what the fast checks read, and its computation;
* `Body.Index.Spec`: what each field of an index holds.

`StrataDyn/BodyIndexProps.lean` proves that `Body.Index.of` gives an index that holds the spec.
-/

namespace Strata.Dyn

public section

namespace LabelMap

variable {β γ : Type}

/-- The values that `m` lists for `l`, or none. -/
@[expose] def listAt (m : LabelMap (List β)) (l : Label) : List β :=
  (m.find? l).getD []

/-- For each element `x` of `xs`, `val x` under the label `key x`. -/
@[expose] def groupBy (key : γ → Label) (val : γ → β) (xs : List γ) : LabelMap (List β) :=
  xs.foldl (init := ∅) fun m x => m.update (key x) fun o => val x :: o.getD []

/-- The labels of `ls`, as a set. -/
@[expose] def setOf (ls : List Label) : LabelMap Unit :=
  ls.foldl (fun m l => m.insert l ()) ∅

/-- The labels of `ls`, each once, as a set and as a list. -/
@[expose] def dedup (ls : List Label) : LabelMap Unit × List Label :=
  ls.foldl (init := (∅, [])) fun p l =>
    if (p.1.find? l).isSome then p else (p.1.insert l (), l :: p.2)

end LabelMap

namespace Body

variable {env : Env Unit} {α : Type}

/-- What the fast checks of the canonical form read about a body, computed once: its number of
blocks, its transfers, what decides dominance in it, and its back edges; its blocks by label; for
each label, the points that transfer to it, the transfers from its block, and the labels its
block transfers to; for each head, the points that back edges to it leave from; the heads, each
once; for each head, the labels of its loop as a set and as a list; for each label, the heads
whose loop holds it; and the labels of the points that leave the body. -/
structure Index (env : Env Unit) (α : Type) where
  size : Nat
  tr : List (Point × Label)
  info : Option (LabelMap (Block env α) × Tree × AncMap × Nat)
  be : List (Point × Label)
  blocks : LabelMap (Block env α)
  into : LabelMap (List Point)
  outOf : LabelMap (List (Point × Label))
  succ : LabelMap (List Label)
  backInto : LabelMap (List Point)
  heads : List Label
  loops : LabelMap (LabelMap Unit × List Label)
  around : LabelMap (List Label)
  exitAt : LabelMap Unit

/-- The labels that `loops` lists for the loop of `h`, or none. -/
@[expose] def loopListIn (loops : LabelMap (LabelMap Unit × List Label)) (h : Label) :
    List Label :=
  match loops.find? h with
  | some (_, ls) => ls
  | none => []

namespace Index

variable (ix : Index env α)

/-- Whether `h` heads a loop. -/
@[expose] def isHead (h : Label) : Bool :=
  (ix.loops.find? h).isSome

/-- Whether the label `x` is in the loop of `h`. -/
@[expose] def inLoop (h x : Label) : Bool :=
  match ix.loops.find? h with
  | some (s, _) => (s.find? x).isSome
  | none => false

/-- The labels of the loop of `h`, each once. -/
@[expose] def loopList (h : Label) : List Label :=
  loopListIn ix.loops h

end Index

/-- `loopSeed` of a back edge from `u` to `h`, whose source is always a point of the body:
`u`'s block, unless it is `h`. -/
@[expose] def backSeed (u : Point) (h : Label) : List Label :=
  if u.label != h then [u.label] else []

/-- The search of `searchLoop`, with at most `fuel` steps, for the natural loop of the back edge
from `u` to `h`, with the predecessor map `pm`. -/
@[expose] def loopSearch (pm : LabelMap (List Label)) (fuel : Nat) (u : Point) (h : Label) :
    Search :=
  let seed := backSeed u h
  search pm h fuel ⟨seed, seed.foldl (fun m l => m.insert l ()) ∅, seed⟩

/-- The labels of the loop of `h`, each once, as a set and as a list, given the blocks by label
`tm`, the predecessor map `pm`, the fuel of the search, and `us`, the points that back edges to
`h` leave from. -/
@[expose] def loopData (tm : LabelMap (Block env α)) (pm : LabelMap (List Label)) (fuel : Nat)
    (h : Label) (us : List Point) : LabelMap Unit × List Label :=
  LabelMap.dedup ((h :: us.flatMap fun u => (loopSearch pm fuel u h).found).filter
    fun x => (tm.find? x).isSome)

/-- `edgeMap`, given the body's transfers `tr`. -/
@[expose] def edgeMapIn (tr : List (Point × Label)) (key val : Point × Label → Label) :
    LabelMap (List Label) :=
  tr.foldl (init := ∅) fun m p => m.insert (key p) (val p :: (m.find? (key p)).getD [])

variable (bs : List (Block env α))

/-- `backEdgesFast`, given the body's transfers `tr` and `info`, which decides dominance in the
body. -/
@[expose] def backEdgesIn (tr : List (Point × Label))
    (info : Option (LabelMap (Block env α) × Tree × AncMap × Nat)) : List (Point × Label) :=
  eraseDupsHash (tr.filter fun (u, l) => domWith bs info u l)

/-- The index of the body, given its blocks by label `tm`, `info`, which decides dominance in
it, and `ep`, the points that leave it. -/
@[expose] def Index.of (tm : LabelMap (Block env α))
    (info : Option (LabelMap (Block env α) × Tree × AncMap × Nat)) (ep : List Point) :
    Index env α :=
  let n := bs.length
  let tr := transfers bs
  let be := backEdgesIn bs tr info
  let backInto := LabelMap.groupBy (·.2) (·.1) be
  let heads := (LabelMap.dedup (be.map (·.2))).2
  let pm := edgeMapIn tr (·.2) (·.1.label)
  let loops : LabelMap (LabelMap Unit × List Label) := heads.foldl (init := ∅) fun m h =>
    m.insert h (loopData tm pm n h (LabelMap.listAt backInto h))
  { size := n, tr, info, be, blocks := tm, backInto, heads, loops
    into := LabelMap.groupBy (·.2) (·.1) tr
    outOf := LabelMap.groupBy (·.1.label) id tr
    succ := edgeMapIn tr (·.1.label) (·.2)
    around := LabelMap.groupBy (·.1) (·.2) (heads.flatMap fun h =>
      (loopListIn loops h).map fun x => (x, h))
    exitAt := ep.foldl (init := ∅) fun m u => m.insert u.label () }

/-- What each field of the index `ix` of the body holds, given `ep`, the points that leave it. -/
structure Index.Spec (ep : List Point) (ix : Index env α) : Prop where
  size : ix.size = bs.length
  tr : ix.tr = transfers bs
  info : ix.info = domInfo bs
  be : ix.be = backEdges bs
  blocks : ∀ l, ix.blocks.find? l = bs.find? (·.label == l)
  into : ∀ l u, u ∈ LabelMap.listAt ix.into l ↔ (u, l) ∈ transfers bs
  outOf : ∀ x t, t ∈ LabelMap.listAt ix.outOf x ↔ t ∈ transfers bs ∧ t.1.label = x
  succ : ix.succ = succMap bs
  backInto : ∀ h u, u ∈ LabelMap.listAt ix.backInto h ↔ (u, h) ∈ backEdges bs
  heads : ∀ h, h ∈ ix.heads ↔ ∃ u, (u, h) ∈ backEdges bs
  isHead : ∀ h, ix.isHead h = true ↔ ∃ u, (u, h) ∈ backEdges bs
  inLoop : ∀ h x, ix.inLoop h x = true ↔ ∃ u, (u, h) ∈ backEdges bs ∧ x ∈ loopBlocks bs u h
  loopList : ∀ h x, x ∈ ix.loopList h ↔ ∃ u, (u, h) ∈ backEdges bs ∧ x ∈ loopBlocks bs u h
  around : ∀ x h, h ∈ LabelMap.listAt ix.around x ↔
    ∃ u, (u, h) ∈ backEdges bs ∧ x ∈ loopBlocks bs u h
  exitAt : ∀ x, (ix.exitAt.find? x).isSome ↔ ∃ u ∈ ep, u.label = x

end Body

end

end Strata.Dyn
