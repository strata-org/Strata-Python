/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Dom
public import StrataMantle.Util.LabelMap
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Checking a tree

`Body.checkScopedBy` decides `Body.ScopedBy` (`StrataMantle/Dom.lean`): that a given tree of a
body is legal and puts every use of the body in scope.  `StrataMantle/DomProps.lean` proves it
correct.  Each Boolean `foo` here decides the `Foo` of `Dom.lean`: `legal` decides `Legal`,
`node` decides `Node`.  Its maps are tries, and it walks a tree with fuel, the body's block count.

For each body it builds the blocks by label once (`Body.tree?`), failing if a label repeats.
Every rule is about a block's chain up the tree (`Body.chain`): the block at a count, then its
parent at the parent's count, and so on.  A block's chain reaches the root, a transfer's target
has its parent on the chain of the point the transfer leaves from, and a value is in scope at
a point if it is defined along the point's chain.

To walk each chain at most once, the checker builds two maps per body.
`Body.ancs` has, for each block, the blocks above its start, each with the latest count of the
block's chain in it.  Each block's entry extends its parent's, and the map is a persistent
trie, so the entries share structure.  `Body.defs` has, for each value, the points that define
it.  A transfer is legal if its target's parent is above the point it leaves from, and a use is
in scope if one of its value's definitions is above it, each looked up in the maps.  For a
block the ancestor map lacks, which happens only under a tree that is not legal, the checker
walks the block's chain instead (`Body.above`).

The decision of `Func.WF`'s scoping (`StrataMantle/DomDecide.lean`) checks uses the same way,
against the tree it computes.
-/

namespace Strata.Mantle

public section

variable {env : Env Unit} {α : Type}

/-- `p` is `q` or an earlier point of its block. -/
@[expose] def Point.le (p q : Point) : Bool :=
  decide (p.label = q.label) && decide (p.count ≤ q.count)

namespace Body

/-- A body's blocks by label, or `none` if two share one. -/
@[expose] def tree? (bs : List (Block env α)) : Option (LabelMap (Block env α)) :=
  bs.foldlM (init := ∅) fun m b =>
    if (m.find? b.label).isSome then none else some (m.insert b.label b)

/-- The parent of block `b` in the tree `t`, whose blocks by label are `tm`: the block it
names, and the count. -/
@[expose] def parent (tm : LabelMap (Block env α)) (t : Tree) (b : Block env α) :
    Option (Block env α × Nat) :=
  (t b.label).bind fun p => (tm.find? p.label).map (·, p.count)

/-- The chain up the tree `t` from block `b` at count `k`: `b` at `k`, then its parent at the
parent's count, and so on, at most `fuel` blocks. -/
@[expose] def chain (tm : LabelMap (Block env α)) (t : Tree) :
    (fuel : Nat) → Block env α → Nat → List (Block env α × Nat)
  | 0, _, _ => []
  | f + 1, b, k => (b, k) ::
    match parent tm t b with
    | some (c, j) => chain tm t f c j
    | none => []

/-- `p` is at or above the start of the chain `ch`: at or before one of its points. -/
@[expose] def above (ch : List (Block env α × Nat)) (p : Point) : Bool :=
  ch.any fun (c, j) => p.le ⟨c.label, j⟩

/-- `p` is a node of the body whose blocks by label are `tm`: `p` names one of them, at a
count no greater than its instruction count. -/
@[expose] def node (tm : LabelMap (Block env α)) (p : Point) : Bool :=
  (tm.find? p.label).any (decide <| p.count ≤ ·.instrs.size)

/-! ### Ancestor maps -/

/-- For each block, by label, the blocks above its start, each with the latest count of the
block's chain in it. -/
abbrev AncMap := LabelMap (LabelMap Nat)

/-- `m` with the ancestors of block `b` in the tree `t` added, and those of the blocks above
it, at most `fuel` blocks. -/
@[expose] def addAncs (tm : LabelMap (Block env α)) (t : Tree) : (fuel : Nat) → AncMap →
    Block env α → AncMap
  | 0, m, _ => m
  | f + 1, m, b =>
    if (m.find? b.label).isSome then m
    else
      match t b.label with
      | none => m.insert b.label ∅
      | some p =>
        match tm.find? p.label with
        | none => m
        | some c =>
          let m := addAncs tm t f m c
          match m.find? p.label with
          | some a => m.insert b.label (a.insert p.label (max p.count ((a.find? p.label).getD 0)))
          | none => m

/-- The ancestors in the tree `t` of the blocks `bs`, whose blocks by label are `tm`. -/
@[expose] def ancs (tm : LabelMap (Block env α)) (t : Tree) (bs : List (Block env α)) : AncMap :=
  bs.foldl (addAncs tm t bs.length) ∅

/-- `p` is at or above count `k` of block `b` in the tree `t`, as the map `m` has it, or else as
`b`'s chain, at most `n` blocks, has it. -/
@[expose] def ancAt (tm : LabelMap (Block env α)) (t : Tree) (n : Nat) (m : AncMap)
    (b : Block env α) (k : Nat) (p : Point) : Bool :=
  match m.find? b.label with
  | some a => p.le ⟨b.label, k⟩ || (a.find? p.label).any (decide <| p.count ≤ ·)
  | none => above (chain tm t n b k) p

/-! ### Legality -/

/-- A transfer to `s` leaves from its target's parent in `t` or below it, where `anc` says
what is at or above the point it leaves from. -/
@[expose] def jumpOK (tm : LabelMap (Block env α)) (t : Tree) (anc : Point → Bool)
    (s : BlockValue) : Bool :=
  ((tm.find? s.target).bind fun v => t v.label).all anc

/-- The transfers of the instructions `is`, the first at count `k`, are legal, where `anc j`
says what is at or above count `j` of their block. -/
@[expose] def instrJumpsOK (tm : LabelMap (Block env α)) (t : Tree) (anc : Nat → Point → Bool) :
    Nat → List (Instruction env α) → Bool
  | _, [] => true
  | k, i :: is => i.succs.toList.all (jumpOK tm t (anc k)) && instrJumpsOK tm t anc (k + 1) is

/-- Block `b` of a body with root `r` is legal, where `anc k` says what is at or above its
count `k`: its start is below `r`, and every transfer out of it is legal. -/
@[expose] def blockOK (tm : LabelMap (Block env α)) (t : Tree) (anc : Nat → Point → Bool)
    (r : Point) (b : Block env α) : Bool :=
  anc 0 r && instrJumpsOK tm t anc 0 b.instrs.toList &&
    b.term.succs.toList.all (jumpOK tm t (anc b.instrs.size))

/-- The tree `t` of the blocks `bs`, whose blocks by label are `tm` and whose ancestors are `m`,
is legal, except that labels are distinct, which `tree?` checks. -/
@[expose] def legal (tm : LabelMap (Block env α)) (t : Tree) (m : AncMap)
    (bs : List (Block env α)) : Bool :=
  match bs with
  | [] => true
  | e :: rest =>
    let n := bs.length
    (t e.label).isNone && bs.all (fun b => blockOK tm t (ancAt tm t n m b) ⟨e.label, 0⟩ b) &&
      rest.all fun b => (t b.label).any (node tm)

/-! ### Definitions -/

/-- For each value id, the points of a body that define it. -/
abbrev DefMap := NatTrie (List Point)

/-- The points that `m` has define `x`. -/
@[expose] def DefMap.get (m : DefMap) (x : ValId) : List Point := (m.find? x.id).getD []

/-- `m`, with `p` defining `x`. -/
@[expose] def DefMap.add (m : DefMap) (x : ValId) (p : Point) : DefMap :=
  m.insert x.id (p :: m.get x)

/-- `m`, with the results of the instructions `is` of block `l`, the first at count `k`. -/
@[expose] def instrDefs (l : Label) : DefMap → Nat → List (Instruction env α) → DefMap
  | m, _, [] => m
  | m, k, i :: is => instrDefs l (m.add i.result.id ⟨l, k + 1⟩) (k + 1) is

/-- `m`, with what block `b` defines. -/
@[expose] def blockDefs (m : DefMap) (b : Block env α) : DefMap :=
  instrDefs b.label (b.params.toList.foldl (fun m d => m.add d.id ⟨b.label, 0⟩) m) 0
    b.instrs.toList

/-- What the blocks `bs` define. -/
@[expose] def defs (bs : List (Block env α)) : DefMap := bs.foldl blockDefs .leaf

/-- `x` is in scope at count `k` of block `b` under the tree `t`: the body defines it at a point
at or above there, as the maps `m` and `dm`, with block count `n`, have it. -/
@[expose] def scopeAt (tm : LabelMap (Block env α)) (t : Tree) (n : Nat) (m : AncMap)
    (dm : DefMap) (b : Block env α) (k : Nat) (x : ValId) : Bool :=
  (dm.get x).any (ancAt tm t n m b k)

end Body

/-- Every operand and every successor argument satisfies `σ`. -/
@[expose] def usesIn (σ : ValId → Bool) (args : Array ValId) (succs : Array BlockValue) : Bool :=
  args.toList.all σ && succs.toList.all (·.args.toList.all σ)

namespace Body

/-- The instructions, the first at count `k`, each use, outside their regions, only what `σ` puts
in scope at its count. -/
@[expose] def instrUsesOK (σ : Nat → ValId → Bool) : Nat → List (Instruction env α) → Bool
  | _, [] => true
  | k, i :: is => usesIn (σ k) i.args i.succs && instrUsesOK σ (k + 1) is

/-- The blocks use, outside their regions, only what `σ b k` puts in scope at count `k` of
block `b`. -/
@[expose] def usesOK (σ : Block env α → Nat → ValId → Bool) (bs : List (Block env α)) : Bool :=
  bs.all fun b => instrUsesOK (σ b) 0 b.instrs.toList &&
    usesIn (σ b b.instrs.size) b.term.args b.term.succs

/-- Whether the tree `t` of the body is legal and puts every use of the body in scope, entered
where `Λ` is visible: `ScopedBy`, decided. -/
@[expose] def checkScopedBy (Λ : ValId → Bool) (bs : List (Block env α)) (t : Tree) : Bool :=
  match tree? bs with
  | none => false
  | some tm =>
    let m := ancs tm t bs
    let n := bs.length
    let dm := defs bs
    legal tm t m bs && usesOK (fun b k x => scopeAt tm t n m dm b k x || Λ x) bs

end Body

end

end Strata.Mantle
