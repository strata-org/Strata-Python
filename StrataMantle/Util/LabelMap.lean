/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.IR

set_option autoImplicit false

/-!
# Maps the kernel reduces

Maps that `decide +kernel` evaluates fast, for the checker:

* `NatTrie`: a map from `Nat`, on the key's binary digits;
* `LabelMap`: a map from labels, on each label's counter.
-/

namespace Strata.Mantle

public section

/-- A map from `Nat`: a trie on the key's bijective binary digits.  Key `0` is at the root,
and `2k+1` and `2k+2` are key `k` of the left and right subtrees.  Its depth is the key's bit
length, so it suits small keys such as value ids and label counters. -/
inductive NatTrie (β : Type) where
  | leaf
  | node (v : Option β) (l r : NatTrie β)

namespace NatTrie

variable {β : Type}

/-- The value at `k`, if any. -/
@[expose] def find? : NatTrie β → Nat → Option β
  | .leaf, _ => none
  | .node v _ _, 0 => v
  | .node _ l r, n + 1 => if n % 2 = 0 then l.find? (n / 2) else r.find? (n / 2)

/-- Map `k` to `x` at most `fuel` levels down. -/
@[expose] def insertAt (x : β) : (fuel : Nat) → NatTrie β → Nat → NatTrie β
  | 0, t, _ => t
  | _ + 1, .leaf, 0 => .node (some x) .leaf .leaf
  | _ + 1, .node _ l r, 0 => .node (some x) l r
  | f + 1, .leaf, n + 1 =>
    if n % 2 = 0 then .node none (insertAt x f .leaf (n / 2)) .leaf
    else .node none .leaf (insertAt x f .leaf (n / 2))
  | f + 1, .node v l r, n + 1 =>
    if n % 2 = 0 then .node v (insertAt x f l (n / 2)) r else .node v l (insertAt x f r (n / 2))

/-- `t` with `k` mapped to `x`.  Key `k` is at most `k` levels down. -/
@[expose] def insert (t : NatTrie β) (k : Nat) (x : β) : NatTrie β := insertAt x (k + 1) t k

end NatTrie

/-- The key of a label in a `LabelMap`: its counter, or `0` if it has none. -/
@[expose] def Label.key : Label → Nat
  -- Labels that differ only in stem, such as the builder's `head.0` and `join.0`, share a
  -- bucket, so a lookup scans it.
  | ⟨.num _ i⟩ => i
  | _ => 0

/-- A map from labels: per key, the labels with that key and their values, latest first. -/
structure LabelMap (β : Type) where
  trie : NatTrie (List (Label × β)) := .leaf

namespace LabelMap

variable {β : Type}

instance : EmptyCollection (LabelMap β) := ⟨⟨.leaf⟩⟩

/-- The labels with `l`'s key, and their values. -/
@[expose] def bucket (m : LabelMap β) (l : Label) : List (Label × β) :=
  (m.trie.find? l.key).getD []

/-- The value at `l`, if any. -/
@[expose] def find? (m : LabelMap β) (l : Label) : Option β :=
  ((m.bucket l).find? fun p => decide (p.1 = l)).map (·.2)

/-- `m` with `l` mapped to `x`. -/
@[expose] def insert (m : LabelMap β) (l : Label) (x : β) : LabelMap β :=
  ⟨m.trie.insert l.key ((l, x) :: m.bucket l)⟩

/-- `m` with `l` mapped to `f` of its value, if any.  It drops the old entry, so a map that is
updated often stays as small as one built by `insert`ing each label once. -/
@[expose] def update (m : LabelMap β) (l : Label) (f : Option β → β) : LabelMap β :=
  let b := m.bucket l
  ⟨m.trie.insert l.key ((l, f (m.find? l)) :: b.filter fun p => !decide (p.1 = l))⟩

/-- The labels `ls`, as a set, or `none` if one occurs twice. -/
@[expose] def ofDistinct? (ls : List Label) : Option (LabelMap Unit) :=
  ls.foldlM (init := ∅) fun m l => if (m.find? l).isSome then none else some (m.insert l ())

end LabelMap

end

end Strata.Mantle
