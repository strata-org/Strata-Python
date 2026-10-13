/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# A 2-3 tree keyed by `Nat`

A balanced search tree that `decide +kernel` reduces: every leaf is at the same depth, and
every comparison is one comparison of `Nat` literals.  Its depth is logarithmic in the number
of entries whatever the keys' size, so it suits large keys such as `Name.key`.

* `find?`: the value at a key.
* `insert?`: add an entry, or fail if the key is already there.
* `insertArray?`, `ofArray?`: add an array of entries, failing on the first repeated key.
* `entries`, `keys`: what a tree holds, left to right.
* `Ordered`: the search invariant.

`ofArray?_isSome_iff` is the duplicate check (`List.Nodup`); `find?_ofArray?` and
`mem_keys_ofArray?` say what the result holds.  There is no deletion.
-/

namespace Strata.Mantle

public section

/-- A 2-3 tree keyed by `Nat`: a node holds one key (`two`) or two (`three`).  `Ordered` is
its search invariant. -/
inductive NatTree23 (β : Type) where
  | leaf
  | two (l : NatTree23 β) (k : Nat) (v : β) (r : NatTree23 β)
  | three (l : NatTree23 β) (k₁ : Nat) (v₁ : β) (m : NatTree23 β) (k₂ : Nat) (v₂ : β)
      (r : NatTree23 β)

namespace NatTree23

variable {β : Type}

/-- What adding one entry below a node yields: the new subtree, or a subtree that grew too
tall and split into two around a key, or the report that the key was already there. -/
inductive Ins (β : Type) where
  | ok (t : NatTree23 β)
  | split (l : NatTree23 β) (k : Nat) (v : β) (r : NatTree23 β)
  | dup

/-- The value at `x`, if any. -/
@[expose] def find? : NatTree23 β → Nat → Option β
  | .leaf, _ => none
  | .two l k v r, x =>
    match compare x k with
    | .lt => find? l x
    | .eq => some v
    | .gt => find? r x
  | .three l k₁ v₁ m k₂ v₂ r, x =>
    match compare x k₁ with
    | .lt => find? l x
    | .eq => some v₁
    | .gt =>
      match compare x k₂ with
      | .lt => find? m x
      | .eq => some v₂
      | .gt => find? r x

/-- Add `(x, v)` below this node. -/
@[expose] def ins : NatTree23 β → Nat → β → Ins β
  | .leaf, x, v => .split .leaf x v .leaf
  | .two l k w r, x, v =>
    match compare x k with
    | .eq => .dup
    | .lt =>
      match ins l x v with
      | .ok l' => .ok (.two l' k w r)
      | .split a b bv c => .ok (.three a b bv c k w r)
      | .dup => .dup
    | .gt =>
      match ins r x v with
      | .ok r' => .ok (.two l k w r')
      | .split a b bv c => .ok (.three l k w a b bv c)
      | .dup => .dup
  | .three l k₁ w₁ m k₂ w₂ r, x, v =>
    match compare x k₁ with
    | .eq => .dup
    | .lt =>
      match ins l x v with
      | .ok l' => .ok (.three l' k₁ w₁ m k₂ w₂ r)
      | .split a b bv c => .split (.two a b bv c) k₁ w₁ (.two m k₂ w₂ r)
      | .dup => .dup
    | .gt =>
      match compare x k₂ with
      | .eq => .dup
      | .lt =>
        match ins m x v with
        | .ok m' => .ok (.three l k₁ w₁ m' k₂ w₂ r)
        | .split a b bv c => .split (.two l k₁ w₁ a) b bv (.two c k₂ w₂ r)
        | .dup => .dup
      | .gt =>
        match ins r x v with
        | .ok r' => .ok (.three l k₁ w₁ m k₂ w₂ r')
        | .split a b bv c => .split (.two l k₁ w₁ m) k₂ w₂ (.two a b bv c)
        | .dup => .dup

/-- `t` with `x` mapped to `v`, or `none` if `x` is already a key of `t`. -/
@[expose] def insert? (t : NatTree23 β) (x : Nat) (v : β) : Option (NatTree23 β) :=
  match t.ins x v with
  | .ok t' => some t'
  | .split l k v r => some (.two l k v r)
  | .dup => none

/-- `t` with the value at `x` replaced by `v`, the shape unchanged; `t` if `x` is not a key. -/
@[expose] def replace : NatTree23 β → Nat → β → NatTree23 β
  | .leaf, _, _ => .leaf
  | .two l k w r, x, v =>
    match compare x k with
    | .lt => .two (replace l x v) k w r
    | .eq => .two l k v r
    | .gt => .two l k w (replace r x v)
  | .three l k₁ w₁ m k₂ w₂ r, x, v =>
    match compare x k₁ with
    | .lt => .three (replace l x v) k₁ w₁ m k₂ w₂ r
    | .eq => .three l k₁ v m k₂ w₂ r
    | .gt =>
      match compare x k₂ with
      | .lt => .three l k₁ w₁ (replace m x v) k₂ w₂ r
      | .eq => .three l k₁ w₁ m k₂ v r
      | .gt => .three l k₁ w₁ m k₂ w₂ (replace r x v)

/-- `t` with `x` mapped to `v`, whether or not `x` was a key. -/
@[expose] def insert (t : NatTree23 β) (x : Nat) (v : β) : NatTree23 β :=
  (t.insert? x v).getD (t.replace x v)

/-- Add the entries of an array to `t` in order, or fail at the first key already present. -/
@[expose] def insertArray? (t : NatTree23 β) : Array (Nat × β) → Option (NatTree23 β)
  -- The kernel reduces the recursion on the list; compiled code runs `insertArrayFold?`.
  | ⟨l⟩ => go t l
where
  /-- Add the entries of `l` to `t` in order. -/
  go (t : NatTree23 β) : List (Nat × β) → Option (NatTree23 β)
    | [] => some t
    | p :: l =>
      match t.insert? p.1 p.2 with
      | some t' => go t' l
      | none => none

/-- `insertArray?` as a fold over the array. -/
def insertArrayFold? (t : NatTree23 β) (a : Array (Nat × β)) : Option (NatTree23 β) :=
  a.foldlM (fun t p => t.insert? p.1 p.2) t

/-- `insertArray?` is a left fold of `insert?`. -/
theorem insertArray?_eq_foldlM (t : NatTree23 β) (a : Array (Nat × β)) :
    t.insertArray? a = a.foldlM (fun t p => t.insert? p.1 p.2) t := by
  rcases a with ⟨l⟩
  rw [List.foldlM_toArray]
  induction l generalizing t with
  | nil => rfl
  | cons p l ih =>
    simp only [insertArray?, insertArray?.go, List.foldlM_cons] at ih ⊢
    cases t.insert? p.1 p.2 with
    | none => rfl
    | some t' => exact ih t'

/-- Compiled code runs `insertArrayFold?` for `insertArray?`. -/
@[csimp] theorem insertArray?_eq_insertArrayFold? : @insertArray? = @insertArrayFold? := by
  funext β t a
  exact insertArray?_eq_foldlM t a

/-- `a` as a tree, or `none` if a key occurs twice in it. -/
@[expose] def ofArray? (a : Array (Nat × β)) : Option (NatTree23 β) := insertArray? .leaf a


/-! ## What a tree holds

`entries` is the specification: a tree is the list of its entries, left to right, and
`Ordered` says that list's keys increase.  Everything below is stated over `entries`. -/

/-- The entries, left to right. -/
@[expose] def entries : NatTree23 β → List (Nat × β)
  | .leaf => []
  | .two l k v r => l.entries ++ (k, v) :: r.entries
  | .three l k₁ v₁ m k₂ v₂ r => l.entries ++ (k₁, v₁) :: (m.entries ++ (k₂, v₂) :: r.entries)

/-- The keys, left to right. -/
@[expose] def keys (t : NatTree23 β) : List Nat := t.entries.map Prod.fst

/-- The keys increase from left to right: the search invariant. -/
@[expose] def Ordered (t : NatTree23 β) : Prop := t.keys.Pairwise (· < ·)

instance (t : NatTree23 β) : Decidable t.Ordered :=
  inferInstanceAs (Decidable (t.keys.Pairwise (· < ·)))

/-- The entries of an `ins` result, left to right: a split's two subtrees around its key, as
its parent or `insert?` reassembles them; none for `.dup`. -/
@[expose] def Ins.entries : Ins β → List (Nat × β)
  | .ok t => t.entries
  | .split l k v r => l.entries ++ (k, v) :: r.entries
  | .dup => []

/-- The keys of `Ins.entries`. -/
@[expose] def Ins.keys (i : Ins β) : List Nat := i.entries.map Prod.fst

/-- The empty tree has no entries. -/
@[simp] theorem entries_leaf : (leaf : NatTree23 β).entries = [] := rfl

/-- The empty tree has no keys. -/
@[simp] theorem keys_leaf : (leaf : NatTree23 β).keys = [] := rfl

/-- A `two` node's keys, left to right. -/
@[simp] theorem keys_two {l r : NatTree23 β} {k : Nat} {v : β} :
    (two l k v r).keys = l.keys ++ k :: r.keys := by
  simp only [keys, entries, List.map_append, List.map_cons]

/-- A `three` node's keys, left to right. -/
@[simp] theorem keys_three {l m r : NatTree23 β} {k₁ k₂ : Nat} {v₁ v₂ : β} :
    (three l k₁ v₁ m k₂ v₂ r).keys = l.keys ++ k₁ :: (m.keys ++ k₂ :: r.keys) := by
  simp only [keys, entries, List.map_append, List.map_cons]

/-- A split's keys, left to right. -/
@[simp] theorem Ins.keys_split {l r : NatTree23 β} {k : Nat} {v : β} :
    (Ins.split l k v r).keys = l.keys ++ k :: r.keys := by
  simp only [Ins.keys, Ins.entries, NatTree23.keys, List.map_append, List.map_cons]

/-- A key of an entry is a key of the tree. -/
theorem mem_keys_of_mem_entries {t : NatTree23 β} {k : Nat} {v : β} (h : (k, v) ∈ t.entries) :
    k ∈ t.keys := List.mem_map_of_mem h

/-- A key of the tree is the key of some entry. -/
theorem exists_of_mem_keys {t : NatTree23 β} {k : Nat} (h : k ∈ t.keys) :
    ∃ v, (k, v) ∈ t.entries := by
  obtain ⟨⟨k', v⟩, hp, rfl⟩ := List.mem_map.mp h
  exact ⟨v, hp⟩

/-- The keys of a tree whose entries are those of `l` and of `t`. -/
private theorem mem_keys_iff_of_entries {t t' : NatTree23 β} {l : List (Nat × β)}
    (h : ∀ p, p ∈ t'.entries ↔ p ∈ l ∨ p ∈ t.entries) (y : Nat) :
    y ∈ t'.keys ↔ y ∈ l.map Prod.fst ∨ y ∈ t.keys := by
  simp only [keys, List.mem_map, h, or_and_right, exists_or]

/-- `Pairwise (· < ·)` of a list split at one element, as facts about the pieces.  The cross
pairs follow from the bounds by transitivity, so they are not carried. -/
private theorem pairwise_mid {A B : List Nat} {k : Nat} :
    (A ++ k :: B).Pairwise (· < ·) ↔ A.Pairwise (· < ·) ∧ B.Pairwise (· < ·) ∧
      (∀ a ∈ A, a < k) ∧ (∀ b ∈ B, k < b) := by
  rw [List.pairwise_append, List.pairwise_cons]
  constructor
  · rintro ⟨hA, ⟨hk, hB⟩, hc⟩
    exact ⟨hA, hB, fun a ha => hc a ha k List.mem_cons_self, hk⟩
  · rintro ⟨hA, hB, hlo, hhi⟩
    refine ⟨hA, ⟨hhi, hB⟩, fun a ha b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hlo a ha
    · exact Nat.lt_trans (hlo a ha) (hhi b hb)

/-! ## Lookup -/

/-- A lookup returns an entry the tree holds, ordered or not. -/
theorem mem_entries_of_find? : ∀ (t : NatTree23 β) (x : Nat) (v : β),
    t.find? x = some v → (x, v) ∈ t.entries := by
  intro t
  induction t with
  | leaf => simp [find?]
  | two l k w r ihl ihr =>
    intro x v h
    simp only [entries, List.mem_append, List.mem_cons]
    rcases Nat.lt_trichotomy x k with hx | rfl | hx
    · simp only [find?, Nat.compare_eq_lt.mpr hx] at h
      exact .inl (ihl x v h)
    · simp only [find?, Nat.compare_eq_eq.mpr rfl, Option.some.injEq] at h
      subst h
      exact .inr (.inl rfl)
    · simp only [find?, Nat.compare_eq_gt.mpr hx] at h
      exact .inr (.inr (ihr x v h))
  | three l k₁ w₁ m k₂ w₂ r ihl ihm ihr =>
    intro x v h
    simp only [entries, List.mem_append, List.mem_cons]
    rcases Nat.lt_trichotomy x k₁ with hx₁ | rfl | hx₁
    · simp only [find?, Nat.compare_eq_lt.mpr hx₁] at h
      exact .inl (ihl x v h)
    · simp only [find?, Nat.compare_eq_eq.mpr rfl, Option.some.injEq] at h
      subst h
      exact .inr (.inl rfl)
    rcases Nat.lt_trichotomy x k₂ with hx₂ | rfl | hx₂
    · simp only [find?, Nat.compare_eq_gt.mpr hx₁, Nat.compare_eq_lt.mpr hx₂] at h
      exact .inr (.inr (.inl (ihm x v h)))
    · simp only [find?, Nat.compare_eq_gt.mpr hx₁, Nat.compare_eq_eq.mpr rfl,
        Option.some.injEq] at h
      subst h
      exact .inr (.inr (.inr (.inl rfl)))
    · simp only [find?, Nat.compare_eq_gt.mpr hx₁, Nat.compare_eq_gt.mpr hx₂] at h
      exact .inr (.inr (.inr (.inr (ihr x v h))))

/-- Every entry an ordered tree holds is found by a lookup. -/
theorem find?_of_mem_entries : ∀ (t : NatTree23 β), t.Ordered → ∀ (x : Nat) (v : β),
    (x, v) ∈ t.entries → t.find? x = some v := by
  intro t
  induction t with
  | leaf => simp
  | two l k w r ihl ihr =>
    intro ho x v hq
    rw [Ordered, keys_two, pairwise_mid] at ho
    obtain ⟨hl, hr, hlo, hhi⟩ := ho
    simp only [entries, List.mem_append, List.mem_cons, Prod.mk.injEq] at hq
    -- The bounds on each child's keys fix the branch `find?` takes.
    rcases hq with hq | ⟨rfl, rfl⟩ | hq
    · have hx : x < k := hlo x (mem_keys_of_mem_entries hq)
      simp only [find?, Nat.compare_eq_lt.mpr hx, ihl hl x v hq]
    · simp only [find?, Nat.compare_eq_eq.mpr rfl]
    · have hx : k < x := hhi x (mem_keys_of_mem_entries hq)
      simp only [find?, Nat.compare_eq_gt.mpr hx, ihr hr x v hq]
  | three l k₁ w₁ m k₂ w₂ r ihl ihm ihr =>
    intro ho x v hq
    rw [Ordered, keys_three, pairwise_mid] at ho
    obtain ⟨hl, hmr, hlo, hhi⟩ := ho
    obtain ⟨hm, hr, hmlo, hmhi⟩ := pairwise_mid.mp hmr
    have h₁₂ : k₁ < k₂ := hhi k₂ (List.mem_append_right _ List.mem_cons_self)
    simp only [entries, List.mem_append, List.mem_cons, Prod.mk.injEq] at hq
    rcases hq with hq | ⟨rfl, rfl⟩ | hq | ⟨rfl, rfl⟩ | hq
    · have hx : x < k₁ := hlo x (mem_keys_of_mem_entries hq)
      simp only [find?, Nat.compare_eq_lt.mpr hx, ihl hl x v hq]
    · simp only [find?, Nat.compare_eq_eq.mpr rfl]
    · have hx₁ : k₁ < x := hhi x (List.mem_append_left _ (mem_keys_of_mem_entries hq))
      have hx₂ : x < k₂ := hmlo x (mem_keys_of_mem_entries hq)
      simp only [find?, Nat.compare_eq_gt.mpr hx₁, Nat.compare_eq_lt.mpr hx₂, ihm hm x v hq]
    · simp only [find?, Nat.compare_eq_gt.mpr h₁₂, Nat.compare_eq_eq.mpr rfl]
    · have hx : k₂ < x := hmhi x (mem_keys_of_mem_entries hq)
      simp only [find?, Nat.compare_eq_gt.mpr (Nat.lt_trans h₁₂ hx), Nat.compare_eq_gt.mpr hx,
        ihr hr x v hq]

/-- A lookup in an ordered tree is a lookup in its entries. -/
theorem find?_eq_some_iff {t : NatTree23 β} (ho : t.Ordered) (x : Nat) (v : β) :
    t.find? x = some v ↔ (x, v) ∈ t.entries :=
  ⟨mem_entries_of_find? t x v, find?_of_mem_entries t ho x v⟩

/-- A key is found exactly when the tree has it. -/
theorem isSome_find?_iff {t : NatTree23 β} (ho : t.Ordered) (x : Nat) :
    (t.find? x).isSome = true ↔ x ∈ t.keys := by
  rw [Option.isSome_iff_exists]
  exact ⟨fun ⟨v, hv⟩ => mem_keys_of_mem_entries ((find?_eq_some_iff ho x v).mp hv),
    fun h => (exists_of_mem_keys h).imp fun v => (find?_eq_some_iff ho x v).mpr⟩

/-! ## Insertion -/

/-- `ins` reports a duplicate exactly when `find?` finds the key, ordered or not. -/
theorem ins_eq_dup_iff : ∀ (t : NatTree23 β) (x : Nat) (v : β),
    (t.ins x v = .dup ↔ (t.find? x).isSome = true) := by
  intro t
  induction t with
  | leaf => simp [ins, find?]
  | two l k w r ihl ihr =>
    intro x v
    rcases Nat.lt_trichotomy x k with h | rfl | h
    · simp only [ins, find?, Nat.compare_eq_lt.mpr h, ← ihl x v]
      cases l.ins x v <;> simp
    · simp [ins, find?]
    · simp only [ins, find?, Nat.compare_eq_gt.mpr h, ← ihr x v]
      cases r.ins x v <;> simp
  | three l k₁ w₁ m k₂ w₂ r ihl ihm ihr =>
    intro x v
    rcases Nat.lt_trichotomy x k₁ with h | rfl | h
    · simp only [ins, find?, Nat.compare_eq_lt.mpr h, ← ihl x v]
      cases l.ins x v <;> simp
    · simp [ins, find?]
    · rcases Nat.lt_trichotomy x k₂ with h' | rfl | h'
      · simp only [ins, find?, Nat.compare_eq_gt.mpr h, Nat.compare_eq_lt.mpr h', ← ihm x v]
        cases m.ins x v <;> simp
      · simp [ins, find?, Nat.compare_eq_gt.mpr h]
      · simp only [ins, find?, Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr h', ← ihr x v]
        cases r.ins x v <;> simp

/-- Adding a key the tree does not have reports no duplicate. -/
private theorem ins_ne_dup {t : NatTree23 β} {x : Nat} {v : β} (hx : x ∉ t.keys) :
    t.ins x v ≠ .dup := fun hc => by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((ins_eq_dup_iff t x v).mp hc)
  exact hx (mem_keys_of_mem_entries (mem_entries_of_find? t x w hw))

/-! ### Adding below a node

Where the child reports no duplicate, the node's result holds the child's result in that
child's place, left to right. -/

/-- `ins` into a `two` node's left child. -/
private theorem entries_ins_two_lt {l r : NatTree23 β} {k x : Nat} {w v : β} (h : x < k)
    (hd : l.ins x v ≠ .dup) :
    ((two l k w r).ins x v).entries = (l.ins x v).entries ++ (k, w) :: r.entries := by
  simp only [ins, Nat.compare_eq_lt.mpr h]
  cases hc : l.ins x v with
  | dup => exact absurd hc hd
  | ok | split => simp only [Ins.entries, entries, List.append_assoc, List.cons_append]

/-- `ins` into a `two` node's right child. -/
private theorem entries_ins_two_gt {l r : NatTree23 β} {k x : Nat} {w v : β} (h : k < x)
    (hd : r.ins x v ≠ .dup) :
    ((two l k w r).ins x v).entries = l.entries ++ (k, w) :: (r.ins x v).entries := by
  simp only [ins, Nat.compare_eq_gt.mpr h]
  cases hc : r.ins x v with
  | dup => exact absurd hc hd
  | ok | split => simp only [Ins.entries, entries]

/-- `ins` into a `three` node's left child. -/
private theorem entries_ins_three_lt {l m r : NatTree23 β} {k₁ k₂ x : Nat} {w₁ w₂ v : β}
    (h : x < k₁) (hd : l.ins x v ≠ .dup) :
    ((three l k₁ w₁ m k₂ w₂ r).ins x v).entries =
      (l.ins x v).entries ++ (k₁, w₁) :: (m.entries ++ (k₂, w₂) :: r.entries) := by
  simp only [ins, Nat.compare_eq_lt.mpr h]
  cases hc : l.ins x v with
  | dup => exact absurd hc hd
  | ok | split => simp only [Ins.entries, entries]

/-- `ins` into a `three` node's middle child. -/
private theorem entries_ins_three_mid {l m r : NatTree23 β} {k₁ k₂ x : Nat} {w₁ w₂ v : β}
    (h₁ : k₁ < x) (h₂ : x < k₂) (hd : m.ins x v ≠ .dup) :
    ((three l k₁ w₁ m k₂ w₂ r).ins x v).entries =
      l.entries ++ (k₁, w₁) :: ((m.ins x v).entries ++ (k₂, w₂) :: r.entries) := by
  simp only [ins, Nat.compare_eq_gt.mpr h₁, Nat.compare_eq_lt.mpr h₂]
  cases hc : m.ins x v with
  | dup => exact absurd hc hd
  | ok | split => simp only [Ins.entries, entries, List.append_assoc, List.cons_append]

/-- `ins` into a `three` node's right child. -/
private theorem entries_ins_three_gt {l m r : NatTree23 β} {k₁ k₂ x : Nat} {w₁ w₂ v : β}
    (h₁ : k₁ < x) (h₂ : k₂ < x) (hd : r.ins x v ≠ .dup) :
    ((three l k₁ w₁ m k₂ w₂ r).ins x v).entries =
      l.entries ++ (k₁, w₁) :: (m.entries ++ (k₂, w₂) :: (r.ins x v).entries) := by
  simp only [ins, Nat.compare_eq_gt.mpr h₁, Nat.compare_eq_gt.mpr h₂]
  cases hc : r.ins x v with
  | dup => exact absurd hc hd
  | ok | split => simp only [Ins.entries, entries, List.append_assoc, List.cons_append]

/-- Adding a key the tree does not have adds exactly that entry, ordered or not. -/
theorem mem_entries_ins : ∀ (t : NatTree23 β) (x : Nat) (v : β), x ∉ t.keys →
    ∀ p, p ∈ (t.ins x v).entries ↔ p = (x, v) ∨ p ∈ t.entries := by
  intro t
  induction t with
  | leaf => intro x v _ p; simp [ins, Ins.entries]
  | two l k w r ihl ihr =>
    intro x v hx p
    simp only [keys_two, List.mem_append, List.mem_cons, not_or] at hx
    obtain ⟨hxl, hxk, hxr⟩ := hx
    -- Each case: the child's result takes the child's place, and `grind` regroups the
    -- disjunction.
    rcases Nat.lt_trichotomy x k with h | rfl | h
    · rw [entries_ins_two_lt h (ins_ne_dup hxl)]
      simp only [entries, List.mem_append, List.mem_cons, ihl x v hxl p]
      grind
    · exact absurd rfl hxk
    · rw [entries_ins_two_gt h (ins_ne_dup hxr)]
      simp only [entries, List.mem_append, List.mem_cons, ihr x v hxr p]
      grind
  | three l k₁ w₁ m k₂ w₂ r ihl ihm ihr =>
    intro x v hx p
    simp only [keys_three, List.mem_append, List.mem_cons, not_or] at hx
    obtain ⟨hxl, hxk₁, hxm, hxk₂, hxr⟩ := hx
    rcases Nat.lt_trichotomy x k₁ with h | rfl | h
    · rw [entries_ins_three_lt h (ins_ne_dup hxl)]
      simp only [entries, List.mem_append, List.mem_cons, ihl x v hxl p]
      grind
    · exact absurd rfl hxk₁
    rcases Nat.lt_trichotomy x k₂ with h' | rfl | h'
    · rw [entries_ins_three_mid h h' (ins_ne_dup hxm)]
      simp only [entries, List.mem_append, List.mem_cons, ihm x v hxm p]
      grind
    · exact absurd rfl hxk₂
    · rw [entries_ins_three_gt h h' (ins_ne_dup hxr)]
      simp only [entries, List.mem_append, List.mem_cons, ihr x v hxr p]
      grind

/-- A bound that holds of `x` and of every key of `t` holds of every key of `t.ins x v`. -/
private theorem forall_mem_keys_ins {t : NatTree23 β} {x : Nat} {v : β} {P : Nat → Prop}
    (hx : x ∉ t.keys) (hPx : P x) (hP : ∀ a ∈ t.keys, P a) : ∀ a ∈ (t.ins x v).keys, P a := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  rcases (mem_entries_ins t x v hx p).mp hp with rfl | hp
  · exact hPx
  · exact hP p.1 (List.mem_map_of_mem hp)

/-- Adding a key an ordered tree does not have keeps the keys increasing. -/
theorem ordered_ins : ∀ (t : NatTree23 β) (x : Nat) (v : β), t.Ordered → x ∉ t.keys →
    (t.ins x v).keys.Pairwise (· < ·) := by
  intro t
  induction t with
  | leaf => intro x v _ _; simp [ins]
  | two l k w r ihl ihr =>
    intro x v ho hx
    rw [Ordered, keys_two, pairwise_mid] at ho
    obtain ⟨hl, hr, hlo, hhi⟩ := ho
    simp only [keys_two, List.mem_append, List.mem_cons, not_or] at hx
    obtain ⟨hxl, hxk, hxr⟩ := hx
    -- Each case: the child's result takes the child's place, and `x` is within the child's
    -- bounds, so they bound the child's new keys too.
    rcases Nat.lt_trichotomy x k with h | rfl | h
    · rw [show ((two l k w r).ins x v).keys = (l.ins x v).keys ++ k :: r.keys by
        simp only [Ins.keys, keys, entries_ins_two_lt h (ins_ne_dup hxl), List.map_append,
          List.map_cons], pairwise_mid]
      exact ⟨ihl x v hl hxl, hr, forall_mem_keys_ins hxl h hlo, hhi⟩
    · exact absurd rfl hxk
    · rw [show ((two l k w r).ins x v).keys = l.keys ++ k :: (r.ins x v).keys by
        simp only [Ins.keys, keys, entries_ins_two_gt h (ins_ne_dup hxr), List.map_append,
          List.map_cons], pairwise_mid]
      exact ⟨hl, ihr x v hr hxr, hlo, forall_mem_keys_ins hxr h hhi⟩
  | three l k₁ w₁ m k₂ w₂ r ihl ihm ihr =>
    intro x v ho hx
    rw [Ordered, keys_three, pairwise_mid] at ho
    obtain ⟨hl, hmr, hlo, hhi⟩ := ho
    obtain ⟨hm, hr, hmlo, hmhi⟩ := pairwise_mid.mp hmr
    have hk₁m : ∀ a ∈ m.keys, k₁ < a := fun a ha => hhi a (List.mem_append_left _ ha)
    have h₁₂ : k₁ < k₂ := hhi k₂ (List.mem_append_right _ List.mem_cons_self)
    simp only [keys_three, List.mem_append, List.mem_cons, not_or] at hx
    obtain ⟨hxl, hxk₁, hxm, hxk₂, hxr⟩ := hx
    rcases Nat.lt_trichotomy x k₁ with h | rfl | h
    · rw [show ((three l k₁ w₁ m k₂ w₂ r).ins x v).keys =
          (l.ins x v).keys ++ k₁ :: (m.keys ++ k₂ :: r.keys) by
        simp only [Ins.keys, keys, entries_ins_three_lt h (ins_ne_dup hxl), List.map_append,
          List.map_cons], pairwise_mid]
      exact ⟨ihl x v hl hxl, hmr, forall_mem_keys_ins hxl h hlo, hhi⟩
    · exact absurd rfl hxk₁
    rcases Nat.lt_trichotomy x k₂ with h' | rfl | h'
    · rw [show ((three l k₁ w₁ m k₂ w₂ r).ins x v).keys =
          l.keys ++ k₁ :: ((m.ins x v).keys ++ k₂ :: r.keys) by
        simp only [Ins.keys, keys, entries_ins_three_mid h h' (ins_ne_dup hxm),
          List.map_append, List.map_cons], pairwise_mid, pairwise_mid]
      refine ⟨hl, ⟨ihm x v hm hxm, hr, forall_mem_keys_ins hxm h' hmlo, hmhi⟩, hlo, ?_⟩
      exact List.forall_mem_append.mpr ⟨forall_mem_keys_ins hxm h hk₁m,
        fun b hb => hhi b (List.mem_append_right _ hb)⟩
    · exact absurd rfl hxk₂
    · rw [show ((three l k₁ w₁ m k₂ w₂ r).ins x v).keys =
          l.keys ++ k₁ :: (m.keys ++ k₂ :: (r.ins x v).keys) by
        simp only [Ins.keys, keys, entries_ins_three_gt h h' (ins_ne_dup hxr),
          List.map_append, List.map_cons], pairwise_mid, pairwise_mid]
      -- `k₁` bounds `r`'s new keys through `k₂`.
      have hk₁r : ∀ b ∈ (r.ins x v).keys, k₁ < b :=
        forall_mem_keys_ins hxr (Nat.lt_trans h₁₂ h') fun b hb => Nat.lt_trans h₁₂ (hmhi b hb)
      refine ⟨hl, ⟨hm, ihr x v hr hxr, hmlo, forall_mem_keys_ins hxr h' hmhi⟩, hlo, ?_⟩
      exact List.forall_mem_append.mpr ⟨hk₁m, List.forall_mem_cons.mpr ⟨h₁₂, hk₁r⟩⟩

/-- `insert?` fails exactly on a key the tree already has. -/
theorem insert?_eq_none_iff {t : NatTree23 β} (ho : t.Ordered) (x : Nat) (v : β) :
    t.insert? x v = none ↔ x ∈ t.keys := by
  rw [insert?, ← isSome_find?_iff ho, ← ins_eq_dup_iff t x v]
  cases t.ins x v <;> simp

/-- Where `insert?` succeeds, the key was not in the tree. -/
theorem insert?_ne_none {t t' : NatTree23 β} {x : Nat} {v : β} (ho : t.Ordered)
    (h : t.insert? x v = some t') : x ∉ t.keys := fun hm => by
  rw [(insert?_eq_none_iff ho x v).mpr hm] at h
  nomatch h

/-- Where `insert?` succeeds, the result holds exactly one more entry, and is ordered. -/
theorem insert?_spec {t t' : NatTree23 β} {x : Nat} {v : β} (ho : t.Ordered)
    (h : t.insert? x v = some t') :
    t'.Ordered ∧ ∀ p, p ∈ t'.entries ↔ p = (x, v) ∨ p ∈ t.entries := by
  have hx := insert?_ne_none ho h
  have hp := ordered_ins t x v ho hx
  have hmem := mem_entries_ins t x v hx
  rw [insert?] at h
  -- A split's halves become a `two` node, with the same keys and entries.
  cases hc : t.ins x v with
  | dup => exact absurd hc (ins_ne_dup hx)
  | ok | split =>
    rw [hc] at h hp hmem
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hp, hmem⟩

/-! ## Building from an array -/

/-- `insertArray?.go` on a non-empty list, as a bind. -/
private theorem go_cons {t : NatTree23 β} {p : Nat × β} {l : List (Nat × β)} :
    insertArray?.go t (p :: l) = (t.insert? p.1 p.2).bind (fun t' => insertArray?.go t' l) := by
  rw [insertArray?.go]; cases t.insert? p.1 p.2 <;> rfl

/-- Where `insertArray?.go` succeeds, the result is ordered and holds exactly the entries of
`l` and of `t`. -/
private theorem go_spec : ∀ (l : List (Nat × β)) (t t' : NatTree23 β), t.Ordered →
    insertArray?.go t l = some t' →
    t'.Ordered ∧ ∀ p, p ∈ t'.entries ↔ p ∈ l ∨ p ∈ t.entries := by
  intro l
  induction l with
  | nil =>
    intro t t' ho h
    simp only [insertArray?.go, Option.some.injEq] at h
    subst h
    exact ⟨ho, fun p => by simp only [List.not_mem_nil, false_or]⟩
  | cons p l ih =>
    intro t t' ho h
    rw [go_cons] at h
    cases hc : t.insert? p.1 p.2 with
    | none => rw [hc, Option.bind_none] at h; nomatch h
    | some t'' =>
      rw [hc, Option.bind_some] at h
      obtain ⟨ho'', hmem''⟩ := insert?_spec ho hc
      obtain ⟨ho', hmem'⟩ := ih t'' t' ho'' h
      refine ⟨ho', fun q => ?_⟩
      rw [hmem' q, hmem'' q, List.mem_cons, or_left_comm, or_assoc]

/-- `insertArray?.go` succeeds exactly when no key is repeated and none is already there. -/
private theorem go_isSome_iff : ∀ (l : List (Nat × β)) (t : NatTree23 β), t.Ordered →
    ((insertArray?.go t l).isSome = true ↔
      (l.map Prod.fst).Nodup ∧ ∀ p ∈ l, p.1 ∉ t.keys) := by
  intro l
  induction l with
  | nil => simp [insertArray?.go]
  | cons p l ih =>
    intro t ho
    rw [go_cons]
    cases hc : t.insert? p.1 p.2 with
    | none =>
      have hp : p.1 ∈ t.keys := (insert?_eq_none_iff ho p.1 p.2).mp hc
      simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
      exact fun _ hall => absurd hp (hall p List.mem_cons_self)
    | some t' =>
      obtain ⟨ho', hmem⟩ := insert?_spec ho hc
      have hp : p.1 ∉ t.keys := insert?_ne_none ho hc
      have hkeys : ∀ y, y ∈ t'.keys ↔ y = p.1 ∨ y ∈ t.keys := fun y => by
        simpa only [List.map_cons, List.map_nil, List.mem_singleton] using
          mem_keys_iff_of_entries (l := [(p.1, p.2)]) (by simpa only [List.mem_singleton]) y
      rw [Option.bind_some, ih t' ho']
      simp only [List.map_cons, List.nodup_cons, List.mem_map]
      -- `l`'s keys miss `t'` exactly when they miss `p.1` and `t`.
      constructor
      · rintro ⟨hnd, hfresh⟩
        refine ⟨⟨fun ⟨q, hq, hq'⟩ => hfresh q hq ((hkeys q.1).mpr (.inl hq')), hnd⟩,
          fun q hq hmq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp hmq
        · exact hfresh q hq ((hkeys q.1).mpr (.inr hmq))
      · rintro ⟨⟨hp₁, hnd⟩, hfresh⟩
        refine ⟨hnd, fun q hq hmq => ?_⟩
        rcases (hkeys q.1).mp hmq with he | he
        · exact hp₁ ⟨q, hq, he⟩
        · exact hfresh q (List.mem_cons_of_mem _ hq) he

/-- Where `insertArray?` succeeds, the result holds exactly the entries of `a` and of `t`. -/
theorem insertArray?_spec {a : Array (Nat × β)} {t t' : NatTree23 β} (ho : t.Ordered)
    (h : t.insertArray? a = some t') :
    t'.Ordered ∧ ∀ p, p ∈ t'.entries ↔ p ∈ a ∨ p ∈ t.entries := by
  rcases a with ⟨l⟩
  simpa only [List.mem_toArray] using go_spec l t t' ho h

/-- `insertArray?` succeeds exactly when no key is repeated and none is already there. -/
theorem insertArray?_isSome_iff {a : Array (Nat × β)} {t : NatTree23 β} (ho : t.Ordered) :
    (t.insertArray? a).isSome = true ↔
      (a.toList.map Prod.fst).Nodup ∧ ∀ p ∈ a, p.1 ∉ t.keys := by
  rcases a with ⟨l⟩
  simpa only [insertArray?, List.mem_toArray] using go_isSome_iff l t ho

/-- The empty tree is ordered. -/
private theorem ordered_leaf : (leaf : NatTree23 β).Ordered := List.Pairwise.nil

/-- The duplicate check: `ofArray?` succeeds exactly when no key occurs twice. -/
theorem ofArray?_isSome_iff {a : Array (Nat × β)} :
    (ofArray? a).isSome = true ↔ (a.toList.map Prod.fst).Nodup := by
  rw [ofArray?, insertArray?_isSome_iff ordered_leaf]
  simp only [keys_leaf, List.not_mem_nil, not_false_eq_true, implies_true, and_true]

/-- `ofArray?`'s result is ordered, so `find?` searches it correctly. -/
theorem ordered_ofArray? {a : Array (Nat × β)} {t : NatTree23 β} (h : ofArray? a = some t) :
    t.Ordered := (insertArray?_spec ordered_leaf h).1

/-- `ofArray?` holds exactly the entries of `a`. -/
theorem entries_ofArray? {a : Array (Nat × β)} {t : NatTree23 β} (h : ofArray? a = some t)
    (p : Nat × β) : p ∈ t.entries ↔ p ∈ a := by
  simpa only [entries_leaf, List.not_mem_nil, or_false] using (insertArray?_spec ordered_leaf h).2 p

/-- A lookup in `ofArray?`'s result is a lookup in `a`. -/
theorem find?_ofArray? {a : Array (Nat × β)} {t : NatTree23 β} (h : ofArray? a = some t)
    (x : Nat) (v : β) : t.find? x = some v ↔ (x, v) ∈ a := by
  rw [find?_eq_some_iff (ordered_ofArray? h) x v, entries_ofArray? h]

/-- `ofArray?`'s result has exactly `a`'s keys. -/
theorem mem_keys_ofArray? {a : Array (Nat × β)} {t : NatTree23 β} (h : ofArray? a = some t)
    (x : Nat) : x ∈ t.keys ↔ x ∈ a.map Prod.fst := by
  simpa using mem_keys_iff_of_entries (t := .leaf) (l := a.toList)
    (fun p => by simp [entries_ofArray? h]) x

/-- A key is found in `ofArray?`'s result exactly when `a` has it. -/
theorem isSome_find?_ofArray? {a : Array (Nat × β)} {t : NatTree23 β} (h : ofArray? a = some t)
    (x : Nat) : (t.find? x).isSome = true ↔ x ∈ a.map Prod.fst := by
  rw [isSome_find?_iff (ordered_ofArray? h), mem_keys_ofArray? h]

end NatTree23

end

end Strata.Mantle
