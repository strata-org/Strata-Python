/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all StrataDyn.Util.LabelMap

set_option autoImplicit false

/-!
# Facts about `NatTrie` and `LabelMap`

What `find?` gives on an empty trie or label map and after an `insert`, for the proofs about
the scoping checker (`StrataDyn/DomProps.lean`) and the dominator computation
(`StrataDyn/DomCompute.lean`).

## Main theorems

* `NatTrie.find?_insert`, `LabelMap.find?_insert`: `insert` maps its key to its value and keeps
  every other key;
* `LabelMap.isSome_find?_foldl_insert`: inserting a key for each element of a list maps exactly
  those keys and the keys the map had.

Everything here is private: a module that uses it imports it with `import all`.
-/

namespace Strata.Dyn

namespace NatTrie

variable {β : Type}

/-- The empty trie maps nothing. -/
@[simp] theorem find?_leaf (j : Nat) : (NatTrie.leaf : NatTrie β).find? j = none := by
  cases j <;> rfl

/-- Inserting with enough fuel maps the key to the value and keeps the rest. -/
theorem find?_insertAt (x : β) :
    ∀ (f : Nat) (t : NatTrie β) (k j : Nat), k < f →
      (insertAt x f t k).find? j = if j = k then some x else t.find? j
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, t, 0, j, _ => by cases t <;> cases j <;> simp [insertAt, find?]
  | f + 1, t, n + 1, j, h => by
    have ih := fun t j => find?_insertAt x f t (n / 2) j (by omega)
    cases j with
    | zero => cases t <;> simp only [insertAt] <;> split <;> rfl
    | succ m =>
      -- Key `m + 1` is key `m / 2` of the left subtree if `m` is even, of the right if odd.  The
      -- goals left after `simp` have `m ≠ n` of the same parity, so `m / 2 ≠ n / 2`.
      by_cases hmn : m = n
      · subst hmn
        cases t <;> by_cases hm : m % 2 = 0 <;> simp only [insertAt, find?, hm, ih, ↓reduceIte]
      · cases t <;> by_cases hn : n % 2 = 0 <;> by_cases hm : m % 2 = 0 <;>
          simp only [insertAt, find?, hn, hm, hmn, ih, ↓reduceIte, Nat.add_right_cancel_iff] <;>
          rw [ite_eq_right (by omega)]

/-- Inserting maps the key to the value and keeps the rest. -/
theorem find?_insert (t : NatTrie β) (k : Nat) (x : β) (j : Nat) :
    (t.insert k x).find? j = if j = k then some x else t.find? j :=
  find?_insertAt x _ t k j (Nat.lt_succ_self k)

end NatTrie

namespace LabelMap

variable {β : Type}

/-- The empty label map maps nothing. -/
@[simp] theorem find?_empty (l : Label) : (∅ : LabelMap β).find? l = none := by
  simp [EmptyCollection.emptyCollection, find?, bucket]

/-- Inserting maps the key to the value and keeps the rest. -/
theorem find?_insert (m : LabelMap β) (l : Label) (x : β) (l₁ : Label) :
    (m.insert l x).find? l₁ = if l₁ = l then some x else m.find? l₁ := by
  simp only [find?, bucket, insert, NatTrie.find?_insert]
  by_cases hk : l₁.key = l.key
  · by_cases hl : l₁ = l
    · subst hl; simp
    · simp [hk, hl, Ne.symm hl]
  · have hl : l₁ ≠ l := fun h => hk (h ▸ rfl)
    simp [hk, hl]

/-- Inserting the key `key x` of each element `x` of `xs` into `m`, whatever the values, maps
exactly the labels that `m` maps and the keys of `xs`. -/
theorem isSome_find?_foldl_insert {γ : Type} (key : γ → Label) (val : γ → β) :
    ∀ (xs : List γ) (m : LabelMap β) (l : Label),
      ((xs.foldl (fun m x => m.insert (key x) (val x)) m).find? l).isSome = true ↔
        (m.find? l).isSome = true ∨ ∃ x ∈ xs, key x = l
  | [], _, _ => by simp
  | x :: xs, m, l => by
    rw [List.foldl_cons, isSome_find?_foldl_insert key val xs, find?_insert]
    by_cases hl : l = key x
    · simp [hl]
    · simp only [hl, ite_false, List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl h
        · exact absurd h.symm hl
        · exact .inr h

end LabelMap

end Strata.Dyn
