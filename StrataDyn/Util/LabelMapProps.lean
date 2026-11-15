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
  those keys and the keys the map had;
* `LabelMap.find?_foldl_insert_fun`: inserting each label of a list with a value that depends on
  the label maps exactly those labels to those values;
* `LabelMap.find?_update`: `update` maps its key to the new value and keeps every other key;
* `LabelMap.ofDistinct?_isSome_iff`: `ofDistinct?` succeeds exactly on labels without duplicates.

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

/-- Inserting each `x` of `xs` with the value `f x`: the map gives `f x` for the labels of `xs`,
and what `m` gives for the others. -/
theorem find?_foldl_insert_fun (f : Label → β) :
    ∀ (xs : List Label) (m : LabelMap β) (l : Label),
      (xs.foldl (fun m x => m.insert x (f x)) m).find? l = if l ∈ xs then some (f l) else m.find? l
  | [], m, l => by simp
  | x :: xs, m, l => by
    rw [List.foldl_cons, find?_foldl_insert_fun f xs, find?_insert]
    by_cases hx : l = x
    · subst hx; simp
    · by_cases hl : l ∈ xs
      · simp [hl]
      · simp [hl, hx]

/-- Updating maps the key to `f` of its old value and keeps the rest. -/
theorem find?_update (m : LabelMap β) (l : Label) (f : Option β → β) (l₁ : Label) :
    (m.update l f).find? l₁ = if l₁ = l then some (f (m.find? l)) else m.find? l₁ := by
  by_cases hl : l₁ = l
  · subst hl
    simp [update, find?, bucket, NatTrie.find?_insert]
  · rw [ite_eq_right hl]
    unfold update find? bucket
    rw [NatTrie.find?_insert]
    by_cases hk : l₁.key = l.key
    · rw [ite_eq_left hk, Option.getD_some, List.find?_cons, hk, List.find?_filter]
      simp only [Ne.symm hl, decide_false]
      congr 2
      funext p
      by_cases hp : p.1 = l₁
      · simp [hp, hl]
      · simp [hp]
    · rw [ite_eq_right hk]

/-- The step of `ofDistinct?` from a set `m` of the labels `seen` succeeds exactly when
`seen ++ ls` has no duplicates, provided `seen` has none. -/
private theorem foldlM_distinct_isSome :
    ∀ (ls seen : List Label) (m : LabelMap Unit),
      (∀ l, (m.find? l).isSome ↔ l ∈ seen) → seen.Nodup →
      ((ls.foldlM (fun (m : LabelMap Unit) l =>
        if (m.find? l).isSome then none else some (m.insert l ())) m).isSome ↔ (seen ++ ls).Nodup)
  | [], seen, _, _, hn => by simpa using hn
  | l :: ls, seen, m, hm, hn => by
    rw [List.foldlM_cons]
    by_cases hl : (m.find? l).isSome = true
    · rw [ite_eq_left hl]
      simp only [Option.bind_eq_bind, Option.bind_none, Option.isSome_none, Bool.false_eq_true,
        false_iff]
      intro hd
      exact (List.nodup_append.mp hd).2.2 l ((hm l).mp hl) l List.mem_cons_self rfl
    · rw [ite_eq_right hl]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hl₁ : l ∉ seen := fun h₁ => hl ((hm l).mpr h₁)
      have hm₁ : ∀ l₁, ((m.insert l ()).find? l₁).isSome ↔ l₁ ∈ seen ++ [l] := by
        intro l₁
        rw [find?_insert]
        by_cases h₂ : l₁ = l
        · simp [h₂]
        · simp [h₂, hm l₁]
      have hn₁ : (seen ++ [l]).Nodup :=
        List.nodup_append.mpr ⟨hn, List.pairwise_singleton _ l, fun a ha b hb hab => by
          rw [List.mem_singleton] at hb
          exact hl₁ (hb ▸ hab ▸ ha)⟩
      rw [foldlM_distinct_isSome ls (seen ++ [l]) _ hm₁ hn₁]
      simp

/-- `ofDistinct? ls` succeeds exactly when `ls` has no duplicates. -/
theorem ofDistinct?_isSome_iff {ls : List Label} :
    (ofDistinct? ls).isSome ↔ ls.Nodup := by
  have h := foldlM_distinct_isSome ls [] ∅ (fun l => by simp) List.nodup_nil
  simpa [ofDistinct?] using h

end LabelMap

end Strata.Dyn
