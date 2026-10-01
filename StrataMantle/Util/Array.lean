/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# Array utilities to help with kernel evaluation of array literals.

Nothing here is public; a module that uses it imports it with `import all`.
-/

namespace Array

variable {α β : Type _}

/-- `R` holds of every pair of elements, the earlier one first. -/
def Pairwise (R : α → α → Prop) : Array α → Prop
  | ⟨l⟩ => l.Pairwise R

/-- No element occurs twice. -/
def Nodup (as : Array α) : Prop := as.Pairwise (· ≠ ·)

instance instDecidablePairwise (R : α → α → Prop) [DecidableRel R] :
    (as : Array α) → Decidable (as.Pairwise R)
  | ⟨l⟩ => inferInstanceAs (Decidable (l.Pairwise R))

instance [DecidableEq α] (as : Array α) : Decidable as.Nodup :=
  instDecidablePairwise _ as

/-- `Array.all` in a form `decide` can evaluate. -/
def allK (p : α → Bool) : Array α → Bool
  | ⟨l⟩ => l.all p

/-- `allK` computes `Array.all`. -/
@[simp] theorem allK_eq_all {p : α → Bool} {as : Array α} : as.allK p = as.all p := by
  cases as; simp [allK]

/-- `Array.map` in a form `decide` can evaluate. -/
def mapK (f : α → β) : Array α → Array β
  | ⟨l⟩ => ⟨l.map f⟩

/-- `mapK` computes `Array.map`. -/
@[simp] theorem mapK_eq_map {f : α → β} {as : Array α} : as.mapK f = as.map f := by
  cases as; simp [mapK]

/-- `Pairwise` on an array literal is `Pairwise` on its list. -/
@[simp, grind =] theorem pairwise_toArray {R : α → α → Prop} {l : List α} :
    l.toArray.Pairwise R ↔ l.Pairwise R := Iff.rfl

/-- `Nodup` on an array literal is `Nodup` on its list. -/
@[simp, grind =] theorem nodup_toArray {l : List α} : l.toArray.Nodup ↔ l.Nodup := Iff.rfl

/-- `Pairwise` on an array's list is `Pairwise` on the array. -/
theorem pairwise_toList {R : α → α → Prop} {as : Array α} :
    as.toList.Pairwise R ↔ as.Pairwise R := by
  cases as; rfl

/-- `Nodup` on an array's list is `Nodup` on the array. -/
theorem nodup_toList {as : Array α} : as.toList.Nodup ↔ as.Nodup := by
  cases as; rfl

/-- A mapped array is pairwise `R` exactly when the original is, with `R` read through
`f`. -/
theorem pairwise_map {R : β → β → Prop} {f : α → β} {as : Array α} :
    (as.map f).Pairwise R ↔ as.Pairwise fun a b => R (f a) (f b) := by
  rw [← pairwise_toList, ← pairwise_toList, Array.toList_map, List.pairwise_map]

/-- A concatenation is pairwise `R` exactly when each side is and `R` holds from every
element of the first to every element of the second. -/
theorem pairwise_append {R : α → α → Prop} {as bs : Array α} :
    (as ++ bs).Pairwise R ↔
      as.Pairwise R ∧ bs.Pairwise R ∧ ∀ a ∈ as, ∀ b ∈ bs, R a b := by
  rw [← pairwise_toList, ← pairwise_toList, ← pairwise_toList, Array.toList_append,
    List.pairwise_append]
  simp only [Array.mem_toList_iff]

/-- A concatenation has no duplicates exactly when neither side does and the two share no
element. -/
theorem nodup_append {as bs : Array α} :
    (as ++ bs).Nodup ↔ as.Nodup ∧ bs.Nodup ∧ ∀ a ∈ as, ∀ b ∈ bs, a ≠ b :=
  pairwise_append

end Array
