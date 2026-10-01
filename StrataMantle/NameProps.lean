/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Name

set_option autoImplicit false

/-!
# Hierarchical names: properties

The order on `Name` is a lawful total order: `Std.TransOrd Name` and `Std.LawfulEqOrd Name`.
-/

namespace Strata.Mantle

namespace Name

-- Segments as pairs, ordered lexicographically: a numeric segment `(none, i)` sorts before
-- every string segment `(some s, 0)`.
attribute [local instance] lexOrd

/-- The segments of a name, root first. -/
def segs : Name → List (Option String × Nat)
| .base => []
| .num n i => segs n ++ [(none, i)]
| .str n s => segs n ++ [(some s, 0)]

/-- A name has one segment per unit of depth. -/
private theorem length_segs : ∀ n : Name, (segs n).length = n.depth
| .base => rfl
| .num n _ => by simp [segs, depth, length_segs n]
| .str n _ => by simp [segs, depth, length_segs n]

/-- A name is determined by its segments. -/
private theorem segs_inj : ∀ {x y : Name}, segs x = segs y → x = y
| .base, .base, _ => rfl
| .base, .num _ _, h | .base, .str _ _, h => by simp [segs] at h
| .num _ _, .base, h | .str _ _, .base, h => by simp [segs] at h
| .num a i, .num b j, h | .num a i, .str b j, h
| .str a i, .num b j, h | .str a i, .str b j, h => by
    simp only [segs] at h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    simp at h2 <;> simp_all [segs_inj h1]

/-- Comparing equal-length prefixes first, then the rest, is lexicographic order. -/
private theorem compareLex_append {xs ys r s : List (Option String × Nat)}
    (h : xs.length = ys.length) :
    List.compareLex compare (xs ++ r) (ys ++ s) =
      (List.compareLex compare xs ys).then (List.compareLex compare r s) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [List.compareLex_nil_nil] <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp [List.compareLex_cons_cons, ih (by simpa using h), Ordering.then_assoc]

/-- Segments compare by kind and string first, then by number. -/
private theorem compare_seg (a b : Option String) (i j : Nat) :
    compare (a, i) (b, j) = (compare a b).then (compare i j) := rfl

/-- On names of equal depth, `cmpAligned` is lexicographic order on segments. -/
private theorem cmpAligned_eq : ∀ {x y : Name}, x.depth = y.depth →
    cmpAligned x y = List.compareLex compare (segs x) (segs y)
| .base, .base, _ => rfl
| .base, .num _ _, h | .base, .str _ _, h => by simp [depth] at h
| .num _ _, .base, h | .str _ _, .base, h => by simp [depth] at h
| .num a i, .num b j, h | .num a i, .str b j, h
| .str a i, .num b j, h | .str a i, .str b j, h => by
    have h' : a.depth = b.depth := by simpa [depth] using h
    simp only [cmpAligned, segs, cmpAligned_eq h',
      compareLex_append ((length_segs a).trans (h'.trans (length_segs b).symm))]
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, compare_seg, cmpStr_eq_compare]
      <;> rfl

/-- Dropping `k` outer segments leaves a prefix of the segment list. -/
private theorem segs_dropOuter : ∀ (n : Name) (k : Nat), k ≤ n.depth →
    ∃ t, segs n = segs (n.dropOuter k) ++ t ∧ t.length = k
| _, 0, _ => ⟨[], by simp [dropOuter]⟩
| .base, _+1, h => by simp [depth] at h
| .num b i, k+1, h => by
    obtain ⟨t, ht, hl⟩ := segs_dropOuter b k (by simpa [depth] using h)
    exact ⟨t ++ [(none, i)], by simp [segs, dropOuter, ht], by simp [hl]⟩
| .str b s, k+1, h => by
    obtain ⟨t, ht, hl⟩ := segs_dropOuter b k (by simpa [depth] using h)
    exact ⟨t ++ [(some s, 0)], by simp [segs, dropOuter, ht], by simp [hl]⟩

/-- `compare` is the lexicographic order on segments. -/
private theorem compare_eq_compareLex (x y : Name) :
    compare x y = List.compareLex compare (segs x) (segs y) := by
  show Name.compare x y = _
  unfold Name.compare
  rcases Nat.lt_trichotomy x.depth y.depth with h | h | h
  · obtain ⟨t, ht, hl⟩ := segs_dropOuter y (y.depth - x.depth) (by omega)
    have hd : x.depth = (y.dropOuter (y.depth - x.depth)).depth := by
      have := congrArg List.length ht; simp [length_segs] at this; omega
    obtain ⟨u, us, rfl⟩ :=
      List.exists_cons_of_ne_nil (l := t) (by rintro rfl; simp at hl; omega)
    simp only [Nat.compare_eq_lt.mpr h]
    rw [ht, ← List.append_nil (segs x),
      compareLex_append (by simpa [length_segs] using hd), ← cmpAligned_eq hd]
    cases cmpAligned x _ <;> simp [List.compareLex_nil_cons]
  · simp only [Nat.compare_eq_eq.mpr h]
    exact cmpAligned_eq h
  · obtain ⟨t, ht, hl⟩ := segs_dropOuter x (x.depth - y.depth) (by omega)
    have hd : (x.dropOuter (x.depth - y.depth)).depth = y.depth := by
      have := congrArg List.length ht; simp [length_segs] at this; omega
    obtain ⟨u, us, rfl⟩ :=
      List.exists_cons_of_ne_nil (l := t) (by rintro rfl; simp at hl; omega)
    simp only [Nat.compare_eq_gt.mpr h]
    rw [ht, ← List.append_nil (segs y),
      compareLex_append (by simpa [length_segs] using hd), ← cmpAligned_eq hd]
    cases cmpAligned _ y <;> simp [List.compareLex_cons_nil]

public instance : Std.TransOrd Name := by
  have : (compare : Name → Name → Ordering) = compareOn segs := by
    funext x y; exact compare_eq_compareLex x y
  unfold Std.TransOrd; rw [this]; infer_instance

public instance : Std.LawfulEqOrd Name where
  eq_of_compare {x y} h := by
    rw [compare_eq_compareLex] at h
    exact segs_inj (Std.LawfulEqCmp.eq_of_compare h)

end Name

end Strata.Mantle
