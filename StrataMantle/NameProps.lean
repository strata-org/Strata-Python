/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Name

set_option autoImplicit false

/-!
# Hierarchical names: properties

* The order on `Name` is a lawful total order: `Std.TransOrd Name` and `Std.LawfulEqOrd Name`.
* `key_inj`: `Name.key` is injective.
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
theorem length_segs : ∀ n : Name, (segs n).length = n.depth
| .base => rfl
| .num n _ => by simp [segs, depth, length_segs n]
| .str n _ => by simp [segs, depth, length_segs n]

/-- A name is determined by its segments. -/
theorem segs_inj : ∀ {x y : Name}, segs x = segs y → x = y
| .base, .base, _ => rfl
| .base, .num _ _, h | .base, .str _ _, h => by simp [segs] at h
| .num _ _, .base, h | .str _ _, .base, h => by simp [segs] at h
| .num a i, .num b j, h | .num a i, .str b j, h
| .str a i, .num b j, h | .str a i, .str b j, h => by
    simp only [segs] at h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    simp at h2 <;> simp_all [segs_inj h1]

/-- Comparing equal-length prefixes first, then the rest, is lexicographic order. -/
theorem compareLex_append {xs ys r s : List (Option String × Nat)}
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
theorem compare_seg (a b : Option String) (i j : Nat) :
    compare (a, i) (b, j) = (compare a b).then (compare i j) := rfl

/-- On names of equal depth, `cmpAligned` is lexicographic order on segments. -/
theorem cmpAligned_eq : ∀ {x y : Name}, x.depth = y.depth →
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
theorem segs_dropOuter : ∀ (n : Name) (k : Nat), k ≤ n.depth →
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
theorem compare_eq_compareLex (x y : Name) :
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

/-! ### `key` is injective

`key n` is `digVal (keyDigits n)`, a numeral determines its digits (`digVal_inj`), and the
digits determine the name (`keyDigits_inj`).  A segment's digits are below `256` and every
marker is at least `256`, so each marker ends a segment. -/

/-- A base-259 numeral, least significant digit first. -/
def digVal : List Nat → Nat
  | [] => 0
  | d :: ds => d + 259 * digVal ds

@[simp] theorem digVal_nil : digVal [] = 0 := rfl

@[simp] theorem digVal_cons (d : Nat) (ds : List Nat) :
    digVal (d :: ds) = d + 259 * digVal ds := rfl

/-- A base-256 numeral, least significant digit first. -/
def natVal : List Nat → Nat
  | [] => 0
  | d :: ds => d + 256 * natVal ds

/-- The base-256 digits of `n`, least significant first, in at most `fuel` digits. -/
def natDigits : (fuel n : Nat) → List Nat
  | 0, _ => []
  | _+1, 0 => []
  | f+1, n+1 => (n+1) % 256 :: natDigits f ((n+1) / 256)

/-- The base-259 digits of `key n`, least significant first. -/
def keyDigits : Name → List Nat
  | .base => [258]
  | .num n i => 257 :: (natDigits i i ++ keyDigits n)
  | .str n s => 256 :: (s.toByteArray.data.toList.map UInt8.toNat ++ keyDigits n)

/-- `keyNatAux` writes `natDigits` below the digits it is given. -/
theorem digVal_natDigits : ∀ (f n : Nat) (l : List Nat),
    digVal (natDigits f n ++ l) = keyNatAux f n (digVal l)
  | 0, _, _ => rfl
  | _+1, 0, _ => rfl
  | f+1, n+1, l => by
      simp only [natDigits, keyNatAux, List.cons_append, digVal_cons, digVal_natDigits f _ l]

/-- `keyBytes` writes a segment's bytes below the digits it is given. -/
theorem digVal_bytes : ∀ (bs : List UInt8) (l : List Nat),
    digVal (bs.map UInt8.toNat ++ l) = keyBytes bs (digVal l)
  | [], _ => rfl
  | _ :: bs, l => by
      simp only [List.map_cons, List.cons_append, digVal_cons, keyBytes, digVal_bytes bs l]

/-- `key` is the numeral `keyDigits` spells. -/
theorem key_eq_digVal : ∀ n : Name, key n = digVal (keyDigits n)
  | .base => rfl
  | .num n i => by
      simp only [key, keyDigits, keyNat, digVal_cons, digVal_natDigits, key_eq_digVal n]
  | .str n s => by simp only [key, keyDigits, digVal_cons, digVal_bytes, key_eq_digVal n]

/-- `natDigits` are base-256 digits. -/
theorem natDigits_lt : ∀ (f n : Nat), ∀ d ∈ natDigits f n, d < 256
  | 0, _, _, h | _+1, 0, _, h => by simp only [natDigits, List.not_mem_nil] at h
  | f+1, n+1, d, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.mod_lt _ (by decide)
      · exact natDigits_lt f _ d h

/-- `natDigits` spells `n`, given enough digits. -/
theorem natVal_natDigits : ∀ (f n : Nat), n ≤ f → natVal (natDigits f n) = n
  | 0, 0, _ => rfl
  | 0, _+1, h => by omega
  | _+1, 0, _ => rfl
  | f+1, n+1, h => by
      have hf : (n+1) / 256 ≤ f := by omega
      simp only [natDigits, natVal, natVal_natDigits f _ hf]
      omega

/-- The digits of a name end with the root's `258`, and the rest are base-259 digits. -/
theorem keyDigits_eq : ∀ n : Name,
    ∃ pre, keyDigits n = pre ++ [258] ∧ ∀ d ∈ pre, d < 259
  | .base => ⟨[], rfl, by simp⟩
  | .num n i => by
      obtain ⟨pre, hpre, hlt⟩ := keyDigits_eq n
      refine ⟨257 :: (natDigits i i ++ pre),
        by simp only [keyDigits, hpre, List.cons_append, List.append_assoc], ?_⟩
      simp only [List.forall_mem_cons, List.forall_mem_append]
      exact ⟨by decide, fun d hd => Nat.lt_trans (natDigits_lt i i d hd) (by decide), hlt⟩
  | .str n s => by
      obtain ⟨pre, hpre, hlt⟩ := keyDigits_eq n
      refine ⟨256 :: (s.toByteArray.data.toList.map UInt8.toNat ++ pre),
        by simp only [keyDigits, hpre, List.cons_append, List.append_assoc], ?_⟩
      simp only [List.forall_mem_cons, List.forall_mem_append, List.forall_mem_map]
      exact ⟨by decide, fun b _ => Nat.lt_trans b.toNat_lt_size (by decide), hlt⟩

/-- A numeral that ends in `258` is at least `258`. -/
theorem le_digVal : ∀ l : List Nat, 258 ≤ digVal (l ++ [258])
  | [] => by simp
  | _ :: l => by have := le_digVal l; simp only [List.cons_append, digVal_cons]; omega

/-- A numeral that ends in `258` determines its digits. -/
theorem digVal_inj : ∀ (l m : List Nat), (∀ d ∈ l, d < 259) → (∀ d ∈ m, d < 259) →
    digVal (l ++ [258]) = digVal (m ++ [258]) → l = m
  | [], [], _, _, _ => rfl
  -- `[258]` spells `258`, and a longer numeral ending in `258` is at least `259 * 258`.
  | [], e :: m, _, hm, h => by
      have := le_digVal m
      have he : e < 259 := hm e List.mem_cons_self
      simp only [List.nil_append, List.cons_append, digVal_cons, digVal_nil] at h
      omega
  | d :: l, [], hl, _, h => by
      have := le_digVal l
      have hd : d < 259 := hl d List.mem_cons_self
      simp only [List.nil_append, List.cons_append, digVal_cons, digVal_nil] at h
      omega
  | d :: l, e :: m, hl, hm, h => by
      obtain ⟨hd, hl'⟩ := List.forall_mem_cons.mp hl
      obtain ⟨he, hm'⟩ := List.forall_mem_cons.mp hm
      simp only [List.cons_append, digVal_cons] at h
      -- Both digits are below the base, so they are the numerals' remainders mod 259.
      obtain rfl : d = e := by omega
      rw [digVal_inj l m hl' hm' (by omega)]

/-- A string is determined by its bytes. -/
theorem string_of_bytes {s t : String}
    (h : s.toByteArray.data.toList = t.toByteArray.data.toList) : s = t :=
  String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp h))

/-- A name's digits start with a marker, at least `256`. -/
theorem keyDigits_head : ∀ n : Name, ∃ c r, keyDigits n = c :: r ∧ 256 ≤ c
  | .base => ⟨258, [], rfl, by omega⟩
  | .num n i => ⟨257, natDigits i i ++ keyDigits n, rfl, by omega⟩
  | .str n s => ⟨256, s.toByteArray.data.toList.map UInt8.toNat ++ keyDigits n, rfl, by omega⟩

/-- A run of segment digits is separated from the next marker, so the split is unique. -/
theorem append_inj_of_lt : ∀ (l₁ l₂ : List Nat) (c₁ c₂ : Nat) (r₁ r₂ : List Nat),
    (∀ d ∈ l₁, d < 256) → (∀ d ∈ l₂, d < 256) → 256 ≤ c₁ → 256 ≤ c₂ →
    l₁ ++ c₁ :: r₁ = l₂ ++ c₂ :: r₂ → l₁ = l₂ ∧ c₁ :: r₁ = c₂ :: r₂
  | [], [], _, _, _, _, _, _, _, _, h => ⟨rfl, h⟩
  | [], e :: l₂, c₁, _, _, _, _, h₂, hc₁, _, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have := h₂ e List.mem_cons_self
      omega
  | d :: l₁, [], _, c₂, _, _, h₁, _, _, hc₂, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have := h₁ d List.mem_cons_self
      omega
  | d :: l₁, e :: l₂, c₁, c₂, r₁, r₂, h₁, h₂, hc₁, hc₂, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨hl, hr⟩ := append_inj_of_lt l₁ l₂ c₁ c₂ r₁ r₂
        (List.forall_mem_cons.mp h₁).2 (List.forall_mem_cons.mp h₂).2 hc₁ hc₂ h
      exact ⟨by rw [hl], hr⟩

/-- A name is determined by its digits. -/
theorem keyDigits_inj : ∀ {x y : Name}, keyDigits x = keyDigits y → x = y
  | .base, .base, _ => rfl
  | .base, .num _ _, h | .base, .str _ _, h
  | .num _ _, .base, h | .str _ _, .base, h
  | .num _ _, .str _ _, h | .str _ _, .num _ _, h => by simp [keyDigits] at h
  | .num a i, .num b j, h => by
      obtain ⟨c₁, r₁, hc₁, hb₁⟩ := keyDigits_head a
      obtain ⟨c₂, r₂, hc₂, hb₂⟩ := keyDigits_head b
      simp only [keyDigits, hc₁, hc₂, List.cons.injEq, true_and] at h
      -- The number's digits run up to the first marker of `a`'s or `b`'s digits.
      obtain ⟨hd, hr⟩ := append_inj_of_lt _ _ c₁ c₂ r₁ r₂
        (natDigits_lt i i) (natDigits_lt j j) hb₁ hb₂ h
      obtain rfl : i = j := by
        rw [← natVal_natDigits i i (Nat.le_refl i), hd, natVal_natDigits j j (Nat.le_refl j)]
      rw [keyDigits_inj (hc₁.trans (hr.trans hc₂.symm))]
  | .str a s, .str b t, h => by
      obtain ⟨c₁, r₁, hc₁, hb₁⟩ := keyDigits_head a
      obtain ⟨c₂, r₂, hc₂, hb₂⟩ := keyDigits_head b
      simp only [keyDigits, hc₁, hc₂, List.cons.injEq, true_and] at h
      -- The string's bytes run up to the first marker of `a`'s or `b`'s digits.
      obtain ⟨hd, hr⟩ := append_inj_of_lt _ _ c₁ c₂ r₁ r₂
        (List.forall_mem_map.mpr fun u _ => u.toNat_lt_size)
        (List.forall_mem_map.mpr fun u _ => u.toNat_lt_size) hb₁ hb₂ h
      obtain rfl : s = t :=
        string_of_bytes ((List.map_inj_right fun _ _ => UInt8.toNat_inj.mp).mp hd)
      rw [keyDigits_inj (hc₁.trans (hr.trans hc₂.symm))]

/-- `key` is injective. -/
public theorem key_inj {x y : Name} (h : key x = key y) : x = y := by
  obtain ⟨p, hp, hp'⟩ := keyDigits_eq x
  obtain ⟨q, hq, hq'⟩ := keyDigits_eq y
  rw [key_eq_digVal, key_eq_digVal, hp, hq] at h
  exact keyDigits_inj (by rw [hp, hq, digVal_inj p q hp' hq' h])

/-- Keys are equal exactly when names are. -/
@[simp, grind =] public theorem key_eq_key {x y : Name} : key x = key y ↔ x = y :=
  ⟨key_inj, fun h => h ▸ rfl⟩

end Name

end Strata.Mantle
