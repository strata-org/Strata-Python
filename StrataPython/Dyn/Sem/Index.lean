/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashMap.Lemmas

set_option autoImplicit false

/-!
# Indexes of an array

Two kinds of index of an array `es`, each a `Std.HashMap` that carries the proof that it equals
a scan of `es`:
* `Index f es` maps each key `k` to the positions `i` with `f es[i] = some k`, in order
  (`positionsBy`);
* `Groups f es`, for a key that is a pair `(c, k)`, maps each class `c` to the number of
  elements of each key `k`, so that `Groups.count c` is the number of distinct keys of class `c`
  (`Groups.count_spec`, in `IndexProps.lean`).

Each update (`push`, `set`, `pop`) changes the map in place.  It takes O(1) expected time, except
`Index.setNone`, which also filters the positions of the old element's key.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- The positions of the elements `x` of `es` with `f x = some k`, in order. -/
def positionsBy {α K : Type} [BEq K] (f : α → Option K) (es : Array α) (k : K) : Array Nat :=
  ((List.range es.size).filter fun i => (es[i]?.bind f) == some k).toArray

/-- The number of elements `x` of `es` with `f x = some k`. -/
def countBy {α K : Type} [BEq K] (f : α → Option K) (es : Array α) (k : K) : Nat :=
  es.toList.countP fun x => f x == some k

/-- `n`, or `none` for `0`: what a count map holds for a key, which is absent when its count is
`0`. -/
def nz (n : Nat) : Option Nat := if n = 0 then none else some n

/-- An index of the positions of `es` by `f`, with the proof that it equals the scan. -/
structure Index (α K : Type) [BEq K] [Hashable K] (f : α → Option K) (es : Array α) where
  map : Std.HashMap K (Array Nat)
  wf : ∀ k, map.getD k #[] = positionsBy f es k

/-- The number of elements of each key `(c, k)` of `es`, grouped by `c`, with the proof that it
equals the scan. -/
structure Groups (α C K : Type) [BEq C] [Hashable C] [BEq K] [Hashable K]
    (f : α → Option (C × K)) (es : Array α) where
  map : Std.HashMap C (Std.HashMap K Nat)
  wf : ∀ c k, (map.getD c ∅)[k]? = nz (countBy f es (c, k))

section Lemmas
variable {α K : Type} [BEq K] [LawfulBEq K] (f : α → Option K)

omit [LawfulBEq K] in
/-- Appending `x` adds its position to the scan of its own key, and to no other. -/
private theorem positionsBy_push (es : Array α) (x : α) (k : K) :
    positionsBy f (es.push x) k =
      if f x == some k then (positionsBy f es k).push es.size else positionsBy f es k := by
  unfold positionsBy
  rw [Array.size_push, List.range_succ, List.filter_append]
  have hold : (List.range es.size).filter (fun i => ((es.push x)[i]?.bind f) == some k)
      = (List.range es.size).filter (fun i => (es[i]?.bind f) == some k) := by
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    simp [Array.getElem?_push, hi, Nat.ne_of_lt hi]
  rw [hold]
  by_cases hx : f x == some k
  · simp [hx]
  · simp [hx]

omit [LawfulBEq K] in
/-- Replacing the element at `i` by one without a key removes `i` from every scan. -/
private theorem positionsBy_set_none (es : Array α) (i : Nat) (hi : i < es.size) (x : α) (hx : f x = none)
    (k : K) : positionsBy f (es.set i x hi) k = (positionsBy f es k).filter (· != i) := by
  unfold positionsBy
  rw [Array.size_set, List.filter_toArray, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro j _
  by_cases hji : j = i
  · subst hji; simp [hx]
  · simp [Ne.symm hji, hji]

/-- A non-empty array is its `pop` with its last element pushed back. -/
private theorem pop_push_last {α : Type} (es : Array α) (h : 0 < es.size) :
    es = es.pop.push es[es.size - 1] := by
  apply Array.ext
  · simp; omega
  · intro j h1 h2
    simp only [Array.getElem_push, Array.size_pop, Array.getElem_pop]
    split
    · rfl
    · congr; simp at h2; omega

/-- If the last element of a non-empty array has no key, the element at `size - 1` has none. -/
private theorem back?_bind_none {α K : Type} (f : α → Option K) (es : Array α) (h : 0 < es.size)
    (hb : (es.back?.bind f) = none) : f es[es.size - 1] = none := by
  have hback : es.back? = some es[es.size - 1] := by
    rw [Array.back?_eq_getElem?]; simp
  simpa [hback] using hb

omit [LawfulBEq K] in
/-- Dropping a last element that has no key leaves every scan as it is. -/
private theorem positionsBy_pop (es : Array α) (hb : (es.back?.bind f) = none) (k : K) :
    positionsBy f es.pop k = positionsBy f es k := by
  rcases Nat.eq_zero_or_pos es.size with h0 | hpos
  · have : es = #[] := Array.eq_empty_of_size_eq_zero h0
    subst this; rfl
  · conv => rhs; rw [pop_push_last es hpos]
    rw [positionsBy_push]
    simp [back?_bind_none f es hpos hb]

/-- A position is in the scan of `k` exactly when its element has the key `k`. -/
private theorem mem_positionsBy (es : Array α) (k : K) (j : Nat) :
    j ∈ positionsBy f es k ↔ j < es.size ∧ (es[j]?.bind f) = some k := by
  simp [positionsBy, List.mem_filter]

/-- A position whose element has another key is not in the scan of `k`. -/
private theorem not_mem_positionsBy (es : Array α) (k : K) (i : Nat) (hi : i < es.size)
    (hk : f es[i] ≠ some k) : i ∉ positionsBy f es k := by
  rw [mem_positionsBy]
  simp [hi, hk]

/-- Removing a position that an array doesn't hold leaves it as it is. -/
private theorem filter_ne_of_not_mem (a : Array Nat) (i : Nat) (h : i ∉ a) :
    a.filter (· != i) = a := by
  rw [Array.filter_eq_self]
  intro j hj
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  exact h hj

omit [LawfulBEq K] in
/-- Appending `x` adds one to the count of its own key. -/
private theorem countBy_push (es : Array α) (x : α) (k : K) :
    countBy f (es.push x) k = countBy f es k + if f x == some k then 1 else 0 := by
  simp [countBy, List.countP_append]

omit [LawfulBEq K] in
/-- Replacing the element at `i` moves one from the count of its old key to its new one. -/
private theorem countBy_set (es : Array α) (i : Nat) (hi : i < es.size) (x : α) (k : K) :
    countBy f (es.set i x hi) k =
      (countBy f es k - if f es[i] == some k then 1 else 0) + if f x == some k then 1 else 0 := by
  unfold countBy
  rw [Array.toList_set, List.countP_set (by simpa using hi)]
  simp

omit [LawfulBEq K] in
/-- Dropping a last element that has no key leaves every count as it is. -/
private theorem countBy_pop (es : Array α) (hb : (es.back?.bind f) = none) (k : K) :
    countBy f es.pop k = countBy f es k := by
  rcases Nat.eq_zero_or_pos es.size with h0 | hpos
  · have : es = #[] := Array.eq_empty_of_size_eq_zero h0
    subst this; rfl
  · conv => rhs; rw [pop_push_last es hpos]
    rw [countBy_push]
    simp [back?_bind_none f es hpos hb]

end Lemmas

/-- `(nz n).getD 0` is `n`. -/
private theorem nz_getD (n : Nat) : (nz n).getD 0 = n := by
  unfold nz; split <;> simp_all

namespace Index
variable {α K : Type} [BEq K] [LawfulBEq K] [Hashable K] {f : α → Option K}

/-- The index of an empty array. -/
def empty : Index α K f #[] :=
  ⟨∅, fun k => by simp [positionsBy]⟩

/-- The index after appending `x`. -/
def push {es : Array α} (ix : Index α K f es) (x : α) : Index α K f (es.push x) :=
  match hk : f x with
  | none => ⟨ix.map, fun k => by rw [ix.wf, positionsBy_push]; simp [hk]⟩
  | some key =>
    ⟨ix.map.alter key (fun o => some ((o.getD #[]).push es.size)), fun k => by
      rw [Std.HashMap.getD_alter, positionsBy_push, hk]
      by_cases h : key = k
      · subst h; simp [← Std.HashMap.getD_eq_getD_getElem?, ix.wf]
      · simp [h, ix.wf]⟩

/-- The index after replacing the element at `i` by `x`, which has no key. -/
def setNone {es : Array α} (ix : Index α K f es) (i : Nat) (hi : i < es.size) (x : α)
    (hx : f x = none) : Index α K f (es.set i x hi) :=
  match hk : f es[i] with
  | none => ⟨ix.map, fun k => by
      rw [ix.wf, positionsBy_set_none f es i hi x hx, filter_ne_of_not_mem]
      exact not_mem_positionsBy f es k i hi (by simp [hk])⟩
  | some key =>
    ⟨ix.map.alter key (fun o => some ((o.getD #[]).filter (· != i))), fun k => by
      rw [Std.HashMap.getD_alter, positionsBy_set_none f es i hi x hx]
      by_cases h : key = k
      · subst h; simp [← Std.HashMap.getD_eq_getD_getElem?, ix.wf]
      · have h1 : (key == k) = false := by simpa using h
        simp only [h1, Bool.false_eq_true, ↓reduceIte]
        rw [ix.wf, filter_ne_of_not_mem]
        exact not_mem_positionsBy f es k i hi (by simp [hk, h])⟩

/-- The index after dropping a last element that has no key. -/
def pop {es : Array α} (ix : Index α K f es) (hb : (es.back?.bind f) = none) :
    Index α K f es.pop :=
  ⟨ix.map, fun k => by rw [ix.wf, positionsBy_pop f es hb]⟩

end Index

namespace Groups
variable {α C K : Type} [BEq C] [LawfulBEq C] [Hashable C] [BEq K] [LawfulBEq K] [Hashable K]
  {f : α → Option (C × K)}

/-- `m` with the count of `(c, k)` replaced by `g` of it. -/
def bump (m : Std.HashMap C (Std.HashMap K Nat)) (c : C) (k : K) (g : Nat → Nat) :
    Std.HashMap C (Std.HashMap K Nat) :=
  m.alter c fun o => some ((o.getD ∅).alter k fun v => nz (g (v.getD 0)))

/-- `bump` changes the count of its own key, and no other. -/
private theorem getD_bump (m : Std.HashMap C (Std.HashMap K Nat)) (c : C) (k : K)
    (g : Nat → Nat) (c' : C) (k' : K) :
    ((bump m c k g).getD c' ∅)[k']? =
      if (c == c' && k == k') then nz (g (((m.getD c ∅)[k]?).getD 0)) else (m.getD c' ∅)[k']? := by
  unfold bump
  rw [Std.HashMap.getD_alter]
  by_cases hc : c = c'
  · subst hc
    simp only [beq_self_eq_true, ↓reduceIte, Option.getD_some, Std.HashMap.getElem?_alter,
      ← Std.HashMap.getD_eq_getD_getElem?]
    by_cases hk : k = k'
    · subst hk; simp
    · simp [hk]
  · simp [hc]

/-- `m` after `bump` at the key `p`, if there is one. -/
def bumpAt (m : Std.HashMap C (Std.HashMap K Nat)) (p : Option (C × K)) (g : Nat → Nat) :
    Std.HashMap C (Std.HashMap K Nat) :=
  match p with
  | none => m
  | some (c, k) => bump m c k g

/-- If `m` holds the counts `n`, then `bumpAt m p g` holds them with `g` applied at `p`. -/
private theorem getD_bumpAt (m : Std.HashMap C (Std.HashMap K Nat)) (n : C × K → Nat)
    (hm : ∀ c k, (m.getD c ∅)[k]? = nz (n (c, k))) (p : Option (C × K)) (g : Nat → Nat)
    (c : C) (k : K) :
    ((bumpAt m p g).getD c ∅)[k]? = nz (if p == some (c, k) then g (n (c, k)) else n (c, k)) := by
  cases p with
  | none => simp [bumpAt, hm]
  | some p =>
    obtain ⟨c0, k0⟩ := p
    simp only [bumpAt, getD_bump, hm, nz_getD]
    by_cases hc : c0 = c <;> by_cases hk : k0 = k <;> subst_vars <;> simp_all

/-- The groups of an empty array. -/
def empty : Groups α C K f #[] :=
  ⟨∅, fun c k => by simp [countBy, nz]⟩

/-- The groups after appending `x`. -/
def push {es : Array α} (g : Groups α C K f es) (x : α) : Groups α C K f (es.push x) :=
  ⟨bumpAt g.map (f x) (· + 1), fun c k => by
    rw [getD_bumpAt g.map (countBy f es) g.wf, countBy_push]
    split <;> simp_all⟩

/-- The groups after replacing the element at `i` by `x`. -/
def set {es : Array α} (g : Groups α C K f es) (i : Nat) (hi : i < es.size) (x : α) :
    Groups α C K f (es.set i x hi) :=
  ⟨bumpAt (bumpAt g.map (f es[i]) (· - 1)) (f x) (· + 1), fun c k => by
    have h1 := getD_bumpAt g.map (countBy f es) g.wf (f es[i]) (· - 1)
    rw [getD_bumpAt _
      (fun ck => if f es[i] == some ck then countBy f es ck - 1 else countBy f es ck) h1,
      countBy_set]
    split <;> split <;> simp_all⟩

/-- The groups after dropping a last element that has no key. -/
def pop {es : Array α} (g : Groups α C K f es) (hb : (es.back?.bind f) = none) :
    Groups α C K f es.pop :=
  ⟨g.map, fun c k => by rw [g.wf, countBy_pop f es hb]⟩

/-- The groups of `acc ++ l`, from those of `acc`. -/
def pushAll {acc : Array α} (g : Groups α C K f acc) : (l : List α) → Groups α C K f (acc ++ l.toArray)
  | [] => (by simp : acc = acc ++ ([] : List α).toArray) ▸ g
  | x :: xs => (by simp : acc.push x ++ xs.toArray = acc ++ (x :: xs).toArray) ▸ pushAll (g.push x) xs

/-- The groups of `es`, built from scratch. -/
def build (es : Array α) : Groups α C K f es :=
  (by simp : #[] ++ es.toList.toArray = es) ▸ pushAll empty es.toList

/-- The number of distinct keys of class `c`. -/
def count {es : Array α} (g : Groups α C K f es) (c : C) : Nat := (g.map.getD c ∅).size

end Groups

end

end StrataPython.Dyn.Sem
