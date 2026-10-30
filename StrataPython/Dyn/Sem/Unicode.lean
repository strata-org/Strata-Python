/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Generated.Unicode

set_option autoImplicit false

/-!
# Unicode properties

`isPrintable`, CPython 3.12's `str.isprintable()` of one character, from the generated table.

The table is read by binary search.  Key theorem: `inRangesFrom_eq`, the binary search over
sorted, disjoint ranges gives the answer of a scan; with `printableRanges_sorted`, the
`@[csimp]` lemma `inPrintableRanges_eq_fast` swaps the search in for the scan.  These proofs are
here, not in a Props file, because a `@[csimp]` lemma must come before the code that uses it.
-/

namespace StrataPython.Dyn.Sem.Unicode

@[expose] public section

/-- Whether the range `r = (lo, hi)` holds the code point `cp`. -/
def inRange (r : Nat × Nat) (cp : Nat) : Bool := r.1 ≤ cp && cp ≤ r.2

/-- Whether one of the ranges `rs` holds the code point `cp`: a scan. -/
def inRanges (rs : Array (Nat × Nat)) (cp : Nat) : Bool := rs.any (inRange · cp)

/-- Whether the code point `cp` is in one of the ranges `rs[lo]` to `rs[hi - 1]`, by binary
search.  The ranges must be sorted and disjoint (`Sorted`). -/
def inRangesFrom (rs : Array (Nat × Nat)) (cp : Nat) (lo hi : Nat) : Bool :=
  if _h : lo < hi then
    let mid := (lo + hi) / 2
    let r := rs.getD mid (0, 0)
    if cp < r.1 then inRangesFrom rs cp lo mid
    else if r.2 < cp then inRangesFrom rs cp (mid + 1) hi
    else true
  else false
termination_by hi - lo

/-- The ranges `rs` are sorted and disjoint: each range `(lo, hi)` has `lo ≤ hi`, and ends before
the next one starts. -/
def Sorted (rs : Array (Nat × Nat)) : Prop :=
  (∀ i, i < rs.size → (rs.getD i (0, 0)).1 ≤ (rs.getD i (0, 0)).2) ∧
  (∀ i, i < rs.size - 1 → (rs.getD i (0, 0)).2 < (rs.getD (i + 1) (0, 0)).1)

/-- In sorted, disjoint ranges, a range ends before any later range starts. -/
private theorem Sorted.hi_lt_lo {rs} (h : Sorted rs) : ∀ {i j}, i < j → j < rs.size →
    (rs.getD i (0, 0)).2 < (rs.getD j (0, 0)).1 := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hnext := h.2 j (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | heq
    · have hij' := ih hlt (by omega)
      have hj' := h.1 j (by omega)
      omega
    · subst heq; exact hnext

/-- In sorted, disjoint ranges, a later range does not start before an earlier one. -/
private theorem Sorted.lo_le {rs} (h : Sorted rs) {i j} (hij : i ≤ j) (hj : j < rs.size) :
    (rs.getD i (0, 0)).1 ≤ (rs.getD j (0, 0)).1 := by
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · have hlo := h.hi_lt_lo hlt hj
    have hi' := h.1 i (by omega)
    omega
  · exact Nat.le_refl _

/-- In sorted, disjoint ranges, a later range does not end before an earlier one. -/
private theorem Sorted.hi_le {rs} (h : Sorted rs) {i j} (hij : i ≤ j) (hj : j < rs.size) :
    (rs.getD i (0, 0)).2 ≤ (rs.getD j (0, 0)).2 := by
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · have hlo := h.hi_lt_lo hlt hj
    have hj' := h.1 j hj
    omega
  · exact Nat.le_refl _

/-- Whether one of the ranges `rs[lo]` to `rs[hi - 1]` holds `cp`. -/
def window (rs : Array (Nat × Nat)) (cp lo hi : Nat) : Prop :=
  ∃ i, lo ≤ i ∧ i < hi ∧ inRange (rs.getD i (0, 0)) cp = true

/-- Over sorted, disjoint ranges, the binary search between `lo` and `hi` finds `cp` exactly when
one of the ranges `rs[lo]` to `rs[hi - 1]` holds it. -/
private theorem inRangesFrom_iff {rs} (hs : Sorted rs) (cp : Nat) :
    ∀ lo hi, hi ≤ rs.size → (inRangesFrom rs cp lo hi = true ↔ window rs cp lo hi) := by
  intro lo hi
  induction lo, hi using inRangesFrom.induct rs cp with
  | case1 lo hi hlt mid r hcp ih =>
    intro hh
    simp only [mid, r] at hcp ih
    rw [inRangesFrom, dite_eq_left_of_eq_true (eq_true hlt)]
    simp only [hcp, ↓reduceIte]
    rw [ih (by omega)]
    constructor
    · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, h1, by omega, h3⟩
    · rintro ⟨i, h1, h2, h3⟩
      refine ⟨i, h1, ?_, h3⟩
      apply Decidable.byContradiction; intro hc
      have hmid := hs.lo_le (i := (lo + hi) / 2) (j := i) (by omega) (by omega)
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at h3
      omega
  | case2 lo hi hlt mid r hcp hcp2 ih =>
    intro hh
    simp only [mid, r] at hcp hcp2 ih
    rw [inRangesFrom, dite_eq_left_of_eq_true (eq_true hlt)]
    simp only [hcp, hcp2, ↓reduceIte]
    rw [ih hh]
    constructor
    · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, by omega, h2, h3⟩
    · rintro ⟨i, h1, h2, h3⟩
      refine ⟨i, ?_, h2, h3⟩
      apply Decidable.byContradiction; intro hc
      have hmid := hs.hi_le (i := i) (j := (lo + hi) / 2) (by omega) (by omega)
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at h3
      omega
  | case3 lo hi hlt mid r hcp hcp2 =>
    intro hh
    simp only [mid, r] at hcp hcp2
    rw [inRangesFrom, dite_eq_left_of_eq_true (eq_true hlt)]
    simp only [hcp, hcp2, ↓reduceIte, true_iff]
    refine ⟨(lo + hi) / 2, by omega, by omega, ?_⟩
    simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
    omega
  | case4 lo hi hlt =>
    intro hh
    rw [inRangesFrom, dite_eq_right_of_eq_false (eq_false hlt)]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨i, h1, h2, -⟩; omega

/-- The binary search over all of sorted, disjoint ranges gives the scan's answer, by induction on
the search: each step drops only ranges that can't hold `cp`. -/
theorem inRangesFrom_eq {rs : Array (Nat × Nat)} (hs : Sorted rs) (cp : Nat) :
    inRangesFrom rs cp 0 rs.size = inRanges rs cp := by
  apply Bool.eq_iff_iff.mpr
  rw [inRangesFrom_iff hs cp 0 rs.size (Nat.le_refl _), inRanges, Array.any_eq_true]
  constructor
  · rintro ⟨i, -, h2, h3⟩
    exact ⟨i, h2, by simpa [Array.getD_eq_getD_getElem?, h2] using h3⟩
  · rintro ⟨i, h2, h3⟩
    exact ⟨i, Nat.zero_le _, h2, by simpa [Array.getD_eq_getD_getElem?, h2] using h3⟩

/-- Whether the ranges `l` are sorted and disjoint, by one pass over the list. -/
def sortedList : List (Nat × Nat) → Bool
  | [] => true
  | [r] => decide (r.1 ≤ r.2)
  | r :: s :: rest => decide (r.1 ≤ r.2) && decide (r.2 < s.1) && sortedList (s :: rest)

/-- `sortedList l` says that each range of `l` has `lo ≤ hi` and ends before the next one starts. -/
private theorem sortedList_spec : ∀ l : List (Nat × Nat), sortedList l = true →
    (∀ i, i < l.length → (l.getD i (0, 0)).1 ≤ (l.getD i (0, 0)).2) ∧
    (∀ i, i < l.length - 1 → (l.getD i (0, 0)).2 < (l.getD (i + 1) (0, 0)).1)
  | [], _ => ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
  | [r], h => by
    simp only [sortedList, decide_eq_true_eq] at h
    refine ⟨fun i hi => ?_, fun i hi => by simp at hi⟩
    simp only [List.length_singleton] at hi
    obtain rfl : i = 0 := by omega
    simpa using h
  | r :: s :: rest, h => by
    simp only [sortedList, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, hrs⟩, hrest⟩ := h
    obtain ⟨ih1, ih2⟩ := sortedList_spec (s :: rest) hrest
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · cases i with
      | zero => simpa using hr
      | succ i => simpa using ih1 i (by simp at hi ⊢; omega)
    · cases i with
      | zero => simpa using hrs
      | succ i => simpa using ih2 i (by simp at hi ⊢; omega)

/-- An array of ranges is sorted and disjoint when the one-pass check `sortedList` accepts its
list. -/
theorem Sorted.of_sortedList {rs : Array (Nat × Nat)} (h : sortedList rs.toList = true) :
    Sorted rs := by
  obtain ⟨h1, h2⟩ := sortedList_spec rs.toList h
  have hget : ∀ i, rs.getD i (0, 0) = rs.toList.getD i (0, 0) := by
    intro i; simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hget]; exact h1 i (by simpa using hi)
  · rw [hget, hget]; exact h2 i (by simpa using hi)

/-- The generated table is sorted and disjoint. -/
theorem printableRanges_sorted : Sorted printableRanges :=
  Sorted.of_sortedList (by decide +kernel)

/-- Whether the code point `cp` is in the table's ranges: the scan. -/
def inPrintableRanges (cp : Nat) : Bool := inRanges printableRanges cp

/-- The same, by binary search. -/
def inPrintableRangesFast (cp : Nat) : Bool :=
  inRangesFrom printableRanges cp 0 printableRanges.size

/-- The scan and the binary search of the table are the same function, so the compiled code runs
the search. -/
@[csimp] theorem inPrintableRanges_eq_fast : @inPrintableRanges = @inPrintableRangesFast := by
  funext cp
  exact (inRangesFrom_eq printableRanges_sorted cp).symm

/-- Whether `c` is printable, as `str.isprintable()` says: an ASCII character is printable from
the space up to `~`; any other character is looked up in the table. -/
def isPrintable (c : Char) : Bool :=
  if c.val < 128 then 0x20 ≤ c.val && c.val < 0x7f else inPrintableRanges c.val.toNat

end

end StrataPython.Dyn.Sem.Unicode
