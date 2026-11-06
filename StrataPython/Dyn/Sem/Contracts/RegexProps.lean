/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Contracts.Regex

set_option autoImplicit false

/-!
# The matcher of `py.reSearch` is correct

The key theorem is `ends_iff`: on a set `S` of positions of `s`, `ends P s r S` holds exactly the
positions `j` with `Matches P s r i j` for some `i` in `S`.  `search_iff` follows: `search P r s`
holds exactly when `r` matches somewhere in `s`.

A set of positions is an array of `s.size + 1` booleans (`Regex.lean`).  The proof of a repeat
needs two facts about the relation: a match never moves back (`Matches.le`), and a run of more
than `j - i` matches from `i` to `j` has a step that matches the empty string, which can be dropped
(`MatchesN.shorten`).  So `s.size + 1` rounds reach every end that more rounds reach.
-/

namespace StrataPython.Dyn.Sem.Contracts.Regex

public section

variable {P : Classes} {s : Array Char}

/-! ## Sets of positions -/

/-- A position of a set of the right size is at most `s.size`. -/
private theorem le_of_getD {S : Array Bool} (hS : S.size = s.size + 1) {j : Nat}
    (h : S.getD j false = true) : j ≤ s.size := by
  rw [Array.getD_eq_getD_getElem?] at h
  by_cases hj : j < S.size
  · omega
  · have hn : S[j]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hj)
    simp [hn] at h

/-- `stepSet` gives a set of positions of the right size. -/
private theorem size_stepSet (f : Char → Bool) (S : Array Bool) : (stepSet s f S).size = s.size + 1 :=
  size_posSet _

/-- `unionSet` gives a set of positions of the right size. -/
private theorem size_unionSet (A B : Array Bool) : (unionSet s A B).size = s.size + 1 :=
  size_posSet _

/-- If `F` keeps the size of a set of positions, so does `F` applied `k` times. -/
private theorem size_iterate {F : Array Bool → Array Bool}
    (hF : ∀ S, S.size = s.size + 1 → (F S).size = s.size + 1) :
    ∀ (k : Nat) (S : Array Bool), S.size = s.size + 1 → (iterate F k S).size = s.size + 1
  | 0, _, hS => hS
  | k + 1, S, hS => size_iterate hF k (F S) (hF S hS)

/-- `closure` gives a set of positions of the right size, from one of the right size. -/
private theorem size_closure (F : Array Bool → Array Bool) (A : Array Bool) (hA : A.size = s.size + 1) :
    ∀ k, (closure s F A k).size = s.size + 1
  | 0 => hA
  | _ + 1 => size_unionSet _ _

/-- `ends` keeps the size of a set of positions. -/
private theorem size_ends (r : Re) : ∀ (S : Array Bool), S.size = s.size + 1 →
    (ends P s r S).size = s.size + 1 := by
  induction r with
  | empty => exact fun _ h => h
  | assert a => exact fun _ _ => size_posSet _
  | cat a b iha ihb => exact fun S h => ihb _ (iha S h)
  | alt a b _ _ => exact fun _ _ => size_unionSet _ _
  | rep r lo hi ih =>
    intro S hS
    cases hi with
    | none => exact size_closure _ _ (size_iterate ih lo S hS) _
    | some h =>
      simp only [ends]
      split
      · exact size_posSet _
      · exact size_closure _ _ (size_iterate ih lo S hS) _
  | char c => exact fun _ _ => by simp [ends, atomTest, size_stepSet]
  | any => exact fun _ _ => by simp [ends, atomTest, size_stepSet]
  | set neg items => exact fun _ _ => by simp [ends, atomTest, size_stepSet]
  | cls k neg => exact fun _ _ => by simp [ends, atomTest, size_stepSet]

/-! ## Facts about the relation -/

mutual
/-- A match never moves back, and ends inside the string. -/
private theorem Matches.le {r : Re} {i j : Nat} : Matches P s r i j → i ≤ j ∧ j ≤ s.size
  | .empty h => ⟨Nat.le_refl _, h⟩
  | .atom _ hi _ => ⟨Nat.le_succ _, hi⟩
  | .assert h _ => ⟨Nat.le_refl _, h⟩
  | .cat h₁ h₂ =>
    have a := Matches.le h₁
    have b := Matches.le h₂
    ⟨Nat.le_trans a.1 b.1, b.2⟩
  | .altL h => Matches.le h
  | .altR h => Matches.le h
  | .rep _ _ h => MatchesN.le h

/-- A run of matches never moves back, and ends inside the string. -/
private theorem MatchesN.le {r : Re} {k i j : Nat} : MatchesN P s r k i j → i ≤ j ∧ j ≤ s.size
  | .zero h => ⟨Nat.le_refl _, h⟩
  | .succ h₁ h₂ =>
    have a := Matches.le h₁
    have b := MatchesN.le h₂
    ⟨Nat.le_trans a.1 b.1, b.2⟩
end

/-- A run of `k` matches followed by one more is a run of `k + 1` matches. -/
private theorem MatchesN.snoc {r : Re} : ∀ {k i j l : Nat}, MatchesN P s r k i j → Matches P s r j l →
    MatchesN P s r (k + 1) i l
  | _, _, _, _, .zero _, h => .succ h (.zero (Matches.le h).2)
  | _, _, _, _, .succ h₁ h₂, h => .succ h₁ (MatchesN.snoc h₂ h)

/-- A run of `k + 1` matches is a run of `k` matches followed by one more. -/
private theorem MatchesN.unsnoc {r : Re} : ∀ {k i l : Nat}, MatchesN P s r (k + 1) i l →
    ∃ j, MatchesN P s r k i j ∧ Matches P s r j l
  | 0, _, _, .succ h₁ h₂ => by
    cases h₂ with
    | zero _ => exact ⟨_, .zero (Nat.le_trans (Matches.le h₁).1 (Matches.le h₁).2), h₁⟩
  | _ + 1, _, _, .succ h₁ h₂ => by
    obtain ⟨j, hj, hl⟩ := MatchesN.unsnoc h₂
    exact ⟨j, .succ h₁ hj, hl⟩

/-- Two runs, one after the other, are one run. -/
private theorem MatchesN.append {r : Re} : ∀ {a b i j l : Nat}, MatchesN P s r a i j →
    MatchesN P s r b j l → MatchesN P s r (a + b) i l
  | _, _, _, _, _, .zero _, h => by simpa using h
  | _, _, _, _, _, .succ h₁ h₂, h => by
    rw [Nat.add_right_comm]
    exact .succ h₁ (MatchesN.append h₂ h)

/-- A run of `a + b` matches is a run of `a` matches, then a run of `b` matches. -/
private theorem MatchesN.split {r : Re} : ∀ {a b i l : Nat}, MatchesN P s r (a + b) i l →
    ∃ j, MatchesN P s r a i j ∧ MatchesN P s r b j l
  | 0, _, _, _, h => ⟨_, .zero (Nat.le_trans (MatchesN.le h).1 (MatchesN.le h).2), by simpa using h⟩
  | a + 1, b, _, _, h => by
    rw [Nat.add_right_comm] at h
    cases h with
    | succ h₁ h₂ =>
      obtain ⟨j, hj, hl⟩ := MatchesN.split h₂
      exact ⟨j, .succ h₁ hj, hl⟩

/-- A run of `m + 1` matches from `i` to `l`, with `m + 1 > l - i`, has a step that matches the
empty string: without it, `m` matches lead from `i` to `l`. -/
private theorem MatchesN.shorten {r : Re} : ∀ {m i l : Nat}, MatchesN P s r (m + 1) i l →
    l - i < m + 1 → MatchesN P s r m i l
  | m, i, l, .succ (j := x) h₁ h₂, hlt => by
    have hx := Matches.le h₁
    have hxl := MatchesN.le h₂
    by_cases hxi : x = i
    · subst hxi; exact h₂
    · cases m with
      | zero => cases h₂; omega
      | succ m =>
        exact .succ h₁ (MatchesN.shorten h₂ (by omega))

/-- A run from `i` to `l` can be shortened to at most `l - i` matches. -/
private theorem MatchesN.short {r : Re} : ∀ (m : Nat) {i l : Nat}, MatchesN P s r m i l →
    ∃ m', m' ≤ m ∧ m' ≤ l - i ∧ MatchesN P s r m' i l
  | 0, _, _, h => ⟨0, Nat.le_refl _, Nat.zero_le _, h⟩
  | m + 1, i, l, h => by
    by_cases hle : m + 1 ≤ l - i
    · exact ⟨m + 1, Nat.le_refl _, hle, h⟩
    · obtain ⟨m', h1, h2, h3⟩ := MatchesN.short m (MatchesN.shorten h (by omega))
      exact ⟨m', by omega, h2, h3⟩

/-! ## The matcher computes the relation -/

/-- `EndsOK P s r`: on every set `S` of `s.size + 1` positions, a position `j` is in
`ends P s r S` exactly when a match of `r` from some position of `S` ends at `j`. -/
abbrev EndsOK (P : Classes) (s : Array Char) (r : Re) : Prop :=
  ∀ (S : Array Bool), S.size = s.size + 1 → ∀ j,
    (ends P s r S).getD j false = true ↔ ∃ i, S.getD i false = true ∧ Matches P s r i j

/-- A run of no matches stays at its position, which is inside the string. -/
private theorem matchesN_zero_iff {r : Re} {i j : Nat} :
    MatchesN P s r 0 i j ↔ i = j ∧ j ≤ s.size := by
  constructor
  · intro h; cases h with | zero h => exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact .zero h

/-- `iterate` of a correct `ends` computes runs of `m` matches. -/
private theorem iterate_iff {r : Re} (ih : EndsOK P s r) : ∀ (m : Nat) (S : Array Bool),
    S.size = s.size + 1 → ∀ l, (iterate (ends P s r) m S).getD l false = true ↔
      ∃ i, S.getD i false = true ∧ MatchesN P s r m i l
  | 0, S, hS, l => by
    simp only [iterate, matchesN_zero_iff]
    exact ⟨fun h => ⟨l, h, rfl, le_of_getD hS h⟩, fun ⟨_, h, rfl, _⟩ => h⟩
  | m + 1, S, hS, l => by
    simp only [iterate]
    rw [iterate_iff ih m _ (size_ends r S hS)]
    constructor
    · rintro ⟨x, hx, hxl⟩
      obtain ⟨i, hi, hix⟩ := (ih S hS x).1 hx
      exact ⟨i, hi, .succ hix hxl⟩
    · rintro ⟨i, hi, h⟩
      cases h with
      | succ hix hxl => exact ⟨_, (ih S hS _).2 ⟨i, hi, hix⟩, hxl⟩

/-- `closure` of a correct `ends` computes runs of at most `t` matches. -/
private theorem closure_iff {r : Re} (ih : EndsOK P s r) (A : Array Bool) (hA : A.size = s.size + 1) :
    ∀ (t l : Nat), (closure s (ends P s r) A t).getD l false = true ↔
      ∃ m, m ≤ t ∧ ∃ i, A.getD i false = true ∧ MatchesN P s r m i l
  | 0, l => by
    simp only [closure]
    constructor
    · intro h; exact ⟨0, Nat.le_refl _, l, h, .zero (le_of_getD hA h)⟩
    · rintro ⟨m, hm, i, hi, h⟩
      have : m = 0 := by omega
      subst this
      obtain ⟨rfl, _⟩ := matchesN_zero_iff.1 h
      exact hi
  | t + 1, l => by
    simp only [closure, unionSet, getD_posSet, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq]
    rw [ih _ (size_closure _ _ hA t)]
    constructor
    · rintro ⟨_, hA' | ⟨x, hx, hxl⟩⟩
      · exact ⟨0, Nat.zero_le _, l, hA', .zero (le_of_getD hA hA')⟩
      · obtain ⟨m, hm, i, hi, him⟩ := (closure_iff ih A hA t x).1 hx
        exact ⟨m + 1, by omega, i, hi, MatchesN.snoc him hxl⟩
    · rintro ⟨m, hm, i, hi, h⟩
      refine ⟨(MatchesN.le h).2, ?_⟩
      cases m with
      | zero =>
        obtain ⟨rfl, _⟩ := matchesN_zero_iff.1 h
        exact Or.inl hi
      | succ m =>
        obtain ⟨x, hix, hxl⟩ := MatchesN.unsnoc h
        exact Or.inr ⟨x, (closure_iff ih A hA t x).2 ⟨m, by omega, i, hi, hix⟩, hxl⟩

/-- A one-character pattern matches exactly one character that its test accepts. -/
private theorem matches_atom_iff {r : Re} {f : Char → Bool} (hf : atomTest P r = some f) {i j : Nat} :
    Matches P s r i j ↔ j = i + 1 ∧ ∃ h : i < s.size, f s[i] = true := by
  constructor
  · intro h
    cases h with
    | atom hf' hi ht =>
      rw [hf] at hf'; cases hf'
      exact ⟨rfl, hi, ht⟩
    | empty _ => simp [atomTest] at hf
    | assert _ _ => simp [atomTest] at hf
    | cat _ _ => simp [atomTest] at hf
    | altL _ => simp [atomTest] at hf
    | altR _ => simp [atomTest] at hf
    | rep _ _ _ => simp [atomTest] at hf
  · rintro ⟨rfl, hi, ht⟩
    exact .atom hf hi ht

/-- `ends` of a one-character pattern reads one character. -/
private theorem ends_atom {r : Re} {f : Char → Bool} (hf : atomTest P r = some f)
    (he : ∀ S, ends P s r S = stepSet s f S) : EndsOK P s r := by
  intro S hS j
  rw [he, stepSet, getD_posSet]
  simp only [matches_atom_iff hf]
  cases j with
  | zero => simp
  | succ i =>
    constructor
    · intro h
      by_cases hi : i < s.size
      · simp only [hi, dite_true, Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨i, h.2.1, rfl, hi, h.2.2⟩
      · simp [hi] at h
    · rintro ⟨i', hS', h, hi', hf'⟩
      cases h
      simp only [hi', dite_true, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, hS', hf'⟩

/-- **The matcher is correct.** On a set `S` of positions of `s`, `ends P s r S` holds exactly the
positions `j` where a match of `r` from a position of `S` can end. By induction on `r`; for a
repeat, a run of more matches than `s.size + 1` can be shortened, since a match never moves back. -/
theorem ends_iff (r : Re) : EndsOK P s r := by
  induction r with
  | empty =>
    intro S hS j
    constructor
    · intro h; exact ⟨j, h, .empty (le_of_getD hS h)⟩
    · rintro ⟨i, hi, h⟩
      cases h with
      | empty _ => exact hi
      | atom hf _ _ => simp [atomTest] at hf
  | char c => exact ends_atom (f := (· == c)) rfl (fun _ => rfl)
  | any => exact ends_atom (f := (· != '\n')) rfl (fun _ => rfl)
  | set neg items => exact ends_atom rfl (fun _ => rfl)
  | cls k neg => exact ends_atom rfl (fun _ => rfl)
  | assert a =>
    intro S hS j
    simp only [ends, getD_posSet, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hj, hS', ha⟩; exact ⟨j, hS', .assert hj ha⟩
    · rintro ⟨i, hi, h⟩
      cases h with
      | assert hj ha => exact ⟨hj, hi, ha⟩
      | atom hf _ _ => simp [atomTest] at hf
  | cat a b iha ihb =>
    intro S hS j
    simp only [ends]
    rw [ihb _ (size_ends a S hS)]
    constructor
    · rintro ⟨x, hx, hxj⟩
      obtain ⟨i, hi, hix⟩ := (iha S hS x).1 hx
      exact ⟨i, hi, .cat hix hxj⟩
    · rintro ⟨i, hi, h⟩
      cases h with
      | cat hix hxj => exact ⟨_, (iha S hS _).2 ⟨i, hi, hix⟩, hxj⟩
      | atom hf _ _ => simp [atomTest] at hf
  | alt a b iha ihb =>
    intro S hS j
    simp only [ends, unionSet, getD_posSet, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq]
    rw [iha S hS, ihb S hS]
    constructor
    · rintro ⟨_, ⟨i, hi, h⟩ | ⟨i, hi, h⟩⟩
      · exact ⟨i, hi, .altL h⟩
      · exact ⟨i, hi, .altR h⟩
    · rintro ⟨i, hi, h⟩
      cases h with
      | altL h => exact ⟨(Matches.le h).2, Or.inl ⟨i, hi, h⟩⟩
      | altR h => exact ⟨(Matches.le h).2, Or.inr ⟨i, hi, h⟩⟩
      | atom hf _ _ => simp [atomTest] at hf
  | rep r lo hi ih =>
    intro S hS j
    -- The positions after `lo` matches, and the repeat's meaning, as runs of matches.
    have hA := size_iterate (F := ends P s r) (size_ends (P := P) r) lo S hS
    have hIt := iterate_iff ih lo S hS
    have hCl := closure_iff ih _ hA
    have hRep : ∀ i, Matches P s (.rep r lo hi) i j ↔
        ∃ c, lo ≤ c ∧ (∀ h, hi = some h → c ≤ h) ∧ MatchesN P s r c i j := by
      intro i
      constructor
      · intro h
        cases h with
        | rep h1 h2 h3 => exact ⟨_, h1, h2, h3⟩
        | atom hf _ _ => simp [atomTest] at hf
      · rintro ⟨c, h1, h2, h3⟩; exact .rep h1 h2 h3
    -- Both sides, for a bound `k` on the rounds after `lo` that is at least `min b (s.size + 1)`.
    have key : ∀ (b : Option Nat) (k : Nat), (∀ h, b = some h → k ≤ h) →
        (b = none → k = s.size + 1) → (∀ h, b = some h → min h (s.size + 1) ≤ k) →
        ((closure s (ends P s r) (iterate (ends P s r) lo S) k).getD j false = true ↔
          ∃ i, S.getD i false = true ∧ ∃ c, lo ≤ c ∧ (∀ h, b = some h → c - lo ≤ h) ∧
            MatchesN P s r c i j) := by
      intro b k hk hnone hmin
      rw [hCl k j]
      constructor
      · rintro ⟨m, hm, x, hx, hxj⟩
        obtain ⟨i, hi, hix⟩ := (hIt x).1 hx
        refine ⟨i, hi, lo + m, Nat.le_add_right _ _, ?_, MatchesN.append hix hxj⟩
        intro h hb; have := hk h hb; omega
      · rintro ⟨i, hi, c, hc, hcb, h⟩
        obtain ⟨x, hix, hxj⟩ := MatchesN.split (a := lo) (b := c - lo) (by
          rw [Nat.add_sub_cancel' hc]; exact h)
        obtain ⟨m', hm'1, hm'2, hm'3⟩ := MatchesN.short (c - lo) hxj
        have hjn := (MatchesN.le hxj).2
        refine ⟨m', ?_, x, (hIt x).2 ⟨i, hi, hix⟩, hm'3⟩
        cases b with
        | none => have := hnone rfl; omega
        | some h => have hmn := hmin h rfl; have hcbh := hcb h rfl; omega
    cases hi with
    | none =>
      simp only [ends]
      rw [key none (s.size + 1) (by simp) (fun _ => rfl) (by simp)]
      simp only [hRep]
      constructor
      · rintro ⟨i, hi, c, hc, _, h⟩; exact ⟨i, hi, c, hc, by simp, h⟩
      · rintro ⟨i, hi, c, hc, _, h⟩; exact ⟨i, hi, c, hc, by simp, h⟩
    | some h =>
      simp only [ends]
      split
      · rename_i hlt
        simp only [getD_posSet, Bool.and_false, Bool.false_eq_true, false_iff, not_exists,
          not_and, hRep]
        intro i _ c hc hch _
        have := hch h rfl; omega
      · rename_i hlt
        rw [key (some (h - lo)) (min (h - lo) (s.size + 1))
          (fun h' hb => by cases hb; exact Nat.min_le_left _ _) (by simp)
          (fun h' hb => by cases hb; exact Nat.le_refl _)]
        simp only [hRep]
        constructor
        · rintro ⟨i, hi, c, hc, hcb, hm⟩
          exact ⟨i, hi, c, hc, fun h' hb => by cases hb; have := hcb _ rfl; omega, hm⟩
        · rintro ⟨i, hi, c, hc, hcb, hm⟩
          exact ⟨i, hi, c, hc, fun h' hb => by cases hb; have := hcb _ rfl; omega, hm⟩

/-- `search` decides whether `r` matches somewhere in `s`. -/
theorem search_iff (r : Re) : search P r s = true ↔ ∃ i j, Matches P s r i j := by
  have hS : (posSet s fun _ => true).size = s.size + 1 := size_posSet _
  have hE := ends_iff (P := P) r _ hS
  have hsz := size_ends (P := P) r _ hS
  unfold search
  rw [Array.any_eq_true]
  constructor
  · rintro ⟨j, hj, hv⟩
    have : (ends P s r (posSet s fun _ => true)).getD j false = true := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]; simpa using hv
    obtain ⟨i, _, h⟩ := (hE j).1 this
    exact ⟨i, j, h⟩
  · rintro ⟨i, j, h⟩
    have hij := Matches.le h
    have hg := (hE j).2 ⟨i, by rw [getD_posSet]; simp; omega, h⟩
    have hj : j < (ends P s r (posSet s fun _ => true)).size := by omega
    refine ⟨j, hj, ?_⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj] at hg
    simpa using hg

end

end StrataPython.Dyn.Sem.Contracts.Regex
