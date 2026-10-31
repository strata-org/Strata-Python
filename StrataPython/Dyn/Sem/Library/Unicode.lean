/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Unicode
public import StrataPython.Dyn.Sem.Generated.LibraryUnicode

set_option autoImplicit false

/-!
# The character classes and case mappings of `str`

CPython 3.12's Unicode classes of one character (`isAlpha`, `isUpper`, `isCased`, …) and its full
case mappings of one character (`toUpper`, `toLower`, `toTitle`, `caseFold`), from the generated
tables of `Generated/LibraryUnicode.lean`, and the methods of `str` built on them: the case
methods with CPython's final-sigma rule, and the class tests of a whole string.

Each class is a scan of its ranges, and each case mapping a scan of its map; given the proofs
that the tables are sorted, `@[csimp]` lemmas swap in binary searches (`inClass_eq_fast`, from
`Unicode.inRangesFrom_eq`, and `inMap_eq_fast`, from `lookupFrom_eq`).
-/

namespace StrataPython.Dyn.Sem.Library.Unicode

open StrataPython.Dyn.Sem.Unicode

@[expose] public section

/-! ## Classes of one character -/

/-- Whether one of the sorted, disjoint ranges `rs` holds `cp`: a scan. Given the proof that `rs`
is sorted, the compiled code runs the binary search instead (`inClass_eq_fast`). -/
def inClass (rs : Array (Nat × Nat)) (_h : Sorted rs) (cp : Nat) : Bool := inRanges rs cp

/-- `inClass` by binary search. -/
def inClassFast (rs : Array (Nat × Nat)) (_h : Sorted rs) (cp : Nat) : Bool :=
  inRangesFrom rs cp 0 rs.size

/-- The scan and the binary search of sorted ranges are the same function, so the compiled code
runs the search. -/
@[csimp] theorem inClass_eq_fast : @inClass = @inClassFast := by
  funext rs h cp
  exact (inRangesFrom_eq h cp).symm

/-- The ranges of `isAlpha` are sorted and disjoint. -/
theorem alphaRanges_sorted : Sorted alphaRanges := Sorted.of_sortedList (by decide +kernel)

/-- `str.isalpha()` of one character. -/
def isAlpha (c : Char) : Bool := inClass alphaRanges alphaRanges_sorted c.toNat

/-- The ranges of `isDecimal` are sorted and disjoint. -/
theorem decimalRanges_sorted : Sorted decimalRanges := Sorted.of_sortedList (by decide +kernel)

/-- `str.isdecimal()` of one character. -/
def isDecimal (c : Char) : Bool := inClass decimalRanges decimalRanges_sorted c.toNat

/-- The ranges of `isDigit` are sorted and disjoint. -/
theorem digitRanges_sorted : Sorted digitRanges := Sorted.of_sortedList (by decide +kernel)

/-- `str.isdigit()` of one character. -/
def isDigit (c : Char) : Bool := inClass digitRanges digitRanges_sorted c.toNat

/-- The ranges of `isNumeric` are sorted and disjoint. -/
theorem numericRanges_sorted : Sorted numericRanges := Sorted.of_sortedList (by decide +kernel)

/-- `str.isnumeric()` of one character. -/
def isNumeric (c : Char) : Bool := inClass numericRanges numericRanges_sorted c.toNat

/-- The ranges of `isSpace` are sorted and disjoint. -/
theorem spaceRanges_sorted : Sorted spaceRanges := Sorted.of_sortedList (by decide +kernel)

/-- `str.isspace()` of one character. -/
def isSpace (c : Char) : Bool := inClass spaceRanges spaceRanges_sorted c.toNat

/-- The ranges of `isUpper` are sorted and disjoint. -/
theorem upperRanges_sorted : Sorted upperRanges := Sorted.of_sortedList (by decide +kernel)

/-- `str.isupper()` of one character (the property Uppercase). -/
def isUpper (c : Char) : Bool := inClass upperRanges upperRanges_sorted c.toNat

/-- The ranges of `isLower` are sorted and disjoint. -/
theorem lowerRanges_sorted : Sorted lowerRanges := Sorted.of_sortedList (by decide +kernel)

/-- `str.islower()` of one character (the property Lowercase). -/
def isLower (c : Char) : Bool := inClass lowerRanges lowerRanges_sorted c.toNat

/-- The ranges of `isTitlecase` are sorted and disjoint. -/
theorem titleRanges_sorted : Sorted titleRanges := Sorted.of_sortedList (by decide +kernel)

/-- Whether the character is a titlecase letter (category Lt). -/
def isTitlecase (c : Char) : Bool := inClass titleRanges titleRanges_sorted c.toNat

/-- The ranges of `isCased` are sorted and disjoint. -/
theorem casedRanges_sorted : Sorted casedRanges := Sorted.of_sortedList (by decide +kernel)

/-- Whether the character is cased (`_PyUnicode_IsCased`). -/
def isCased (c : Char) : Bool := inClass casedRanges casedRanges_sorted c.toNat

/-- The ranges of `isCaseIgnorable` are sorted and disjoint. -/
theorem caseIgnorableRanges_sorted : Sorted caseIgnorableRanges := Sorted.of_sortedList (by decide +kernel)

/-- Whether the character is case-ignorable (`_PyUnicode_IsCaseIgnorable`). -/
def isCaseIgnorable (c : Char) : Bool := inClass caseIgnorableRanges caseIgnorableRanges_sorted c.toNat

/-- The ranges of `isIdentStart` are sorted and disjoint. -/
theorem identStartRanges_sorted : Sorted identStartRanges := Sorted.of_sortedList (by decide +kernel)

/-- Whether the character may start an identifier. -/
def isIdentStart (c : Char) : Bool := inClass identStartRanges identStartRanges_sorted c.toNat

/-- The ranges of `isIdentContinue` are sorted and disjoint. -/
theorem identContinueRanges_sorted : Sorted identContinueRanges := Sorted.of_sortedList (by decide +kernel)

/-- Whether the character may continue an identifier. -/
def isIdentContinue (c : Char) : Bool := inClass identContinueRanges identContinueRanges_sorted c.toNat

/-- The ranges of `isLineBreak` are sorted and disjoint. -/
theorem lineBreakRanges_sorted : Sorted lineBreakRanges := Sorted.of_sortedList (by decide +kernel)

/-- Whether the character is a line boundary of `str.splitlines`. -/
def isLineBreak (c : Char) : Bool := inClass lineBreakRanges lineBreakRanges_sorted c.toNat

/-- `str.isalnum()` of one character: one of the four classes, as CPython defines it. -/
def isAlnum (c : Char) : Bool := isAlpha c || isDecimal c || isDigit c || isNumeric c

/-! ## Case mappings of one character -/

/-- The keys of the map `m` strictly increase. -/
def KeysSorted (m : Array (Nat × List Nat)) : Prop :=
  ∀ i, i + 1 < m.size → (m.getD i (0, [])).1 < (m.getD (i + 1) (0, [])).1

/-- In a map whose keys strictly increase, an earlier key is smaller than a later one. -/
private theorem KeysSorted.lt {m : Array (Nat × List Nat)} (h : KeysSorted m) :
    ∀ {i j}, i < j → j < m.size → (m.getD i (0, [])).1 < (m.getD j (0, [])).1 := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hnext := h j (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | heq
    · have := ih hlt (by omega); omega
    · subst heq; exact hnext

/-- In a map whose keys strictly increase, entries with the same key are the same entry. -/
private theorem KeysSorted.inj {m : Array (Nat × List Nat)} (h : KeysSorted m) {i j}
    (hi : i < m.size) (hj : j < m.size)
    (he : (m.getD i (0, [])).1 = (m.getD j (0, [])).1) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · have := h.lt hlt hj; omega
  · exact heq
  · have := h.lt hgt hi; omega

/-- The value of `cp` in the map `m`, between the entries `lo` and `hi - 1`, by binary search. -/
def lookupFrom (m : Array (Nat × List Nat)) (cp : Nat) (lo hi : Nat) : Option (List Nat) :=
  if _h : lo < hi then
    let mid := (lo + hi) / 2
    let e := m.getD mid (0, [])
    if cp < e.1 then lookupFrom m cp lo mid
    else if e.1 < cp then lookupFrom m cp (mid + 1) hi
    else some e.2
  else none
termination_by hi - lo

/-- Over a map whose keys strictly increase, the binary search between `lo` and `hi` gives `v`
exactly when an entry between them has the key `cp` and the value `v`. -/
private theorem lookupFrom_iff {m : Array (Nat × List Nat)} (hs : KeysSorted m) (cp : Nat)
    (v : List Nat) : ∀ lo hi, hi ≤ m.size → (lookupFrom m cp lo hi = some v ↔
      ∃ i, lo ≤ i ∧ i < hi ∧ (m.getD i (0, [])).1 = cp ∧ (m.getD i (0, [])).2 = v) := by
  intro lo hi
  induction lo, hi using lookupFrom.induct m cp with
  | case1 lo hi hlt mid e hcp ih =>
    intro hh
    simp only [mid, e] at hcp ih
    rw [lookupFrom, dite_eq_left_of_eq_true (eq_true hlt)]
    simp only [hcp, ↓reduceIte]
    rw [ih (by omega)]
    constructor
    · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, h1, by omega, h3⟩
    · rintro ⟨i, h1, h2, h3, h4⟩
      refine ⟨i, h1, ?_, h3, h4⟩
      apply Decidable.byContradiction; intro hc
      rcases Nat.lt_or_eq_of_le (Nat.not_lt.mp hc) with hlt' | heq
      · have := hs.lt hlt' (by omega); omega
      · subst heq; omega
  | case2 lo hi hlt mid e hcp hcp2 ih =>
    intro hh
    simp only [mid, e] at hcp hcp2 ih
    rw [lookupFrom, dite_eq_left_of_eq_true (eq_true hlt)]
    simp only [hcp, hcp2, ↓reduceIte]
    rw [ih hh]
    constructor
    · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, by omega, h2, h3⟩
    · rintro ⟨i, h1, h2, h3, h4⟩
      refine ⟨i, ?_, h2, h3, h4⟩
      apply Decidable.byContradiction; intro hc
      rcases Nat.lt_or_eq_of_le (Nat.not_lt.mp hc) with hlt' | heq
      · have := hs.lt hlt' (by omega); omega
      · subst heq; omega
  | case3 lo hi hlt mid e hcp hcp2 =>
    intro hh
    simp only [mid, e] at hcp hcp2
    rw [lookupFrom, dite_eq_left_of_eq_true (eq_true hlt)]
    simp only [hcp, hcp2, ↓reduceIte, Option.some.injEq]
    have hkey : (m.getD ((lo + hi) / 2) (0, [])).1 = cp := by omega
    constructor
    · intro hv; exact ⟨(lo + hi) / 2, by omega, by omega, hkey, hv⟩
    · rintro ⟨i, h1, h2, h3, h4⟩
      have := hs.inj (i := i) (j := (lo + hi) / 2) (by omega) (by omega) (by omega)
      subst this; exact h4
  | case4 lo hi hlt =>
    intro hh
    rw [lookupFrom, dite_eq_right_of_eq_false (eq_false hlt)]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨i, h1, h2, -⟩; omega

/-- The value of `cp` in the map `m`: a scan. -/
def lookup (m : Array (Nat × List Nat)) (cp : Nat) : Option (List Nat) :=
  (m.find? (·.1 == cp)).map (·.2)

/-- Over a map whose keys strictly increase, the binary search gives the scan's answer. -/
theorem lookupFrom_eq {m : Array (Nat × List Nat)} (hs : KeysSorted m) (cp : Nat) :
    lookupFrom m cp 0 m.size = lookup m cp := by
  have hget : ∀ i (h : i < m.size), m.getD i (0, []) = m[i] := by
    intro i h; simp [Array.getD_eq_getD_getElem?, h]
  cases hl : lookupFrom m cp 0 m.size with
  | some v =>
    obtain ⟨i, -, hi, hk, hv⟩ := (lookupFrom_iff hs cp v 0 m.size (Nat.le_refl _)).mp hl
    rw [hget i hi] at hk hv
    have hfind : m.find? (·.1 == cp) = some m[i] := by
      rw [Array.find?_eq_some_iff_getElem]
      refine ⟨by simp [hk], i, hi, rfl, fun j hj => ?_⟩
      have := hs.lt hj hi
      rw [hget j (by omega), hget i hi] at this
      simp; omega
    simp [lookup, hfind, hv]
  | none =>
    have hnone : m.find? (·.1 == cp) = none := by
      rw [Array.find?_eq_none]
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
      intro hp
      have := (lookupFrom_iff hs cp m[i].2 0 m.size (Nat.le_refl _)).mpr
        ⟨i, Nat.zero_le _, hi, by rw [hget i hi]; simpa using hp, by rw [hget i hi]⟩
      rw [hl] at this; cases this
    simp [lookup, hnone]

/-- Whether the keys of `l` strictly increase, by one pass over the list. -/
def keysSortedList : List (Nat × List Nat) → Bool
  | a :: b :: rest => decide (a.1 < b.1) && keysSortedList (b :: rest)
  | _ => true

/-- `keysSortedList l` says that each key of `l` is smaller than the next. -/
private theorem keysSortedList_spec : ∀ l : List (Nat × List Nat), keysSortedList l = true →
    ∀ i, i + 1 < l.length → (l.getD i (0, [])).1 < (l.getD (i + 1) (0, [])).1
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | a :: b :: rest, h, i, hi => by
    simp only [keysSortedList, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using keysSortedList_spec (b :: rest) h.2 i (by simp at hi ⊢; omega)

/-- An array whose list passes `keysSortedList` has strictly increasing keys. -/
theorem KeysSorted.of_list {m : Array (Nat × List Nat)} (h : keysSortedList m.toList = true) :
    KeysSorted m := by
  intro i hi
  have hget : ∀ i, m.getD i (0, []) = m.toList.getD i (0, []) := by
    intro i; simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [hget, hget]
  exact keysSortedList_spec m.toList h i (by simpa using hi)

/-- The value of `cp` in the map `m`, given the proof that its keys strictly increase: a scan,
which the compiled code runs as the binary search (`inMap_eq_fast`). -/
def inMap (m : Array (Nat × List Nat)) (_h : KeysSorted m) (cp : Nat) : Option (List Nat) :=
  lookup m cp

/-- `inMap` by binary search. -/
def inMapFast (m : Array (Nat × List Nat)) (_h : KeysSorted m) (cp : Nat) : Option (List Nat) :=
  lookupFrom m cp 0 m.size

/-- The scan and the binary search of a map are the same function, so the compiled code runs
the search. -/
@[csimp] theorem inMap_eq_fast : @inMap = @inMapFast := by
  funext m h cp
  exact (lookupFrom_eq h cp).symm

/-- The keys of `upperMap` strictly increase. -/
theorem upperMap_sorted : KeysSorted upperMap := KeysSorted.of_list (by decide +kernel)

/-- The keys of `lowerMap` strictly increase. -/
theorem lowerMap_sorted : KeysSorted lowerMap := KeysSorted.of_list (by decide +kernel)

/-- The keys of `titleMap` strictly increase. -/
theorem titleMap_sorted : KeysSorted titleMap := KeysSorted.of_list (by decide +kernel)

/-- The keys of `casefoldMap` strictly increase. -/
theorem casefoldMap_sorted : KeysSorted casefoldMap := KeysSorted.of_list (by decide +kernel)

/-- The characters of the code points `cps`. No case mapping gives a surrogate (the generator
checks it). -/
def chars (cps : List Nat) : List Char := cps.map Char.ofNat

/-- `str.upper()` of one character: its full uppercase mapping. -/
def toUpper (c : Char) : List Char := ((inMap upperMap upperMap_sorted c.toNat).map chars).getD [c]

/-- `str.lower()` of one character, without the final-sigma rule. -/
def toLower (c : Char) : List Char := ((inMap lowerMap lowerMap_sorted c.toNat).map chars).getD [c]

/-- `str.title()` of one character: its full titlecase mapping, `toUpper` unless the map says
otherwise. -/
def toTitle (c : Char) : List Char := ((inMap titleMap titleMap_sorted c.toNat).map chars).getD (toUpper c)

/-- `str.casefold()` of one character: its full case folding, `toLower` unless the map says
otherwise. -/
def caseFold (c : Char) : List Char := ((inMap casefoldMap casefoldMap_sorted c.toNat).map chars).getD (toLower c)

/-! ## Case methods of `str` -/

/-- CPython's `handle_capital_sigma`: a capital sigma at `i` of `s` becomes a final sigma `ς`
when a cased character comes before it and none comes after it, skipping case-ignorable
characters both ways; otherwise it becomes `σ`. -/
def sigma (s : Array Char) (i : Nat) : Char :=
  let before := back i
  let final := match before with
    | some c => isCased c && (match forward (i + 1) with | some d => !isCased d | none => true)
    | none => false
  if final then 'ς' else 'σ'
where
  /-- The first character before `j` that is not case-ignorable. -/
  back : Nat → Option Char
    | 0 => none
    | j + 1 => let c := s.getD j ' '; if isCaseIgnorable c then back j else some c
  /-- The first character from `j` on that is not case-ignorable. -/
  forward (j : Nat) : Option Char :=
    if j < s.size then
      let c := s.getD j ' '
      if isCaseIgnorable c then forward (j + 1) else some c
    else none
  termination_by s.size - j

/-- CPython's `lower_ucs4`: the lowercase of the character at `i` of `s`, with the final-sigma
rule. -/
def lowerAt (s : Array Char) (i : Nat) : List Char :=
  let c := s.getD i ' '
  if c == 'Σ' then [sigma s i] else toLower c

/-- The characters of `s`, each mapped by `f i c` and joined. -/
def mapAt (s : String) (f : Array Char → Nat → Char → List Char) : String :=
  let a := s.toList.toArray
  String.ofList ((List.range a.size).flatMap fun i => f a i (a.getD i ' '))

/-- `str.upper()`. -/
def upper (s : String) : String := mapAt s fun _ _ c => toUpper c

/-- `str.lower()`, with the final-sigma rule. -/
def lower (s : String) : String := mapAt s fun a i _ => lowerAt a i

/-- `str.casefold()`. -/
def casefold (s : String) : String := mapAt s fun _ _ c => caseFold c

/-- `str.swapcase()`: an uppercase character becomes lowercase (with the final-sigma rule), a
lowercase one uppercase, and any other stays. -/
def swapcase (s : String) : String :=
  mapAt s fun a i c => if isUpper c then lowerAt a i else if isLower c then toUpper c else [c]

/-- `str.capitalize()`: the first character in titlecase, the others in lowercase. -/
def capitalize (s : String) : String :=
  mapAt s fun a i c => if i == 0 then toTitle c else lowerAt a i

/-- `str.title()`: a character after a cased one in lowercase, any other in titlecase. -/
def title (s : String) : String :=
  mapAt s fun a i c => if i > 0 && isCased (a.getD (i - 1) ' ') then lowerAt a i else toTitle c

/-! ## Class tests of `str` -/

/-- Whether the string is not empty and every character has the class `p`: the meaning of
`isalpha`, `isdecimal`, `isdigit`, `isnumeric`, `isalnum` and `isspace`. -/
def allNonEmpty (p : Char → Bool) (s : String) : Bool := !s.isEmpty && s.toList.all p

/-- `str.isupper()`: no lowercase or titlecase character, and at least one uppercase one. -/
def isUpperStr (s : String) : Bool :=
  !s.toList.any (fun c => isLower c || isTitlecase c) && s.toList.any isUpper

/-- `str.islower()`: no uppercase or titlecase character, and at least one lowercase one. -/
def isLowerStr (s : String) : Bool :=
  !s.toList.any (fun c => isUpper c || isTitlecase c) && s.toList.any isLower

/-- `str.istitle()`: uppercase and titlecase characters only after uncased ones, lowercase ones
only after cased ones, and at least one cased character. -/
def isTitleStr (s : String) : Bool := go s.toList false false
where
  go : List Char → Bool → Bool → Bool
    | [], _, cased => cased
    | c :: cs, prev, cased =>
      if isUpper c || isTitlecase c then !prev && go cs true true
      else if isLower c then prev && go cs true true
      else go cs false cased

/-- `str.isidentifier()`: a first character that may start an identifier, and others that may
continue one. -/
def isIdentifierStr (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentStart c && cs.all isIdentContinue

/-- `str.isprintable()`: every character is printable; true for the empty string. -/
def isPrintableStr (s : String) : Bool := s.toList.all isPrintable

/-- `str.isascii()`: every character is below 128; true for the empty string. -/
def isAsciiStr (s : String) : Bool := s.toList.all fun c => c.toNat < 128

end

end StrataPython.Dyn.Sem.Library.Unicode
