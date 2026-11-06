/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Unicode

set_option autoImplicit false

/-!
# Regular expressions for `py.reSearch`

`py.reSearch pattern s` holds when `re.search(pattern, s)` finds a match, in the syntax of
Python's `re` module.  This file gives that test for a subset of `re`'s syntax:

* `parse` reads a pattern, or gives `none` for a pattern that is invalid, outside the subset, or
  not well defined (one on which CPython's compiler warns, or that nests more than `maxDepth`
  groups, so that its compiler could overflow the recursion limit);
* `Matches P s r i j`, the meaning: the pattern `r` matches the characters of `s` from position
  `i` to position `j`, where `P` gives Python's character classes;
* `ends P s r S`, the matcher: the positions where `r` can end, from the positions of `S`;
* `search P r s`, whether `r` matches somewhere in `s`.

`RegexProps.lean` proves that `ends` computes exactly the ends that `Matches` allows.  The compiled
code runs faster versions of `iterate`, `closure` and `ends`; the `@[csimp]` theorems that prove
them equal stay in this file, since `search` must be compiled after them.

**The subset.** Literal characters; `.`; sets `[…]` with ranges, negation and escapes; the
escapes of ASCII characters that are neither letters nor digits (punctuation, the space and the
control characters), `\n`, `\t`, `\r`, `\f`, `\v` and `\xhh`; the classes `\d`, `\D`,
`\w`, `\W`, `\s`, `\S`; the assertions `^`, `$`, `\A`, `\Z`, `\b`, `\B`; groups `(…)`, `(?:…)`
and `(?P<name>…)`; `|`; and the quantifiers `*`, `+`, `?`, `{m}`, `{m,}`, `{,n}` and `{m,n}`,
with counts of at most 1000 written with at most 4 digits, greedy or lazy.  Only whether a match
exists counts, so a lazy quantifier means what the greedy one means.  There are no flags: `^`
holds only at the start, and `.` matches every character but `\n`.

**Its own parser.** `StrataPython/Regex/ReParser.lean` also parses `re` patterns, for their
translation to SMT (`ReToCore.lean`).  Its recursive functions are `partial`, and the check of
the rules' table rejects a rule that runs a `partial` definition, whose result proofs can't see.
So `parse` is a total function of its own.
-/

namespace StrataPython.Dyn.Sem.Contracts.Regex

@[expose] public section

/-! ## Patterns -/

/-- A class of characters: `\d`, `\w` or `\s`. -/
inductive ClassKind where
  | digit
  | word
  | space
  deriving Repr, DecidableEq, Inhabited

/-- One item of a set `[…]`. -/
inductive SetItem where
  | char (c : Char)
  /-- The characters from `lo` to `hi`, by code point. -/
  | range (lo hi : Char)
  /-- A class, or its complement if `neg`. -/
  | cls (k : ClassKind) (neg : Bool)
  deriving Repr, DecidableEq, Inhabited

/-- A zero-width assertion. -/
inductive Assertion where
  /-- `^`: the start of the string. -/
  | caret
  /-- `\A`: the start of the string. -/
  | strStart
  /-- `$`: the end of the string, or just before a `\n` that ends it. -/
  | dollar
  /-- `\Z`: the end of the string. -/
  | strEnd
  /-- `\b`: a boundary between a word character and another character, or an end. -/
  | wordB
  /-- `\B`: not a word boundary, in a non-empty string. -/
  | notWordB
  deriving Repr, DecidableEq, Inhabited

/-- A pattern of the subset. -/
inductive Re where
  /-- Matches the empty string. -/
  | empty
  | char (c : Char)
  /-- `.`: any character but `\n`. -/
  | any
  /-- A set `[…]`, or its complement `[^…]` if `neg`. -/
  | set (neg : Bool) (items : List SetItem)
  /-- `\d`, `\w` or `\s`, or its complement if `neg`. -/
  | cls (k : ClassKind) (neg : Bool)
  | assert (a : Assertion)
  | cat (a b : Re)
  | alt (a b : Re)
  /-- `r` repeated at least `lo` times, and at most `hi` times if `hi` is given. -/
  | rep (r : Re) (lo : Nat) (hi : Option Nat)
  deriving Repr, DecidableEq, Inhabited

/-! ## Character classes and tests -/

/-- Python's character predicates behind `\d`, `\w` and `\s`: `str.isdecimal`, `str.isalnum`
and `str.isspace`, one character at a time. -/
structure Classes where
  isDecimal : Char → Bool
  isAlnum : Char → Bool
  isSpace : Char → Bool

/-- CPython 3.12's predicates, from the library's Unicode tables, which a test checks on every
code point. -/
def pyClasses : Classes where
  isDecimal := Library.Unicode.isDecimal
  isAlnum := Library.Unicode.isAlnum
  isSpace := Library.Unicode.isSpace

/-- Whether `c` is a word character: `\w` is `str.isalnum` or `_`. -/
def Classes.isWord (P : Classes) (c : Char) : Bool := P.isAlnum c || c == '_'

/-- Whether `c` is in the class `k`. -/
def Classes.holds (P : Classes) : ClassKind → Char → Bool
  | .digit, c => P.isDecimal c
  | .word, c => P.isWord c
  | .space, c => P.isSpace c

/-- Whether `c` is in the item `it`. -/
def SetItem.holds (P : Classes) (c : Char) : SetItem → Bool
  | .char d => c == d
  | .range lo hi => decide (lo.val ≤ c.val ∧ c.val ≤ hi.val)
  | .cls k neg => P.holds k c != neg

/-- The test that a one-character pattern applies to the character it reads, if `r` is one. -/
def atomTest (P : Classes) : Re → Option (Char → Bool)
  | .char d => some (· == d)
  | .any => some (· != '\n')
  | .set neg items => some fun c => items.any (SetItem.holds P c) != neg
  | .cls k neg => some fun c => P.holds k c != neg
  | _ => none

/-- Whether the character of `s` before position `i` is a word character. -/
def wordBefore (P : Classes) (s : Array Char) (i : Nat) : Bool :=
  match i with
  | 0 => false
  | i + 1 => if h : i < s.size then P.isWord s[i] else false

/-- Whether the character of `s` at position `i` is a word character. -/
def wordAt (P : Classes) (s : Array Char) (i : Nat) : Bool :=
  if h : i < s.size then P.isWord s[i] else false

/-- Whether the assertion `a` holds at position `i` of `s`. -/
def Assertion.holds (P : Classes) (s : Array Char) (i : Nat) : Assertion → Bool
  | .caret | .strStart => i == 0
  | .dollar => i == s.size || (i + 1 == s.size && s[i]? == some '\n')
  | .strEnd => i == s.size
  | .wordB => wordBefore P s i != wordAt P s i
  | .notWordB => s.size != 0 && wordBefore P s i == wordAt P s i

/-! ## The meaning -/

mutual
/-- `Matches P s r i j`: the pattern `r` matches the characters of `s` from position `i` to
position `j`, with `i ≤ j ≤ s.size`. -/
inductive Matches (P : Classes) (s : Array Char) : Re → Nat → Nat → Prop where
  | empty {i : Nat} : i ≤ s.size → Matches P s .empty i i
  | atom {r : Re} {f : Char → Bool} {i : Nat} (hf : atomTest P r = some f) (hi : i < s.size)
      (ht : f s[i] = true) : Matches P s r i (i + 1)
  | assert {a : Assertion} {i : Nat} : i ≤ s.size → a.holds P s i = true →
      Matches P s (.assert a) i i
  | cat {a b : Re} {i j k : Nat} : Matches P s a i j → Matches P s b j k → Matches P s (.cat a b) i k
  | altL {a b : Re} {i j : Nat} : Matches P s a i j → Matches P s (.alt a b) i j
  | altR {a b : Re} {i j : Nat} : Matches P s b i j → Matches P s (.alt a b) i j
  | rep {r : Re} {lo : Nat} {hi : Option Nat} {k i j : Nat} : lo ≤ k →
      (∀ h, hi = some h → k ≤ h) → MatchesN P s r k i j → Matches P s (.rep r lo hi) i j

/-- `MatchesN P s r k i j`: `k` matches of `r`, one after another, lead from `i` to `j`. -/
inductive MatchesN (P : Classes) (s : Array Char) : Re → Nat → Nat → Nat → Prop where
  | zero {r : Re} {i : Nat} : i ≤ s.size → MatchesN P s r 0 i i
  | succ {r : Re} {k i j l : Nat} : Matches P s r i j → MatchesN P s r k j l →
      MatchesN P s r (k + 1) i l
end

/-! ## The matcher

A set of positions of `s` is an array of `s.size + 1` booleans: `S.getD j false` says whether `j` is in
it. -/

/-- The positions from `0` to `s.size` where `p` holds. -/
def posSet (s : Array Char) (p : Nat → Bool) : Array Bool :=
  Array.ofFn (n := s.size + 1) fun j => p j.val

/-- The positions just after a character that `f` accepts, read from a position of `S`. -/
def stepSet (s : Array Char) (f : Char → Bool) (S : Array Bool) : Array Bool :=
  posSet s fun j =>
    match j with
    | 0 => false
    | i + 1 => if h : i < s.size then S.getD i false && f s[i] else false

/-- The union of two sets of positions. -/
def unionSet (s : Array Char) (A B : Array Bool) : Array Bool :=
  posSet s fun j => A.getD j false || B.getD j false

/-- `F` applied `k` times. -/
def iterate (F : Array Bool → Array Bool) : Nat → Array Bool → Array Bool
  | 0, S => S
  | k + 1, S => iterate F k (F S)

/-- `U_{k}`, where `U_0 = A` and `U_{t+1} = A ∪ F U_t`: the positions that zero to `k`
applications of `F` reach from `A`, when `F` distributes over unions. -/
def closure (s : Array Char) (F : Array Bool → Array Bool) (A : Array Bool) :
    Nat → Array Bool
  | 0 => A
  | k + 1 => unionSet s A (F (closure s F A k))

/-- `U_k` from `U`, as `closure` computes it, but stopping as soon as a round adds nothing. -/
def closureFrom (s : Array Char) (F : Array Bool → Array Bool) (A U : Array Bool) :
    Nat → Array Bool
  | 0 => U
  | k + 1 =>
    let U' := unionSet s A (F U)
    if U' == U then U else closureFrom s F A U' k

/-- `closure` with the early stop: the compiled code runs it (`closure_eq_fast`). -/
def closureFast (s : Array Char) (F : Array Bool → Array Bool) (A : Array Bool) (k : Nat) :
    Array Bool :=
  closureFrom s F A A k

/-- Once a round of `closure` adds nothing, no later round does. -/
private theorem closure_stable {s : Array Char} {F : Array Bool → Array Bool} {A : Array Bool}
    {t : Nat} (h : closure s F A (t + 1) = closure s F A t) :
    ∀ m, closure s F A (t + m) = closure s F A t
  | 0 => rfl
  | m + 1 => by
    rw [← Nat.add_assoc, closure, closure_stable h m]
    exact h

/-- `closureFrom`, started at round `t`, gives round `t + k`. -/
private theorem closureFrom_closure (s : Array Char) (F : Array Bool → Array Bool)
    (A : Array Bool) : ∀ (k t : Nat),
    closureFrom s F A (closure s F A t) k = closure s F A (t + k)
  | 0, t => rfl
  | k + 1, t => by
    simp only [closureFrom]
    split
    · rename_i h
      have h' : closure s F A (t + 1) = closure s F A t := beq_iff_eq.1 h
      rw [closure_stable h' (k + 1)]
    · have hc := closureFrom_closure s F A k (t + 1)
      simp only [closure] at hc
      rw [hc, Nat.add_right_comm, Nat.add_assoc]

/-- The compiled code computes `closure` with the early stop.  It is here, not in
`RegexProps.lean`, because `repClosure` below, which `endsFast` runs, must be compiled after it
to run the fast version. -/
@[csimp] theorem closure_eq_fast : @closure = @closureFast := by
  funext s F A k
  have hc := closureFrom_closure s F A k 0
  simp only [closure, Nat.zero_add] at hc
  exact hc.symm

/-- `iterate`, but stopping as soon as a round changes nothing: the compiled code runs it
(`iterate_eq_fast`). -/
def iterateFast (F : Array Bool → Array Bool) : Nat → Array Bool → Array Bool
  | 0, S => S
  | k + 1, S =>
    let S' := F S
    if S' == S then S else iterateFast F k S'

/-- Once `F` fixes `S`, every number of rounds of `iterate` gives `S`. -/
private theorem iterate_fixed {F : Array Bool → Array Bool} {S : Array Bool} (h : F S = S) :
    ∀ k, iterate F k S = S
  | 0 => rfl
  | k + 1 => by rw [iterate, h, iterate_fixed h k]

/-- The compiled code computes `iterate` with the early stop.  It is here, not in
`RegexProps.lean`, because `repIterate` below, which `endsFast` runs, must be compiled after it
to run the fast version. -/
@[csimp] theorem iterate_eq_fast : @iterate = @iterateFast := by
  funext F k S
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [iterate, iterateFast]
    split
    · rename_i h
      rw [beq_iff_eq.1 h, iterate_fixed (beq_iff_eq.1 h) k]
    · exact ih _

/-- The positions where `r` can end a match that starts at a position of `S`.  A repeat applies
its body `lo` times, then closes under at most `hi - lo` more applications.  A match of the body
never moves back, so `s.size + 1` more rounds reach every position that more rounds would. -/
def ends (P : Classes) (s : Array Char) : Re → Array Bool → Array Bool
  | .empty, S => S
  | .assert a, S => posSet s fun j => S.getD j false && a.holds P s j
  | .cat a b, S => ends P s b (ends P s a S)
  | .alt a b, S => unionSet s (ends P s a S) (ends P s b S)
  | .rep r lo hi, S =>
    match hi with
    | some h =>
      if h < lo then posSet s fun _ => false
      else closure s (ends P s r) (iterate (ends P s r) lo S) (min (h - lo) (s.size + 1))
    | none => closure s (ends P s r) (iterate (ends P s r) lo S) (s.size + 1)
  | r, S => match atomTest P r with
    | some f => stepSet s f S
    | none => posSet s fun _ => false

/-! ### Repeats of a one-character test, in one pass

The rounds of `iterate` and `closure` cost a pass over `s` each, so a repeat of a one-character test
with a large count, or with no upper bound, would take time quadratic in the length of `s`. For such
a repeat, one `stepSet` or `runSet` computes the `lo` required matches and `sweep` the closure, in
one pass from left to right each. `charTest` also counts an alternation of one-character tests as
one test. `endsFast` uses them, and the compiled code runs it (`ends_eq_fast`). A repeat of any
other pattern keeps the rounds of `closure`, one per iteration of its body. -/

/-- A set of positions built by `posSet` has one entry per position, `0` to `s.size`. -/
theorem size_posSet {s : Array Char} (p : Nat → Bool) : (posSet s p).size = s.size + 1 := by
  simp [posSet]

/-- Position `j` is in `posSet s p` when `j ≤ s.size` and `p j` holds. -/
theorem getD_posSet {s : Array Char} (p : Nat → Bool) (j : Nat) :
    (posSet s p).getD j false = (decide (j ≤ s.size) && p j) := by
  simp only [posSet, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases h : j < s.size + 1
  · simp [h, show j ≤ s.size by omega]
  · simp [h, show ¬ j ≤ s.size by omega]

/-- The test of a one-character pattern, or of an alternation of such patterns. -/
def charTest (P : Classes) : Re → Option (Char → Bool)
  | .alt a b => match charTest P a, charTest P b with
    | some f, some g => some fun c => f c || g c
    | _, _ => none
  | r => atomTest P r

/-- The number of characters that `f` accepts just before position `j` of `s`, in a row. -/
def runLen (s : Array Char) (f : Char → Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => if h : i < s.size then (if f s[i] then runLen s f i + 1 else 0) else 0

/-- The rest of `runSet`: `acc` holds the positions before `j`, and `L` is `runLen s f j`. -/
def runSetGo (s : Array Char) (f : Char → Bool) (S : Array Bool) (lo j L : Nat)
    (acc : Array Bool) : Array Bool :=
  let acc := acc.push (decide (lo ≤ L) && S.getD (j - lo) false)
  if h : j < s.size then runSetGo s f S lo (j + 1) (if f s[j] then L + 1 else 0) acc else acc
termination_by s.size - j

/-- The positions reached from a position of `S` by `lo` characters in a row that `f` accepts, in
one pass. -/
def runSet (s : Array Char) (f : Char → Bool) (S : Array Bool) (lo : Nat) : Array Bool :=
  runSetGo s f S lo 0 0 #[]

/-- The fewest characters that `f` accepts in a row from a position of `A` to `j`, if any. -/
def distAt (s : Array Char) (f : Char → Bool) (A : Array Bool) : Nat → Option Nat
  | 0 => if A.getD 0 false then some 0 else none
  | i + 1 =>
    if A.getD (i + 1) false then some 0
    else if h : i < s.size then (if f s[i] then (distAt s f A i).map (· + 1) else none) else none

/-- Whether a distance is at most `k`. -/
def within (k : Nat) : Option Nat → Bool
  | some d => decide (d ≤ k)
  | none => false

/-- The rest of `sweep`: `acc` holds the positions up to `j`, and `d` is `distAt s f A j`. -/
def sweepGo (s : Array Char) (f : Char → Bool) (A : Array Bool) (k j : Nat) (d : Option Nat)
    (acc : Array Bool) : Array Bool :=
  if h : j < s.size then
    let d := if A.getD (j + 1) false then some 0
      else match d with
        | some x => if f s[j] then some (x + 1) else none
        | none => none
    sweepGo s f A k (j + 1) d (acc.push (within k d))
  else acc
termination_by s.size - j

/-- The positions reached from a position of `A` by at most `k` characters in a row that `f`
accepts, in one pass. -/
def sweep (s : Array Char) (f : Char → Bool) (A : Array Bool) (k : Nat) : Array Bool :=
  let d := distAt s f A 0
  sweepGo s f A k 0 d #[within k d]

/-- `iterate F lo S`, where `F` is the steps of `r`: by one `stepSet` or by `runSet` when `r` has a
`charTest`. -/
def repIterate (P : Classes) (s : Array Char) (r : Re) (F : Array Bool → Array Bool) (lo : Nat)
    (S : Array Bool) : Array Bool :=
  match charTest P r with
  | some f => if lo = 1 then stepSet s f S else if 0 < lo then runSet s f S lo else S
  | none => iterate F lo S

/-- `closure s F A k`, where `F` is the steps of `r`: by `sweep` when `r` has a `charTest`. -/
def repClosure (P : Classes) (s : Array Char) (r : Re) (F : Array Bool → Array Bool)
    (A : Array Bool) (k : Nat) : Array Bool :=
  match charTest P r with
  | some f => if 0 < k then sweep s f A k else A
  | none => closure s F A k

/-- `ends`, with the repeats by `repIterate` and `repClosure`. -/
def endsFast (P : Classes) (s : Array Char) : Re → Array Bool → Array Bool
  | .empty, S => S
  | .assert a, S => posSet s fun j => S.getD j false && a.holds P s j
  | .cat a b, S => endsFast P s b (endsFast P s a S)
  | .alt a b, S => unionSet s (endsFast P s a S) (endsFast P s b S)
  | .rep r lo hi, S =>
    match hi with
    | some h =>
      if h < lo then posSet s fun _ => false
      else repClosure P s r (endsFast P s r) (repIterate P s r (endsFast P s r) lo S)
        (min (h - lo) (s.size + 1))
    | none =>
      repClosure P s r (endsFast P s r) (repIterate P s r (endsFast P s r) lo S) (s.size + 1)
  | r, S => match atomTest P r with
    | some f => stepSet s f S
    | none => posSet s fun _ => false

/-- Two arrays of `s.size + 1` entries that agree at every position are equal. -/
private theorem positions_ext {s : Array Char} {X Y : Array Bool} (hX : X.size = s.size + 1)
    (hY : Y.size = s.size + 1) (h : ∀ j, j ≤ s.size → X.getD j false = Y.getD j false) : X = Y := by
  apply Array.ext (by rw [hX, hY])
  intro i h1 h2
  have e := h i (by omega)
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2, Option.getD_some] at e
  exact e

/-- `ends` of a pattern with a `charTest` is one step of that test. -/
private theorem ends_of_charTest {P : Classes} {s : Array Char} {r : Re} {f : Char → Bool}
    (hf : charTest P r = some f) : ends P s r = stepSet s f := by
  induction r generalizing f with
  | alt a b iha ihb =>
    simp only [charTest] at hf
    split at hf
    · rename_i fa fb ha hb
      cases hf
      funext S
      rw [ends, iha ha, ihb hb]
      apply positions_ext (size_posSet _) (size_posSet _)
      intro j hj
      simp only [stepSet, getD_posSet, hj, decide_true, Bool.true_and]
      cases j with
      | zero => rfl
      | succ i =>
        by_cases hi : i < s.size
        · simp only [hi, dite_true]
          cases (S.getD i false) <;> simp
        · simp [hi]
    · cases hf
  | _ => funext S; simp_all [charTest, atomTest, ends]

/-- `iterate` applies its last step last. -/
private theorem iterate_succ' (F : Array Bool → Array Bool) :
    ∀ (m : Nat) (S : Array Bool), iterate F (m + 1) S = F (iterate F m S)
  | 0, _ => rfl
  | m + 1, S => iterate_succ' F m (F S)

/-- After `m ≥ 1` steps of `f` from `S`, position `j` is in the set exactly when the `m` characters
before it pass `f` and position `j - m` is in `S`. -/
private theorem getD_iterate_stepSet {s : Array Char} {f : Char → Bool} :
    ∀ (m : Nat) (S : Array Bool) (j : Nat), 0 < m →
      (iterate (stepSet s f) m S).getD j false =
        (decide (j ≤ s.size) && decide (m ≤ runLen s f j) && S.getD (j - m) false)
  | 0, _, _, h => absurd h (Nat.lt_irrefl 0)
  | m + 1, S, j, _ => by
    rw [iterate_succ', stepSet, getD_posSet]
    cases j with
    | zero => simp [runLen]
    | succ i =>
      by_cases hi : i < s.size
      · cases m with
        | zero =>
          simp only [iterate, hi, dite_true, runLen]
          by_cases hfi : f s[i] <;> simp [hfi, show i + 1 ≤ s.size by omega]
        | succ m =>
          simp only [hi, ↓reduceDIte, runLen]
          rw [getD_iterate_stepSet (s := s) (f := f) (m + 1) S i (by omega)]
          by_cases hfi : f s[i]
          · simp only [hfi, ↓reduceIte, Nat.add_le_add_iff_right,
              show i + 1 - (m + 1 + 1) = i - (m + 1) by omega, show i + 1 ≤ s.size by omega,
              show i ≤ s.size by omega, decide_true, Bool.true_and, Bool.and_true]
          · simp [hfi]
      · simp [hi, runLen]

/-- `runSetGo` from position `j`, given the entries before `j`, gives `s.size + 1` entries, and
position `q` is in them exactly when `lo ≤ runLen s f q` and `q - lo` is in `S`. -/
private theorem runSetGo_spec {s : Array Char} {f : Char → Bool} {S : Array Bool} {lo : Nat}
    (j : Nat) (acc : Array Bool) (hj : j ≤ s.size) (hsize : acc.size = j)
    (hget : ∀ q, q < j → acc.getD q false = (decide (lo ≤ runLen s f q) && S.getD (q - lo) false)) :
    (runSetGo s f S lo j (runLen s f j) acc).size = s.size + 1 ∧
      ∀ q, q ≤ s.size → (runSetGo s f S lo j (runLen s f j) acc).getD q false =
        (decide (lo ≤ runLen s f q) && S.getD (q - lo) false) := by
  unfold runSetGo
  have hpush : ∀ q, q ≤ j → (acc.push (decide (lo ≤ runLen s f j) && S.getD (j - lo) false)).getD
      q false = (decide (lo ≤ runLen s f q) && S.getD (q - lo) false) := by
    intro q hq
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
    by_cases hqj : q = j
    · subst hqj
      simp only [hsize, ↓reduceIte, Option.getD_some]
    · simp only [show q ≠ acc.size by omega, ↓reduceIte]
      rw [← Array.getD_eq_getD_getElem?]
      exact hget q (by omega)
  by_cases hlt : j < s.size
  · simp only [hlt, ↓reduceDIte]
    have hL : (if f s[j] then runLen s f j + 1 else 0) = runLen s f (j + 1) := by
      simp [runLen, hlt]
    rw [hL]
    exact runSetGo_spec (j + 1) _ (by omega) (by simp [hsize]) (fun q hq => hpush q (by omega))
  · simp only [hlt, ↓reduceDIte]
    have hjs : j = s.size := by omega
    subst hjs
    exact ⟨by simp [hsize], hpush⟩
termination_by s.size - j

/-- For `lo ≥ 1`, `runSet` is `lo` steps of `f`. -/
private theorem iterate_stepSet_eq_runSet {s : Array Char} {f : Char → Bool} {S : Array Bool}
    {lo : Nat} (hlo : 0 < lo) : iterate (stepSet s f) lo S = runSet s f S lo := by
  obtain ⟨m, rfl⟩ : ∃ m, lo = m + 1 := ⟨lo - 1, by omega⟩
  have hspec := runSetGo_spec (s := s) (f := f) (S := S) (lo := m + 1) 0 #[] (Nat.zero_le _) rfl
    (fun q hq => absurd hq (Nat.not_lt_zero q))
  have hsz : (iterate (stepSet s f) (m + 1) S).size = s.size + 1 := by
    rw [iterate_succ']; exact size_posSet _
  apply positions_ext hsz hspec.1
  intro j hj
  rw [getD_iterate_stepSet (s := s) (f := f) (m + 1) S j (by omega), hspec.2 j hj]
  simp [hj]

/-- After `t` rounds of `closure` of one step of `f` from `A`, a position `j ≤ s.size` is in the set
exactly when `distAt s f A j` is at most `t`. -/
private theorem getD_closure_stepSet {s : Array Char} {f : Char → Bool} {A : Array Bool} :
    ∀ (t j : Nat), j ≤ s.size →
      (closure s (stepSet s f) A t).getD j false = within t (distAt s f A j)
  | 0, 0, _ => by simp only [closure, distAt]; split <;> simp_all [within]
  | 0, j + 1, _ => by
    simp only [closure, distAt]
    split
    · simp_all [within]
    · rename_i hA
      simp only [Bool.not_eq_true] at hA
      rw [hA]
      split
      · split
        · cases distAt s f A j <;> simp [within]
        · rfl
      · rfl
  | t + 1, 0, _ => by
    show (unionSet s A (stepSet s f (closure s (stepSet s f) A t))).getD 0 false = _
    rw [unionSet, getD_posSet, stepSet, getD_posSet]
    simp only [distAt, Nat.zero_le, decide_true, Bool.true_and, Bool.and_false, Bool.or_false]
    split <;> simp_all [within]
  | t + 1, j + 1, hj => by
    have hlt : j < s.size := by omega
    have ih := getD_closure_stepSet (s := s) (f := f) (A := A) t j (by omega)
    show (unionSet s A (stepSet s f (closure s (stepSet s f) A t))).getD (j + 1) false = _
    rw [unionSet, getD_posSet, stepSet, getD_posSet]
    simp only [distAt, hj, hlt, decide_true, Bool.true_and, dite_true, ih]
    by_cases hA : A.getD (j + 1) false
    · simp [hA, within]
    · simp only [hA, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      by_cases hfi : f s[j]
      · simp only [hfi, Bool.and_true, ↓reduceIte]
        cases distAt s f A j <;> simp [within]
      · simp [hfi, within]

/-- `sweepGo` from position `j`, given the entries up to `j`, gives `s.size + 1` entries, and
position `q` is in them exactly when `distAt s f A q` is at most `k`. -/
private theorem sweepGo_spec {s : Array Char} {f : Char → Bool} {A : Array Bool} {k : Nat}
    (j : Nat) (acc : Array Bool) (hj : j ≤ s.size) (hsize : acc.size = j + 1)
    (hget : ∀ q, q ≤ j → acc.getD q false = within k (distAt s f A q)) :
    (sweepGo s f A k j (distAt s f A j) acc).size = s.size + 1 ∧
      ∀ q, q ≤ s.size → (sweepGo s f A k j (distAt s f A j) acc).getD q false =
        within k (distAt s f A q) := by
  unfold sweepGo
  by_cases hlt : j < s.size
  · simp only [hlt, ↓reduceDIte]
    have hd : (if A.getD (j + 1) false then some 0
        else match distAt s f A j with
          | some x => if f s[j] then some (x + 1) else none
          | none => none) = distAt s f A (j + 1) := by
      simp only [distAt, hlt, ↓reduceDIte]
      split
      · rfl
      · cases distAt s f A j <;> simp
    rw [hd]
    apply sweepGo_spec (j + 1) _ (by omega) (by simp [hsize])
    intro q hq
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
    by_cases hqj : q = j + 1
    · subst hqj
      simp only [hsize, ↓reduceIte, Option.getD_some]
    · simp only [show q ≠ acc.size by omega, ↓reduceIte]
      rw [← Array.getD_eq_getD_getElem?]
      exact hget q (by omega)
  · simp only [hlt, ↓reduceDIte]
    have hjs : j = s.size := by omega
    subst hjs
    exact ⟨hsize, hget⟩
termination_by s.size - j

/-- For `k ≥ 1`, `sweep` is `k` rounds of `closure` of one step of `f`. -/
private theorem closure_stepSet_eq_sweep {s : Array Char} {f : Char → Bool} {A : Array Bool}
    {k : Nat} (hk : 0 < k) : closure s (stepSet s f) A k = sweep s f A k := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hspec := sweepGo_spec (f := f) (A := A) (k := t + 1) 0 #[within (t + 1) (distAt s f A 0)]
    (Nat.zero_le _) rfl (fun q hq => by have : q = 0 := by omega
                                        subst this; rfl)
  have hsz : (closure s (stepSet s f) A (t + 1)).size = s.size + 1 := size_posSet _
  apply positions_ext hsz hspec.1
  intro j hj
  rw [getD_closure_stepSet (t + 1) j hj, hspec.2 j hj]

/-- `repIterate` computes `iterate` of the steps of `ends`. -/
private theorem iterate_eq_repIterate {P : Classes} {s : Array Char} (r : Re) (lo : Nat)
    (S : Array Bool) : iterate (ends P s r) lo S = repIterate P s r (ends P s r) lo S := by
  unfold repIterate
  split
  · rename_i f hf
    rw [ends_of_charTest hf]
    split
    · rename_i hlo
      subst hlo; rfl
    · split
      · exact iterate_stepSet_eq_runSet (by omega)
      · rename_i hlo
        have : lo = 0 := by omega
        subst this; rfl
  · rfl

/-- `repClosure` computes `closure` of the steps of `ends`. -/
private theorem closure_eq_repClosure {P : Classes} {s : Array Char} (r : Re) (A : Array Bool)
    (k : Nat) : closure s (ends P s r) A k = repClosure P s r (ends P s r) A k := by
  unfold repClosure
  split
  · rename_i f hf
    rw [ends_of_charTest hf]
    split
    · exact closure_stepSet_eq_sweep (by omega)
    · rename_i hk
      have : k = 0 := by omega
      subst this; rfl
  · rfl

/-- The compiled code computes `ends` with `repIterate` and `repClosure`.  It is here, not in
`RegexProps.lean`, because `search` below must be compiled after it to run the fast version. -/
@[csimp] theorem ends_eq_fast : @ends = @endsFast := by
  funext P s r
  induction r with
  | rep r lo hi ih =>
    funext S
    have hr : ends P s r = endsFast P s r := ih
    cases hi with
    | none => simp only [ends, endsFast, ← hr, iterate_eq_repIterate, closure_eq_repClosure]
    | some h => simp only [ends, endsFast, ← hr, iterate_eq_repIterate, closure_eq_repClosure]
  | cat a b iha ihb => funext S; simp only [ends, endsFast, iha, ihb]
  | alt a b iha ihb => funext S; simp only [ends, endsFast, iha, ihb]
  | _ => rfl

/-- Whether `r` matches somewhere in `s`: `re.search` finds a match. -/
def search (P : Classes) (r : Re) (s : Array Char) : Bool :=
  (ends P s r (posSet s fun _ => true)).any id

/-! ## The parser

`parse` reads the pattern left to right, one token at a time, with a stack of open groups.  It
gives `none` for every pattern that it doesn't read as CPython 3.12 does: an invalid pattern
(where `re.compile` raises), a pattern outside the subset, and a pattern on which CPython's
compiler warns or nests more than `maxDepth` groups. -/

/-- The greatest group nesting that `parse` reads.  The rules run up to a Python call depth of
900, below CPython's recursion limit of 1000, and CPython 3.12's compiler takes up to about 3.5
Python frames per group.  Measured on CPython 3.12.15, with `re.purge()` before each compile so
that the pattern cache doesn't hide a failure: at call depths 905 and 930, CPython compiles 42
nested plain groups and 29 of the costliest shape measured (`(b|(b|…c)*)*`), and every random
pattern of 20 nested groups; at 950, most of them raise `RecursionError`.  Measure again before
raising this bound. -/
def maxDepth : Nat := 20

/-- The greatest repetition count that `parse` reads. -/
def maxCount : Nat := 1000

/-- The greatest number of digits of a repetition count that `parse` reads.  CPython raises
`ValueError` on a count written with more than 4300 digits, whatever its value. -/
def maxDigits : Nat := 4

/-- What is left of `cs` after a token: a strictly shorter list. -/
abbrev Rest (cs : List Char) := {r : List Char // r.length < cs.length}

/-- `r` as what is left of `cs`, if it is shorter. -/
def shorter (cs r : List Char) : Option (Rest cs) :=
  if h : r.length < cs.length then some ⟨r, h⟩ else none

/-- Whether `c` is an ASCII letter or digit. -/
def isAsciiAlnum (c : Char) : Bool := c.isAlphanum && c.val < 128

/-- The value of a hexadecimal digit. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.val.toNat - '0'.val.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.val.toNat - 'a'.val.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.val.toNat - 'A'.val.toNat + 10)
  else none

/-- The character of `\xhh`, from the two digits after the `x`. -/
def hexChar (a b : Char) : Option Char := do
  let x ← hexVal a
  let y ← hexVal b
  pure (Char.ofNat (16 * x + y))

/-- The character of the escape `\c` that stands for one character, other than `\x` and `\b`: a
control escape, or an ASCII character that is neither a letter nor a digit. -/
def simpleEscape (c : Char) : Option Char :=
  match c with
  | 'n' => some '\n'
  | 't' => some '\t'
  | 'r' => some '\r'
  | 'f' => some '\x0c'
  | 'v' => some '\x0b'
  | c => if c.val < 128 && !isAsciiAlnum c then some c else none

/-- The class of the escape `\c`, if it is one. -/
def classEscape : Char → Option (ClassKind × Bool)
  | 'd' => some (.digit, false)
  | 'D' => some (.digit, true)
  | 'w' => some (.word, false)
  | 'W' => some (.word, true)
  | 's' => some (.space, false)
  | 'S' => some (.space, true)
  | _ => none

/-- An item of a set before a possible range: a character, escaped or not, or a class. -/
inductive SetAtom where
  | char (c : Char) (escaped : Bool)
  | cls (k : ClassKind) (neg : Bool)

/-- The set item of an atom. -/
def SetAtom.item : SetAtom → SetItem
  | .char d _ => .char d
  | .cls k neg => .cls k neg

/-- One atom of a set, with what follows it.  In a set, `\b` is a backspace. -/
def setAtom (cs : List Char) : Option (SetAtom × List Char) :=
  match cs with
  | '\\' :: 'x' :: a :: b :: rest => (hexChar a b).map fun d => (.char d true, rest)
  | '\\' :: c :: rest =>
    match classEscape c with
    | some (k, neg) => some (.cls k neg, rest)
    | none =>
      if c == 'b' then some (.char '\x08' true, rest)
      else if c == 'x' then none
      else (simpleEscape c).map fun d => (.char d true, rest)
  | '\\' :: [] => none
  | c :: rest => some (.char c false, rest)
  | [] => none

/-- The items of a set, up to its closing `]`, with what follows it.  `first` says whether no
item has been read yet: a `]` there is a literal.  Where CPython warns (a doubled `-`, `&`, `~` or
`|` that begins an item other than the first, or a range that ends with an unescaped `-`), or
raises (an unterminated set, a reversed range, a class in a range), it gives `none`. -/
def setItems (cs : List Char) (first : Bool) (acc : List SetItem) :
    Option (List SetItem × List Char) :=
  match _hcs : cs with
  | [] => none
  | c :: rest =>
    if c == ']' && !first then some (acc.reverse, rest)
    else if !first && (c == '-' || c == '&' || c == '~' || c == '|') && rest.head? == some c then
      none
    else
      match setAtom cs with
      | none => none
      | some (lo, rest') =>
        if _hlen : rest'.length < cs.length then
          match lo, rest' with
          | .char l _, '-' :: h :: rest'' =>
            if h == ']' then setItems ('-' :: h :: rest'') false (.char l :: acc)
            else
              match setAtom (h :: rest'') with
              | some (.char hc esc, rest''') =>
                if _hlen2 : rest'''.length < cs.length then
                  if !esc && hc == '-' then none
                  else if l.val ≤ hc.val then setItems rest''' false (.range l hc :: acc)
                  else none
                else none
              | _ => none
          | .cls _ _, '-' :: h :: _ =>
            if h == ']' then setItems rest' false (lo.item :: acc) else none
          | _, _ => setItems rest' false (lo.item :: acc)
        else none
termination_by cs.length
decreasing_by all_goals (subst _hcs; simp_all <;> omega)

/-- The value of the decimal digits at the start of `cs`, how many there are, and what follows
them. -/
def readDigits : List Char → Nat → Nat → Nat × Nat × List Char
  | c :: rest, v, n =>
    if c.isDigit then readDigits rest (10 * v + (c.val.toNat - '0'.val.toNat)) (n + 1)
    else (v, n, c :: rest)
  | [], v, n => (v, n, [])

/-- A counted quantifier after its `{`: `m}`, `m,}`, `,n}` or `m,n}`, with at least one count,
each of at most `maxDigits` digits and at most `maxCount`, and `m ≤ n`. -/
def braceQuant (cs : List Char) : Option (Nat × Option Nat × List Char) :=
  let (m, nm, rest) := readDigits cs 0 0
  if nm > maxDigits || m > maxCount then none else
  match rest with
  | '}' :: rest' => if nm == 0 then none else some (m, some m, rest')
  | ',' :: rest' =>
    let (n, nn, rest'') := readDigits rest' 0 0
    match rest'' with
    | '}' :: rest''' =>
      if nm == 0 && nn == 0 then none
      else if nn == 0 then some (m, none, rest''')
      else if nn > maxDigits || n > maxCount || m > n then none
      else some (m, some n, rest''')
    | _ => none
  | _ => none

/-- An identifier in ASCII, the name of a group, up to its `>`, and what follows the `>`. -/
def readName : List Char → List Char → Option (String × List Char)
  | '>' :: rest, acc =>
    let name := String.ofList acc.reverse
    match acc.reverse with
    | c :: _ =>
      if (c.isAlpha || c == '_') && acc.all (fun d => d.val < 128 && (d.isAlphanum || d == '_'))
      then some (name, rest) else none
    | [] => none
  | c :: rest, acc => readName rest (c :: acc)
  | [], _ => none

/-- A token of a pattern. -/
inductive Token where
  /-- `(`, `(?:` or `(?P<name>`. -/
  | openGroup (name : Option String)
  | close
  | bar
  | quant (lo : Nat) (hi : Option Nat)
  | item (r : Re)
  | assertion (a : Assertion)

/-- Drop the `?` that makes a quantifier lazy. -/
def dropLazy : List Char → List Char
  | '?' :: rest => rest
  | cs => cs

/-- The first token of `cs`, with what follows it, or `none` where `parse` gives up. -/
def nextToken (cs : List Char) : Option (Token × List Char) :=
  match cs with
  | [] => none
  | '(' :: '?' :: ':' :: rest => some (.openGroup none, rest)
  | '(' :: '?' :: 'P' :: '<' :: rest => (readName rest []).map fun (n, r) => (.openGroup (some n), r)
  | '(' :: '?' :: _ => none
  | '(' :: rest => some (.openGroup none, rest)
  | ')' :: rest => some (.close, rest)
  | '|' :: rest => some (.bar, rest)
  | '*' :: rest => some (.quant 0 none, dropLazy rest)
  | '+' :: rest => some (.quant 1 none, dropLazy rest)
  | '?' :: rest => some (.quant 0 (some 1), dropLazy rest)
  | '{' :: rest => (braceQuant rest).map fun (lo, hi, r) => (.quant lo hi, dropLazy r)
  | '[' :: '^' :: rest => (setItems rest true []).map fun (items, r) => (.item (.set true items), r)
  | '[' :: rest =>
    if rest.head? == some '[' then none
    else (setItems rest true []).map fun (items, r) => (.item (.set false items), r)
  | '.' :: rest => some (.item .any, rest)
  | '^' :: rest => some (.assertion .caret, rest)
  | '$' :: rest => some (.assertion .dollar, rest)
  | '\\' :: 'x' :: a :: b :: rest => (hexChar a b).map fun d => (.item (.char d), rest)
  | '\\' :: c :: rest =>
    match classEscape c with
    | some (k, neg) => some (.item (.cls k neg), rest)
    | none =>
      match c with
      | 'b' => some (.assertion .wordB, rest)
      | 'B' => some (.assertion .notWordB, rest)
      | 'A' => some (.assertion .strStart, rest)
      | 'Z' => some (.assertion .strEnd, rest)
      | 'x' => none
      | c => (simpleEscape c).map fun d => (.item (.char d), rest)
  | '\\' :: [] => none
  | c :: rest => some (.item (.char c), rest)

/-- What the last item of a sequence is, for a quantifier that follows it. -/
inductive Last where
  /-- No item yet: a quantifier here has nothing to repeat. -/
  | nothing
  /-- An assertion, which CPython doesn't repeat. -/
  | assertion
  /-- An item that a quantifier may repeat. -/
  | item
  /-- A quantified item: another quantifier is a multiple repeat. -/
  | quantified
  deriving DecidableEq, Repr

/-- An open group, or the whole pattern. -/
structure Frame where
  /-- The alternatives before the last `|`. -/
  alts : List Re := []
  /-- The items of the current alternative, the latest first. -/
  items : List Re := []
  last : Last := .nothing

/-- `items`, latest first, as one sequence. -/
def seqOf : List Re → Re
  | [] => .empty
  | [r] => r
  | r :: rs => .cat (seqOf rs) r

/-- The frame's alternatives, as one pattern. -/
def Frame.finish (f : Frame) : Re :=
  f.alts.foldl (fun acc a => .alt a acc) (seqOf f.items)

/-- Read the tokens of `cs`, with the open groups `stack` around the frame `cur`, and `names`
the group names so far. -/
def parseLoop (cs : List Char) (stack : List Frame) (cur : Frame) (names : List String) :
    Option Re :=
  if cs.isEmpty then (if stack.isEmpty then some cur.finish else none)
  else
    match nextToken cs with
    | none => none
    | some (tok, rest) =>
      if _h : rest.length < cs.length then
        match tok with
        | .openGroup name =>
          if stack.length + 1 > maxDepth then none
          else
            match name with
            | some n =>
              if names.contains n then none else parseLoop rest (cur :: stack) {} (n :: names)
            | none => parseLoop rest (cur :: stack) {} names
        | .close =>
          match stack with
          | [] => none
          | p :: st =>
            parseLoop rest st { p with items := cur.finish :: p.items, last := .item } names
        | .bar =>
          parseLoop rest stack { alts := seqOf cur.items :: cur.alts, items := [], last := .nothing }
            names
        | .quant lo hi =>
          match cur.last, cur.items with
          | .item, r :: items =>
            parseLoop rest stack { cur with items := .rep r lo hi :: items, last := .quantified }
              names
          | _, _ => none
        | .item r => parseLoop rest stack { cur with items := r :: cur.items, last := .item } names
        | .assertion a =>
          parseLoop rest stack { cur with items := .assert a :: cur.items, last := .assertion }
            names
      else none
termination_by cs.length

/-- The pattern `p`, or `none` for a pattern that is invalid, outside the subset, or not well
defined. -/
def parse (p : String) : Option Re := parseLoop p.toList [] {} []

end

end StrataPython.Dyn.Sem.Contracts.Regex
