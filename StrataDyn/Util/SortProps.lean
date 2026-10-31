/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Util.Sort
import all StrataDyn.Util.Sort

set_option autoImplicit false

/-!
# The sort returns a permutation of its input

`sort lt xs` returns a permutation of `xs`, whatever `lt` does in its monad, whether every
comparison succeeds or one fails. (Whether the result is sorted depends on `lt`, and is not
claimed here.)

## Main theorems

* `sort_perm`, the top-level theorem: for every lawful monad `m`, every result of `sort lt xs`
  holds a permutation of `xs`;
* `sort_perm_id`: the same in the identity monad, stated without `SatisfiesM`.

`SatisfiesM p x` says that every result of the monadic program `x` satisfies `p`; it and its
lemmas (`pure'`, `triv`, `imp`, `bind'`, `map'`) let a caller compose `sort_perm` with the steps
around the sort.

## The proof

`WP x Q E s` says that every run of a step `x` of the sort from the state `s` ends in a state
where `Q` holds, or, if a comparison fails, where `E` holds. The comparisons run in `m` and
never touch the sort's state, so only the sort's own updates change it.

Outside a merge, the array is a permutation of `xs`. During `merge_lo`, the first run waits in
`tmp`, and the array has a gap with one slot for each item of `tmp` not placed yet. Copying those
items into the gap gives a permutation of `xs` (`LoInv`). Placing an item of `tmp` keeps that
copy as it is, and placing an item of the second run swaps two blocks of it. The fixup after a
failed comparison (CPython's `Fail`) makes exactly that copy. `merge_hi` is the mirror image
(`HiInv`). A merge needs its two runs side by side inside the array, which the run stack keeps
(`StackOK`).

Everything else in the module is private, its tactic macro included.
-/

namespace Strata.Dyn.Util.Sort

universe u

/-! ## Results of a monadic program -/

/-- `SatisfiesM p x`: every result of `x` satisfies `p`. That is, `x` is a program `y` whose
results carry a proof of `p`, with the proofs dropped. -/
@[expose] public def SatisfiesM {m : Type → Type u} [Functor m] {β : Type} (p : β → Prop)
    (x : m β) : Prop :=
  ∃ y : m {b // p b}, Subtype.val <$> y = x

section SatisfiesM
variable {m : Type → Type u} [Monad m] [LawfulMonad m] {β γ : Type}

/-- A `pure` result satisfies `p` if its value does. -/
public theorem SatisfiesM.pure' {p : β → Prop} {b : β} (h : p b) : SatisfiesM p (pure b : m β) :=
  ⟨pure ⟨b, h⟩, by simp⟩

/-- Every result satisfies `True`. -/
public theorem SatisfiesM.triv {x : m β} : SatisfiesM (fun _ => True) x :=
  ⟨(fun b => ⟨b, trivial⟩) <$> x, by simp [Functor.map_map]⟩

/-- `SatisfiesM` is monotone in the predicate. -/
public theorem SatisfiesM.imp {p q : β → Prop} {x : m β} (hx : SatisfiesM p x)
    (h : ∀ b, p b → q b) : SatisfiesM q x := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(fun b => ⟨b.1, h b.1 b.2⟩) <$> y, by simp [Functor.map_map]⟩

/-- If every result of `x` satisfies `p`, and every result of `f b` satisfies `q` when `p b`
holds, then every result of `x >>= f` satisfies `q`. -/
public theorem SatisfiesM.bind' {p : β → Prop} {q : γ → Prop} {x : m β} {f : β → m γ}
    (hx : SatisfiesM p x) (hf : ∀ b, p b → SatisfiesM q (f b)) : SatisfiesM q (x >>= f) := by
  obtain ⟨y, rfl⟩ := hx
  let g : {b // p b} → m {c // q c} := fun b => Classical.choose (hf b.1 b.2)
  have hg : ∀ b, Subtype.val <$> g b = f b.1 := fun b => Classical.choose_spec (hf b.1 b.2)
  exact ⟨y >>= g, by simp [hg]⟩

/-- If every result of `x` satisfies `p`, and `p b` gives `q (f b)`, then every result of
`f <$> x` satisfies `q`. -/
public theorem SatisfiesM.map' {p : β → Prop} {q : γ → Prop} {x : m β} {f : β → γ}
    (hx : SatisfiesM p x) (h : ∀ b, p b → q (f b)) : SatisfiesM q (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind' fun b hb => SatisfiesM.pure' (h b hb)

end SatisfiesM

/-! ## Weakest preconditions in the sort's monad -/

section WP
variable {m : Type → Type u} [Monad m] [LawfulMonad m] {ε α β γ : Type}

/-- How a run ends: `Q` of the result and the state, or `E` of the error and the state. -/
def Post (Q : β → State α → Prop) (E : ε → State α → Prop) (r : Except ε β × State α) : Prop :=
  match r.1 with
  | .ok b => Q b r.2
  | .error e => E e r.2

/-- `WP x Q E s`: every run of `x` from `s` ends in a state where `Q` holds of the result, or,
if `x` throws, where `E` holds of the error. -/
def WP (x : SortM m ε α β) (Q : β → State α → Prop) (E : ε → State α → Prop) (s : State α) :
    Prop :=
  SatisfiesM (Post Q E) (x.run.run s)

variable {Q Q' : β → State α → Prop} {E E' : ε → State α → Prop} {s : State α}

/-- `WP` is monotone: if every run of `x` from `s` ends where `Q` or `E` holds, and `Q` gives
`Q'` and `E` gives `E'`, then every run ends where `Q'` or `E'` holds. -/
theorem WP.conseq {x : SortM m ε α β} (h : WP x Q E s) (hq : ∀ b s', Q b s' → Q' b s')
    (he : ∀ e s', E e s' → E' e s') : WP x Q' E' s :=
  SatisfiesM.imp h fun r hr => by
    obtain ⟨r, s'⟩ := r
    cases r with
    | ok b => exact hq b s' hr
    | error e => exact he e s' hr

/-- `pure b` ends in the state it starts from, with `b`. -/
theorem wp_pure {b : β} (h : Q b s) : WP (pure b : SortM m ε α β) Q E s :=
  SatisfiesM.pure' h

/-- `throw e` ends in the state it starts from, with the error `e`. -/
theorem wp_throw {e : ε} (h : E e s) : WP (throw e : SortM m ε α β) Q E s :=
  SatisfiesM.pure' h

/-- `x >>= f` meets `Q` if `x` ends where `f` meets `Q`; an error of `x` skips `f`. -/
theorem wp_bind {x : SortM m ε α β} {f : β → SortM m ε α γ} {Q : γ → State α → Prop}
    (h : WP x (fun b s' => WP (f b) Q E s') E s) : WP (x >>= f) Q E s := by
  unfold WP at *
  simp only [ExceptT.run_bind, StateT.run_bind]
  refine SatisfiesM.bind' h fun r hr => ?_
  obtain ⟨r, s'⟩ := r
  cases r with
  | ok b => exact hr
  | error e => exact SatisfiesM.pure' hr

/-- `tryCatch x h` meets `Q` if `x` does, or if it throws where `h` meets `Q`. -/
theorem wp_tryCatch {x : SortM m ε α β} {h : ε → SortM m ε α β}
    (hx : WP x Q (fun e s' => WP (h e) Q E s') s) : WP (tryCatch x h) Q E s := by
  unfold WP at *
  simp only [ExceptT.run_tryCatch, StateT.run_bind]
  refine SatisfiesM.bind' hx fun r hr => ?_
  obtain ⟨r, s'⟩ := r
  cases r with
  | ok b => exact SatisfiesM.pure' hr
  | error e => exact hr

/-- `modifyThe f` replaces the state `s` by `f s`. -/
theorem wp_modifyThe {f : State α → State α} {Q : Unit → State α → Prop} (h : Q () (f s)) :
    WP (modifyThe (State α) f : SortM m ε α Unit) Q E s := by
  unfold WP
  have hrun : (modifyThe (State α) f : SortM m ε α Unit).run.run s = pure (.ok (), f s) := by
    show (Except.ok <$> (modify f : StateT (State α) m Unit)).run s = _
    simp
  rw [hrun]
  exact SatisfiesM.pure' (p := Post Q E) h

/-- `modifyGetThe f` returns `(f s).1` and replaces the state `s` by `(f s).2`. -/
theorem wp_modifyGetThe {f : State α → β × State α} (h : Q (f s).1 (f s).2) :
    WP (modifyGetThe (State α) f : SortM m ε α β) Q E s := by
  unfold WP
  have hrun : (modifyGetThe (State α) f : SortM m ε α β).run.run s =
      pure (.ok (f s).1, (f s).2) := by
    show (Except.ok <$> (modifyGet f : StateT (State α) m β)).run s = _
    simp
  rw [hrun]
  exact SatisfiesM.pure' (p := Post Q E) h

/-- `readState f` returns `f s` and leaves the state `s` alone. -/
theorem wp_readState {f : State α → β} (h : Q (f s) s) : WP (readState f : SortM m ε α β) Q E s :=
  wp_modifyGetThe h

/-- A step of `m`, such as a comparison, may return anything, and leaves the state alone. -/
theorem wp_liftM {x : m β} (h : ∀ b, Q b s) : WP (liftM x : SortM m ε α β) Q E s := by
  unfold WP
  have hrun : (liftM x : SortM m ε α β).run.run s = (fun a => (.ok a, s)) <$> x := by
    show (Except.ok <$> (StateT.lift x : StateT (State α) m β)).run s = _
    simp
  rw [hrun]
  exact SatisfiesM.map' SatisfiesM.triv fun b _ => h b

end WP

/-! ## Arrays read through `get` -/

/-- Closes an equation between `if`s on index ranges, by cases on the conditions. -/
local macro "ite_cases" : tactic =>
  `(tactic| ((repeat' split) <;> first | rfl | omega | (congr 1 <;> omega)))

section Arrays
variable {α : Type} [Inhabited α]

/-- `get` reads an index in range. -/
theorem get_of_lt {a : Array α} {i : Nat} (h : i < a.size) : get a i = a[i] := by
  simp [get, h]

/-- `get` gives `default` past the end. -/
theorem get_of_le {a : Array α} {i : Nat} (h : a.size ≤ i) : get a i = default := by
  simp [get, Nat.not_lt.mpr h]

/-- `setIfInBounds i x` changes the item at `i` only, if `i` is in range. -/
theorem get_setIfInBounds (a : Array α) (i j : Nat) (x : α) :
    get (a.setIfInBounds i x) j = if j = i ∧ j < a.size then x else get a j := by
  by_cases hj : j < a.size
  · have hj' : j < (a.setIfInBounds i x).size := by simpa using hj
    rw [get_of_lt hj', get_of_lt hj, Array.getElem_setIfInBounds hj]
    by_cases h : i = j
    · subst h; simp [hj]
    · simp [h, Ne.symm h]
  · have hj' : (a.setIfInBounds i x).size ≤ j := by simpa using Nat.not_lt.mp hj
    rw [get_of_le hj', get_of_le (Nat.not_lt.mp hj)]
    simp [hj]

/-- `a.extract lo hi` holds `a[lo + i]` at `i`, for `lo + i < hi`. -/
theorem get_extract (a : Array α) {lo hi i : Nat} (h : lo + i < hi) :
    get (a.extract lo hi) i = get a (lo + i) := by
  by_cases hi' : lo + i < a.size
  · have hlt : i < (a.extract lo hi).size := by simp; omega
    rw [get_of_lt hlt, get_of_lt hi', Array.getElem_extract]
  · rw [get_of_le (by simp; omega), get_of_le (by omega)]

/-- Two arrays of the same size are equal if `get` reads the same items from them. -/
theorem ext_get {a b : Array α} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → get a i = get b i) : a = b :=
  Array.ext hs fun i h1 h2 => by rw [← get_of_lt h1, ← get_of_lt h2]; exact h i h1

/-- The loop of `copyRange`, from step `k`, keeps the size, writes `src[start + j]` at `dst + j`
for `k ≤ j < n` where the index is in range, and keeps every other item. -/
theorem copyRange_go_spec (src : Array α) (dst start n : Nat) (a : Array α) (k : Nat) :
    (copyRange.go src dst start n a k).size = a.size ∧
    ∀ i, get (copyRange.go src dst start n a k) i =
      if dst + k ≤ i ∧ i < dst + n ∧ i < a.size then get src (start + (i - dst)) else get a i := by
  induction h : n - k generalizing a k with
  | zero =>
    rw [copyRange.go, ite_eq_right (by omega)]
    refine ⟨rfl, fun i => ?_⟩
    rw [ite_eq_right (by omega)]
  | succ d ih =>
    rw [copyRange.go, ite_eq_left (by omega)]
    obtain ⟨hs, hg⟩ := ih (a.setIfInBounds (dst + k) (get src (start + k))) (k + 1) (by omega)
    refine ⟨by simp [hs], fun i => ?_⟩
    rw [hg, get_setIfInBounds]
    simp only [Array.size_setIfInBounds]
    ite_cases

/-- `copyRange` keeps the size. -/
theorem size_copyRange (a src : Array α) (dst start n : Nat) :
    (copyRange a src dst start n).size = a.size :=
  (copyRange_go_spec src dst start n a 0).1

/-- `copyRange` writes `src[start + k]` at `dst + k`, for `k < n`, where the index is in range,
and keeps every other item. -/
theorem get_copyRange (a src : Array α) (dst start n i : Nat) :
    get (copyRange a src dst start n) i =
      if dst ≤ i ∧ i < dst + n ∧ i < a.size then get src (start + (i - dst)) else get a i := by
  rw [copyRange, (copyRange_go_spec src dst start n a 0).2 i, Nat.add_zero]

/-- The forward loop of `moveWithin`, for `dst ≤ start`, from a state where the first `k` items
are moved, ends with all `n` moved, as `copyRange` from the original array does. -/
theorem moveWithin_fwd_eq (a : Array α) (dst start n : Nat) (hds : dst ≤ start) (b : Array α)
    (k : Nat) (hk : k ≤ n) (hs : b.size = a.size)
    (hb : ∀ i, get b i =
      if dst ≤ i ∧ i < dst + k ∧ i < a.size then get a (start + (i - dst)) else get a i) :
    moveWithin.fwd dst start n b k = copyRange a a dst start n := by
  induction h : n - k generalizing b k with
  | zero =>
    rw [moveWithin.fwd, ite_eq_right (by omega)]
    obtain rfl : k = n := by omega
    exact ext_get (by rw [hs, size_copyRange]) fun i _ => by rw [hb, get_copyRange]
  | succ d ih =>
    rw [moveWithin.fwd, ite_eq_left (by omega)]
    refine ih _ (k + 1) (by omega) (by simp [hs]) (fun i => ?_) (by omega)
    have hsk : get b (start + k) = get a (start + k) := by rw [hb, ite_eq_right (by omega)]
    rw [get_setIfInBounds, hsk, hb i, hs]
    ite_cases

/-- The backward loop of `moveWithin`, for `start < dst`, from a state where all but the first
`k` items are moved, ends with all `n` moved, as `copyRange` from the original array does. -/
theorem moveWithin_bwd_eq (a : Array α) (dst start n : Nat) (hds : start < dst) :
    ∀ (k : Nat) (b : Array α), k ≤ n → b.size = a.size →
      (∀ i, get b i = if dst + k ≤ i ∧ i < dst + n ∧ i < a.size then get a (start + (i - dst))
        else get a i) →
      moveWithin.bwd dst start b k = copyRange a a dst start n
  | 0, b, _, hs, hb => by
    rw [moveWithin.bwd]
    exact ext_get (by rw [hs, size_copyRange]) fun i _ => by
      rw [hb, get_copyRange, Nat.add_zero]
  | k + 1, b, hk, hs, hb => by
    rw [moveWithin.bwd]
    refine moveWithin_bwd_eq a dst start n hds k _ (by omega) (by simp [hs]) fun i => ?_
    have hsk : get b (start + k) = get a (start + k) := by rw [hb, ite_eq_right (by omega)]
    rw [get_setIfInBounds, hsk, hb i, hs]
    ite_cases

/-- `moveWithin` moves as if it read from a copy of the array, as `memmove` does. -/
theorem moveWithin_eq_copyRange (a : Array α) (dst start n : Nat) :
    moveWithin a dst start n = copyRange a a dst start n := by
  rw [moveWithin]
  split
  · exact moveWithin_fwd_eq a dst start n ‹_› a 0 (Nat.zero_le _) rfl fun i => by
      rw [ite_eq_right (by omega)]
  · exact moveWithin_bwd_eq a dst start n (by omega) n a (Nat.le_refl _) rfl fun i => by
      rw [ite_eq_right (by omega)]

/-- Copying no items changes nothing. -/
theorem copyRange_zero (a src : Array α) (dst start : Nat) : copyRange a src dst start 0 = a :=
  ext_get (size_copyRange ..) fun i _ => by rw [get_copyRange, ite_eq_right (by omega)]

/-- Copying one item is one `setIfInBounds`. -/
theorem copyRange_one (a src : Array α) (dst start : Nat) :
    copyRange a src dst start 1 = a.setIfInBounds dst (get src start) :=
  ext_get (by rw [size_copyRange, Array.size_setIfInBounds]) fun i _ => by
    rw [get_copyRange, get_setIfInBounds]
    ite_cases

/-! ## Segments and permutations -/

/-- The `n` items of `a` from index `lo`. -/
def seg (a : Array α) (lo n : Nat) : List α := (List.range n).map fun i => get a (lo + i)

/-- A segment splits into two adjacent ones. -/
theorem seg_add (a : Array α) (lo n k : Nat) :
    seg a lo (n + k) = seg a lo n ++ seg a (lo + n) k := by
  simp [seg, List.range_add, Nat.add_assoc]

/-- Segments are equal if `get` reads the same items in them. -/
theorem seg_congr {a b : Array α} {lo lo' n : Nat}
    (h : ∀ i, i < n → get a (lo + i) = get b (lo' + i)) : seg a lo n = seg b lo' n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- An array's list is its segment from `0`, of its whole size. -/
theorem toList_eq_seg (a : Array α) : a.toList = seg a 0 a.size := by
  apply List.ext_getElem (by simp [seg])
  intro i h1 _
  simp [seg, get_of_lt (show i < a.size by simpa using h1)]

/-- An array that differs from `a` only in the window `[lo, lo + n)`, where it holds a
permutation of `a`'s window, is a permutation of `a`. -/
theorem perm_window {a b : Array α} (lo n : Nat) (hs : b.size = a.size) (hle : lo + n ≤ a.size)
    (hout : ∀ i, i < lo ∨ lo + n ≤ i → get b i = get a i)
    (hw : (seg b lo n).Perm (seg a lo n)) : b.toList.Perm a.toList := by
  obtain ⟨r, hr⟩ : ∃ r, a.size = lo + n + r := ⟨a.size - (lo + n), by omega⟩
  have split3 : ∀ c : Array α, c.size = lo + n + r →
      c.toList = seg c 0 lo ++ seg c lo n ++ seg c (lo + n) r := by
    intro c hc
    rw [toList_eq_seg, hc, seg_add, seg_add]
    simp
  rw [split3 b (by omega), split3 a hr]
  have h1 : seg b 0 lo = seg a 0 lo := seg_congr fun i _ => hout _ (by omega)
  have h3 : seg b (lo + n) r = seg a (lo + n) r := seg_congr fun i _ => hout _ (by omega)
  rw [h1, h3]
  exact (hw.append_left _).append_right _

/-- An array that is `a` with the adjacent blocks `a[lo, lo + n1)` and `a[lo + n1, lo + n1 + n2)`
swapped is a permutation of `a`. -/
theorem perm_swap {a b : Array α} (lo n1 n2 : Nat) (hs : b.size = a.size)
    (hle : lo + n1 + n2 ≤ a.size) (hout : ∀ i, i < lo ∨ lo + n1 + n2 ≤ i → get b i = get a i)
    (h1 : ∀ i, i < n2 → get b (lo + i) = get a (lo + n1 + i))
    (h2 : ∀ i, i < n1 → get b (lo + n2 + i) = get a (lo + i)) : b.toList.Perm a.toList := by
  refine perm_window lo (n1 + n2) hs (by omega) (fun i hi => hout i (by omega)) ?_
  have hb : seg b lo (n1 + n2) = seg a (lo + n1) n2 ++ seg a lo n1 := by
    rw [show n1 + n2 = n2 + n1 from Nat.add_comm _ _, seg_add, seg_congr h1, seg_congr h2]
  rw [hb, seg_add]
  exact List.perm_append_comm

/-- Reversing `a[lo, lo + n)`, as `reverseRange` does, gives a permutation of `a`. -/
theorem perm_reverse (a : Array α) (lo n : Nat) (h : lo + n ≤ a.size) :
    (copyRange a (a.extract lo (lo + n)).reverse lo 0 n).toList.Perm a.toList := by
  have hr : (a.extract lo (lo + n)).reverse.size = n := by simp; omega
  refine perm_window lo n (size_copyRange ..) h
    (fun i hi => by rw [get_copyRange, ite_eq_right (by omega)]) ?_
  have e1 : seg (copyRange a (a.extract lo (lo + n)).reverse lo 0 n) lo n =
      (a.extract lo (lo + n)).reverse.toList := by
    rw [toList_eq_seg (a.extract lo (lo + n)).reverse, hr]
    refine seg_congr fun i hi => ?_
    rw [get_copyRange, ite_eq_left (by omega)]
    congr 1; omega
  have e2 : (a.extract lo (lo + n)).toList = seg a lo n := by
    rw [toList_eq_seg, show (a.extract lo (lo + n)).size = n by simp; omega]
    exact seg_congr fun i hi => by rw [get_extract _ (by omega), Nat.zero_add]
  rw [e1, Array.toList_reverse, e2]
  exact List.reverse_perm _

/-- Moving `a[l, start)` one slot right and putting `a[start]` at `l`, as `binarySort` does,
gives a permutation of `a`. -/
theorem perm_insert (a : Array α) (l start : Nat) (hl : l ≤ start) (hs : start < a.size) :
    ((moveWithin a (l + 1) l (start - l)).setIfInBounds l (get a start)).toList.Perm a.toList := by
  rw [moveWithin_eq_copyRange]
  refine perm_swap l (start - l) 1 (by simp [size_copyRange]) (by omega) (fun i hi => ?_)
    (fun i hi => ?_) (fun i hi => ?_)
  · rw [get_setIfInBounds, get_copyRange, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [get_setIfInBounds, ite_eq_left ⟨by omega, by rw [size_copyRange]; omega⟩]
    congr 1; omega
  · rw [get_setIfInBounds, ite_eq_right (by omega), get_copyRange, ite_eq_left (by omega)]
    congr 1; omega

end Arrays

/-! ## The invariants of the merges -/

section Merge
variable {α : Type} [Inhabited α]

/-- `a` holds the items of `xs`, in some order. -/
def PermOf (xs a : Array α) : Prop := a.toList.Perm xs.toList

omit [Inhabited α] in
/-- A permutation of `xs` has the size of `xs`. -/
theorem PermOf.size {xs a : Array α} (h : PermOf xs a) : a.size = xs.size := by
  simpa using h.length_eq

/-- `merge_lo`'s invariant, with `na` items of the first run left at the end of `tmp` and `nb`
items of the second run left at the end of `a[pb, pb + nbO)`: the counts and the runs are in
range, and copying the rest of the first run into the gap before the rest of the second run
gives a permutation of `xs`. -/
def LoInv (xs tmp : Array α) (naO pb nbO na nb : Nat) (a : Array α) : Prop :=
  na ≤ naO ∧ nb ≤ nbO ∧ naO ≤ pb ∧ pb + nbO ≤ a.size ∧
    PermOf xs (copyRange a tmp (loJ pb nbO nb - na) (naO - na) na)

variable {xs tmp a : Array α} {naO pb nbO na nb k : Nat}

/-- At the start of `merge_lo`, with the first run `a[pa, pb)` copied to `tmp`, the gap is the
first run itself, so its invariant holds. -/
theorem LoInv.start {pa : Nat} (h : PermOf xs a) (hpb : pb = pa + na) (hle : pb + nb ≤ a.size) :
    LoInv xs (a.extract pa (pa + na)) na pb nb na nb a := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, by omega, hle, ?_⟩
  have e : copyRange a (a.extract pa (pa + na)) (loJ pb nb nb - na) (na - na) na = a := by
    refine ext_get (size_copyRange ..) fun i _ => ?_
    rw [get_copyRange]
    unfold loJ
    split
    · rw [get_extract _ (by omega)]
      congr 1; omega
    · rfl
  rw [e]
  exact h

/-- Placing the next `k` items of `tmp` into the gap keeps `merge_lo`'s invariant. -/
theorem LoInv.takeA (hk : k ≤ na) (h : LoInv xs tmp naO pb nbO na nb a) :
    LoInv xs tmp naO pb nbO (na - k) nb (copyRange a tmp (loJ pb nbO nb - na) (naO - na) k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by omega, h2, h3, by rw [size_copyRange]; exact h4, ?_⟩
  have e : copyRange (copyRange a tmp (loJ pb nbO nb - na) (naO - na) k) tmp
      (loJ pb nbO nb - (na - k)) (naO - (na - k)) (na - k) =
      copyRange a tmp (loJ pb nbO nb - na) (naO - na) na := by
    refine ext_get (by simp [size_copyRange]) fun i _ => ?_
    simp only [get_copyRange, size_copyRange]
    unfold loJ
    ite_cases
  rw [e]
  exact h5

/-- Placing the next item of `tmp` into the gap keeps `merge_lo`'s invariant. -/
theorem LoInv.takeA1 (hna : 1 ≤ na) (h : LoInv xs tmp naO pb nbO na nb a) :
    LoInv xs tmp naO pb nbO (na - 1) nb
      (a.setIfInBounds (loJ pb nbO nb - na) (get tmp (naO - na))) := by
  rw [← copyRange_one]
  exact h.takeA hna

/-- Moving the next `k` items of the second run into the gap keeps `merge_lo`'s invariant. -/
theorem LoInv.takeB (hk : k ≤ nb) (h : LoInv xs tmp naO pb nbO na nb a) :
    LoInv xs tmp naO pb nbO na (nb - k)
      (moveWithin a (loJ pb nbO nb - na) (loJ pb nbO nb) k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [moveWithin_eq_copyRange]
  refine ⟨h1, by omega, h3, by rw [size_copyRange]; exact h4, List.Perm.trans ?_ h5⟩
  refine perm_swap (loJ pb nbO nb - na) na k (by simp [size_copyRange])
    (by rw [size_copyRange]; unfold loJ; omega) (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_) <;>
  · simp only [get_copyRange, size_copyRange]
    unfold loJ at *
    ite_cases

/-- Moving the next item of the second run into the gap keeps `merge_lo`'s invariant. -/
theorem LoInv.takeB1 (hnb : 1 ≤ nb) (h : LoInv xs tmp naO pb nbO na nb a) :
    LoInv xs tmp naO pb nbO na (nb - 1)
      (a.setIfInBounds (loJ pb nbO nb - na) (get a (loJ pb nbO nb))) := by
  rw [← copyRange_one, ← moveWithin_eq_copyRange]
  exact h.takeB hnb

/-- Under `merge_lo`'s invariant, its fixup `loFix` leaves a permutation of `xs`. -/
theorem LoInv.fix (h : LoInv xs tmp naO pb nbO na nb a) :
    PermOf xs (copyRange a tmp (loJ pb nbO nb - na) (naO - na) na) :=
  h.2.2.2.2

/-- When `tmp` has no items left, the array is a permutation of `xs`. -/
theorem LoInv.perm (h : LoInv xs tmp naO pb nbO 0 nb a) : PermOf xs a := by
  have hfix := h.fix
  rwa [copyRange_zero] at hfix

/-- `merge_hi`'s invariant, with `na` items of the first run left at the start of
`a[pa, pa + naO)` and `nb` items of the second run left at the start of `tmp`: the counts and
the runs are in range, and copying the rest of the second run into the gap after the rest of the
first run gives a permutation of `xs`. -/
def HiInv (xs tmp : Array α) (pa naO nbO na nb : Nat) (a : Array α) : Prop :=
  na ≤ naO ∧ nb ≤ nbO ∧ pa + naO + nbO ≤ a.size ∧ PermOf xs (copyRange a tmp (pa + na) 0 nb)

variable {pa : Nat}

/-- At the start of `merge_hi`, with the second run `a[pb, pb + nb)` copied to `tmp`, the gap is
the second run itself, so its invariant holds. -/
theorem HiInv.start (h : PermOf xs a) (hpb : pb = pa + na) (hle : pb + nb ≤ a.size) :
    HiInv xs (a.extract pb (pb + nb)) pa na nb na nb a := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, by omega, ?_⟩
  have e : copyRange a (a.extract pb (pb + nb)) (pa + na) 0 nb = a := by
    refine ext_get (size_copyRange ..) fun i _ => ?_
    rw [get_copyRange]
    split
    · rw [get_extract _ (by omega)]
      congr 1; omega
    · rfl
  rw [e]
  exact h

/-- Moving the last `k` items of the first run to the end of the gap keeps `merge_hi`'s
invariant. -/
theorem HiInv.takeA (hk : k ≤ na) (h : HiInv xs tmp pa naO nbO na nb a) :
    HiInv xs tmp pa naO nbO (na - k) nb (moveWithin a (pa + (na - k) + nb) (pa + (na - k)) k) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [moveWithin_eq_copyRange]
  refine ⟨by omega, h2, by rw [size_copyRange]; exact h3, List.Perm.trans ?_ h4⟩
  refine perm_swap (pa + (na - k)) k nb (by simp [size_copyRange])
    (by rw [size_copyRange]; omega) (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_) <;>
  · simp only [get_copyRange, size_copyRange]
    ite_cases

/-- Moving the last item of the first run to the end of the gap keeps `merge_hi`'s invariant. -/
theorem HiInv.takeA1 (hna : 1 ≤ na) (h : HiInv xs tmp pa naO nbO na nb a) :
    HiInv xs tmp pa naO nbO (na - 1) nb
      (a.setIfInBounds (pa + na + nb - 1) (get a (pa + na - 1))) := by
  have h' := h.takeA hna
  rwa [moveWithin_eq_copyRange, copyRange_one, show pa + (na - 1) + nb = pa + na + nb - 1 by omega,
    show pa + (na - 1) = pa + na - 1 by omega] at h'

/-- Placing the last `k` items of `tmp` at the end of the gap keeps `merge_hi`'s invariant. -/
theorem HiInv.takeB (hk : k ≤ nb) (h : HiInv xs tmp pa naO nbO na nb a) :
    HiInv xs tmp pa naO nbO na (nb - k) (copyRange a tmp (pa + na + (nb - k)) (nb - k) k) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by omega, by rw [size_copyRange]; exact h3, ?_⟩
  have e : copyRange (copyRange a tmp (pa + na + (nb - k)) (nb - k) k) tmp (pa + na) 0 (nb - k) =
      copyRange a tmp (pa + na) 0 nb := by
    refine ext_get (by simp [size_copyRange]) fun i _ => ?_
    simp only [get_copyRange, size_copyRange]
    ite_cases
  rw [e]
  exact h4

/-- Placing the last item of `tmp` at the end of the gap keeps `merge_hi`'s invariant. -/
theorem HiInv.takeB1 (hnb : 1 ≤ nb) (h : HiInv xs tmp pa naO nbO na nb a) :
    HiInv xs tmp pa naO nbO na (nb - 1)
      (a.setIfInBounds (pa + na + nb - 1) (get tmp (nb - 1))) := by
  have h' := h.takeB hnb
  rwa [copyRange_one, show pa + na + (nb - 1) = pa + na + nb - 1 by omega] at h'

/-- Under `merge_hi`'s invariant, its fixup `hiFix` leaves a permutation of `xs`. -/
theorem HiInv.fix (h : HiInv xs tmp pa naO nbO na nb a) :
    PermOf xs (copyRange a tmp (pa + na) 0 nb) :=
  h.2.2.2

/-- When `tmp` has no items left, the array is a permutation of `xs`. -/
theorem HiInv.perm (h : HiInv xs tmp pa naO nbO na 0 a) : PermOf xs a := by
  have hfix := h.fix
  rwa [copyRange_zero] at hfix

end Merge

/-! ## Steps that only read the state -/

section ReadOnly
variable {m : Type → Type u} [Monad m] [LawfulMonad m] {ε α β γ : Type}

/-- `x` leaves the state as it is, and its result satisfies `R`. -/
def RO (x : SortM m ε α β) (R : β → Prop) : Prop :=
  ∀ s, WP x (fun b s' => s' = s ∧ R b) (fun _ s' => s' = s) s

/-- `pure b` only reads the state. -/
theorem RO.pure {b : β} {R : β → Prop} (h : R b) : RO (pure b : SortM m ε α β) R :=
  fun _ => wp_pure ⟨rfl, h⟩

/-- Two steps that only read the state make one. -/
theorem RO.bind {x : SortM m ε α β} {f : β → SortM m ε α γ} {R : β → Prop} {R' : γ → Prop}
    (hx : RO x R) (hf : ∀ b, R b → RO (f b) R') : RO (x >>= f) R' := fun s =>
  wp_bind ((hx s).conseq (fun b s' ⟨hs, hb⟩ => by subst hs; exact hf b hb s') fun _ _ hs => hs)

/-- `RO` is monotone in the predicate on the result. -/
theorem RO.imp {x : SortM m ε α β} {R R' : β → Prop} (hx : RO x R) (h : ∀ b, R b → R' b) :
    RO x R' :=
  fun s => (hx s).conseq (fun b _ ⟨hs, hb⟩ => ⟨hs, h b hb⟩) fun _ _ hs => hs

/-- A step `x` that only reads the state (`RO x R`: it keeps the state, and its result satisfies
`R`) followed by `f`: if `f b` satisfies `Q` and `E` from `s` for every `b` with `R b`, and `E`
holds at `s` for every error (which `x` may throw before any change), then so does `x >>= f`. -/
theorem RO.wp {x : SortM m ε α β} {f : β → SortM m ε α γ} {R : β → Prop}
    {Q : γ → State α → Prop} {E : ε → State α → Prop} {s : State α} (hx : RO x R)
    (hf : ∀ b, R b → WP (f b) Q E s) (he : ∀ e, E e s) : WP (x >>= f) Q E s :=
  wp_bind ((hx s).conseq (fun b _ ⟨hs, hb⟩ => by subst hs; exact hf b hb) fun e _ hs => by
    subst hs; exact he e)

/-- A comparison only reads the state. -/
theorem ro_isLt (lt : α → α → m (Except ε Bool)) (x y : α) : RO (isLt lt x y) fun _ => True :=
  fun _ => by
    unfold isLt
    refine wp_bind (wp_liftM fun r => ?_)
    cases r with
    | ok b => exact wp_pure ⟨rfl, trivial⟩
    | error e => exact wp_throw rfl

/-- `expand` only reads the state, if its test does. -/
theorem ro_expand {stop : Nat → SortM m ε α Bool} (hs : ∀ o, RO (stop o) fun _ => True)
    (maxofs lastofs ofs : Nat) : RO (expand stop maxofs lastofs ofs) fun _ => True := by
  induction h : maxofs - ofs using Nat.strongRecOn generalizing lastofs ofs with
  | _ d ih =>
    rw [expand]
    split
    · refine RO.bind (hs ofs) fun b _ => ?_
      split
      · exact RO.pure trivial
      · exact ih _ (by omega) _ _ rfl
    · exact RO.pure trivial

/-- `bisect` only reads the state, if its test does. -/
theorem ro_bisect {right : Nat → SortM m ε α Bool} (hr : ∀ k, RO (right k) fun _ => True)
    (lo hi : Nat) : RO (bisect right lo hi) fun _ => True := by
  induction h : hi - lo using Nat.strongRecOn generalizing lo hi with
  | _ d ih =>
    rw [bisect]
    split
    · refine RO.bind (hr _) fun b _ => ?_
      split
      · exact ih _ (by omega) _ _ rfl
      · exact ih _ (by omega) _ _ rfl
    · exact RO.pure trivial

/-- `gallopLeft`, whose reads `at_` only read the state, only reads the state, and returns at
most `n`. -/
theorem ro_gallopLeft (lt : α → α → m (Except ε Bool)) (key : α) (at_ : Nat → SortM m ε α α)
    (hat : ∀ i, RO (at_ i) fun _ => True) (n hint : Nat) :
    RO (gallopLeft lt key at_ n hint) fun k => k ≤ n := by
  have hlt : ∀ i, RO (do isLt lt (← at_ i) key) fun _ => True :=
    fun i => RO.bind (hat i) fun _ _ => ro_isLt _ _ _
  have hnot : ∀ i, RO (do return !(← isLt lt (← at_ i) key)) fun _ => True :=
    fun i => RO.bind (hat i) fun _ _ => RO.bind (ro_isLt _ _ _) fun _ _ => RO.pure trivial
  unfold gallopLeft
  refine RO.bind (hat _) fun _ _ => RO.bind (ro_isLt _ _ _) fun _ _ => ?_
  split <;>
  exact RO.bind (ro_expand (fun _ => by first | exact hnot _ | exact hlt _) _ _ _) fun _ _ =>
    RO.bind (RO.pure (R := fun _ => True) trivial) fun _ _ =>
      RO.bind (ro_bisect hnot _ _) fun _ _ => RO.pure (Nat.min_le_right _ _)

/-- `gallopRight`, whose reads `at_` only read the state, only reads the state, and returns at
most `n`. -/
theorem ro_gallopRight (lt : α → α → m (Except ε Bool)) (key : α) (at_ : Nat → SortM m ε α α)
    (hat : ∀ i, RO (at_ i) fun _ => True) (n hint : Nat) :
    RO (gallopRight lt key at_ n hint) fun k => k ≤ n := by
  have hlt : ∀ i, RO (do isLt lt key (← at_ i)) fun _ => True :=
    fun i => RO.bind (hat i) fun _ _ => ro_isLt _ _ _
  have hnot : ∀ i, RO (do return !(← isLt lt key (← at_ i))) fun _ => True :=
    fun i => RO.bind (hat i) fun _ _ => RO.bind (ro_isLt _ _ _) fun _ _ => RO.pure trivial
  unfold gallopRight
  refine RO.bind (hat _) fun _ _ => RO.bind (ro_isLt _ _ _) fun _ _ => ?_
  split <;>
  exact RO.bind (ro_expand (fun _ => by first | exact hnot _ | exact hlt _) _ _ _) fun _ _ =>
    RO.bind (RO.pure (R := fun _ => True) trivial) fun _ _ =>
      RO.bind (ro_bisect hlt _ _) fun _ _ => RO.pure (Nat.min_le_right _ _)

/-- `readState f` only reads the state. -/
theorem ro_readState {f : State α → β} : RO (readState f : SortM m ε α β) fun _ => True :=
  fun _ => wp_readState ⟨rfl, trivial⟩

variable [Inhabited α]

/-- Reading an item only reads the state. -/
theorem ro_itemAt (i : Nat) : RO (itemAt i : SortM m ε α α) fun _ => True := ro_readState

/-- `insertPos` only reads the state, and returns a position in `[l, r]`. -/
theorem ro_insertPos (lt : α → α → m (Except ε Bool)) (pivot : α) (l r : Nat) :
    RO (insertPos lt pivot l r) fun p => l ≤ r → l ≤ p ∧ p ≤ r := by
  induction h : r - l using Nat.strongRecOn generalizing l r with
  | _ d ih =>
    rw [insertPos]
    split
    · refine RO.bind (ro_itemAt _) fun _ _ => RO.bind (ro_isLt _ _ _) fun b _ => ?_
      split
      · exact (ih _ (by omega) l _ rfl).imp fun p hp _ => by have hp' := hp (by omega); omega
      · exact (ih _ (by omega) _ r rfl).imp fun p hp _ => by have hp' := hp (by omega); omega
    · exact RO.pure fun _ => by omega

/-- `runEnd` only reads the state, and returns an index in `[i, hi]`. -/
theorem ro_runEnd (lt : α → α → m (Except ε Bool)) (hi : Nat) (desc : Bool)
    (i : Nat) : RO (runEnd lt hi desc i) fun j => i ≤ hi → i ≤ j ∧ j ≤ hi := by
  induction h : hi - i using Nat.strongRecOn generalizing i with
  | _ d ih =>
    rw [runEnd]
    split
    · refine RO.bind (ro_itemAt _) fun _ _ => RO.bind (ro_itemAt _) fun _ _ =>
        RO.bind (ro_isLt _ _ _) fun b _ => ?_
      split
      · exact (ih _ (by omega) (i + 1) rfl).imp fun j hj _ => by
          have hj' := hj (by omega)
          omega
      · exact RO.pure fun _ => by omega
    · exact RO.pure fun _ => by omega

/-- `countRun` only reads the state, and the run it finds has between `1` and `hi - lo` items. -/
theorem ro_countRun (lt : α → α → m (Except ε Bool)) (lo hi : Nat) :
    RO (countRun lt lo hi) fun r => lo < hi → 1 ≤ r.1 ∧ r.1 ≤ hi - lo := by
  unfold countRun
  split
  · exact RO.pure fun _ => by dsimp only; omega
  · exact RO.bind (ro_itemAt _) fun _ _ => RO.bind (ro_itemAt _) fun _ _ =>
      RO.bind (ro_isLt _ _ _) fun _ _ => RO.bind (ro_runEnd _ _ _ _) fun e he =>
      RO.pure fun _ => by
        have he' := he (by omega)
        dsimp only
        omega

end ReadOnly

/-! ## The sort's own state updates -/

section Updates
variable {m : Type → Type u} [Monad m] [LawfulMonad m] {ε α β γ : Type}
  {Q : β → State α → Prop} {E : ε → State α → Prop} {s : State α}

/-- `storeMinGallop` changes `minGallop` only. -/
theorem wp_storeMinGallop {mg : Nat} {Q : Unit → State α → Prop}
    (h : Q () { s with minGallop := mg }) : WP (storeMinGallop mg : SortM m ε α Unit) Q E s :=
  wp_modifyThe h

/-- `extractNow lo hi` returns `arr[lo, hi)` and leaves the state alone. -/
theorem wp_extractNow {lo hi : Nat} {Q : Array α → State α → Prop}
    (h : Q (s.arr.extract lo hi) s) : WP (extractNow lo hi : SortM m ε α (Array α)) Q E s :=
  wp_readState h

/-- `withFix fix x` meets `Q` if `x` does, or if `x` throws where `fix` then meets `E`. -/
theorem wp_withFix {fix : SortM m ε α Unit} {x : SortM m ε α β}
    (h : WP x Q (fun e s' => WP fix (fun _ s'' => E e s'') E s') s) :
    WP (withFix fix x) Q E s :=
  wp_tryCatch (h.conseq (fun _ _ hq => hq) fun _ _ hf =>
    wp_bind (hf.conseq (fun _ _ he => wp_throw he) fun _ _ he => he))

/-- A read-only step `x` under `withFix fix`, followed by `f`: if `f b` satisfies `Q` and `E` from
`s` for every `b` with `R b`, and the fixup `fix`, run from `s` after an error `e`, ends where
`E e` holds, then `withFix fix x >>= f` satisfies `Q` and `E` from `s`. -/
theorem RO.withFix_wp {fix : SortM m ε α Unit} {x : SortM m ε α β} {f : β → SortM m ε α γ}
    {R : β → Prop} {Q : γ → State α → Prop} (hx : RO x R) (hf : ∀ b, R b → WP (f b) Q E s)
    (hfix : ∀ e, WP fix (fun _ s' => E e s') E s) : WP (withFix fix x >>= f) Q E s :=
  wp_bind (wp_withFix ((hx s).conseq (fun b _ ⟨hs, hb⟩ => by subst hs; exact hf b hb)
    fun e _ hs => by subst hs; exact hfix e))

/-- A join point after a conditional step: if `R` holds after `x` when `c` holds, and before it
otherwise, the join point `J` needs only `R`. -/
theorem wp_ite_jp {c : Prop} [Decidable c] {x : SortM m ε α Unit} {J : Unit → SortM m ε α β}
    (R : State α → Prop) (hx : c → WP x (fun _ s' => R s') E s) (hn : ¬c → R s)
    (hJ : ∀ s', R s' → WP (J ()) Q E s') : WP (if c then x >>= J else J ()) Q E s := by
  split
  · exact wp_bind ((hx ‹_›).conseq (fun _ s' h => hJ s' h) fun _ _ h => h)
  · exact hJ s (hn ‹_›)

/-- `setAt i x` sets the item at `i`. -/
theorem wp_setAt {i : Nat} {x : α} {Q : Unit → State α → Prop}
    (h : Q () { s with arr := s.arr.setIfInBounds i x }) :
    WP (setAt i x : SortM m ε α Unit) Q E s :=
  wp_modifyThe h

omit [LawfulMonad m] in
/-- An `if` meets `Q` if each branch does when it runs. -/
theorem wp_ite {c : Prop} [Decidable c] {t e : SortM m ε α β} (ht : c → WP t Q E s)
    (he : ¬c → WP e Q E s) : WP (if c then t else e) Q E s := by
  split
  · exact ht ‹_›
  · exact he ‹_›

omit [LawfulMonad m] in
/-- A dependent `if` meets `Q` if each branch does when it runs. -/
theorem wp_dite {c : Prop} [Decidable c] {t : c → SortM m ε α β} {e : ¬c → SortM m ε α β}
    (ht : ∀ h, WP (t h) Q E s) (he : ∀ h, WP (e h) Q E s) : WP (dite c t e) Q E s := by
  split
  · exact ht _
  · exact he _

variable [Inhabited α]

/-- `itemAt i` returns the item at `i` and leaves the state alone. -/
theorem wp_itemAt {i : Nat} {Q : α → State α → Prop} (h : Q (get s.arr i) s) :
    WP (itemAt i : SortM m ε α α) Q E s :=
  wp_readState h

/-- `copyItem dst src` sets the item at `dst` to the item at `src`. -/
theorem wp_copyItem {dst src : Nat} {Q : Unit → State α → Prop}
    (h : Q () { s with arr := s.arr.setIfInBounds dst (get s.arr src) }) :
    WP (copyItem dst src : SortM m ε α Unit) Q E s :=
  wp_modifyThe h

/-- `moveFrom` copies items from another array into the array. -/
theorem wp_moveFrom {src : Array α} {dst start n : Nat} {Q : Unit → State α → Prop}
    (h : Q () { s with arr := copyRange s.arr src dst start n }) :
    WP (moveFrom src dst start n : SortM m ε α Unit) Q E s :=
  wp_modifyThe h

/-- `move` moves items within the array. -/
theorem wp_move {dst start n : Nat} {Q : Unit → State α → Prop}
    (h : Q () { s with arr := moveWithin s.arr dst start n }) :
    WP (move dst start n : SortM m ε α Unit) Q E s :=
  wp_modifyThe h

end Updates

/-! ## `merge_lo` -/

section MergeLoProof
variable {m : Type → Type u} [Monad m] [LawfulMonad m] {ε α : Type} [Inhabited α]

/-- How `merge_lo`'s loops end: `done`, or `copy` with one item of the first run left; with
`merge_lo`'s invariant, and the run stack `p0`. -/
def LoExit (xs tmp : Array α) (naO pb nbO : Nat) (p0 : Array Run) : Exit → State α → Prop
  | .done na nb, s => LoInv xs tmp naO pb nbO na nb s.arr ∧ s.pending = p0
  | .copy na nb, s => na = 1 ∧ LoInv xs tmp naO pb nbO na nb s.arr ∧ s.pending = p0

/-- `merge_lo`'s loops keep its invariant, and when a comparison fails they leave a permutation
of `xs`. -/
theorem wp_lo (lt : α → α → m (Except ε Bool)) (xs tmp : Array α) (naO pb nbO : Nat)
    (p0 : Array Run) (n : Nat) :
    (∀ mg na nb (hb : 0 < nb) (s : State α), na + nb ≤ n → 2 ≤ na →
      LoInv xs tmp naO pb nbO na nb s.arr → s.pending = p0 →
      WP (loGallop lt tmp naO pb nbO mg na nb hb) (LoExit xs tmp naO pb nbO p0)
        (fun _ s' => PermOf xs s'.arr) s) ∧
    (∀ mg acount bcount na nb (hb : 0 < nb) (s : State α), na + nb ≤ n → 2 ≤ na →
      LoInv xs tmp naO pb nbO na nb s.arr → s.pending = p0 →
      WP (loSimple lt tmp naO pb nbO mg acount bcount na nb hb) (LoExit xs tmp naO pb nbO p0)
        (fun _ s' => PermOf xs s'.arr) s) := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ hn h2 => absurd hn (by omega),
      fun _ _ _ _ _ _ _ hn h2 => absurd hn (by omega)⟩
  | succ n ih =>
    obtain ⟨ihG, ihS⟩ := ih
    constructor
    · intro mg na nb hb s hn h2 hI hp
      rw [loGallop]
      refine wp_bind (wp_storeMinGallop ?_)
      refine wp_bind (wp_itemAt ?_)
      refine RO.withFix_wp (ro_gallopRight _ _ _ (fun _ => RO.pure trivial) _ _) (fun k hk => ?_)
        (fun _ => wp_moveFrom hI.fix)
      refine wp_ite_jp (fun s' => LoInv xs tmp naO pb nbO (na - k) nb s'.arr ∧ s'.pending = p0)
        (fun _ => wp_moveFrom ⟨hI.takeA hk, hp⟩)
        (fun h => by obtain rfl : k = 0 := by omega
                     exact ⟨hI, hp⟩) (fun s1 ⟨hI1, hp1⟩ => ?_)
      refine wp_ite (fun h => ?_) (fun h0 => ?_)
      · simp only [beq_iff_eq] at h
        exact wp_pure ⟨h, hI1, hp1⟩
      refine wp_ite (fun _ => wp_pure ⟨hI1, hp1⟩) (fun h1 => ?_)
      simp only [beq_iff_eq] at h0 h1
      refine wp_bind (wp_copyItem ?_)
      have hI2 := hI1.takeB1 hb
      refine wp_ite (fun _ => wp_pure ⟨hI2, hp1⟩) (fun h3 => ?_)
      refine RO.withFix_wp (ro_gallopLeft _ _ _ (fun _ => ro_itemAt _) _ _) (fun k1 hk1 => ?_)
        (fun _ => wp_moveFrom hI2.fix)
      refine wp_ite_jp
        (fun s' => LoInv xs tmp naO pb nbO (na - k) (nb - 1 - k1) s'.arr ∧ s'.pending = p0)
        (fun _ => wp_move ⟨hI2.takeB hk1, hp1⟩)
        (fun h => by obtain rfl : k1 = 0 := by omega
                     exact ⟨hI2, hp1⟩) (fun s3 ⟨hI3, hp3⟩ => ?_)
      refine wp_ite (fun _ => wp_pure ⟨hI3, hp3⟩) (fun h4 => ?_)
      simp only [beq_iff_eq] at h4
      refine wp_bind (wp_setAt ?_)
      have hI4 := hI3.takeA1 (by omega)
      refine wp_ite (fun h5 => ?_) (fun h5 => ?_)
      · simp only [beq_iff_eq] at h5
        exact wp_pure ⟨h5, hI4, hp3⟩
      simp only [beq_iff_eq] at h5
      refine wp_dite (fun h6 => ?_) (fun _ => wp_pure ⟨hI4, hp3⟩)
      refine wp_ite (fun _ => ihG _ _ _ _ _ (by omega) (by omega) hI4 hp3) (fun _ => ?_)
      exact wp_bind (wp_storeMinGallop (ihS _ _ _ _ _ _ _ (by omega) (by omega) hI4 hp3))
    · intro mg acount bcount na nb hb s hn h2 hI hp
      rw [loSimple]
      refine wp_bind (wp_itemAt ?_)
      refine RO.withFix_wp (ro_isLt _ _ _) (fun k _ => ?_) (fun _ => wp_moveFrom hI.fix)
      refine wp_ite (fun _ => ?_) (fun _ => ?_)
      · refine wp_bind (wp_setAt ?_)
        have hI1 := hI.takeB1 hb
        refine wp_dite (fun _ => ?_) (fun _ => wp_pure ⟨hI1, hp⟩)
        exact wp_ite (fun _ => ihG _ _ _ _ _ (by omega) h2 hI1 hp)
          (fun _ => ihS _ _ _ _ _ _ _ (by omega) h2 hI1 hp)
      · refine wp_bind (wp_setAt ?_)
        have hI1 := hI.takeA1 (by omega)
        refine wp_ite (fun h => ?_) (fun h => ?_)
        · simp only [beq_iff_eq] at h
          exact wp_pure ⟨h, hI1, hp⟩
        simp only [beq_iff_eq] at h
        refine wp_ite (fun _ => ?_) (fun _ => wp_pure ⟨hI1, hp⟩)
        exact wp_ite (fun _ => ihG _ _ _ _ _ (by omega) (by omega) hI1 hp)
          (fun _ => ihS _ _ _ _ _ _ _ (by omega) (by omega) hI1 hp)

/-- `merge_lo` of the adjacent runs `a[pa, pb)` and `a[pb, pb + nb)`, both non-empty and inside the
array, started from an array that is a permutation of `xs`, leaves a permutation of `xs` and the
run stack as it was, also when a comparison fails. -/
theorem wp_mergeLo (lt : α → α → m (Except ε Bool)) (xs : Array α) (pa na pb nb : Nat)
    (s : State α) (hP : PermOf xs s.arr) (hpb : pb = pa + na) (hle : pb + nb ≤ xs.size)
    (hna : 1 ≤ na) (hnb : 1 ≤ nb) :
    WP (mergeLo lt pa na pb nb) (fun _ s' => PermOf xs s'.arr ∧ s'.pending = s.pending)
      (fun _ s' => PermOf xs s'.arr) s := by
  have hsz := hP.size
  unfold mergeLo
  refine wp_bind (wp_extractNow ?_)
  generalize htmp : s.arr.extract pa (pa + na) = tmp
  extract_lets jp
  have hI : LoInv xs tmp na pb nb na nb s.arr := htmp ▸ LoInv.start hP hpb (by omega)
  have hJ : ∀ ex s', LoExit xs tmp na pb nb s.pending ex s' →
      WP (jp ex) (fun _ s' => PermOf xs s'.arr ∧ s'.pending = s.pending)
        (fun _ s' => PermOf xs s'.arr) s' := by
    intro ex s' h
    cases ex with
    | done na' nb' => exact wp_moveFrom ⟨h.1.fix, h.2⟩
    | copy na' nb' =>
      obtain ⟨rfl, hI', hp'⟩ := h
      have h1 := hI'.takeB (Nat.le_refl nb')
      refine wp_bind (wp_move (wp_setAt ⟨?_, hp'⟩))
      have h2 := h1.takeA1 (Nat.le_refl 1)
      have e : loJ pb nb (nb' - nb') - 1 = loJ pb nb nb' - 1 + nb' := by
        obtain ⟨_, _, _, _, _⟩ := hI'
        unfold loJ
        omega
      rw [e] at h2
      exact h2.perm
  refine wp_bind (wp_copyItem ?_)
  have hI1 := hI.takeB1 hnb
  rw [show loJ pb nb nb - na = pa by unfold loJ; omega, show loJ pb nb nb = pb by unfold loJ; omega]
    at hI1
  refine wp_dite (fun h => ?_) (fun _ => wp_bind (wp_pure (hJ (.done _ _) _ ⟨hI1, rfl⟩)))
  refine wp_ite (fun h1 => ?_) (fun h1 => ?_)
  · simp only [beq_iff_eq] at h1
    exact wp_bind (wp_pure (hJ (.copy _ _) _ ⟨h1, hI1, rfl⟩))
  · simp only [beq_iff_eq] at h1
    refine wp_bind (wp_readState (wp_bind ?_))
    refine WP.conseq ((wp_lo lt xs tmp na pb nb s.pending _).2 _ _ _ _ _ _ _ (Nat.le_refl _) ?_ hI1
      rfl) (fun ex s' h => hJ ex s' h) fun _ _ h => h
    omega

end MergeLoProof

/-! ## `merge_hi` -/

section MergeHiProof
variable {m : Type → Type u} [Monad m] [LawfulMonad m] {ε α : Type} [Inhabited α]

/-- How `merge_hi`'s loops end: `done`, or `copy` with one item of the second run left; with
`merge_hi`'s invariant, and the run stack `p0`. -/
def HiExit (xs tmp : Array α) (pa naO nbO : Nat) (p0 : Array Run) : Exit → State α → Prop
  | .done na nb, s => HiInv xs tmp pa naO nbO na nb s.arr ∧ s.pending = p0
  | .copy na nb, s => nb = 1 ∧ HiInv xs tmp pa naO nbO na nb s.arr ∧ s.pending = p0

/-- `merge_hi`'s loops keep its invariant, and when a comparison fails they leave a permutation
of `xs`. -/
theorem wp_hi (lt : α → α → m (Except ε Bool)) (xs tmp : Array α) (pa naO nbO : Nat)
    (p0 : Array Run) (n : Nat) :
    (∀ mg na nb (ha : 0 < na) (s : State α), na + nb ≤ n → 2 ≤ nb →
      HiInv xs tmp pa naO nbO na nb s.arr → s.pending = p0 →
      WP (hiGallop lt tmp pa mg na nb ha) (HiExit xs tmp pa naO nbO p0)
        (fun _ s' => PermOf xs s'.arr) s) ∧
    (∀ mg acount bcount na nb (ha : 0 < na) (s : State α), na + nb ≤ n → 2 ≤ nb →
      HiInv xs tmp pa naO nbO na nb s.arr → s.pending = p0 →
      WP (hiSimple lt tmp pa mg acount bcount na nb ha) (HiExit xs tmp pa naO nbO p0)
        (fun _ s' => PermOf xs s'.arr) s) := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ hn h2 => absurd hn (by omega),
      fun _ _ _ _ _ _ _ hn h2 => absurd hn (by omega)⟩
  | succ n ih =>
    obtain ⟨ihG, ihS⟩ := ih
    constructor
    · intro mg na nb ha s hn h2 hI hp
      rw [hiGallop]
      refine wp_bind (wp_storeMinGallop ?_)
      refine RO.withFix_wp (ro_gallopRight _ _ _ (fun _ => ro_itemAt _) _ _) (fun k hk => ?_)
        (fun _ => wp_moveFrom hI.fix)
      refine wp_ite_jp
        (fun s' => HiInv xs tmp pa naO nbO (na - (na - k)) nb s'.arr ∧ s'.pending = p0)
        (fun _ => wp_move ⟨hI.takeA (Nat.sub_le _ _), hp⟩)
        (fun h => by
          rw [show na - (na - k) = na by omega]
          exact ⟨hI, hp⟩) (fun s1 ⟨hI1, hp1⟩ => ?_)
      refine wp_ite (fun _ => wp_pure ⟨hI1, hp1⟩) (fun h0 => ?_)
      simp only [beq_iff_eq] at h0
      refine wp_bind (wp_setAt ?_)
      have hI2 := hI1.takeB1 (by omega)
      refine wp_ite (fun h => ?_) (fun h3 => ?_)
      · simp only [beq_iff_eq] at h
        exact wp_pure ⟨h, hI2, hp1⟩
      simp only [beq_iff_eq] at h3
      refine wp_bind (wp_itemAt ?_)
      refine RO.withFix_wp (ro_gallopLeft _ _ _ (fun _ => RO.pure trivial) _ _) (fun k2 hk2 => ?_)
        (fun _ => wp_moveFrom hI2.fix)
      refine wp_ite_jp (fun s' => HiInv xs tmp pa naO nbO (na - (na - k)) (nb - 1 - (nb - 1 - k2))
          s'.arr ∧ s'.pending = p0)
        (fun _ => wp_moveFrom ⟨hI2.takeB (Nat.sub_le _ _), hp1⟩)
        (fun h => by
          rw [show nb - 1 - (nb - 1 - k2) = nb - 1 by omega]
          exact ⟨hI2, hp1⟩) (fun s3 ⟨hI3, hp3⟩ => ?_)
      refine wp_ite (fun h => ?_) (fun h4 => ?_)
      · simp only [beq_iff_eq] at h
        exact wp_pure ⟨h, hI3, hp3⟩
      refine wp_ite (fun _ => wp_pure ⟨hI3, hp3⟩) (fun h5 => ?_)
      simp only [beq_iff_eq] at h4 h5
      refine wp_bind (wp_copyItem ?_)
      have hI4 := hI3.takeA1 (by omega)
      refine wp_dite (fun h6 => ?_) (fun _ => wp_pure ⟨hI4, hp3⟩)
      refine wp_ite (fun _ => ihG _ _ _ _ _ (by omega) (by omega) hI4 hp3) (fun _ => ?_)
      exact wp_bind (wp_storeMinGallop (ihS _ _ _ _ _ _ _ (by omega) (by omega) hI4 hp3))
    · intro mg acount bcount na nb ha s hn h2 hI hp
      rw [hiSimple]
      refine wp_bind (wp_itemAt ?_)
      refine RO.withFix_wp (ro_isLt _ _ _) (fun k _ => ?_) (fun _ => wp_moveFrom hI.fix)
      refine wp_ite (fun _ => ?_) (fun _ => ?_)
      · refine wp_bind (wp_setAt ?_)
        have hI1 := hI.takeA1 ha
        refine wp_dite (fun _ => ?_) (fun _ => wp_pure ⟨hI1, hp⟩)
        exact wp_ite (fun _ => ihG _ _ _ _ _ (by omega) h2 hI1 hp)
          (fun _ => ihS _ _ _ _ _ _ _ (by omega) h2 hI1 hp)
      · refine wp_bind (wp_setAt ?_)
        have hI1 := hI.takeB1 (by omega)
        refine wp_ite (fun h => ?_) (fun h => ?_)
        · simp only [beq_iff_eq] at h
          exact wp_pure ⟨h, hI1, hp⟩
        simp only [beq_iff_eq] at h
        refine wp_ite (fun _ => ?_) (fun _ => wp_pure ⟨hI1, hp⟩)
        exact wp_ite (fun _ => ihG _ _ _ _ _ (by omega) (by omega) hI1 hp)
          (fun _ => ihS _ _ _ _ _ _ _ (by omega) (by omega) hI1 hp)

/-- `merge_hi` of the adjacent runs `a[pa, pb)` and `a[pb, pb + nb)`, both non-empty and inside the
array, started from an array that is a permutation of `xs`, leaves a permutation of `xs` and the
run stack as it was, also when a comparison fails. -/
theorem wp_mergeHi (lt : α → α → m (Except ε Bool)) (xs : Array α) (pa na pb nb : Nat)
    (s : State α) (hP : PermOf xs s.arr) (hpb : pb = pa + na) (hle : pb + nb ≤ xs.size)
    (hna : 1 ≤ na) (hnb : 1 ≤ nb) :
    WP (mergeHi lt pa na pb nb) (fun _ s' => PermOf xs s'.arr ∧ s'.pending = s.pending)
      (fun _ s' => PermOf xs s'.arr) s := by
  have hsz := hP.size
  unfold mergeHi
  refine wp_bind (wp_extractNow ?_)
  generalize htmp : s.arr.extract pb (pb + nb) = tmp
  extract_lets jp
  have hI : HiInv xs tmp pa na nb na nb s.arr := htmp ▸ HiInv.start hP hpb (by omega)
  have hJ : ∀ ex s', HiExit xs tmp pa na nb s.pending ex s' →
      WP (jp ex) (fun _ s' => PermOf xs s'.arr ∧ s'.pending = s.pending)
        (fun _ s' => PermOf xs s'.arr) s' := by
    intro ex s' h
    cases ex with
    | done na' nb' => exact wp_moveFrom ⟨h.1.fix, h.2⟩
    | copy na' nb' =>
      obtain ⟨rfl, hI', hp'⟩ := h
      have h1 := hI'.takeA (Nat.le_refl na')
      simp only [Nat.sub_self, Nat.add_zero] at h1
      refine wp_bind (wp_move (wp_setAt ⟨?_, hp'⟩))
      have h2 := h1.takeB1 (Nat.le_refl 1)
      simp only [Nat.add_zero, Nat.add_sub_cancel, Nat.sub_self] at h2
      exact h2.perm
  refine wp_bind (wp_copyItem ?_)
  have hI1 := hI.takeA1 hna
  refine wp_dite (fun h => ?_) (fun _ => wp_bind (wp_pure (hJ (.done _ _) _ ⟨hI1, rfl⟩)))
  refine wp_ite (fun h1 => ?_) (fun h1 => ?_)
  · simp only [beq_iff_eq] at h1
    exact wp_bind (wp_pure (hJ (.copy _ _) _ ⟨h1, hI1, rfl⟩))
  · simp only [beq_iff_eq] at h1
    refine wp_bind (wp_readState (wp_bind ?_))
    refine WP.conseq ((wp_hi lt xs tmp pa na nb s.pending _).2 _ _ _ _ _ _ _ (Nat.le_refl _) ?_ hI1
      rfl) (fun ex s' h => hJ ex s' h) fun _ _ h => h
    omega

end MergeHiProof

/-! ## The run stack -/

section Stack

/-- `pop` drops the last item. -/
theorem get_pop {α : Type} [Inhabited α] (p : Array α) (k : Nat) :
    get p.pop k = if k < p.size - 1 then get p k else default := by
  by_cases hk : k < p.size - 1
  · rw [get_of_lt (by simpa using hk), get_of_lt (by omega), Array.getElem_pop, ite_eq_left hk]
  · rw [get_of_le (by simp; omega), ite_eq_right hk]

/-- `push x` adds `x` after the last item. -/
theorem get_push {α : Type} [Inhabited α] (p : Array α) (x : α) (k : Nat) :
    get (p.push x) k = if k < p.size then get p k else if k = p.size then x else default := by
  by_cases hk : k < p.size
  · rw [get_of_lt (by simp; omega), get_of_lt hk, Array.getElem_push_lt hk, ite_eq_left hk]
  · rw [ite_eq_right hk]
    by_cases he : k = p.size
    · subst he
      rw [get_of_lt (by simp), Array.getElem_push_eq, ite_eq_left rfl]
    · rw [get_of_le (by simp; omega), ite_eq_right he]

/-- The end of the `k`-th run of the stack. -/
def runEndAt (p : Array Run) (k : Nat) : Nat := (p.getD k default).base + (p.getD k default).len

/-- The runs of the stack lie side by side, end at or before `lo`, and the top one ends at
`lo`. -/
def StackOK (p : Array Run) (lo : Nat) : Prop :=
  (∀ k, k + 1 < p.size → runEndAt p k = (p.getD (k + 1) default).base) ∧
  (∀ k, k < p.size → runEndAt p k ≤ lo) ∧
  (0 < p.size → runEndAt p (p.size - 1) = lo)

/-- `getD` with `default` is `get`. -/
theorem getD_eq_get (p : Array Run) (k : Nat) : p.getD k default = get p k := rfl

/-- A run read past the end of the stack is empty. -/
theorem len_getD_of_le {p : Array Run} {k : Nat} (h : p.size ≤ k) :
    (p.getD k default).len = 0 := by
  rw [getD_eq_get, get_of_le h]
  rfl

/-- The empty stack covers nothing. -/
theorem stackOK_empty : StackOK #[] 0 :=
  ⟨fun _ h => absurd h (by simp), fun _ h => absurd h (by simp), fun h => absurd h (by simp)⟩

/-- The run stack after `merge_at(i)`. -/
def mergedStack (p : Array Run) (i : Nat) : Array Run :=
  let ra := p.getD i default
  let rb := p.getD (i + 1) default
  let p := p.setIfInBounds i { ra with len := ra.len + rb.len }
  let p := if i + 3 == p.size then p.setIfInBounds (i + 1) (p.getD (i + 2) default) else p
  p.pop

/-- After `merge_at(i)`, for the second or third run from the top, the stack has one run less:
the runs below `i` stay, run `i` covers runs `i` and `i + 1`, and the runs above move down. -/
theorem get_mergedStack {p : Array Run} {i : Nat} (hi : i + 2 = p.size ∨ i + 3 = p.size) :
    (mergedStack p i).size = p.size - 1 ∧ ∀ k, k < p.size - 1 →
      get (mergedStack p i) k = if k < i then get p k
        else if k = i then { get p i with len := (get p i).len + (get p (i + 1)).len }
        else get p (k + 1) := by
  unfold mergedStack
  simp only [getD_eq_get, Array.size_setIfInBounds]
  rcases hi with hi | hi
  · have hc : (i + 3 == p.size) = false := by simp; omega
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by simp, fun k hk => ?_⟩
    rw [get_pop, get_setIfInBounds]
    simp only [Array.size_setIfInBounds]
    ite_cases
  · have hc : (i + 3 == p.size) = true := by simp; omega
    simp only [hc, ↓reduceIte]
    refine ⟨by simp, fun k hk => ?_⟩
    rw [get_pop, get_setIfInBounds, get_setIfInBounds, get_setIfInBounds]
    simp only [Array.size_setIfInBounds]
    ite_cases

/-- `merge_at(i)`, for the second or third run from the top, keeps the runs side by side. -/
theorem stackOK_mergedStack {p : Array Run} {lo i : Nat} (h : StackOK p lo)
    (hi : i + 2 = p.size ∨ i + 3 = p.size) : StackOK (mergedStack p i) lo := by
  obtain ⟨hsz, hg⟩ := get_mergedStack hi
  obtain ⟨hadj, hend, htop⟩ := h
  simp only [StackOK, runEndAt, getD_eq_get] at *
  have a1 := hadj i (by omega)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun hk => ?_⟩
  · rw [hg k (by omega), hg (k + 1) (by omega)]
    by_cases h1 : k + 1 < i
    · rw [ite_eq_left (by omega), ite_eq_left h1]
      exact hadj k (by omega)
    by_cases h2 : k + 1 = i
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h2]
      subst h2
      exact hadj k (by omega)
    by_cases h3 : k = i
    · subst h3
      rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega),
        ite_eq_right (by omega)]
      have a2 := hadj (k + 1) (by omega)
      dsimp only
      omega
    · rw [ite_eq_right (by omega), ite_eq_right h3, ite_eq_right (by omega),
        ite_eq_right (by omega)]
      exact hadj (k + 1) (by omega)
  · rw [hg k (by omega)]
    by_cases h1 : k < i
    · rw [ite_eq_left h1]
      exact hend k (by omega)
    by_cases h2 : k = i
    · subst h2
      rw [ite_eq_right h1, ite_eq_left rfl]
      have e2 := hend (k + 1) (by omega)
      dsimp only
      omega
    · rw [ite_eq_right h1, ite_eq_right h2]
      exact hend (k + 1) (by omega)
  · rw [hsz] at hk ⊢
    rw [hg _ (by omega)]
    rcases hi with hi | hi
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      have ht := htop (by omega)
      rw [show p.size - 1 = i + 1 by omega] at ht
      dsimp only
      omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      have ht := htop (by omega)
      rwa [show p.size - 1 - 1 + 1 = p.size - 1 by omega]

/-- Changing powers keeps the runs side by side. -/
theorem stackOK_setPower {p : Array Run} {lo : Nat} (h : StackOK p lo) (i pw : Nat) :
    StackOK (p.setIfInBounds i
      { base := (p.getD i default).base, len := (p.getD i default).len, power := pw }) lo := by
  have hb : ∀ k, (get (p.setIfInBounds i
      { base := (p.getD i default).base, len := (p.getD i default).len, power := pw }) k).base =
        (get p k).base ∧ (get (p.setIfInBounds i
      { base := (p.getD i default).base, len := (p.getD i default).len, power := pw }) k).len =
        (get p k).len := by
    intro k
    rw [get_setIfInBounds]
    split
    · rename_i hk
      rw [hk.1]
      exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  obtain ⟨hadj, hend, htop⟩ := h
  simp only [StackOK, runEndAt, getD_eq_get, Array.size_setIfInBounds] at *
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun hk => ?_⟩
  · rw [(hb k).1, (hb k).2, (hb (k + 1)).1]
    exact hadj k hk
  · rw [(hb k).1, (hb k).2]
    exact hend k hk
  · rw [(hb _).1, (hb _).2]
    exact htop hk

/-- Pushing a run that starts where the top one ends keeps the runs side by side. -/
theorem stackOK_push {p : Array Run} {lo n : Nat} (h : StackOK p lo) :
    StackOK (p.push { base := lo, len := n, power := 0 }) (lo + n) := by
  obtain ⟨hadj, hend, htop⟩ := h
  simp only [StackOK, runEndAt, getD_eq_get, Array.size_push] at *
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun _ => ?_⟩
  · rw [get_push, get_push, ite_eq_left (by omega)]
    by_cases h1 : k + 1 < p.size
    · rw [ite_eq_left h1]
      exact hadj k h1
    · rw [ite_eq_right h1, ite_eq_left (by omega)]
      have ht := htop (by omega)
      rwa [show p.size - 1 = k by omega] at ht
  · rw [get_push]
    by_cases h1 : k < p.size
    · rw [ite_eq_left h1]
      have hk' := hend k h1
      omega
    · rw [ite_eq_right h1, ite_eq_left (by omega)]
      exact Nat.le_refl _
  · rw [get_push, ite_eq_right (by omega), ite_eq_left (by omega)]

end Stack

/-! ## The whole sort -/

section Sorting
variable {m : Type → Type u} [Monad m] [LawfulMonad m] {ε α : Type} [Inhabited α]

/-- `merge_at(i)`, for the second or third run from the top, started from an array that is a
permutation of `xs` and a run stack whose runs lie side by side up to `lo ≤ xs.size`
(`StackOK`), leaves a permutation of `xs` and keeps the runs side by side. -/
theorem wp_mergeAt (lt : α → α → m (Except ε Bool)) (xs : Array α) (lo i : Nat) (s : State α)
    (hP : PermOf xs s.arr) (hS : StackOK s.pending lo) (hlo : lo ≤ xs.size)
    (hi : i + 2 = s.pending.size ∨ i + 3 = s.pending.size) :
    WP (mergeAt lt i) (fun _ s' => PermOf xs s'.arr ∧ StackOK s'.pending lo)
      (fun _ s' => PermOf xs s'.arr) s := by
  have hS' := stackOK_mergedStack hS hi
  obtain ⟨hadj, hend, _⟩ := hS
  unfold mergeAt
  refine wp_bind (wp_modifyGetThe ?_)
  refine RO.wp (ro_itemAt _) (fun _ _ => ?_) (fun _ => hP)
  refine RO.wp (ro_gallopRight _ _ _ (fun _ => ro_itemAt _) _ _) (fun k hk => ?_) (fun _ => hP)
  refine wp_ite (fun _ => wp_pure ⟨hP, hS'⟩) (fun hna => ?_)
  simp only [beq_iff_eq] at hna
  refine RO.wp (ro_itemAt _) (fun _ _ => ?_) (fun _ => hP)
  refine RO.wp (ro_gallopLeft _ _ _ (fun _ => ro_itemAt _) _ _) (fun nb hnb => ?_) (fun _ => hP)
  refine wp_ite (fun _ => wp_pure ⟨hP, hS'⟩) (fun hnb0 => ?_)
  simp only [beq_iff_eq] at hnb0
  have hi1 : i + 1 < s.pending.size := by
    refine Nat.lt_of_not_le fun h => ?_
    have hlen := len_getD_of_le h
    omega
  have a1 := hadj i hi1
  have e1 := hend (i + 1) hi1
  unfold runEndAt at a1 e1
  have hsz := hP.size
  refine wp_ite (fun _ => ?_) (fun _ => ?_)
  · refine WP.conseq (wp_mergeLo lt xs _ _ _ _ _ hP (by omega) (by omega) (by omega) (by omega))
      (fun _ s' h => ⟨h.1, ?_⟩) fun _ _ h => h
    rw [h.2]
    exact hS'
  · refine WP.conseq (wp_mergeHi lt xs _ _ _ _ _ hP (by omega) (by omega) (by omega) (by omega))
      (fun _ s' h => ⟨h.1, ?_⟩) fun _ _ h => h
    rw [h.2]
    exact hS'

/-- The merges of `found_new_run`, started from a permutation of `xs` and runs side by side up to
`lo ≤ xs.size`, leave a permutation of `xs` and keep the runs side by side. -/
theorem wp_collapse (lt : α → α → m (Except ε Bool)) (xs : Array α) (lo power : Nat)
    (hlo : lo ≤ xs.size) : ∀ (c : Nat) (s : State α), PermOf xs s.arr → StackOK s.pending lo →
      WP (foundNewRun.collapse lt power c) (fun _ s' => PermOf xs s'.arr ∧ StackOK s'.pending lo)
        (fun _ s' => PermOf xs s'.arr) s
  | 0, s, hP, hS => by
    rw [foundNewRun.collapse]
    exact wp_pure ⟨hP, hS⟩
  | c + 1, s, hP, hS => by
    rw [foundNewRun.collapse]
    refine wp_bind (wp_readState ?_)
    refine wp_ite (fun h => ?_) (fun _ => wp_pure ⟨hP, hS⟩)
    exact wp_bind (WP.conseq (wp_mergeAt lt xs lo _ s hP hS hlo (Or.inl (by omega)))
      (fun _ s' h => wp_collapse lt xs lo power hlo c s' h.1 h.2) fun _ _ h => h)

/-- `found_new_run`, started from a permutation of `xs` and runs side by side up to
`lo ≤ xs.size`, leaves a permutation of `xs` and keeps the runs side by side. -/
theorem wp_foundNewRun (lt : α → α → m (Except ε Bool)) (xs : Array α) (lo listLen n2 : Nat)
    (s : State α) (hP : PermOf xs s.arr) (hS : StackOK s.pending lo) (hlo : lo ≤ xs.size) :
    WP (foundNewRun lt listLen n2) (fun _ s' => PermOf xs s'.arr ∧ StackOK s'.pending lo)
      (fun _ s' => PermOf xs s'.arr) s := by
  unfold foundNewRun
  refine wp_bind (wp_readState ?_)
  refine wp_ite (fun _ => wp_pure ⟨hP, hS⟩) (fun _ => ?_)
  exact wp_bind (WP.conseq (wp_collapse lt xs lo _ hlo _ s hP hS)
    (fun _ _ h => wp_modifyThe ⟨h.1, stackOK_setPower h.2 _ _⟩) fun _ _ h => h)

/-- The merges of `merge_force_collapse`, started from a permutation of `xs` and runs side by
side up to `lo ≤ xs.size`, leave a permutation of `xs`. -/
theorem wp_forceCollapse_go (lt : α → α → m (Except ε Bool)) (xs : Array α) (lo : Nat)
    (hlo : lo ≤ xs.size) : ∀ (c : Nat) (s : State α), PermOf xs s.arr → StackOK s.pending lo →
      WP (forceCollapse.go lt c) (fun _ s' => PermOf xs s'.arr) (fun _ s' => PermOf xs s'.arr) s
  | 0, s, hP, _ => by
    rw [forceCollapse.go]
    exact wp_pure hP
  | c + 1, s, hP, hS => by
    rw [forceCollapse.go]
    refine wp_bind (wp_readState ?_)
    dsimp only
    by_cases h : s.pending.size > 1
    · rw [ite_eq_left h]
      refine wp_bind (WP.conseq (wp_mergeAt lt xs lo _ s hP hS hlo ?_)
        (fun _ s' h => wp_forceCollapse_go lt xs lo hlo c s' h.1 h.2) fun _ _ h => h)
      split <;> omega
    · rw [ite_eq_right h]
      exact wp_pure hP

/-- `merge_force_collapse`, started from a permutation of `xs` and runs side by side up to
`lo ≤ xs.size`, leaves a permutation of `xs`. -/
theorem wp_forceCollapse (lt : α → α → m (Except ε Bool)) (xs : Array α) (lo : Nat)
    (s : State α) (hP : PermOf xs s.arr) (hS : StackOK s.pending lo) (hlo : lo ≤ xs.size) :
    WP (forceCollapse lt) (fun _ s' => PermOf xs s'.arr) (fun _ s' => PermOf xs s'.arr) s :=
  wp_bind (wp_readState (wp_forceCollapse_go lt xs lo hlo _ s hP hS))

/-- The loop of `binarysort` on `a[lo, hi)`, with `hi ≤ xs.size`, from `start ≥ lo` and an array
that is a permutation of `xs`, leaves a permutation of `xs` and the run stack as it was. -/
theorem wp_binarySort_go (lt : α → α → m (Except ε Bool)) (xs : Array α) (lo hi : Nat)
    (p0 : Array Run) (hhi : hi ≤ xs.size) (start : Nat) :
    ∀ (s : State α), lo ≤ start → PermOf xs s.arr → s.pending = p0 →
      WP (binarySort.go lt lo hi start) (fun _ s' => PermOf xs s'.arr ∧ s'.pending = p0)
        (fun _ s' => PermOf xs s'.arr) s := by
  induction h : hi - start using Nat.strongRecOn generalizing start with
  | _ d ih =>
    intro s hl hP hp
    rw [binarySort.go]
    refine wp_ite (fun hs => ?_) (fun _ => wp_pure ⟨hP, hp⟩)
    refine wp_bind (wp_itemAt ?_)
    refine RO.wp (ro_insertPos _ _ _ _) (fun l hl' => ?_) (fun _ => hP)
    have hl'' := hl' hl
    have hsz := hP.size
    exact wp_bind (wp_modifyThe (ih _ (by omega) (start + 1) rfl _ (by omega)
      ((perm_insert _ _ _ hl''.2 (by omega)).trans hP) hp))

/-- `binarysort(lo, hi, start)`, with `lo ≤ start` and `hi ≤ xs.size`, from an array that is a
permutation of `xs`, leaves a permutation of `xs` and the run stack as it was. -/
theorem wp_binarySort (lt : α → α → m (Except ε Bool)) (xs : Array α) (lo hi start : Nat)
    (s : State α) (hP : PermOf xs s.arr) (hl : lo ≤ start) (hhi : hi ≤ xs.size) :
    WP (binarySort lt lo hi start) (fun _ s' => PermOf xs s'.arr ∧ s'.pending = s.pending)
      (fun _ s' => PermOf xs s'.arr) s := by
  unfold binarySort
  exact wp_binarySort_go lt xs lo hi s.pending hhi _ s (by split <;> omega) hP rfl

/-- The main loop of the sort from `lo`, with `nr` items left (`lo + nr = xs.size`), an array that
is a permutation of `xs` and runs side by side up to `lo`, leaves a permutation of `xs`, with
runs side by side up to the end of the array. -/
theorem wp_runs (lt : α → α → m (Except ε Bool)) (xs : Array α) (listLen minrun : Nat)
    (nr : Nat) : ∀ (lo : Nat) (s : State α), lo + nr = xs.size → PermOf xs s.arr →
      StackOK s.pending lo →
      WP (runs lt listLen minrun lo nr) (fun _ s' => PermOf xs s'.arr ∧ StackOK s'.pending xs.size)
        (fun _ s' => PermOf xs s'.arr) s := by
  induction nr using Nat.strongRecOn with
  | _ nr ih =>
  intro lo s hlo hP hS
  have hsz := hP.size
  rw [runs]
  refine wp_dite (fun hpos => ?_) (fun hz => wp_pure ⟨hP, by
    rw [← hlo, show nr = 0 by omega, Nat.add_zero]
    exact hS⟩)
  refine RO.wp (ro_countRun _ _ _) (fun x hx => ?_) (fun _ => hP)
  obtain ⟨n, desc⟩ := x
  have hn := hx (by omega)
  dsimp (config := { zeta := false }) only at hn ⊢
  refine wp_ite_jp (fun s' => PermOf xs s'.arr ∧ StackOK s'.pending lo)
    (fun _ => wp_modifyThe ⟨(perm_reverse _ _ _ (by omega)).trans hP, hS⟩)
    (fun _ => ⟨hP, hS⟩) (fun s1 ⟨hP1, hS1⟩ => ?_)
  dsimp (config := { zeta := false }) only
  extract_lets jp
  have hJ : ∀ (n' : Nat) (s2 : State α), 1 ≤ n' → n' ≤ nr → PermOf xs s2.arr →
      StackOK s2.pending lo →
      WP (jp n') (fun _ s' => PermOf xs s'.arr ∧ StackOK s'.pending xs.size)
        (fun _ s' => PermOf xs s'.arr) s2 := by
    intro n' s2 h1 h2 hP2 hS2
    refine wp_bind (WP.conseq (wp_foundNewRun lt xs lo listLen n' s2 hP2 hS2 (by omega))
      (fun _ s3 h3 => ?_) fun _ _ h => h)
    refine wp_bind (wp_modifyThe ?_)
    refine wp_dite (fun _ => ?_) (fun hh => absurd ⟨by omega, h2⟩ hh)
    exact ih (nr - n') (by omega) (lo + n') _ (by omega) h3.1 (stackOK_push h3.2)
  refine wp_ite (fun hlt => ?_) (fun _ => wp_bind (wp_pure (hJ n s1 hn.1 (by omega) hP1 hS1)))
  have hf : 1 ≤ (if nr ≤ minrun then nr else minrun) ∧
      (if nr ≤ minrun then nr else minrun) ≤ nr := by
    split <;> omega
  exact wp_bind (WP.conseq (wp_binarySort lt xs _ _ _ s1 hP1 (by omega) (by omega))
    (fun _ s2 h2 => wp_bind (wp_pure (hJ _ s2 hf.1 hf.2 h2.1 (by rw [h2.2]; exact hS1))))
    fun _ _ h => h)

end Sorting

/-! ## The theorem -/

/-- For any lawful monad `m`, any comparison `lt` in `m` and any array `xs`, every result of
`sort lt xs` holds a permutation of `xs`, whether every comparison succeeds or one fails. -/
public theorem sort_perm {m : Type → Type u} [Monad m] [LawfulMonad m] {ε α : Type} [Inhabited α]
    (lt : α → α → m (Except ε Bool)) (xs : Array α) :
    SatisfiesM (fun r : Array α × Option ε => r.1.toList.Perm xs.toList) (sort lt xs) := by
  unfold sort
  split
  · exact SatisfiesM.pure' (List.Perm.refl _)
  have hbody := wp_bind (WP.conseq (wp_runs lt xs xs.size (minRun xs.size) xs.size 0
      { arr := xs, minGallop := minGallopInit, pending := #[] } (Nat.zero_add _)
      (List.Perm.refl _) stackOK_empty)
    (fun _ s h => wp_forceCollapse lt xs xs.size s h.1 h.2 (Nat.le_refl _)) fun _ _ h => h)
  refine SatisfiesM.bind' hbody fun r hr => ?_
  obtain ⟨r, s⟩ := r
  cases r with
  | ok u => exact SatisfiesM.pure' hr
  | error e => exact SatisfiesM.pure' hr

/-- In the identity monad, `sort lt xs` returns a permutation of `xs`. -/
public theorem sort_perm_id {ε α : Type} [Inhabited α] (lt : α → α → Except ε Bool)
    (xs : Array α) : (sort (m := Id) lt xs).1.toList.Perm xs.toList := by
  obtain ⟨y, hy⟩ := sort_perm (m := Id) lt xs
  rw [← hy]
  exact y.2

end Strata.Dyn.Util.Sort
