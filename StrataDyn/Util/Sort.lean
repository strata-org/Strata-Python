/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# CPython's list sort

A port of the sort of CPython 3.12's `Objects/listobject.c` (`list_sort_impl` and its helpers),
over an array and a comparison `lt` in any monad. It makes the same comparisons, in the same
order, on the same operands, as CPython does, so a comparison with side effects (a user `__lt__`
that prints) behaves as in CPython. A comparison that fails stops the sort, and the array is left
as CPython leaves it: a permutation of the input, partly sorted.

The parts, under CPython's names:
* `binarySort`, `countRun`: the binary insertion sort and the detection of natural runs;
* `gallopLeft`, `gallopRight`: exponential then binary search in a sorted run;
* `mergeLo`, `mergeHi`, `mergeAt`: the merge of two adjacent runs, with galloping and the
  adaptive `minGallop`;
* `powerLoop`, `foundNewRun`, `forceCollapse`: the run stack, merged by powersort's policy;
* `sort`: the whole sort.

Nothing here is specific to Python: the caller gives the comparison, and sorts the pairs it
needs (e.g. a key with its item). Python's choice of comparison, `reverse=` and the empty-list
protocol of `list.sort` are the caller's. But the order of the comparisons is CPython's: a front
end whose language leaves that order open (e.g. JavaScript's `Array.prototype.sort`, whose
engines differ) must not take this sort as that language's semantics, unless it makes the order a
choice.

The array lives in the sort's state only. The sort reads items and fields of the state
(`readState`), never the array or the whole state, and writes the array through `modifyArr`, which
takes it out of the state first. So no computation holds a second reference to the array, and
every write after the first changes it in place (the first copies the caller's array if the
caller still holds it). In a monad that runs the rest of the sort inside each
comparison's continuation (a continuation-passing monad), a reference that a computation held
would stay alive until that continuation returns, and the next write would copy the whole array.

Each loop terminates by a measure that it decreases: the number of items left to place or to
merge, or the width of a search interval. The two run-stack loops run at most once per run on the
stack. Where a recursive call needs a guard for its measure, the guard always holds under
CPython's invariants.
-/

namespace Strata.Dyn.Util.Sort

@[expose] public section

/-- A run on the pending stack: its start in the array, its length, and its powersort power. -/
structure Run where
  base : Nat
  len : Nat
  power : Nat
  deriving Repr, Inhabited

/-- The sort's state: the array being sorted, CPython's `min_gallop`, and the run stack. -/
structure State (α : Type) where
  arr : Array α
  minGallop : Nat
  pending : Array Run

/-- CPython's `MIN_GALLOP`. -/
def minGallopInit : Nat := 7

universe u
variable {m : Type → Type u} [Monad m] {ε α : Type} [Inhabited α]

/-- The sort's monad: a failed comparison throws `ε`, and the state survives the throw. -/
abbrev SortM (m : Type → Type u) (ε α : Type) := ExceptT ε (StateT (State α) m)

/-- `lt x y`, throwing its error. -/
@[inline] def isLt (lt : α → α → m (Except ε Bool)) (x y : α) : SortM m ε α Bool := do
  match ← (lt x y : m _) with
  | .ok b => pure b
  | .error e => throw e

/-- The item at `i`. Every index the sort reads is in range. -/
@[inline] def get (a : Array α) (i : Nat) : α := a.getD i default

/-- `f` of the state, which stays as it is. Only `f`'s result leaves the state. -/
@[inline] def readState {β : Type} (f : State α → β) : SortM m ε α β :=
  modifyGetThe (State α) fun s => (f s, s)

/-- The item at `i` of the array. -/
@[inline] def itemAt (i : Nat) : SortM m ε α α := readState fun s => get s.arr i

/-- `arr[lo, hi)`, as a new array. -/
@[inline] def extractNow (lo hi : Nat) : SortM m ε α (Array α) :=
  readState fun s => s.arr.extract lo hi

/-- Replace the array `a` by `f a`. The array leaves the state before `f` runs, so that `f` finds
it unshared. -/
@[inline] def modifyArr (f : Array α → Array α) : SortM m ε α Unit :=
  modifyThe (State α) fun ⟨arr, minGallop, pending⟩ => ⟨f arr, minGallop, pending⟩

/-- `a` with `a[dst + k] := src[start + k]` for `k < n`, where `src` is another array. -/
def copyRange (a src : Array α) (dst start n : Nat) : Array α := go a 0
where
  go (a : Array α) (k : Nat) : Array α :=
    if k < n then go (a.setIfInBounds (dst + k) (get src (start + k))) (k + 1) else a
  termination_by n - k

/-- `a` with `a[start, start + n)` moved to `a[dst, dst + n)`, in place, as `memmove` does: from
the front when the items move left, from the back when they move right. -/
def moveWithin (a : Array α) (dst start n : Nat) : Array α :=
  if dst ≤ start then fwd a 0 else bwd a n
where
  fwd (a : Array α) (k : Nat) : Array α :=
    if k < n then fwd (a.setIfInBounds (dst + k) (get a (start + k))) (k + 1) else a
  termination_by n - k
  bwd (a : Array α) : Nat → Array α
    | 0 => a
    | k + 1 => bwd (a.setIfInBounds (dst + k) (get a (start + k))) k

/-! ## Binary insertion sort and runs -/

/-- Where `pivot` belongs in the sorted `arr[l, r)`: after every item that is not greater than it,
as `binarysort`'s inner loop finds it. -/
def insertPos (lt : α → α → m (Except ε Bool)) (pivot : α) (l r : Nat) :
    SortM m ε α Nat := do
  if l < r then
    let p := l + (r - l) / 2
    if ← isLt lt pivot (← itemAt p) then insertPos lt pivot l p
    else insertPos lt pivot (p + 1) r
  else pure l
termination_by r - l

/-- `binarysort(lo, hi, start)`: sorts `arr[lo, hi)`, given that `arr[lo, start)` is sorted. A
failed comparison leaves the array a permutation of what it was. -/
def binarySort (lt : α → α → m (Except ε Bool)) (lo hi start : Nat) : SortM m ε α Unit := do
  go (if lo == start then start + 1 else start)
where
  go (start : Nat) : SortM m ε α Unit := do
    if start < hi then
      let pivot ← itemAt start
      let l ← insertPos lt pivot lo start
      -- Shift `arr[l, start)` one slot right and put the pivot at `l`.
      modifyArr fun a => (moveWithin a (l + 1) l (start - l)).setIfInBounds l pivot
      go (start + 1)
  termination_by hi - start

/-- The end of a run that reaches `arr[i - 1]`: the first `j ≥ i` where `arr[j] < arr[j - 1]`
differs from `desc`, or `hi`. -/
def runEnd (lt : α → α → m (Except ε Bool)) (hi : Nat) (desc : Bool) (i : Nat) :
    SortM m ε α Nat := do
  if i < hi then
    if (← isLt lt (← itemAt i) (← itemAt (i - 1))) == desc then runEnd lt hi desc (i + 1)
    else pure i
  else pure i
termination_by hi - i

/-- `count_run(lo, hi)`: the length of the run that starts at `lo < hi`, and whether it is
strictly descending. -/
def countRun (lt : α → α → m (Except ε Bool)) (lo hi : Nat) :
    SortM m ε α (Nat × Bool) := do
  if lo + 1 ≥ hi then return (1, false)
  let desc ← isLt lt (← itemAt (lo + 1)) (← itemAt lo)
  let e ← runEnd lt hi desc (lo + 2)
  return (e - lo, desc)

/-! ## Galloping -/

/-- The exponential search of `gallop_left` and `gallop_right`: the last offset `lastofs` and the
first offset `ofs` (of the form `2^k - 1`) at which `stop ofs` holds, or `maxofs`. -/
def expand (stop : Nat → SortM m ε α Bool) (maxofs : Nat) (lastofs ofs : Nat) :
    SortM m ε α (Nat × Nat) := do
  if ofs < maxofs then
    if ← stop ofs then pure (lastofs, ofs)
    else expand stop maxofs ofs (2 * ofs + 1)
  else pure (lastofs, maxofs)
termination_by maxofs - ofs

/-- The binary search that ends both gallops: the first `k` in `[lo, hi)` with `right k`, or `hi`,
where `right` is monotone. -/
def bisect (right : Nat → SortM m ε α Bool) (lo hi : Nat) : SortM m ε α Nat := do
  if lo < hi then
    let mid := lo + (hi - lo) / 2
    if ← right mid then bisect right lo mid else bisect right (mid + 1) hi
  else pure hi
termination_by hi - lo

/-- `gallop_left(key, a[0, n), hint)`: the `k` in `[0, n]` with `a[k-1] < key ≤ a[k]`, starting
the search at `hint < n`, where `at_ i` reads `a[i]`. The search never passes `n`; the final `min`
states that bound for the callers. -/
def gallopLeft (lt : α → α → m (Except ε Bool)) (key : α) (at_ : Nat → SortM m ε α α)
    (n hint : Nat) : SortM m ε α Nat := do
  let (lo, hi) ←
    if ← isLt lt (← at_ hint) key then do
      -- Gallop right: `a[hint + lastofs] < key ≤ a[hint + ofs]`.
      let (lastofs, ofs) ← expand (fun o => do return !(← isLt lt (← at_ (hint + o)) key))
        (n - hint) 0 1
      pure (hint + lastofs + 1, hint + ofs)
    else do
      -- Gallop left: `a[hint - ofs] < key ≤ a[hint - lastofs]`.
      let (lastofs, ofs) ← expand (fun o => do isLt lt (← at_ (hint - o)) key) (hint + 1) 0 1
      pure (hint + 1 - ofs, hint - lastofs)
  let k ← bisect (fun i => do return !(← isLt lt (← at_ i) key)) lo hi
  pure (min k n)

/-- `gallop_right(key, a[0, n), hint)`: the `k` in `[0, n]` with `a[k-1] ≤ key < a[k]`, starting
the search at `hint < n`, where `at_ i` reads `a[i]`. -/
def gallopRight (lt : α → α → m (Except ε Bool)) (key : α) (at_ : Nat → SortM m ε α α)
    (n hint : Nat) : SortM m ε α Nat := do
  let (lo, hi) ←
    if ← isLt lt key (← at_ hint) then do
      -- Gallop left: `a[hint - ofs] ≤ key < a[hint - lastofs]`.
      let (lastofs, ofs) ← expand (fun o => do return !(← isLt lt key (← at_ (hint - o))))
        (hint + 1) 0 1
      pure (hint + 1 - ofs, hint - lastofs)
    else do
      -- Gallop right: `a[hint + lastofs] ≤ key < a[hint + ofs]`.
      let (lastofs, ofs) ← expand (fun o => do isLt lt key (← at_ (hint + o))) (n - hint) 0 1
      pure (hint + lastofs + 1, hint + ofs)
  let k ← bisect (fun i => do isLt lt key (← at_ i)) lo hi
  pure (min k n)

/-! ## Merging two runs -/

/-- How a merge loop ended, with the counts of items left in each run: `done` is CPython's
`Succeed`, and `copy` is its `CopyB` (in `merge_lo`) or `CopyA` (in `merge_hi`). A failed
comparison throws instead. -/
inductive Exit where
  | done (na nb : Nat)
  | copy (na nb : Nat)

/-- Run `x`; if it throws, run `fix` (CPython's `Fail` label) and throw again. -/
@[inline] def withFix {β : Type} (fix : SortM m ε α Unit) (x : SortM m ε α β) : SortM m ε α β :=
  tryCatch x fun e => do fix; throw e

/-- Set `arr[i] := x`. -/
@[inline] def setAt (i : Nat) (x : α) : SortM m ε α Unit :=
  modifyArr fun a => a.setIfInBounds i x

/-- Set `arr[dst] := arr[src]`. -/
@[inline] def copyItem (dst src : Nat) : SortM m ε α Unit :=
  modifyArr fun a => a.setIfInBounds dst (get a src)

/-- Copy `src[start, start + n)`, from the temporary copy of a run, to `arr[dst, dst + n)`. -/
@[inline] def moveFrom (src : Array α) (dst start n : Nat) : SortM m ε α Unit :=
  modifyArr fun a => copyRange a src dst start n

/-- Move `arr[start, start + n)` to `arr[dst, dst + n)`, in place. -/
@[inline] def move (dst start n : Nat) : SortM m ε α Unit :=
  modifyArr fun a => moveWithin a dst start n

/-- Set CPython's `ms->min_gallop`. -/
@[inline] def storeMinGallop (mg : Nat) : SortM m ε α Unit :=
  modifyThe (State α) fun s => { s with minGallop := mg }

section MergeLo
variable (lt : α → α → m (Except ε Bool)) (tmp : Array α) (naO pb nbO : Nat)

/-! `merge_lo`: the first run, `naO` items, is in `tmp`; the second, `nbO` items, starts at `pb`
in the array. With `na` and `nb` items left, the next item of the first run is `tmp[naO - na]`,
the next of the second is `arr[pb + nbO - nb]`, and the next slot to fill is that index minus
`na`. -/

/-- The index of the next item of the second run. -/
@[inline] def loJ (nb : Nat) : Nat := pb + nbO - nb

/-- CPython's `Fail` and `Succeed` fixup: the rest of the first run goes after the merged part. -/
def loFix (na nb : Nat) : SortM m ε α Unit :=
  moveFrom tmp (loJ pb nbO nb - na) (naO - na) na

mutual
/-- `merge_lo`'s galloping mode, one round of its `do … while`. -/
def loGallop (mg na nb : Nat) (_hb : 0 < nb) : SortM m ε α Exit := do
  let mg := mg - (if mg > 1 then 1 else 0)
  storeMinGallop mg
  let key ← itemAt (loJ pb nbO nb)
  let k ← withFix (loFix tmp naO pb nbO na nb)
    (gallopRight lt key (fun i => pure (get tmp (naO - na + i))) na 0)
  let acount := k
  if k > 0 then
    moveFrom tmp (loJ pb nbO nb - na) (naO - na) k
  let na := na - k
  if na == 1 then return .copy na nb
  if na == 0 then return .done na nb
  -- One item of the second run.
  copyItem (loJ pb nbO nb - na) (loJ pb nbO nb)
  let nb' := nb - 1
  if nb' == 0 then return .done na nb'
  let k ← withFix (loFix tmp naO pb nbO na nb')
    (gallopLeft lt (get tmp (naO - na)) (fun i => itemAt (loJ pb nbO nb' + i)) nb' 0)
  let bcount := k
  if k > 0 then
    move (loJ pb nbO nb' - na) (loJ pb nbO nb') k
  let nb' := nb' - k
  if nb' == 0 then return .done na nb'
  -- One item of the first run.
  setAt (loJ pb nbO nb' - na) (get tmp (naO - na))
  let na' := na - 1
  if na' == 1 then return .copy na' nb'
  if h : 0 < nb' ∧ na' + nb' < na + nb then
    if acount ≥ minGallopInit || bcount ≥ minGallopInit then
      loGallop mg na' nb' h.1
    else
      let mg := mg + 1
      storeMinGallop mg
      loSimple mg 0 0 na' nb' h.1
  else return .done na' nb'
termination_by na + nb
decreasing_by all_goals omega

/-- `merge_lo`'s simple mode: one item at a time, until one run wins `mg` times in a row. -/
def loSimple (mg acount bcount na nb : Nat) (hb : 0 < nb) : SortM m ε α Exit := do
  let j := loJ pb nbO nb
  let x ← itemAt j
  let k ← withFix (loFix tmp naO pb nbO na nb) (isLt lt x (get tmp (naO - na)))
  if k then
    setAt (j - na) x
    let nb' := nb - 1
    if h : 0 < nb' then
      if bcount + 1 ≥ mg then loGallop (mg + 1) na nb' h else loSimple mg 0 (bcount + 1) na nb' h
    else return .done na nb'
  else
    setAt (j - na) (get tmp (naO - na))
    let na' := na - 1
    if na' == 1 then return .copy na' nb
    if na' < na then
      if acount + 1 ≥ mg then loGallop (mg + 1) na' nb hb else loSimple mg (acount + 1) 0 na' nb hb
    else return .done na' nb
termination_by na + nb
decreasing_by all_goals omega
end

end MergeLo

/-- `merge_lo(pa, na, pb, nb)`: merges the run `arr[pa, pa + na)` with the run that follows it,
`arr[pb, pb + nb)`, `pb = pa + na`, through a copy of the first run; for `na ≤ nb`. -/
def mergeLo (lt : α → α → m (Except ε Bool)) (pa na pb nb : Nat) : SortM m ε α Unit := do
  let tmp ← extractNow pa (pa + na)
  copyItem pa pb
  let exit ←
    if h : 0 < nb - 1 then
      if na == 1 then pure (Exit.copy na (nb - 1))
      else loSimple lt tmp na pb nb (← readState (·.minGallop)) 0 0 na (nb - 1) h
    else pure (Exit.done na (nb - 1))
  match exit with
  | .done na' nb' => loFix tmp na pb nb na' nb'
  | .copy na' nb' =>
    -- CPython's `CopyB`: the rest of the second run, then the last item of the first.
    let j := loJ pb nb nb'
    move (j - na') j nb'
    setAt (j - na' + nb') (get tmp (na - na'))

section MergeHi
variable (lt : α → α → m (Except ε Bool)) (tmp : Array α) (pa : Nat)

/-! `merge_hi`: the second run is in `tmp`, and the first, starting at `pa`, is in the array; the
merge fills the array from the right. With `na` and `nb` items left, the next item of the first
run is `arr[pa + na - 1]`, the next of the second is `tmp[nb - 1]`, and the next slot to fill is
`pa + na + nb - 1`. -/

/-- CPython's `Fail` and `Succeed` fixup: the rest of the second run goes before the merged
part. -/
def hiFix (na nb : Nat) : SortM m ε α Unit := moveFrom tmp (pa + na) 0 nb

mutual
/-- `merge_hi`'s galloping mode, one round of its `do … while`. -/
def hiGallop (mg na nb : Nat) (_ha : 0 < na) : SortM m ε α Exit := do
  let mg := mg - (if mg > 1 then 1 else 0)
  storeMinGallop mg
  let k ← withFix (hiFix tmp pa na nb)
    (gallopRight lt (get tmp (nb - 1)) (fun i => itemAt (pa + i)) na (na - 1))
  let k := na - k
  let acount := k
  let na := na - k
  if k > 0 then
    move (pa + na + nb) (pa + na) k
  if na == 0 then return .done na nb
  -- One item of the second run.
  setAt (pa + na + nb - 1) (get tmp (nb - 1))
  let nb' := nb - 1
  if nb' == 1 then return .copy na nb'
  let key ← itemAt (pa + na - 1)
  let k ← withFix (hiFix tmp pa na nb')
    (gallopLeft lt key (fun i => pure (get tmp i)) nb' (nb' - 1))
  let k := nb' - k
  let bcount := k
  let nb' := nb' - k
  if k > 0 then
    moveFrom tmp (pa + na + nb') nb' k
  if nb' == 1 then return .copy na nb'
  if nb' == 0 then return .done na nb'
  -- One item of the first run.
  copyItem (pa + na + nb' - 1) (pa + na - 1)
  let na' := na - 1
  if h : 0 < na' ∧ na' + nb' < na + nb then
    if acount ≥ minGallopInit || bcount ≥ minGallopInit then
      hiGallop mg na' nb' h.1
    else
      let mg := mg + 1
      storeMinGallop mg
      hiSimple mg 0 0 na' nb' h.1
  else return .done na' nb'
termination_by na + nb
decreasing_by all_goals omega

/-- `merge_hi`'s simple mode: one item at a time, until one run wins `mg` times in a row. -/
def hiSimple (mg acount bcount na nb : Nat) (ha : 0 < na) : SortM m ε α Exit := do
  let x ← itemAt (pa + na - 1)
  let k ← withFix (hiFix tmp pa na nb) (isLt lt (get tmp (nb - 1)) x)
  if k then
    setAt (pa + na + nb - 1) x
    let na' := na - 1
    if h : 0 < na' then
      if acount + 1 ≥ mg then hiGallop (mg + 1) na' nb h else hiSimple mg (acount + 1) 0 na' nb h
    else return .done na' nb
  else
    setAt (pa + na + nb - 1) (get tmp (nb - 1))
    let nb' := nb - 1
    if nb' == 1 then return .copy na nb'
    if nb' < nb then
      if bcount + 1 ≥ mg then hiGallop (mg + 1) na nb' ha else hiSimple mg 0 (bcount + 1) na nb' ha
    else return .done na nb'
termination_by na + nb
decreasing_by all_goals omega
end

end MergeHi

/-- `merge_hi(pa, na, pb, nb)`: as `mergeLo`, through a copy of the second run; for `na ≥ nb`. -/
def mergeHi (lt : α → α → m (Except ε Bool)) (pa na pb nb : Nat) : SortM m ε α Unit := do
  let tmp ← extractNow pb (pb + nb)
  copyItem (pa + na + nb - 1) (pa + na - 1)
  let exit ←
    if h : 0 < na - 1 then
      if nb == 1 then pure (Exit.copy (na - 1) nb)
      else hiSimple lt tmp pa (← readState (·.minGallop)) 0 0 (na - 1) nb h
    else pure (Exit.done (na - 1) nb)
  match exit with
  | .done na' nb' => hiFix tmp pa na' nb'
  | .copy na' _ =>
    -- CPython's `CopyA`: the rest of the first run moves right by one, and the first item of the
    -- second run goes before it.
    move (pa + 1) pa na'
    setAt pa (get tmp 0)

/-! ## The run stack -/

/-- `merge_at(i)`: merges the runs at `i` and `i + 1` of the stack, `i` being the second or the
third from the top. -/
def mergeAt (lt : α → α → m (Except ε Bool)) (i : Nat) : SortM m ε α Unit := do
  let (ra, rb) ← modifyGetThe (State α) fun s =>
    let p := s.pending
    let ra := p.getD i default
    let rb := p.getD (i + 1) default
    -- The merged run takes the place of both; a run above them slides down.
    let p := p.setIfInBounds i { ra with len := ra.len + rb.len }
    let p := if i + 3 == p.size then p.setIfInBounds (i + 1) (p.getD (i + 2) default) else p
    ((ra, rb), { s with pending := p.pop })
  -- Items of the first run before the second run's first item are already in place.
  let k ← gallopRight lt (← itemAt rb.base) (fun j => itemAt (ra.base + j)) ra.len 0
  let pa := ra.base + k
  let na := ra.len - k
  if na == 0 then return
  -- Items of the second run after the first run's last item are already in place.
  let nb ← gallopLeft lt (← itemAt (pa + na - 1)) (fun j => itemAt (rb.base + j)) rb.len
    (rb.len - 1)
  if nb == 0 then return
  if na ≤ nb then mergeLo lt pa na rb.base nb else mergeHi lt pa na rb.base nb

/-- `powerloop(s1, n1, n2, n)`: the powersort power of the run boundary between the runs
`[s1, s1 + n1)` and `[s1 + n1, s1 + n1 + n2)` of a list of length `n`: one more than the number
of leading binary digits that the midpoints' fractions `a / n` and `b / n` share. -/
def powerLoop (s1 n1 n2 n : Nat) : Nat :=
  go (2 * s1 + n1) (2 * s1 + n1 + n1 + n2) 1
where
  /-- One digit: `a` and `b` are twice the midpoints, scaled. -/
  go (a b result : Nat) : Nat :=
    if a ≥ n then
      -- Both digits are 1.
      if a - n < b - n ∧ b - n < n then go (2 * (a - n)) (2 * (b - n)) (result + 1) else result
    -- The digits differ.
    else if b ≥ n then result
    -- Both digits are 0.
    else if a < b then go (2 * a) (2 * b) (result + 1)
    else result
  termination_by n - (b - a)
  decreasing_by all_goals omega

/-- `found_new_run(n2)`: before a new run of `n2` items is pushed, gives the top run its power,
and merges the runs below it with a greater power. -/
def foundNewRun (lt : α → α → m (Except ε Bool)) (listLen n2 : Nat) : SortM m ε α Unit := do
  let (size, top) ← readState fun s => (s.pending.size, s.pending.getD (s.pending.size - 1) default)
  if size == 0 then return
  let power := powerLoop top.base top.len n2 listLen
  -- Each merge removes one run, so at most `size - 1` merges happen.
  collapse power size
  modifyThe (State α) fun s =>
    let i := s.pending.size - 1
    let r := s.pending.getD i default
    { s with pending := s.pending.setIfInBounds i { r with power := power } }
where
  collapse (power : Nat) : Nat → SortM m ε α Unit
    | 0 => pure ()
    | c + 1 => do
      let (size, below) ← readState fun s =>
        (s.pending.size, (s.pending.getD (s.pending.size - 2) default).power)
      if size > 1 ∧ below > power then
        mergeAt lt (size - 2)
        collapse power c

/-- `merge_force_collapse`: merges all runs of the stack until one is left. -/
def forceCollapse (lt : α → α → m (Except ε Bool)) : SortM m ε α Unit := do
  go (← readState (·.pending.size))
where
  -- Each merge removes one run, so at most `size - 1` merges happen.
  go : Nat → SortM m ε α Unit
    | 0 => pure ()
    | c + 1 => do
      -- The run that merges with the one above it, if the stack holds two runs or more.
      let n? ← readState fun s =>
        let p := s.pending
        let n := p.size - 2
        if p.size > 1 then
          some (if n > 0 ∧ (p.getD (n - 1) default).len < (p.getD (n + 1) default).len then n - 1
            else n)
        else none
      if let some n := n? then
        mergeAt lt n
        go c

/-- `merge_compute_minrun(n)`: the minimum run length for a list of `n` items: `n` below 64,
otherwise a number in `[32, 64]` such that `n / minrun` is just below a power of two. -/
def minRun (n : Nat) : Nat := go n 0
where
  go (n r : Nat) : Nat :=
    if n ≥ 64 then go (n / 2) (r ||| (n % 2)) else n + r
  termination_by n
  decreasing_by omega

/-- Reverse `arr[lo, lo + n)`. -/
def reverseRange (lo n : Nat) : SortM m ε α Unit :=
  modifyArr fun a => copyRange a ((a.extract lo (lo + n)).reverse) lo 0 n

/-- The main loop of `list_sort_impl`: finds the runs from `lo`, extends short ones to `minrun`
items, and pushes them on the stack. -/
def runs (lt : α → α → m (Except ε Bool)) (listLen minrun lo nremaining : Nat) :
    SortM m ε α Unit := do
  if _h : 0 < nremaining then
    let (n, desc) ← countRun lt lo (lo + nremaining)
    if desc then reverseRange lo n
    let n ← if n < minrun then do
        let force := if nremaining ≤ minrun then nremaining else minrun
        binarySort lt lo (lo + force) (lo + n)
        pure force
      else pure n
    foundNewRun lt listLen n
    modifyThe (State α) fun s => { s with pending := s.pending.push { base := lo, len := n, power := 0 } }
    if _h2 : 0 < n ∧ n ≤ nremaining then runs lt listLen minrun (lo + n) (nremaining - n)
termination_by nremaining
decreasing_by omega

/-- CPython 3.12's list sort of `xs` by `lt`, with the same comparisons in the same order. It
returns the sorted array, or, if a comparison failed, the array as CPython leaves it (a
permutation of `xs`) with the error. -/
def sort (lt : α → α → m (Except ε Bool)) (xs : Array α) : m (Array α × Option ε) := do
  if xs.size < 2 then return (xs, none)
  let body : SortM m ε α Unit := do
    runs lt xs.size (minRun xs.size) 0 xs.size
    forceCollapse lt
  let (r, s) ← (body.run).run { arr := xs, minGallop := minGallopInit, pending := #[] }
  match r with
  | .ok () => return (s.arr, none)
  | .error e => return (s.arr, some e)

end

end Strata.Dyn.Util.Sort
