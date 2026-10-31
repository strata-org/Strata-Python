/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Util.Search
public import StrataPython.Dyn.Sem.Library.Unicode

set_option autoImplicit false

/-!
# Searching, splitting and padding of `str`

CPython 3.12's methods of `str` that search, split, strip and pad, as functions on Lean values:
a string is an array of code points, and an index is an `Int`. Their wiring as methods (binding
the arguments, reading `__index__`) comes in a later part of the library.

The contract on the `Int` arguments: `start` and `end` may be any `Int`, since CPython clamps
them. A count, a `maxsplit` or a width must fit in CPython's `Py_ssize_t`, and a `tabsize` in a C
`int`; CPython raises `OverflowError` otherwise, and the caller raises it before calling these
functions.

Substring search uses the Knuth–Morris–Pratt algorithm of `StrataDyn/Util/Search.lean`, in
time linear in the two lengths. The result of a search doesn't depend on the algorithm.
-/

namespace StrataPython.Dyn.Sem.Library.Str

open StrataPython.Dyn.Sem.Library.Unicode (isSpace isLineBreak)

@[expose] public section

/-- A string as CPython indexes it: its code points. -/
abbrev Chars := Array Char

/-- The code points of `s`. -/
def chars (s : String) : Chars := s.foldl (·.push ·) #[]

/-- The string of the code points `a`. -/
def str (a : Chars) : String := a.foldl (·.push ·) ""

/-- `a[i, j)`. -/
def slice (a : Chars) (i j : Nat) : Chars := a.extract i j

/-! ## Indices -/

/-- CPython's `ADJUST_INDICES`: `start` and `end` of a slice of a string of length `len`, with a
negative index counted from the end and clamped at zero, and `end` clamped at `len`. `start` may
stay above `len`. -/
def adjust (start stop : Option Int) (len : Nat) : Int × Int :=
  let len : Int := len
  let e := stop.getD len
  let e := if e > len then len else if e < 0 then max (e + len) 0 else e
  let s := start.getD 0
  let s := if s < 0 then max (s + len) 0 else s
  (s, e)

/-! ## Substring search -/

/-- The starts of the non-overlapping occurrences of the non-empty `p` in `a[lo, hi)`, from the
left, up to `limit` of them (`StrataDyn/Util/Search.lean`). -/
def occurrences (a p : Chars) (hp : 0 < p.size) (lo hi limit : Nat) : Array Nat :=
  Strata.Dyn.Util.Search.occurrences a p hp lo hi limit

/-- An array that is not empty has a positive size. -/
theorem size_pos_of_not_isEmpty {α : Type} {a : Array α} (h : ¬a.isEmpty = true) : 0 < a.size :=
  Nat.pos_of_ne_zero fun h0 => h (Array.isEmpty_iff_size_eq_zero.mpr h0)

/-- `str.find(sub, start, end)`: the lowest index of `sub` in `s[start:end]`, or `-1`. -/
def find (s sub : Chars) (start stop : Option Int) : Int :=
  let (st, e) := adjust start stop s.size
  if e - st < sub.size then -1
  else if h : sub.isEmpty then st
  else match ((occurrences s sub (size_pos_of_not_isEmpty h) st.toNat e.toNat 1)[0]? :
      Option Nat) with
    | some i => i
    | none => -1

/-- `str.rfind(sub, start, end)`: the highest index of `sub` in `s[start:end]`, or `-1`; a search
from the left of the reversed strings. -/
def rfind (s sub : Chars) (start stop : Option Int) : Int :=
  let (st, e) := adjust start stop s.size
  if e - st < sub.size then -1
  else if h : sub.isEmpty then e
  else
    let rs := (slice s st.toNat e.toNat).reverse
    match ((occurrences rs sub.reverse (by simpa using size_pos_of_not_isEmpty h) 0 rs.size 1)[0]? :
        Option Nat) with
    | some i => e - i - sub.size
    | none => -1

/-- `str.count(sub, start, end)`: the number of non-overlapping occurrences of `sub` in
`s[start:end]`. -/
def count (s sub : Chars) (start stop : Option Int) : Nat :=
  let (st, e) := adjust start stop s.size
  if e - st < sub.size then 0
  else if h : sub.isEmpty then (e - st).toNat + 1
  else (occurrences s sub (size_pos_of_not_isEmpty h) st.toNat e.toNat (e - st).toNat).size

/-- `str.startswith(prefix, start, end)` for one prefix (CPython's `tailmatch` from the left). -/
def startsWith (s p : Chars) (start stop : Option Int) : Bool :=
  let (st, e) := adjust start stop s.size
  if e - p.size < st then false
  else slice s st.toNat (st.toNat + p.size) == p

/-- `str.endswith(suffix, start, end)` for one suffix (CPython's `tailmatch` from the right). -/
def endsWith (s p : Chars) (start stop : Option Int) : Bool :=
  let (st, e) := adjust start stop s.size
  if e - p.size < st then false
  else slice s (e.toNat - p.size) e.toNat == p

/-! ## Replacing -/

/-- `str.replace(old, new, count)`: `s` with the first `count` occurrences of `old` (all of them
if `count` is negative) replaced by `new`. An empty `old` matches before every character and at
the end. -/
def replace (s old new : Chars) (count : Int) : Chars :=
  let limit : Nat := if count < 0 then s.size + 1 else count.toNat
  if h : old.isEmpty then
    -- `new` before each of the first `limit` characters, and at the end if `limit` allows.
    let n := min limit (s.size + 1)
    let body := (List.range s.size).foldl (fun acc i =>
      (if i < n then acc ++ new else acc).push (s.getD i ' ')) #[]
    if n > s.size then body ++ new else body
  else
    let at_ := occurrences s old (size_pos_of_not_isEmpty h) 0 s.size limit
    let (acc, last) := at_.foldl (fun (acc, prev) i => (acc ++ slice s prev i ++ new, i + old.size))
      (#[], 0)
    acc ++ slice s last s.size

/-! ## Splitting -/

/-- `str.split(sep, maxsplit)` with a non-empty separator (an empty one is CPython's `ValueError`,
raised by the caller); `maxsplit < 0` means no limit. -/
def split (s sep : Chars) (hp : 0 < sep.size) (maxsplit : Int) : Array Chars :=
  let limit : Nat := if maxsplit < 0 then s.size else maxsplit.toNat
  let at_ := occurrences s sep hp 0 s.size limit
  let (acc, last) := at_.foldl (fun (acc, prev) i => (acc.push (slice s prev i), i + sep.size))
    (#[], 0)
  acc.push (slice s last s.size)

/-- `str.rsplit(sep, maxsplit)` with a non-empty separator: the splits from the right. -/
def rsplit (s sep : Chars) (hp : 0 < sep.size) (maxsplit : Int) : Array Chars :=
  (split s.reverse sep.reverse (by simpa using hp) maxsplit).reverse.map Array.reverse

/-- The first index from `i` on whose character is not whitespace, or the end. -/
def skipSpace (s : Chars) (i : Nat) : Nat :=
  if i < s.size ∧ isSpace (s.getD i ' ') then skipSpace s (i + 1) else i
termination_by s.size - i

/-- The first index from `i` on whose character is whitespace, or the end. -/
def skipWord (s : Chars) (i : Nat) : Nat :=
  if i < s.size ∧ !isSpace (s.getD i ' ') then skipWord s (i + 1) else i
termination_by s.size - i

/-- `skipSpace` never goes back. -/
private theorem le_skipSpace (s : Chars) (i : Nat) : i ≤ skipSpace s i := by
  unfold skipSpace; split
  · have := le_skipSpace s (i + 1); omega
  · omega
termination_by s.size - i

/-- `skipWord` never goes back. -/
private theorem le_skipWord (s : Chars) (i : Nat) : i ≤ skipWord s i := by
  unfold skipWord; split
  · have := le_skipWord s (i + 1); omega
  · omega
termination_by s.size - i

/-- `str.split(None, maxsplit)`: the runs of non-whitespace characters, at most `maxsplit + 1` of
them; when `maxsplit` runs out, the last part is the rest of the string, without its leading
whitespace. -/
def splitWhitespace (s : Chars) (maxsplit : Int) : Array Chars :=
  let limit : Nat := if maxsplit < 0 then s.size else maxsplit.toNat
  go 0 #[] limit
where
  go (i₀ : Nat) (acc : Array Chars) (left : Nat) : Array Chars :=
    let i := skipSpace s i₀
    if hi : i ≥ s.size then acc
    else if left == 0 then
      -- CPython keeps the rest as it is, trailing whitespace included.
      acc.push (slice s i s.size)
    else
      -- `s[i]` is not whitespace, so the word goes on at least to `i + 1`.
      let j := skipWord s (i + 1)
      go j (acc.push (slice s i j)) (left - 1)
  termination_by s.size - i₀
  decreasing_by
    have h₀ := le_skipSpace s i₀
    have h₁ := le_skipWord s (skipSpace s i₀ + 1)
    omega

/-- `str.rsplit(None, maxsplit)`: as `splitWhitespace`, from the right. -/
def rsplitWhitespace (s : Chars) (maxsplit : Int) : Array Chars :=
  (splitWhitespace s.reverse maxsplit).reverse.map Array.reverse

/-- `str.partition(sep)` with a non-empty separator: the part before the first `sep`, `sep`,
and the part after it; or `s` and two empty strings. -/
def partition (s sep : Chars) (hp : 0 < sep.size) : Chars × Chars × Chars :=
  match ((occurrences s sep hp 0 s.size 1)[0]? : Option Nat) with
  | some i => (slice s 0 i, sep, slice s (i + sep.size) s.size)
  | none => (s, #[], #[])

/-- `str.rpartition(sep)` with a non-empty separator: as `partition`, at the last `sep`; or two
empty strings and `s`. -/
def rpartition (s sep : Chars) : Chars × Chars × Chars :=
  match rfind s sep none none with
  | -1 => (#[], #[], s)
  | i => (slice s 0 i.toNat, sep, slice s (i.toNat + sep.size) s.size)

/-- `str.splitlines(keepends)`: the lines of `s`, split at the line boundaries, `\r\n` counting
as one; each line keeps its boundary if `keepends`. -/
def splitlines (s : Chars) (keepends : Bool) : Array Chars := go 0 0 #[]
where
  go (start i : Nat) (acc : Array Chars) : Array Chars :=
    if h : i < s.size then
      let c := s.getD i ' '
      if isLineBreak c then
        if c == '\r' && s.getD (i + 1) ' ' == '\n' then
          go (i + 2) (i + 2) (acc.push (slice s start (if keepends then i + 2 else i)))
        else go (i + 1) (i + 1) (acc.push (slice s start (if keepends then i + 1 else i)))
      else go start (i + 1) acc
    else if start < s.size then acc.push (slice s start s.size) else acc
  termination_by s.size - i
  decreasing_by all_goals omega

/-! ## Stripping -/

/-- `str.strip`, `lstrip` and `rstrip`: `s` without the characters of `cs` (whitespace if `cs` is
`none`) at its left end if `left`, and at its right end if `right`. -/
def strip (s : Chars) (cs : Option Chars) (left right : Bool) : Chars :=
  let drop (c : Char) : Bool := match cs with
    | none => isSpace c
    | some cs => cs.contains c
  let i := if left then fromLeft drop 0 else 0
  let j := if right then fromRight drop i s.size else s.size
  slice s i j
where
  /-- The first index from `i` on whose character is not dropped. -/
  fromLeft (drop : Char → Bool) (i : Nat) : Nat :=
    if i < s.size ∧ drop (s.getD i ' ') then fromLeft drop (i + 1) else i
  termination_by s.size - i
  /-- The end, down to `lo`, after the last character that is not dropped. -/
  fromRight (drop : Char → Bool) (lo : Nat) : Nat → Nat
    | 0 => 0
    | j + 1 => if lo < j + 1 ∧ drop (s.getD j ' ') then fromRight drop lo j else j + 1

/-- `str.removeprefix(prefix)`. -/
def removePrefix (s p : Chars) : Chars :=
  if slice s 0 p.size == p then slice s p.size s.size else s

/-- `str.removesuffix(suffix)`; an empty suffix removes nothing. -/
def removeSuffix (s p : Chars) : Chars :=
  if !p.isEmpty && p.size ≤ s.size && slice s (s.size - p.size) s.size == p then
    slice s 0 (s.size - p.size)
  else s

/-! ## Padding -/

/-- `n` copies of `c`. -/
def fill (n : Nat) (c : Char) : Chars := Array.replicate n c

/-- `str.ljust(width, fillchar)`. -/
def ljust (s : Chars) (width : Int) (c : Char) : Chars :=
  if width ≤ s.size then s else s ++ fill (width.toNat - s.size) c

/-- `str.rjust(width, fillchar)`. -/
def rjust (s : Chars) (width : Int) (c : Char) : Chars :=
  if width ≤ s.size then s else fill (width.toNat - s.size) c ++ s

/-- `str.center(width, fillchar)`: CPython puts the extra fill character on the left when both
the margin and `width` are odd. -/
def center (s : Chars) (width : Int) (c : Char) : Chars :=
  if width ≤ s.size then s
  else
    let marg := width.toNat - s.size
    let left := marg / 2 + (marg &&& width.toNat &&& 1)
    fill left c ++ s ++ fill (marg - left) c

/-- `str.zfill(width)`: zeros on the left, after a leading sign. -/
def zfill (s : Chars) (width : Int) : Chars :=
  if width ≤ s.size then s
  else
    let z := fill (width.toNat - s.size) '0'
    match s[0]? with
    | some c => if c == '+' || c == '-' then #[c] ++ z ++ slice s 1 s.size else z ++ s
    | none => z

/-- `str.expandtabs(tabsize)`: each tab becomes spaces up to the next multiple of `tabsize` (none
if `tabsize ≤ 0`); the column restarts after `\n` and `\r`. -/
def expandtabs (s : Chars) (tabsize : Int) : Chars :=
  (s.foldl (fun (acc, col) c =>
    if c == '\t' then
      if tabsize > 0 then
        let n := tabsize.toNat - col % tabsize.toNat
        (acc ++ fill n ' ', col + n)
      else (acc, col)
    else if c == '\n' || c == '\r' then (acc.push c, 0)
    else (acc.push c, col + 1)) (#[], 0)).1

end

end StrataPython.Dyn.Sem.Library.Str
