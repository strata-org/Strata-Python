/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Basics
public import StrataPython.Dyn.Sem.Hash
public import StrataPython.Dyn.Sem.Arith
public import StrataPython.Dyn.Sem.Invariant

set_option autoImplicit false

/-!
# Dict lookups

`dictLookup` finds a key in a dict table as CPython 3.12 does, in any monad that can stop with a
gap and, where the level allows it, choose:

* identity first, then the entries of the key's hash in insertion order, the stored key compared
  with the probe (`stored == key`);
* where a possibly equal hash meets a key whose comparison could run user code, or a symbolic
  hash value, a choice of which groups of entries collide; two built-in keys compare without
  user code and draw nothing;
* a gap where the answer depends on CPython's table layout: after a false comparison when user
  code could run, after a deletion when user code could run, and for a probe whose hash changed
  since the dict stored it (CPython may still find it by identity); and a gap when the dict
  changes during a comparison.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- Whether two floats are equal as numbers (`0.0 == -0.0`), or `none` for a NaN, whose
comparison inside a container depends on identity. -/
def floatEq (a b : UInt64) : Option Bool :=
  if Arith.isNaN a || Arith.isNaN b then none
  else some (a == b || (Arith.isZero a && Arith.isZero b))

/-- `a == b` for two values that are not objects, as CPython 3.12 compares them, where that
needs no protocol: numbers by value (`True == 1`, `1 == 1.0`), strings and bytes by content,
tuples and slices member by member, ranges as sequences, and constants by identity; values of
two other kinds are never equal.  `none` where the model doesn't decide it yet: a NaN against a
float, a symbolic hash, a bound method. -/
def pyEqImm : Value → Value → Option Bool
  | .int a, .int b => some (a == b)
  | .bool a, .bool b => some (a == b)
  | .int a, .bool b | .bool b, .int a => some (a == if b then 1 else 0)
  | .float a, .float b => floatEq a b
  | .str a, .str b => some (a.s == b.s)
  | .bytes a, .bytes b => some (a == b)
  | .tuple xs, .tuple ys =>
    if xs.size ≠ ys.size then some false
    else (xs.attach.zip ys).foldl (fun acc (⟨x, _⟩, y) => match acc with
      | some true => pyEqImm x y
      | r => r) (some true)
  | .slice a b c, .slice d e f => do
    if !(← pyEqImm a d) then return false
    if !(← pyEqImm b e) then return false
    pyEqImm c f
  | .range a b c, .range d e f =>
    let n := rangeLen a b c
    let m := rangeLen d e f
    some (n == m && (n == 0 || (a == d && (n == 1 || c == f))))
  | a, b =>
    if a.isConstant && b.isConstant then some (a == b)
    else match a, b with
      | .float x, .int y => some (Arith.compare .eq (.float x) (.int y))
      | .int x, .float y => some (Arith.compare .eq (.int x) (.float y))
      | .float x, .bool y => some (Arith.compare .eq (.float x) (.bool y))
      | .bool x, .float y => some (Arith.compare .eq (.bool x) (.float y))
      | .symHash _, _ | _, .symHash _ | .bound .., _ | _, .bound .. | .method .., _
      | _, .method .. | .traceback, _ | _, .traceback | .undef _, _ | _, .undef _
      | .obj _, _ | _, .obj _ => none
      | _, _ => some false
termination_by a => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ xs›; omega)

/-- Whether two different hashes may be equal in some runs and not in others: at least one is
symbolic, and they are not the addresses of two different objects. -/
def Hash.possiblyEq (a b : Hash) : Bool :=
  a != b && !(a.kind == .exact && b.kind == .exact) && !(a.kind == .addr && b.kind == .addr)

/-- Whether a comparison of a probe of class `kc` with a stored key of class `c` could run user
code. -/
def KeyClass.mayRunUser (kc c : KeyClass) : Bool := kc == .user || c == .user

/-- Whether a lookup of a probe of class `kc` must consider a collision with a stored key of class
`c`: unless both are built-in values, whose comparison is false whenever their hashes differ. -/
def KeyClass.collides (kc c : KeyClass) : Bool := kc != .builtin || c != .builtin

/-- What a lookup needs from its monad. -/
structure LookupOps.{u} (m : Type → Type u) where
  /-- Stop with a gap. -/
  gap : {α : Type} → String → m α
  /-- A number below `n + 1`, chosen; `none` at a level that allows no choice. -/
  chooser : Option (Nat → m Nat)
  /-- `stored == probe` for a stored key, where it may run user code. -/
  eq : Value → m Bool
  /-- The dict's keys' version now, to see a change during a comparison. -/
  keysVersion : m Nat

/-- The number of groups of kind `k`, other than `h`'s own, that a probe of class `kc` must
consider, in a table whose groups by hash kind and key class are `groups` and whose groups by hash
kind are `kinds`: every group of the kind when the probe may run user code or is a symbolic hash
value, and otherwise the groups with a key of class `symHash` or `user`. -/
def collisionCount (groups : Std.HashMap (HashKind × KeyClass) (Std.HashMap Hash Nat))
    (kinds : Std.HashMap HashKind (Std.HashMap Hash Nat)) (kc : KeyClass) (h : Hash)
    (k : HashKind) : Nat :=
  if kc != .builtin then
    (kinds.getD k ∅).size - (if h.kind == k && (kinds.getD k ∅).contains h then 1 else 0)
  else
    let s := groups.getD (k, .symHash) ∅
    let u := groups.getD (k, .user) ∅
    let both := s.fold (init := 0) fun n g _ => if u.contains g then n + 1 else n
    s.size + u.size - both - (if h.kind == k && (s.contains h || u.contains h) then 1 else 0)

/-- The hashes of the groups that a probe of class `kc` and hash `h` must consider, by kind, in
the order of the entries `es` (hash and class): exact, address, other symbolic. -/
def collisionHashesOf (es : List (Hash × KeyClass)) (kc : KeyClass) (h : Hash) :
    Array Hash × Array Hash × Array Hash :=
  es.foldl (init := (#[], #[], #[])) fun (ex, ad, os) (eh, ec) =>
    if eh != h && h.possiblyEq eh && kc.collides ec then
      match eh.kind with
      | .exact => if ex.contains eh then (ex, ad, os) else (ex.push eh, ad, os)
      | .addr => if ad.contains eh then (ex, ad, os) else (ex, ad.push eh, os)
      | .otherSymbolic => if os.contains eh then (ex, ad, os) else (ex, ad, os.push eh)
    else (ex, ad, os)

namespace DictTable

/-- `collisionCount` in the dict table `t`. -/
def collisionGroups (t : DictTable) (kc : KeyClass) (h : Hash) (k : HashKind) : Nat :=
  collisionCount t.groups.map t.kindGroups.map kc h k

/-- `collisionHashesOf` the live entries of `t`, in order. -/
def collisionHashes (t : DictTable) (kc : KeyClass) (h : Hash) :
    Array Hash × Array Hash × Array Hash :=
  collisionHashesOf (t.entries.toList.filterMap fun e? => e?.map fun e => (e.hash, e.cls)) kc h

end DictTable

section
universe u
variable {m : Type → Type u} [Monad m]

/-- `stored == probe` for the stored entry `e` and the probe `k` of class `kc`: identity first;
two keys that may run user code through `eq`; two built-in keys by `pyEqImm`; two symbolic hash
values by their sources, a gap for different ones. -/
def lookupCompare (ops : LookupOps m) (kc : KeyClass) (k : Value) (e : DictEntry) : m Bool :=
  match e.key, k with
  | .obj a, .obj b => if a == b then pure true else
    if kc.mayRunUser e.cls then ops.eq e.key else ops.gap "comparing two objects is not modelled yet"
  | stored, probe =>
    if kc.mayRunUser e.cls then ops.eq stored
    else match stored, probe with
      | .symHash a, .symHash b =>
        if a == b then pure true
        else ops.gap "== on two possibly equal symbolic hash values depends on the hash seed"
      | _, _ => match pyEqImm stored probe with
        | some r => pure r
        | none => ops.gap "comparing these dict keys is not modelled yet"

/-- Compare the probe with the candidates `cs` in order, until one is equal: after a false
comparison, a gap if that one or a later one could run user code, since CPython's table layout
decides their order and whether one is compared again; a gap if the dict's keys change during a
comparison. -/
def lookupLoop (ops : LookupOps m) (t : DictTable) (kc : KeyClass) (k : Value) (v0 : Nat) :
    List Nat → m (Option Nat)
  | [] => pure none
  | i :: rest => do
    let some e := t.entry? i | lookupLoop ops t kc k v0 rest
    let r ← lookupCompare ops kc k e
    if (← ops.keysVersion) != v0 then
      ops.gap "a dict that changes during a lookup is not modelled yet"
    if r then pure (some i) else
    if kc.mayRunUser e.cls || rest.any (fun j => (t.entry? j).any (kc.mayRunUser ·.cls)) then
      ops.gap "a dict lookup after a false __eq__ depends on CPython's table layout"
    lookupLoop ops t kc k v0 rest

/-- **The position of the key `k`**, of class `kc` and hash `h`, in the dict table `t`, as CPython
3.12 finds it, or `none`. -/
def dictLookup (ops : LookupOps m) (t : DictTable) (k : Value) (kc : KeyClass) (h : Hash) :
    m (Option Nat) := do
  if kc == .user then
    let moved : Bool := match k with
      | .obj id => (t.objPositions id).any fun i => (t.entry? i).any (·.hash != h)
      | _ => (t.userImmPositions k).any fun i => (t.entry? i).any (·.hash != h)
    if moved then
      ops.gap "a lookup of a key whose hash changed after it was stored depends on CPython's table layout"
  let e := if h.kind == .exact then 0 else t.collisionGroups kc h .exact
  let a := if h.kind == .addr then 0 else t.collisionGroups kc h .addr
  let b := t.collisionGroups kc h .otherSymbolic
  let pick ← if b == 0 && e == 0 && a == 0 then pure 0 else match ops.chooser with
    | some choose => choose (2 ^ b * (1 + e) * (1 + a) - 1)
    | none => ops.gap "a dict lookup where hashes may collide, at a level without choices"
  let cands : List Nat ← if pick == 0 then pure (t.positions h).toList else do
    let (exs, ads, oss) := t.collisionHashes kc h
    if exs.size != e || ads.size != a || oss.size != b then
      ops.gap (modelInvariantPrefix ++ "the group counts of a dict table disagree with its entries")
    let ei := pick % (1 + e)
    let r := pick / (1 + e)
    let ai := r % (1 + a)
    let bits := r / (1 + a)
    let chosen : Array Hash :=
      (if ei == 0 then #[] else exs[ei - 1]?.toArray) ++ (if ai == 0 then #[] else ads[ai - 1]?.toArray) ++
        (oss.zipIdx.filterMap fun (g, j) => if bits.testBit j then some g else none)
    pure ((List.range t.entries.size).filter fun i =>
      (t.entry? i).any fun en => en.hash == h || chosen.contains en.hash)
  if t.deleted && cands.length ≥ 2 &&
      (kc == .user || cands.any fun j => (t.entry? j).any (·.cls == .user)) then
    ops.gap "a dict lookup after a deletion depends on CPython's table layout"
  lookupLoop ops t kc k (← ops.keysVersion) cands

/-- Compare the probe with the set entries at the slots `cs` in order, until one is equal; a gap
if `unchanged` says that the set changed during a comparison that may run user code.  Unless the
order is CPython's (`ordered`), also a gap after a false comparison if that entry or a later one
may run user code: CPython's probe sequence may visit an entry's slot again and compare it again,
as often as its layout decides. -/
def setLoop (ops : LookupOps m) (unchanged : m Bool) (t : SetTable) (kc : KeyClass) (k : Value)
    (ordered : Bool) : List Nat → m (Option Nat)
  | [] => pure none
  | i :: rest => do
    let .entry eh ek ec := t.slot i | setLoop ops unchanged t kc k ordered rest
    let r ← lookupCompare ops kc k ⟨eh, ek, ec⟩
    if kc.mayRunUser ec then
      if !(← unchanged) then ops.gap "a set that changes during a lookup is not modelled yet"
    if r then pure (some i) else
    if !ordered && (kc.mayRunUser ec || rest.any fun j => match t.slot j with
        | .entry _ _ c => kc.mayRunUser c
        | _ => false) then
      ops.gap "a set lookup after a false __eq__ depends on CPython's table layout"
    setLoop ops unchanged t kc k ordered rest

/-- **The slot of the key `k`**, of class `kc` and hash `h`, in the set table `t`, as CPython 3.12
finds it, or `none`.  The entries with the hash `h` are those that the search of `h` finds
(`SetTable.search`).  While the table's layout is exact, they are compared in CPython's order;
otherwise their order may differ from CPython's, which is a gap where a comparison may run user
code.  Hashes that may collide are chosen among, as in `dictLookup`. -/
def setLookup (ops : LookupOps m) (unchanged : m Bool) (t : SetTable) (k : Value) (kc : KeyClass)
    (h : Hash) : m (Option Nat) := do
  let count := collisionCount t.groups.map t.kindGroups.map kc h
  let e := if h.kind == .exact then 0 else count .exact
  let a := if h.kind == .addr then 0 else count .addr
  let b := count .otherSymbolic
  let pick ← if b == 0 && e == 0 && a == 0 then pure 0 else match ops.chooser with
    | some choose => choose (2 ^ b * (1 + e) * (1 + a) - 1)
    | none => ops.gap "a set lookup where hashes may collide, at a level without choices"
  -- `t.active` walks the whole table, so only the paths that need it compute it.
  let classOf (i : Nat) : Option KeyClass := match t.slot i with
    | .entry _ _ c => some c
    | _ => none
  let (cands, ordered) ← if pick == 0 then
      -- Every entry is placed along the probe sequence of its own hash's number, also in a layout
      -- that isn't CPython's, so the search finds every entry with the hash `h`; only its order is
      -- CPython's just for an exact layout.
      match t.search h with
        | some s =>
          pure (if t.exactLayout then (s.candidates, true) else (s.candidates.eraseDups, false))
        | none => ops.gap (modelInvariantPrefix ++ "a set table without an empty slot")
    else do
      let active := t.active
      let (exs, ads, oss) := collisionHashesOf
        (active.filterMap fun (i, eh, _) => (classOf i).map (eh, ·)) kc h
      if exs.size != e || ads.size != a || oss.size != b then
        ops.gap
          (modelInvariantPrefix ++ "the group counts of a set table disagree with its entries")
      let ei := pick % (1 + e)
      let r := pick / (1 + e)
      let ai := r % (1 + a)
      let bits := r / (1 + a)
      let chosen : Array Hash :=
        (if ei == 0 then #[] else exs[ei - 1]?.toArray) ++
          (if ai == 0 then #[] else ads[ai - 1]?.toArray) ++
          (oss.zipIdx.filterMap fun (g, j) => if bits.testBit j then some g else none)
      pure ((active.filter fun (_, eh, _) => eh == h || chosen.contains eh).map (·.1), false)
  if !ordered && cands.length ≥ 2 &&
      (kc == .user || cands.any fun i => classOf i == some .user) then
    ops.gap "a set lookup whose order of comparisons depends on the table's layout"
  setLoop ops unchanged t kc k ordered cands

end

end

end StrataPython.Dyn.Sem
