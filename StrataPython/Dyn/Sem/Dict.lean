/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.ValueProps
public import StrataPython.Dyn.Sem.Index

set_option autoImplicit false

/-!
# Dict tables

A Python dict's entries, in insertion order, as CPython 3.12's compact dict keeps them: an array
whose deleted entries are holes.  Iteration visits the live entries in order.

A lookup needs the entries whose hash equals the key's, in insertion order.  The simple version
scans the array (`DictTable.positions`); the table also keeps an `Index` by hash, which carries the
proof that it equals the scan, and `@[csimp]` swaps it in.  An index by the object id of the key
serves identity lookups, and one by the key itself, for the keys of class `user` that are not
objects (a tuple that holds one), serves the check of a key whose hash changed.  `Groups` count the distinct hashes of the
live entries by hash kind, and by hash kind and key class, for the check of possibly equal
hashes.

Two more fields serve the rules: `deleted`, a sticky flag set by a deletion and cleared only by
`clear`, and `keysVersion`, which changes whenever a key is added or removed, so that an iterator
sees a change of keys.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- What a key's equality may run, decided when the key is stored and fixed for its lifetime.
A tuple or a slice compares its members, so it takes the strongest class of its members,
recursively, in the order `builtin`, `symHash`, `user`, which is the order of the constructors
and of `compare`: `(K(),)` is `user` when `K` is a user class, and `(1, "a")` is `builtin`.  A
frozenset counts as `user`, conservatively. -/
inductive KeyClass where
  /-- A built-in value whose members, if any, are `builtin` too: an immediate, or an object whose
  type is exactly a built-in type.  Its equality never runs user code. -/
  | builtin
  /-- A `symHash` value, or a value with one as a member and no `user` member: two `symHash`
  values with different sources are possibly equal values. -/
  | symHash
  /-- An instance of a user class, or of a subclass of a built-in type (its type can gain an
  `__eq__` at any time), or a value with such a member. -/
  | user
  deriving DecidableEq, Repr, Inhabited, Ord

instance : Hashable KeyClass := ⟨fun k => hash k.ctorIdx⟩

/-- The kind of a stored hash, for the check of possibly equal hashes. -/
inductive HashKind where
  | exact
  | addr
  | otherSymbolic
  deriving DecidableEq, Repr, Inhabited, Ord

instance : Hashable HashKind := ⟨fun k => hash k.ctorIdx⟩

/-- The kind of `h`. -/
def Hash.kind : Hash → HashKind
  | .exact _ => .exact
  | .symbolic src => if src.isAddr then .addr else .otherSymbolic

/-- The key part of a dict's entry: the key's hash, the key, and its class.  The values are kept
apart, so that replacing a value leaves the indexes as they are. -/
structure DictEntry where
  hash : Hash
  key : Value
  cls : KeyClass
  deriving BEq, Repr

/-- The hash of an entry. -/
def DictEntry.hashKey : Option DictEntry → Option Hash := fun e? => e?.map (·.hash)

/-- The object id of an entry's key, if its key is an object. -/
def DictEntry.objKey : Option DictEntry → Option ObjId := fun e? => e?.bind fun e =>
  match e.key with
  | .obj id => some id
  | _ => none

/-- The key of an entry of class `user` that is not an object: a tuple or slice that holds one. -/
def DictEntry.userImmKey : Option DictEntry → Option Value := fun e? => e?.bind fun e =>
  match e.key, e.cls with
  | .obj _, _ => none
  | k, .user => some k
  | _, _ => none

/-- The hash kind and key class of an entry, with its hash. -/
def DictEntry.groupKey : Option DictEntry → Option ((HashKind × KeyClass) × Hash) := fun e? =>
  e?.map fun e => ((e.hash.kind, e.cls), e.hash)

/-- The hash kind of an entry, with its hash. -/
def DictEntry.kindKey : Option DictEntry → Option (HashKind × Hash) := fun e? =>
  e?.map fun e => (e.hash.kind, e.hash)

/-- A Python dict's entries, in insertion order, with their indexes. -/
structure DictTable where
  /-- The key part of each entry; a hole (`none`) where an entry was deleted. -/
  entries : Array (Option DictEntry)
  /-- The value of each entry, at the same position (`undef` at a hole). -/
  values : Array Value
  /-- The number of live entries. -/
  used : Nat
  /-- Whether a key was deleted since the dict was made or cleared. -/
  deleted : Bool
  /-- Changes whenever a key is added or removed. -/
  keysVersion : Nat
  byHash : Index (Option DictEntry) Hash DictEntry.hashKey entries
  byObj : Index (Option DictEntry) ObjId DictEntry.objKey entries
  byUserImm : Index (Option DictEntry) Value DictEntry.userImmKey entries
  groups : Groups (Option DictEntry) (HashKind × KeyClass) Hash DictEntry.groupKey entries
  kindGroups : Groups (Option DictEntry) HashKind Hash DictEntry.kindKey entries

namespace DictTable

/-- The empty dict. -/
def empty : DictTable := ⟨#[], #[], 0, false, 0, .empty, .empty, .empty, .empty, .empty⟩

instance : Inhabited DictTable := ⟨empty⟩

/-- The positions of the live entries with hash `h`, in insertion order: the scan. -/
def positions (t : DictTable) (h : Hash) : Array Nat := positionsBy DictEntry.hashKey t.entries h

/-- The same, through the index. -/
def positionsFast (t : DictTable) (h : Hash) : Array Nat := t.byHash.map.getD h #[]

/-- The index gives the scan's answer, for every table. -/
@[csimp] theorem positions_eq_positionsFast : @positions = @positionsFast := by
  funext t h
  exact (t.byHash.wf h).symm

/-- The positions of the live entries whose key is the object `id`, through its index. -/
def objPositions (t : DictTable) (id : ObjId) : Array Nat := t.byObj.map.getD id #[]

/-- The positions of the live entries of class `user` whose key is `k`, a tuple or slice, through
its index. -/
def userImmPositions (t : DictTable) (k : Value) : Array Nat := t.byUserImm.map.getD k #[]

/-- The number of distinct hashes of kind `k` among the live entries of key class `c`. -/
def groupCount (t : DictTable) (k : HashKind) (c : KeyClass) : Nat := t.groups.count (k, c)

/-- The number of distinct hashes of kind `k` among the live entries, of any key class. -/
def kindGroupCount (t : DictTable) (k : HashKind) : Nat := t.kindGroups.count k

/-- The key part of the live entry at position `i`, if there is one. -/
def entry? (t : DictTable) (i : Nat) : Option DictEntry := (t.entries[i]?).bind id

/-- The value at position `i` (`undef` if there is none). -/
def value (t : DictTable) (i : Nat) : Value := t.values.getD i (.undef "")

/-- `t` with an entry appended; the caller has found that its key is not in `t`. -/
def insertNew (t : DictTable) (e : DictEntry) (v : Value) : DictTable :=
  -- Taking `t` apart first leaves each array and map with one reference, so that it is updated in
  -- place.
  let ⟨entries, values, used, deleted, keysVersion, byHash, byObj, byUserImm, groups, kindGroups⟩ := t
  let byHash := byHash.push (some e)
  let byObj := byObj.push (some e)
  let byUserImm := byUserImm.push (some e)
  let groups := groups.push (some e)
  let kindGroups := kindGroups.push (some e)
  { entries := entries.push (some e), values := values.push v, used := used + 1, deleted,
    keysVersion := keysVersion + 1, byHash, byObj, byUserImm, groups, kindGroups }

/-- `t` with the value at position `i` replaced; the keys don't change. -/
def setValue (t : DictTable) (i : Nat) (v : Value) : DictTable :=
  { t with values := t.values.setIfInBounds i v }

/-- `t` with the live entry at position `i` deleted: a hole, and the deletion flag set. -/
def deleteAt (t : DictTable) (i : Nat) : DictTable :=
  let ⟨entries, values, used, deleted, keysVersion, byHash, byObj, byUserImm, groups, kindGroups⟩ := t
  if hi : i < entries.size then
    match entries[i] with
    | some _ =>
      let byHash := byHash.setNone i hi none rfl
      let byObj := byObj.setNone i hi none rfl
      let byUserImm := byUserImm.setNone i hi none rfl
      let groups := groups.set i hi none
      let kindGroups := kindGroups.set i hi none
      { entries := entries.set i none hi, values := values.setIfInBounds i (.undef ""),
        used := used - 1, deleted := true, keysVersion := keysVersion + 1, byHash, byObj, byUserImm, groups, kindGroups }
    | none => ⟨entries, values, used, deleted, keysVersion, byHash, byObj, byUserImm, groups, kindGroups⟩
  else ⟨entries, values, used, deleted, keysVersion, byHash, byObj, byUserImm, groups, kindGroups⟩

/-- `t` without its last slot, a hole. -/
def popHole (t : DictTable) (hb : t.entries.back? = some none) : DictTable :=
  match t, hb with
  | ⟨entries, values, used, deleted, keysVersion, byHash, byObj, byUserImm, groups, kindGroups⟩, hb =>
    let byHash := byHash.pop (by simp [hb, DictEntry.hashKey])
    let byObj := byObj.pop (by simp [hb, DictEntry.objKey])
    let byUserImm := byUserImm.pop (by simp [hb, DictEntry.userImmKey])
    let groups := groups.pop (by simp [hb, DictEntry.groupKey])
    let kindGroups := kindGroups.pop (by simp [hb, DictEntry.kindKey])
    { entries := entries.pop, values := values.pop, used, deleted, keysVersion, byHash, byObj,
      byUserImm, groups, kindGroups }

/-- `popHole` drops the last slot. -/
private theorem entries_popHole (t : DictTable) (hb : t.entries.back? = some none) :
    (t.popHole hb).entries = t.entries.pop := by
  cases t; rfl

/-- `t` without the holes at its end from position `n` on. -/
def dropHolesFrom (t : DictTable) (n : Nat) : DictTable :=
  if n < t.entries.size then
    match hb : t.entries.back? with
    | some none =>
      have hlt : (t.popHole hb).entries.size < t.entries.size := by
        have : 0 < t.entries.size := by
          rcases Nat.eq_zero_or_pos t.entries.size with h0 | h
          · simp [Array.eq_empty_of_size_eq_zero h0] at hb
          · exact h
        rw [entries_popHole]; simp [Array.size_pop]; omega
      (t.popHole hb).dropHolesFrom n
    | _ => t
  else t
termination_by t.entries.size

/-- The position of the last live entry, searching down from position `n - 1`. -/
def lastLive (t : DictTable) : Nat → Option Nat
  | 0 => none
  | n + 1 => if (t.entry? n).isSome then some n else t.lastLive n

/-- The position of the entry that `popitem` removes, the last live one, with the entry and its
value. -/
def popitemAt? (t : DictTable) : Option (Nat × DictEntry × Value) := do
  let i ← t.lastLive t.entries.size
  let e ← t.entry? i
  return (i, e, t.value i)

/-- `t` without its live entry at `i`, as `popitem` leaves it. -/
def removePopped (t : DictTable) (i : Nat) : DictTable := (t.deleteAt i).dropHolesFrom i

/-- `dict.popitem`: the last live entry with its value, and `t` without it.  The entry array then
ends at the popped entry's position, as CPython's `dk_nentries` does: the holes after that
position go, so that the next `popitem` doesn't pass them again, and the holes before it stay,
which a reverse iterator sees. -/
def popitem (t : DictTable) : Option ((DictEntry × Value) × DictTable) := do
  let (i, e, v) ← t.popitemAt?
  return ((e, v), t.removePopped i)

/-- `dict.clear`: no entries, the deletion flag cleared, and a new version of the keys. -/
def clear (t : DictTable) : DictTable := { empty with keysVersion := t.keysVersion + 1 }

/-- The live entries of `t`, in insertion order, with their values. -/
def live (t : DictTable) : Array (DictEntry × Value) :=
  (t.entries.zipIdx).filterMap fun (e?, i) => e?.map (·, t.value i)

/-- A dict with the live entries of `t`, in the same order, and no holes.  It keeps the deletion
flag of `t`. -/
def compact (t : DictTable) : DictTable :=
  let fresh := t.live.foldl (fun acc (e, v) => acc.insertNew e v) empty
  { fresh with deleted := t.deleted, keysVersion := t.keysVersion }

end DictTable

end

end StrataPython.Dyn.Sem
