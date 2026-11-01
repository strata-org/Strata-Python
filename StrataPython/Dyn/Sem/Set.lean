/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Dict

set_option autoImplicit false

/-!
# Set tables

CPython 3.12's `setobject.c` table: its slots (empty, dummy or an entry with its hash), `fill`
(entries and dummies), `used` (entries), its probing (`LINEAR_PROBES = 9`, `PERTURB_SHIFT = 5`),
the slot `set_add_entry` takes (the last dummy of the probe sequence, else the empty slot that
ends it), `set_table_resize`'s policy, `set_insert_clean`, and `set_pop`'s `finger`.

While every entry that was ever placed in the table had an exact hash, the table is CPython's,
so iteration in table order is CPython's order, and so is the sequence of entries that a lookup
compares, revisits included.  An entry whose hash is symbolic is placed by a placeholder number
(`Hash.placement`), which can move the entries that collide with it, and they stay moved after
it is gone.  So placing one sets the sticky flag `inexact`, which only `clear` resets; a set
built from an inexact set must keep it.

`Groups` count the distinct hashes of the entries by hash kind, and by hash kind and key class,
for the check of possibly equal hashes.  The functions here don't compare keys: `SetTable.search` gives the
entries whose stored hash equals the given one, in the order CPython compares them, and the rules
compare them.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- The number that places a hash in a table: an exact hash's own number, or a placeholder for a
symbolic one. -/
def Hash.placement : Hash → UInt64
  | .exact h => UInt64.ofInt h
  | .symbolic src => hash src

/-- A slot of a set's table. -/
inductive SetSlot where
  | empty
  /-- A deleted entry: CPython's `dummy`. -/
  | dummy
  | entry (hash : Hash) (key : Value) (cls : KeyClass)
  deriving BEq, Repr

/-- The hash kind and key class of an entry, with its hash. -/
def SetSlot.groupKey : SetSlot → Option ((HashKind × KeyClass) × Hash)
  | .entry h _ c => some ((h.kind, c), h)
  | _ => none

/-- The hash kind of an entry, with its hash. -/
def SetSlot.kindKey : SetSlot → Option (HashKind × Hash)
  | .entry h _ _ => some (h.kind, h)
  | _ => none

/-- Whether a slot holds an entry placed by a placeholder number: one with a symbolic hash. -/
def SetSlot.isPlaceholder : SetSlot → Bool
  | .entry (.symbolic _) _ _ => true
  | _ => false

/-- A Python set's table. -/
structure SetTable where
  /-- The slots; their number is a power of two, at least 8. -/
  slots : Array SetSlot
  /-- The number of entries and dummies. -/
  fill : Nat
  /-- The number of entries. -/
  used : Nat
  /-- Where `pop` starts its scan. -/
  finger : Nat
  /-- Whether the table's order may differ from CPython's: an entry was placed by a placeholder
  number since the set was made or cleared, or the set was built from an inexact set. -/
  inexact : Bool
  /-- A count of the changes of the slots, so that a lookup sees in one step whether user code
  changed the set during a comparison.  It never repeats a value for one set: a write that gives
  the set another table keeps counting from the set's own version. -/
  version : Nat
  groups : Groups SetSlot (HashKind × KeyClass) Hash SetSlot.groupKey slots
  kindGroups : Groups SetSlot HashKind Hash SetSlot.kindKey slots

namespace SetTable

/-- CPython's `PySet_MINSIZE`. -/
def minSize : Nat := 8

/-- The empty set. -/
def empty : SetTable := ⟨Array.replicate minSize .empty, 0, 0, 0, false, 0, .build _, .build _⟩

instance : Inhabited SetTable := ⟨empty⟩

/-- CPython's `mask`: the number of slots, minus one. -/
def mask (t : SetTable) : Nat := t.slots.size - 1

/-- Whether the table's layout is CPython's. -/
def exactLayout (t : SetTable) : Bool := !t.inexact

/-- The slot at `i` (`empty` out of range). -/
def slot (t : SetTable) (i : Nat) : SetSlot := t.slots.getD i .empty

/-- The number of distinct hashes of kind `k` among the entries of key class `c`. -/
def groupCount (t : SetTable) (k : HashKind) (c : KeyClass) : Nat := t.groups.count (k, c)

/-- The number of distinct hashes of kind `k` among the entries, of any key class. -/
def kindGroupCount (t : SetTable) (k : HashKind) : Nat := t.kindGroups.count k

/-- `t` with slot `i` replaced by `x` (nothing out of range), the flag `inexact` set if `x` is
placed by a placeholder number, and `version` increased by one.  `fill` and `used` don't change. -/
def put (t : SetTable) (i : Nat) (x : SetSlot) : SetTable :=
  -- Taking `t` apart first leaves the slots and the groups with one reference, so that they are
  -- updated in place.
  let ⟨slots, fill, used, finger, inexact, version, groups, kindGroups⟩ := t
  if hi : i < slots.size then
    let groups := groups.set i hi x
    let kindGroups := kindGroups.set i hi x
    ⟨slots.set i x hi, fill, used, finger, inexact || x.isPlaceholder, version + 1, groups,
      kindGroups⟩
  else ⟨slots, fill, used, finger, inexact, version, groups, kindGroups⟩

/-- CPython's probing of a table of `mask + 1` slots, for at most `rounds` rounds from the slot
`i`, with `perturb` starting at the hash's number: each round visits slot `i` and, if there is
room before the end, the 9 that follow it; then `perturb >>= 5` and
`i = (i * 5 + 1 + perturb) & mask`.  `step` sees each slot and stops the walk with a result, or
goes on with a new state; `none` if the rounds run out. -/
def probe {σ β : Type} (mask : Nat) (step : σ → Nat → Except β σ) :
    (rounds : Nat) → (perturb : UInt64) → (i : Nat) → σ → Option β
  | 0, _, _, _ => none
  | rounds + 1, perturb, i, s =>
    let probes := if i + 9 ≤ mask then 9 else 0
    match (List.range (probes + 1)).foldlM (fun s j => step s (i + j)) s with
    | .error b => some b
    | .ok s =>
      let perturb' := perturb >>> 5
      probe mask step rounds perturb' ((i * 5 + 1 + perturb'.toNat) % (mask + 1)) s

/-- Enough rounds to reach every slot: `perturb` is `0` after 13 shifts, and then
`i = (i * 5 + 1) & mask` visits every slot of a power-of-two table within `mask + 1` rounds. -/
def enoughRounds (size : Nat) : Nat := 13 + size

/-- What a search for a hash finds. -/
structure Search where
  /-- The entries whose stored hash is the searched one, in the order CPython compares them,
  revisits included.  Each is a slot index. -/
  candidates : List Nat
  /-- The empty slot that ends the search. -/
  emptyAt : Nat
  /-- The last dummy that the search passed: where `set_add_entry` puts a new entry. -/
  freeslot : Option Nat
  deriving Repr, BEq

/-- CPython's search for the hash `h`, along the probe sequence of its number, up to its first
empty slot; `none` if no empty slot is reached, which a table that `SetTable`'s functions build
never gives (its `fill` stays below three fifths of its size). -/
def search (t : SetTable) (h : Hash) : Option Search :=
  let num := h.placement
  probe t.mask step (enoughRounds t.slots.size) num (num.toNat % t.slots.size) ([], none)
where
  step : List Nat × Option Nat → Nat → Except Search (List Nat × Option Nat)
    | (cands, free), i =>
      match t.slot i with
      | .empty => .error ⟨cands.reverse, i, free⟩
      | .dummy => .ok (cands, some i)
      | .entry h' _ _ => .ok (if h' == h then i :: cands else cands, free)

/-- `set_insert_clean`: `slots` with `e` in the first empty slot of the probe sequence of the
number `num` (a table being rebuilt has no dummies). -/
def insertClean (slots : Array SetSlot) (num : UInt64) (e : SetSlot) : Array SetSlot :=
  let step : Unit → Nat → Except Nat Unit := fun _ i =>
    if slots.getD i .dummy == .empty then .error i else .ok ()
  match probe (slots.size - 1) step (enoughRounds slots.size) num (num.toNat % slots.size) () with
  | some i => slots.setIfInBounds i e
  | none => slots

/-- The table, after reinserting `t`'s entries in table order into a new table whose size is the
smallest power of two above `max minused t.used` (at least 8): CPython's `set_table_resize`,
with `set_insert_clean`.  A table of 8 slots without dummies that stays at 8 slots is left as it
is.  It keeps the finger and the flag. -/
def resize (t : SetTable) (minused : Nat) : SetTable :=
  let minused := max minused t.used
  let size := Id.run do
    let mut s := minSize
    for _ in [0:64] do
      if s ≤ minused then s := s * 2
    return s
  if size == minSize && t.slots.size == minSize && t.fill == t.used then t else
  let entries := t.slots.filter fun | .entry .. => true | _ => false
  let slots := entries.foldl (fun (acc : Array SetSlot) e => match e with
    | .entry h _ _ => insertClean acc h.placement e
    | _ => acc) (Array.replicate size SetSlot.empty)
  { slots, fill := entries.size, used := entries.size, finger := t.finger, inexact := t.inexact,
    version := t.version + 1, groups := .build slots, kindGroups := .build slots }

/-- `t` with a new entry for `key` of hash `h`, where the search `s` for `h` found no equal key:
`set_add_entry`'s `found_unused_or_dummy`.  It goes to the search's last dummy if there is one,
else to its empty slot, and then the table grows as CPython's does. -/
def addNew (t : SetTable) (s : Search) (h : Hash) (key : Value) (cls : KeyClass) : SetTable :=
  let e := SetSlot.entry h key cls
  let used := t.used + 1
  match s.freeslot with
  | some i => { t.put i e with used }
  | none =>
    let fill := t.fill + 1
    let t' : SetTable := { t.put s.emptyAt e with fill, used }
    if t'.fill * 5 < t'.mask * 3 then t'
    else t'.resize (if t'.used > 50000 then t'.used * 2 else t'.used * 4)

/-- `t` with the entry at slot `i` deleted: a dummy (`set_discard_entry`). -/
def discardAt (t : SetTable) (i : Nat) : SetTable :=
  match t.slot i with
  | .entry .. =>
    let used := t.used - 1
    { t.put i .dummy with used }
  | _ => t

/-- The entries of `t`, in table order, with their slots. -/
def active (t : SetTable) : List (Nat × Hash × Value) :=
  (List.range t.slots.size).filterMap fun i => match t.slot i with
    | .entry h k _ => some (i, h, k)
    | _ => none

/-- The first slot from `i` on that holds an entry, wrapping around, within `fuel` slots. -/
def nextEntry (t : SetTable) : (fuel : Nat) → (i : Nat) → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    match t.slot i with
    | .entry .. => some i
    | _ => t.nextEntry fuel ((i + 1) % t.slots.size)

/-- The slot of the member that `pop` removes, with its hash and the member. -/
def popAt? (t : SetTable) : Option (Nat × Hash × Value) :=
  if t.used = 0 then none
  else
    match t.nextEntry t.slots.size (t.finger % t.slots.size) with
    | some i => match t.slot i with
      | .entry h k _ => some (i, h, k)
      | _ => none
    | none => none

/-- `t` without its member at slot `i`, with the finger after it, as `pop` leaves it. -/
def removePopped (t : SetTable) (i : Nat) : SetTable := { t.discardAt i with finger := i + 1 }

/-- `set_pop`: the first entry from the finger on, wrapping around, and the table without it,
with the finger after it; `none` for an empty set. -/
def pop (t : SetTable) : Option ((Hash × Value) × SetTable) :=
  t.popAt?.map fun (i, h, k) => ((h, k), t.removePopped i)

/-- `set_clear_internal`: an empty table of the minimum size, keeping the finger. -/
def clear (t : SetTable) : SetTable := { empty with finger := t.finger, version := t.version + 1 }

end SetTable

end

end StrataPython.Dyn.Sem
