/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Dict
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Dict

set_option autoImplicit false

/-!
# Dict tables

The entries' order, holes, flags and indexes of `DictTable`.
-/

namespace StrataPython.Dyn.Sem.DictTest

open StrataPython.Dyn.Sem

/-- An entry for the `int` key `i`, whose hash is `h`. -/
def intKey (i : Int) (h : Int := i) : DictEntry := ⟨.exact h, .int i, .builtin⟩

/-- An entry for the object key `id` of a user class, whose hash is `h`. -/
def objKey (id : ObjId) (h : Int) : DictEntry := ⟨.exact h, .obj id, .user⟩

/-- The keys of the live entries of `t`, in order. -/
def keys (t : DictTable) : List Value := t.live.toList.map (·.1.key)

/-- A dict with the int keys 1, 2, 3 (values 10, 20, 30). -/
def d123 : DictTable :=
  ((DictTable.empty.insertNew (intKey 1) (.int 10)).insertNew (intKey 2) (.int 20)).insertNew
    (intKey 3) (.int 30)

#guard keys d123 == [.int 1, .int 2, .int 3]
#guard d123.used == 3 && !d123.deleted
#guard d123.positions (.exact 2) == #[1]
#guard d123.positions (.exact 7) == #[]

-- A deletion leaves a hole, sets the sticky flag, and changes the keys' version.
def d13 : DictTable := d123.deleteAt 1
#guard keys d13 == [.int 1, .int 3]
#guard d13.used == 2 && d13.deleted
#guard d13.keysVersion != d123.keysVersion
#guard d13.positions (.exact 2) == #[]
#guard d13.entries.size == 3

-- Replacing a value keeps the keys and their version.
def d13v : DictTable := d13.setValue 2 (.int 99)
#guard d13v.value 2 == .int 99 && d13v.keysVersion == d13.keysVersion

-- An insert after a deletion goes to the end, and the flag stays set.
def d134 : DictTable := d13.insertNew (intKey 4) (.int 40)
#guard keys d134 == [.int 1, .int 3, .int 4]
#guard d134.deleted

-- Entries of one hash are found in insertion order.
def collide : DictTable :=
  ((DictTable.empty.insertNew (objKey 5 7) (.int 0)).insertNew (intKey 1) (.int 1)).insertNew
    (objKey 6 7) (.int 2)
#guard collide.positions (.exact 7) == #[0, 2]
#guard (collide.deleteAt 0).positions (.exact 7) == #[2]

-- The object index, and the groups: the two objects of hash 7 are one group.
#guard collide.objPositions 6 == #[2]
#guard collide.objPositions 9 == #[]
#guard (collide.deleteAt 2).objPositions 6 == #[]
#guard collide.groupCount .exact .user == 1
#guard collide.groupCount .exact .builtin == 1
#guard (collide.deleteAt 2).groupCount .exact .user == 1
#guard ((collide.deleteAt 2).deleteAt 0).groupCount .exact .user == 0
#guard ((DictTable.empty.insertNew (objKey 5 7) (.int 0)).insertNew (objKey 6 8) (.int 1)).groupCount
  .exact .user == 2

-- Compaction keeps the live entries, their order and values, and the deletion flag.
def compacted : DictTable := d134.compact
#guard keys compacted == [.int 1, .int 3, .int 4]
#guard compacted.entries.size == 3 && compacted.deleted
#guard compacted.positions (.exact 4) == #[2]
#guard (compacted.live.toList.map (·.2)) == [.int 10, .int 30, .int 40]

-- Deleting a hole or a position out of range changes nothing.
#guard (let t := d123.deleteAt 9
  keys t == keys d123 && t.used == 3 && !t.deleted && t.keysVersion == d123.keysVersion)
#guard (let t := d13.deleteAt 1
  keys t == keys d13 && t.used == 2 && t.entries.size == 3 && t.keysVersion == d13.keysVersion)

-- `popitem` takes the last live entry, and the table ends where it was, the hole before it kept:
-- in CPython, `d = {1: 10, 2: 20, 3: 30}; del d[2]` and then two `popitem()`s give `(3, 30)` and
-- `(1, 10)`, and after the first one `dk_nentries` is 2.
#guard (do
    let ((e, v), t) ← d13.popitem
    let ((e', v'), t') ← t.popitem
    return ([e.key, v, e'.key, v'], t.entries.size, t'.entries.size, t'.used, t'.popitem.isNone)) ==
  some ([.int 3, .int 30, .int 1, .int 10], 2, 0, 0, true)
#guard (DictTable.empty.popitem.map (·.1.2)) == none

-- `clear` empties the dict, resets the deletion flag, and gives the keys a new version.
#guard (let t := d13.clear
  keys t == [] && t.used == 0 && !t.deleted && t.keysVersion > d13.keysVersion)

-- The key classes are ordered by strength, so that the strongest class of a tuple's members is
-- their maximum.
#guard compare KeyClass.builtin .symHash == .lt && compare KeyClass.symHash .user == .lt

-- `{5: "a", K5(): "b"}`, where `K5.__hash__` returns 5: one exact hash, in two key classes.
def mixed : DictTable :=
  (DictTable.empty.insertNew (intKey 5) (.int 0)).insertNew (objKey 9 5) (.int 1)
#guard mixed.groupCount .exact .builtin == 1 && mixed.groupCount .exact .user == 1
#guard mixed.kindGroupCount .exact == 1 && mixed.kindGroupCount .addr == 0
#guard (mixed.deleteAt 0).kindGroupCount .exact == 1 && ((mixed.deleteAt 0).deleteAt 1).kindGroupCount .exact == 0

end StrataPython.Dyn.Sem.DictTest
