/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Set
public import StrataPython.Dyn.Sem.Hash
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Set
meta import StrataPython.Dyn.Sem.Hash

set_option autoImplicit false

/-!
# Set tables

The expected iteration orders, table layouts (the slots, `fill`, `used` and `finger`), pops and
comparison orders are what CPython 3.12.15 gives for the same operations on `int`s.  The other
`#guard`s check the model's own flag and counts.
-/

namespace StrataPython.Dyn.Sem.SetTest

open StrataPython.Dyn.Sem

/-- `s.add(i)`: a new entry, unless a candidate of the search holds `i`. -/
def addInt (t : SetTable) (i : Int) : SetTable :=
  let h : Hash := .exact (hashInt i)
  match t.search h with
  | some s => if s.candidates.any (fun j => match t.slot j with
      | .entry _ k _ => k == .int i | _ => false) then t else t.addNew s h (.int i) .builtin
  | none => t

/-- `s.discard(i)`. -/
def discardInt (t : SetTable) (i : Int) : SetTable :=
  let h : Hash := .exact (hashInt i)
  match t.search h with
  | some s => match s.candidates.find? (fun j => match t.slot j with
      | .entry _ k _ => k == .int i | _ => false) with
    | some j => t.discardAt j
    | none => t
  | none => t

/-- A set of `n` ints, `0` to `n - 1`. -/
def upTo (n : Nat) : SetTable :=
  (List.range n).foldl (fun t (i : Nat) => addInt t i) .empty

-- Every change of the slots increases the version: an add, a discard, a pop, a resize and a clear.
#guard (addInt (upTo 3) 7).version > (upTo 3).version
#guard (discardInt (upTo 3) 1).version > (upTo 3).version
#guard (match (upTo 3).pop with | some (_, t) => t.version > (upTo 3).version | none => false)
#guard ((upTo 3).resize 100).version > (upTo 3).version
#guard (upTo 3).clear.version > (upTo 3).version
-- No change of the slots leaves it alone: a resize that keeps an 8-slot table, and a put out of
-- range.
#guard ((upTo 3).resize 0).version == (upTo 3).version
#guard ((upTo 3).put 100 .empty).version == (upTo 3).version

/-- The set after the operations `ops`: `true` adds, `false` discards. -/
def run (ops : List (Bool × Int)) (t : SetTable := .empty) : SetTable :=
  ops.foldl (fun t (add, i) => if add then addInt t i else discardInt t i) t

/-- The members of `t`, in iteration order. -/
def members (t : SetTable) : List Value := t.active.map (·.2.2)

#guard members (run [(true, 27), (true, (-26)), (false, (-26)), (true, (-21)), (true, 59), (false, 27), (true, 73), (false, 59), (false, (-21)), (true, 272), (true, (-19)), (true, 153), (false, 73), (false, (-19)), (false, 153), (true, 242), (true, 299), (false, 299), (true, 46), (true, 230), (true, 238), (false, 230), (true, 222)]) == [.int 272, .int 242, .int 238, .int 222, .int 46]
#guard members (run [(true, 110), (true, 182), (true, 77), (true, 74), (false, 110), (true, 125), (true, 97), (true, (-13)), (false, 97), (false, 77), (false, 182), (true, 292), (false, 125), (true, 129), (true, 246), (true, (-15)), (true, 88), (true, 290), (false, 129), (true, 298), (true, 95), (true, 292), (true, 186), (true, 262), (false, (-15)), (false, 186), (false, 95), (true, 204), (false, 292), (true, 92)]) == [.int 290, .int 262, .int 74, .int 298, .int 204, .int (-13), .int 246, .int 88, .int 92]
#guard members (run [(true, 170), (true, 92), (true, 133), (true, 144), (true, 27), (false, 92), (false, 133), (false, 170), (false, 144), (false, 27), (true, 223)]) == [.int 223]
#guard members (run [(true, 262), (true, 14), (true, 213), (true, 285), (true, (-23)), (true, 298), (true, 150), (true, 151), (false, 285), (false, (-23)), (true, 175), (false, 151), (true, 2), (false, 14), (true, 136), (true, (-14)), (true, 264), (true, 274), (false, 213), (true, 192), (false, 264), (true, 188), (true, 109), (false, 2), (true, 85), (true, 32)]) == [.int 192, .int 32, .int 262, .int 136, .int 298, .int 109, .int 175, .int (-14), .int 274, .int 150, .int 85, .int 188]
#guard members (run [(true, (-39)), (false, (-39)), (true, 25), (true, (-37)), (true, 102), (true, (-4)), (true, 83), (true, 35), (true, 64), (true, 207), (true, 64), (true, 49), (true, 155), (true, 66), (false, 83), (true, (-36)), (true, 93), (true, 49), (true, 126), (true, 128), (true, 136), (false, (-36)), (false, 35), (true, 197), (true, 262), (true, 195), (true, 126), (true, (-7)), (true, 11), (true, 52), (true, 41), (true, 275), (true, 152), (true, (-7)), (true, 37), (true, (-36))]) == [.int 128, .int 262, .int 136, .int 11, .int 275, .int 152, .int 25, .int 155, .int 37, .int 41, .int 49, .int 52, .int 64, .int 66, .int 195, .int 197, .int 207, .int (-37), .int (-36), .int 93, .int 102, .int (-7), .int (-4), .int 126]
#guard members (run [(true, 252), (true, 285), (false, 285), (true, 129), (false, 129), (false, 252), (true, 219), (true, 21), (true, 49), (true, 58), (false, 49), (false, 21)]) == [.int 58, .int 219]
#guard members (run [(true, 116), (false, 116), (true, 17), (false, 17), (true, 184), (true, 214), (true, 206), (false, 184), (true, (-41)), (true, 43), (true, 26), (false, 206), (true, 11), (true, 116), (true, 221), (true, 4), (true, (-21)), (false, 26), (false, (-21)), (true, 237), (false, 4), (true, 263), (true, 260), (true, 91), (true, 223), (true, 209), (true, 217), (true, 82), (true, 53), (true, 20), (true, 150), (true, (-13)), (true, 169), (false, 150), (true, 29), (true, 279), (true, 23), (false, 23), (true, 62), (true, (-2))]) == [.int 260, .int 263, .int 11, .int 209, .int 82, .int 20, .int 214, .int (-41), .int 217, .int 279, .int 91, .int 221, .int 29, .int 223, .int 169, .int 43, .int 237, .int (-13), .int 116, .int 53, .int (-2), .int 62]
#guard members (run [(true, 199), (false, 199), (true, 32), (true, 213), (true, 165), (false, 165), (false, 213), (false, 32), (true, 175), (true, 146), (true, 269), (false, 146), (false, 175), (true, 3), (false, 269), (false, 3), (true, 88), (true, 166), (true, 296), (true, 82), (true, 224), (true, 242), (true, 117), (false, 82), (true, 43), (true, (-13)), (false, (-13)), (true, 83)]) == [.int 224, .int 166, .int 296, .int 43, .int 242, .int 83, .int 117, .int 88]

-- `pop` starts at the finger, which survives an `add`: after `{1, 2, 3}`, `pop()` gives 1;
-- after `add(1)`, the next `pop()` gives 2.
#guard (do
    let t := run [(true, 1), (true, 2), (true, 3)]
    let ((_, a), t) ← t.pop
    let t := addInt t 1
    let ((_, b), _) ← t.pop
    return (a, b)) == some (.int 1, .int 2)

-- Five pops from `set(range(20))` give [0, 1, 2, 3, 4], and leave the rest in CPython's order.
def popN : Nat → SetTable → List Value × SetTable
  | 0, t => ([], t)
  | n + 1, t => match t.pop with
    | some ((_, k), t') => let (ks, t'') := popN n t'; (k :: ks, t'')
    | none => ([], t)
#guard (popN 5 (run ((List.range 20).map fun (i : Nat) => (true, (i : Int))))).1 ==
  [.int 0, .int 1, .int 2, .int 3, .int 4]
#guard members (popN 5 (run ((List.range 20).map fun (i : Nat) => (true, (i : Int))))).2 ==
  [.int 5, .int 6, .int 7, .int 8, .int 9, .int 10, .int 11, .int 12, .int 13, .int 14, .int 15, .int 16, .int 17, .int 18, .int 19]

-- Hashes that wrap, and `-1`, whose hash is `-2`: {2**61 - 1, 2**61, -1, -2, 8, 16, 0}.
#guard members (run [(true, 2305843009213693951), (true, 2305843009213693952), (true, (-1)), (true, (-2)), (true, 8), (true, 16), (true, 0)]) ==
  [.int 2305843009213693951, .int 2305843009213693952, .int 0, .int 8, .int 16, .int (-2), .int (-1)]

-- The table grows as CPython's does: 5 adds to an empty set give a table of 32 slots.
#guard (run ((List.range 5).map fun (i : Nat) => (true, (i : Int)))).slots.size == 32
#guard (run ((List.range 4).map fun (i : Nat) => (true, (i : Int)))).slots.size == 8

/-- Adds the user objects `0 … n-1`, all with the exact hash `h`, as new members (their `__eq__`
is false), then the `int`s `1000 … 1000 + extra - 1`. -/
def collide (h : Int) (n extra : Nat) : SetTable :=
  let t := (List.range n).foldl (fun t id =>
    match t.search (Hash.exact h) with
    | some sr => t.addNew sr (.exact h) (.obj id) .user
    | none => t) SetTable.empty
  run ((List.range extra).map fun (i : Nat) => (true, ((1000 + i : Nat) : Int))) t

/-- The objects that a lookup of hash `h` compares, in order. -/
def compared (t : SetTable) (h : Int) : List ObjId :=
  match t.search (Hash.exact h) with
  | some sr => sr.candidates.filterMap fun i => match t.slot i with
    | .entry _ (.obj id) _ => some id
    | _ => none
  | none => []

-- A resize reinserts in table order, so four objects of one hash are compared in another order
-- than they were added (CPython 3.12.15, with a fifth object of the same hash as the key).
#guard compared (collide 1 4 1) 1 == [0, 3, 1, 2]
#guard compared (collide 2 4 1) 2 == [2, 3, 0, 1]
#guard compared (collide 3 4 1) 3 == [1, 2, 0, 3]
#guard compared (collide 1 4 0) 1 == [0, 1, 2, 3]

/-- The slots of `t`: `E` empty, `D` dummy, or an `int` member. -/
def slotText (t : SetTable) : List String := t.slots.toList.map fun
  | .empty => "E"
  | .dummy => "D"
  | .entry _ (.int i) _ => toString i
  | .entry .. => "?"

/-- The size, `fill`, `used` and `finger` of `t`. -/
def counts (t : SetTable) : List Nat := [t.slots.size, t.fill, t.used, t.finger]

-- A table of 8 slots full of dummies is rebuilt at 8 slots: `{1, 2, 3, 4}`, discard them all,
-- add 5.
def rebuilt : SetTable := run ([1, 2, 3, 4].map ((true, ·)) ++ [1, 2, 3, 4].map ((false, ·)) ++
  [(true, 5)])
#guard slotText rebuilt == ["E", "E", "E", "E", "E", "5", "E", "E"]
#guard counts rebuilt == [8, 1, 1, 0]

-- A table shrinks: `set(range(20))`, discard 0 to 18, then add and discard each of 100 to 176.
-- The add of 176 resizes the table from 128 slots to 16.
def shrunk : SetTable :=
  run ((List.range 20).map (fun (i : Nat) => (true, (i : Int))) ++
    (List.range 19).map (fun (i : Nat) => (false, (i : Int))) ++
    (List.range 77).flatMap fun (i : Nat) => [(true, ((100 + i : Nat) : Int)), (false, ((100 + i : Nat) : Int))])
#guard slotText shrunk == ["D", "E", "E", "19", "E", "E", "E", "E", "E", "E", "E", "E", "E", "E", "E", "E"]
#guard counts shrunk == [16, 2, 1, 0]

-- Past 50000 members the table grows by `used * 2`: `set(range(78643))` has 262144 slots, and
-- `set(range(78642))` has 131072.
#guard (run ((List.range 78643).map fun (i : Nat) => (true, (i : Int)))).slots.size == 262144
#guard (run ((List.range 78642).map fun (i : Nat) => (true, (i : Int)))).slots.size == 131072

-- A resize that keeps a table of 8 slots without dummies leaves it as it is, and so does a
-- `minused` below `used`.
#guard slotText ((run [(true, 1), (true, 9)]).resize 3) == slotText (run [(true, 1), (true, 9)])
#guard ((run [(true, 1), (true, 2), (true, 3), (true, 4)]).resize 0).used == 4

-- A new member takes the last dummy of its probe sequence: `{1, 9}`, discard 1, add 17.
def reused : SetTable := run [(true, 1), (true, 9), (false, 1), (true, 17)]
#guard slotText reused == ["E", "17", "E", "E", "E", "E", "9", "E"]
#guard counts reused == [8, 2, 2, 0] && members reused == [.int 17, .int 9]

-- `pop` wraps past the end: `{1, 6}`, pop, pop, add 3, pop gives 1, 6 and 3.
#guard (do
    let ((_, a), t) ← (run [(true, 1), (true, 6)]).pop
    let ((_, b), t) ← t.pop
    let ((_, c), t) ← (addInt t 3).pop
    return ([a, b, c], slotText t, counts t)) ==
  some ([.int 1, .int 6, .int 3], ["E", "D", "E", "D", "E", "E", "D", "E"], [8, 3, 0, 4])
-- `pop` of an empty set.
#guard (SetTable.empty.pop.map (·.1)) == none
-- `clear` keeps the finger: `{1, 6}`, pop, pop, clear, add 1 and 5; the next pop gives 1.
#guard (do
    let (_, t) ← (run [(true, 1), (true, 6)]).pop
    let (_, t) ← t.pop
    let t := run [(true, 1), (true, 5)] t.clear
    let ((_, a), _) ← t.pop
    return (counts t, a)) == some ([8, 2, 2, 7], .int 1)

-- A member placed by a placeholder number makes the layout inexact, and its removal doesn't
-- make it exact again: in CPython, `s.add("a"); s.add(4); s.add(12); s.discard("a")` gives
-- `[4, 12]` under some hash seeds and `[12, 4]` under others.  Only `clear` resets the flag.
def strA : Value := .ofString "a"
def hashA : Hash := .symbolic (.buffer [97])
def withA : SetTable :=
  match SetTable.empty.search hashA with
  | some sr => SetTable.empty.addNew sr hashA strA .builtin
  | none => .empty
def aGone : SetTable :=
  let t := run [(true, 4), (true, 12)] withA
  match t.search hashA with
  | some sr => match sr.candidates.head? with
    | some i => t.discardAt i
    | none => t
  | none => t
#guard SetTable.empty.exactLayout && !withA.exactLayout
#guard aGone.used == 2 && !aGone.exactLayout
#guard !(aGone.resize 8).exactLayout
#guard aGone.clear.exactLayout
-- A symbolic hash is placed by its source's hash.
#guard hashA.placement == hash (HashSrc.buffer [97])
-- A search keeps only the entries whose stored hash is the searched one: an exact hash whose
-- number is the placeholder of `"a"` finds no candidate.
#guard (withA.search (.exact (hashA.placement.toNat : Int))).map (·.candidates) == some []
#guard (withA.search hashA).map (·.candidates.length) == some 1

-- The groups: two user objects of one hash are one group; an `int` is another.
#guard (collide 1 2 1).groupCount .exact .user == 1
#guard (collide 1 2 1).groupCount .exact .builtin == 1
#guard withA.groupCount .otherSymbolic .builtin == 1 && aGone.groupCount .otherSymbolic .builtin == 0

-- `put` sets the flag itself when it places a symbolic hash.
#guard !(SetTable.empty.put 3 (.entry hashA strA .builtin)).exactLayout
#guard (SetTable.empty.put 3 (.entry (.exact 3) (.int 3) .builtin)).exactLayout
-- The groups of one kind, of any key class: an `int` and a user object of hash 1 are one.
#guard (collide 1 2 1).kindGroupCount .exact == 2
#guard (run [(true, 1)] (collide 1 1 0)).kindGroupCount .exact == 1

end StrataPython.Dyn.Sem.SetTest
