/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.DictLookup
meta import StrataPython.Dyn.Sem.DictLookup

set_option autoImplicit false

/-!
# Dict lookups

`dictLookup` run in a monad whose choices come from a list of answers and whose gaps are errors:

* two built-in keys compare without a choice;
* a symbolic hash value as the probe chooses among the possibly equal groups: the answer
  `0` finds nothing, and a chosen collision with a `str` key stops with a gap;
* a user key's `__eq__` decides, a false one gaps, and so does a lookup after a deletion where
  user code could run;
* a probe object, or a tuple that holds one, stored under another hash gaps;
* the choice among exact, address and other symbolic groups decodes to the chosen groups;
* a needed choice gaps where the level allows none, and so does a change of the keys during a
  comparison;
* a false comparison doesn't gap when the probe and every candidate are structural, on the exact
  branch only, and `Value.structuralImm?` decides the values other than tuples, slices and
  objects.
-/

namespace StrataPython.Dyn.Sem.DictLookupTest

open StrataPython.Dyn.Sem

/-- A lookup's monad: the oracle's answers, then the comparisons it ran, and gaps as errors. -/
abbrev M := StateT (List Nat × List String) (Except String)

/-- The operations, with `user` deciding the user comparisons, `version` giving the keys'
version after each comparison, `choices` whether the level allows a choice, and `structural`
which keys run no user code. -/
def ops (user : Value → Bool) (version : M Nat := pure 0) (choices : Bool := true)
    (structural : Value → Bool := fun _ => false) : LookupOps M where
  gap msg := throw msg
  chooser := if !choices then none else some fun n => do
    let (as, log) ← get
    match as with
    | a :: rest => set (rest, log ++ [s!"choose {n}"]); pure (a % (n + 1))
    | [] => set (as, log ++ [s!"choose {n}"]); pure 0
  eq stored := do
    modify fun (as, log) => (as, log ++ [s!"eq {reprStr stored}"])
    pure (user stored)
  keysVersion := version
  structural k ks := do
    modify fun (as, log) => (as, log ++ ["structural"])
    pure ((k :: ks).all structural)

/-- A dict of the entries `es`: hash, key, class. -/
def table (es : List (Hash × Value × KeyClass)) : DictTable :=
  es.foldl (fun t (h, k, c) => t.insertNew ⟨h, k, c⟩ (.int 0)) .empty

/-- Look `k` up, with the oracle's answers `as`: the position found and what ran, or the gap. -/
def look (t : DictTable) (k : Value) (kc : KeyClass) (h : Hash) (as : List Nat := [])
    (user : Value → Bool := fun _ => false) (version : M Nat := pure 0) (choices : Bool := true)
    (structural : Value → Bool := fun _ => false) :
    Except String (Option Nat × List String) :=
  (dictLookup (ops user version choices structural) t k kc h |>.run (as, [])).map
    fun (r, _, log) => (r, log)

/-- The gap of a lookup that stops with one. -/
def gapOf (r : Except String (Option Nat × List String)) : Option String :=
  match r with
  | .error m => some m
  | .ok _ => none

def a : Value := .ofString "a"
def b : Value := .ofString "b"
def ha : Hash := strHash (.ofString "a")
def hb : Hash := strHash (.ofString "b")
def strs : DictTable := table [(ha, a, .builtin), (hb, b, .builtin)]

-- Two built-in keys: found by equal hash, no choice.
#guard (look strs b .builtin hb).toOption == some (some 1, [])
-- A built-in probe of another hash: not there, no choice.
#guard (look strs (.int 5) .builtin (.exact 5)).toOption == some (none, [])

-- A symbolic hash value as the probe: two other symbolic groups, so four kinds of run.
def sh : Value := .symHash (.buffer [99].toByteArray)
def hsh : Hash := .symbolic (HashSrc.buffer [99].toByteArray).reduced
#guard (look strs sh .symHash hsh [0]).toOption == some (none, ["choose 3"])
-- Answer 1: the group of "a" collides, and `==` of the two values is not modelled.
#guard gapOf (look strs sh .symHash hsh [1]) == some "comparing these dict keys is not modelled yet"

-- User keys of one hash: the first comparison is exact.
def k1 : Value := .obj 10
def k2 : Value := .obj 11
def users : DictTable := table [(.exact 7, k1, .user), (.exact 7, k2, .user)]
#guard (look users (.obj 12) .user (.exact 7) [0] (fun s => s == k1)).toOption ==
  some (some 0, ["structural", "eq StrataPython.Dyn.Sem.Value.obj 10"])
-- A false `__eq__` with another user key left gaps.
#guard gapOf (look users (.obj 12) .user (.exact 7) [0] (fun s => s == k2)) ==
  some "a dict lookup after a false __eq__ depends on CPython's table layout"
-- Identity finds the first key without its `__eq__`; the second one is found only after the
-- first key's `__eq__`, whose repeats depend on the layout.
#guard (look users k1 .user (.exact 7) [0]).toOption == some (some 0, [])
#guard gapOf (look users k2 .user (.exact 7) [0]) ==
  some "a dict lookup after a false __eq__ depends on CPython's table layout"

-- After a deletion, two user keys of the probe's hash gap.
def usersDel : DictTable :=
  (table [(.exact 1, .obj 9, .user), (.exact 7, k1, .user), (.exact 7, k2, .user)]).deleteAt 0
#guard gapOf (look usersDel k1 .user (.exact 7)) ==
  some "a dict lookup after a deletion depends on CPython's table layout"

-- The probe object is stored under another hash.
#guard gapOf (look users k1 .user (.exact 8)) ==
  some "a lookup of a key whose hash changed after it was stored depends on CPython's table layout"

-- A false `__eq__` gaps even with no other candidate: CPython may compare the same entry again
-- (CPython 3.12: with `K.__eq__` true on its second call, `d = {k: 1}; d[224] = 2` leaves one
-- key).
def one : DictTable := table [(.exact 224, k1, .user)]
#guard gapOf (look one (.int 224) .builtin (.exact 224) [0] (fun _ => false)) ==
  some "a dict lookup after a false __eq__ depends on CPython's table layout"

-- A tuple that holds a user object, stored under another hash, gaps: CPython may still find it
-- by identity.
def tup : Value := .tuple #[.obj 3]
def tups : DictTable := table [(.exact 5, tup, .user)]
#guard gapOf (look tups tup .user (.exact 6)) ==
  some "a lookup of a key whose hash changed after it was stored depends on CPython's table layout"
-- Another tuple of another hash is simply not there.
#guard (look tups (.tuple #[.obj 4]) .user (.exact 6)).toOption == some (none, [])

-- The choice decoding for exact and address groups: a user probe with a symbolic hash meets an
-- exact group (`1`), an address group (`K()`), and both.
def kh : Hash := .symbolic (.combine "K" [.exact 12345])
def mixed : DictTable :=
  table [(.exact 1, .int 1, .builtin), (.symbolic (.addr 7), .obj 7, .user)]
#guard (look mixed (.obj 9) .user kh [0]).toOption == some (none, ["choose 3"])
#guard (look mixed (.obj 9) .user kh [1] (fun s => s == .int 1)).toOption ==
  some (some 0, ["choose 3", "eq StrataPython.Dyn.Sem.Value.int 1"])
#guard (look mixed (.obj 9) .user kh [2] (fun s => s == .obj 7)).toOption ==
  some (some 1, ["choose 3", "eq StrataPython.Dyn.Sem.Value.obj 7"])
#guard gapOf (look mixed (.obj 9) .user kh [3]) ==
  some "a dict lookup after a false __eq__ depends on CPython's table layout"
-- An exact probe hash meets no exact group, and an address probe no address group.
#guard (look mixed (.obj 9) .user (.exact 99) [0]).toOption == some (none, ["choose 1"])
#guard (look mixed (.obj 9) .user (.exact 99) [1] (fun s => s == .obj 7)).toOption ==
  some (some 1, ["choose 1", "eq StrataPython.Dyn.Sem.Value.obj 7"])
#guard (look mixed (.obj 9) .user (.symbolic (.addr 9)) [1] (fun s => s == .int 1)).toOption ==
  some (some 0, ["choose 1", "eq StrataPython.Dyn.Sem.Value.int 1"])

-- Where the level allows no choice, a needed one gaps.
#guard gapOf (look mixed (.obj 9) .user kh (choices := false)) ==
  some "a dict lookup where hashes may collide, at a level without choices"

-- A change of the keys during a comparison gaps.
def bumping : M Nat := do
  let (_, log) ← get
  pure log.length
#guard gapOf (look users (.obj 12) .user (.exact 7) [0] (fun s => s == k1) bumping) ==
  some "a dict that changes during a lookup is not modelled yet"

-- Two different objects that run no user code are not compared yet.
def objs : DictTable := table [(.exact 7, .obj 20, .builtin)]
#guard gapOf (look objs (.obj 21) .builtin (.exact 7)) ==
  some "comparing two objects is not modelled yet"

-- The way out: when the probe and every candidate are structural, a false comparison doesn't
-- gap, and every candidate is compared in insertion order.
#guard (look users (.obj 12) .user (.exact 7) [0] (fun _ => false) (structural := fun _ => true)).toOption ==
  some (none,
    ["structural", "eq StrataPython.Dyn.Sem.Value.obj 10", "eq StrataPython.Dyn.Sem.Value.obj 11"])
#guard (look users (.obj 12) .user (.exact 7) [0] (fun s => s == k2) (structural := fun _ => true)).toOption ==
  some (some 1,
    ["structural", "eq StrataPython.Dyn.Sem.Value.obj 10", "eq StrataPython.Dyn.Sem.Value.obj 11"])
-- One candidate that isn't structural keeps the gap, and so does a probe that isn't.
#guard gapOf (look users (.obj 12) .user (.exact 7) [0] (fun s => s == k2)
    (structural := fun v => v != k2)) ==
  some "a dict lookup after a false __eq__ depends on CPython's table layout"
#guard gapOf (look users (.obj 12) .user (.exact 7) [0] (fun s => s == k2)
    (structural := fun v => v != .obj 12)) ==
  some "a dict lookup after a false __eq__ depends on CPython's table layout"
-- One candidate: when both keys are structural, a false comparison doesn't gap.
#guard (look one (.int 224) .builtin (.exact 224) [0] (fun _ => false) (structural := fun _ => true)).toOption ==
  some (none, ["structural", "eq StrataPython.Dyn.Sem.Value.obj 10"])

-- The store isn't read where the loop can't need it: no candidate, the probe object itself as
-- the first candidate (found by identity), and only built-in keys.
#guard (look users (.obj 12) .user (.exact 9) [0] (structural := fun _ => true)).toOption ==
  some (none, [])
#guard (look users k1 .user (.exact 7) [0] (structural := fun _ => true)).toOption ==
  some (some 0, [])
#guard (look strs b .builtin hb (structural := fun _ => true)).toOption == some (some 1, [])
-- A change of the keys during a comparison still gaps when every key is structural.
#guard gapOf (look users (.obj 12) .user (.exact 7) [0] (fun s => s == k1) bumping
    (structural := fun _ => true)) ==
  some "a dict that changes during a lookup is not modelled yet"
-- Off the exact branch, the way out is not taken: a symbolic probe hash that meets an exact and an
-- address group keeps the gap on the branch where both collide.
#guard gapOf (look mixed (.obj 9) .user kh [3] (structural := fun _ => true)) ==
  some "a dict lookup after a false __eq__ depends on CPython's table layout"
-- After a deletion, two user candidates still gap.
#guard gapOf (look usersDel k1 .user (.exact 7) (structural := fun _ => true)) ==
  some "a dict lookup after a deletion depends on CPython's table layout"

-- `Value.structuralImm?` on the values other than tuples, slices and objects, and `none` for those,
-- whose members the walk checks.
#guard [Value.none, .notImplemented, .ellipsis, .bool true, .int 3, .ofString "s",
    .bytes #[1], .range 0 3 1, .builtin .«int», .float 0x3FF8000000000000].all
  (·.structuralImm? == some true)
#guard (Value.float 0x7FF8000000000000).structuralImm? == some false
-- A built-in object that is neither a type nor a function, such as `exit`, is not structural.
#guard (Value.builtin .«exit»).structuralImm? == some false
#guard (Value.tuple #[.int 1, .ofString "a"]).structuralImm? == none
#guard (Value.slice (.int 1) .none (.int 2)).structuralImm? == none
#guard sh.structuralImm? == some false
#guard (Value.obj 3).structuralImm? == none
#guard Value.traceback.structuralImm? == some false

-- The set lookup: one user key of hash 7 in a set whose layout isn't CPython's, so a false
-- comparison gaps unless both keys are structural.
def userSet : SetTable :=
  let t := SetTable.empty
  match t.search (.exact 7) with
  | some sr => { t.addNew sr (.exact 7) k1 .user with inexact := true }
  | none => t

/-- Look `k` up in the set `t`, as `look` does in a dict. -/
def lookSet (t : SetTable) (k : Value) (kc : KeyClass) (h : Hash)
    (user : Value → Bool := fun _ => false) (structural : Value → Bool := fun _ => false) :
    Except String (Option Nat × List String) :=
  (setLookup (ops user (structural := structural)) (pure true) t k kc h |>.run ([], [])).map
    fun (r, _, log) => (r, log)

#guard gapOf (lookSet userSet (.obj 12) .user (.exact 7)) ==
  some "a set lookup after a false __eq__ depends on CPython's table layout"
#guard (lookSet userSet (.obj 12) .user (.exact 7) (structural := fun _ => true)).toOption ==
  some (none, ["structural", "eq StrataPython.Dyn.Sem.Value.obj 10"])
-- While the set's layout is CPython's, a false comparison never gaps, so `structural` isn't called.
#guard (lookSet { userSet with inexact := false } (.obj 12) .user (.exact 7)
    (structural := fun _ => true)).toOption ==
  some (none, ["eq StrataPython.Dyn.Sem.Value.obj 10"])
-- A true comparison finds the key's slot, the one that identity finds, after one comparison.
#guard (lookSet userSet (.obj 12) .user (.exact 7) (fun s => s == k1)
    (structural := fun _ => true)).toOption.map (·.2) ==
  some ["structural", "eq StrataPython.Dyn.Sem.Value.obj 10"]
#guard (lookSet userSet (.obj 12) .user (.exact 7) (fun s => s == k1)
    (structural := fun _ => true)).toOption.map (·.1) ==
  (lookSet userSet k1 .user (.exact 7)).toOption.map (·.1)
#guard ((lookSet userSet k1 .user (.exact 7)).toOption.map (·.1)).join.isSome

end StrataPython.Dyn.Sem.DictLookupTest
