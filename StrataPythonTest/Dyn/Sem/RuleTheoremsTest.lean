/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Table
import StrataDyn.DSL
import StrataDyn.DDMRead
import StrataDyn.Exec.Run
meta import StrataPython.Dyn.Sem.Table
meta import StrataDyn.DDMRead
meta import StrataDyn.Exec.Run

set_option autoImplicit false

/-!
# `#py_rule_theorems`, the record's effects, and coverage

* A rule written over `PyM` gets its theorem; a rule written directly in `Sem`, without a lemma
  of its own, fails `#py_rule_theorems`; so does a `PyM` rule above its declared effect.
* A computation at `reads` can't use a `writes` primitive: Lean finds no instance.
* `#dyn_coverage Py (complete)` names what has no rule yet: the contract operations.
-/

namespace StrataPython.Dyn.Sem.RuleTheoremsTest

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn.Sem

/-- Instructions over Python's values that test the record's primitives. -/
public environment PyT extends Py where
  namespace pt
  open py
  insn good (x : Value) : Value
  insn direct (x : Value) : Value
  insn tooHigh (x : Value) : Value
  insn callNew (f : Value) (^err (exc : Value)) : Value
  insn raiseIn (x : Value) (^err (exc : Value)) : Value
  insn classOfNew (x : Value) (^err (exc : Value)) : Value
  insn setOld (k : Value) : Value
  insn probeCase (i : base.Int) : Value
  insn requireIn (x : Value) (^err (exc : Value)) : Value
  insn eqVal (x : Value) : Value
  insn setAny (k : Value) : Value
  insn pick (x : Value) (^err (exc : Value)) : Value
  insn dictPrims (^err (exc : Value)) : Value
  insn setPrims (^err (exc : Value)) : Value
  insn slotInexact (^err (exc : Value)) : Value
  insn popInexact (n : base.Int) (^err (exc : Value)) : Value
  insn frozenSeal (k : base.Int) (^err (exc : Value)) : Value
  insn listPrims (^err (exc : Value)) : Value
  insn oldPrims (^err (exc : Value)) : Value
  insn newPrims (^err (exc : Value)) : Value
  insn hashOf (i : base.Int) : Value
  insn frozenOr (^err (exc : Value)) : Value
  insn hashDeep (x : Value) : Value
  insn frozenWalk (^err (exc : Value)) : Value
  insn frozenMerge (^err (exc : Value)) : Value
  insn frozenAdd (^err (exc : Value)) : Value
  end pt

#dyn_types PyT

section
variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

/-- `x`, through `PyM`, after reading the start. -/
@[dyn_sem PyT.good, expose] public def good (x : Value) : Sem ε E Value :=
  runTotal "pt.good" #[] (pure x : PyM σ .pure false Value)

/-- `x`, after writing to the output, directly in `Sem`. -/
@[dyn_sem PyT.direct, expose] public def direct (x : Value) : Sem ε E Value := do
  modifyThe Output fun o => ⟨o.pieces.push "x"⟩
  pure x

/-- `x`, after writing to the output, through `PyM` at `writes`. -/
@[dyn_sem PyT.tooHigh, expose] public def tooHigh (x : Value) : Sem ε E Value :=
  runTotalFree "pt.tooHigh" #[] (do PyWrites.write "x"; pure x : PyM σ .writes true Value)

/-- A new `()` and `{}`, then `f((), {})`: an allocation, then a call one Python call deeper. -/
@[dyn_sem PyT.callNew, expose]
public def callNew (f : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let kw ← PyPure.allocDict
    PyCalls.callFunc f (.tuple #[]) kw : PyM σ .calls false Value)

/-- `ValueError("m")`, raised while `x` is being handled, without reading the start. -/
@[dyn_sem PyT.raiseIn, expose]
public def raiseIn (x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    PyWrites.setHandled x
    Proto.raiseBuiltin "ValueError" "m" : PyM σ .writes true Value)

/-- `type()` of a new exception of the class `x`. -/
@[dyn_sem PyT.classOfNew, expose]
public def classOfNew (x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let l ← PyPure.allocExc x #[] #[] (PyPure.imm (m := PyM σ .reads true) Imm.none)
    PyReads.classOf l : PyM σ .reads true Value)

/-- An own-object write to the `builtins` dict, which is older than the operation. -/
@[dyn_sem PyT.setOld, expose] public def setOld (k : Value) : Sem ε E Value :=
  runTotal "pt.setOld" #[] (do
    PyNew.dictSetNew (Value.obj 0) k k none fun _ => pure false
    pure k : PyM σ .pure false Value)

/-- A write at `writes` to the `builtins` dict, which is older than the operation, then a lookup of
what it wrote. -/
@[dyn_sem PyT.setAny, expose] public def setAny (k : Value) : Sem ε E Value :=
  runTotalFree "pt.setAny" #[] (do
    PyWrites.dictSet (Value.obj 0) k (Value.ofString "set") none fun _ => pure false
    return (← PyReads.dictFind (Value.obj 0) k none fun _ => pure false).getD Value.none
    : PyM σ .writes true Value)

/-- A lookup in the `builtins` dict of the key that `i` picks, with or without a given hash:
the hash that doesn't match, an object without its hash, an unhashable key, a NaN, a tuple
that holds an object, and tuples nested 901 and 900 deep. -/
@[dyn_sem PyT.probeCase, expose] public def probeCase (i : Int) : Sem ε E Value :=
  runTotalFree "pt.probeCase" #[] (do
    let (k, h) : Value × Option Hash := match i with
      | 0 => (.int 1, some (.exact 99))
      | 1 => (.obj 0, none)
      | 2 => (.builtin .__spec__, none)
      | 3 => (.ofFloat (0.0 / 0.0), none)
      | 4 => (.tuple #[.obj 0], none)
      | 5 => ((List.range 901).foldl (fun v _ => .tuple #[v]) (.int 0), none)
      | _ => ((List.range 900).foldl (fun v _ => .tuple #[v]) (.int 0), none)
    let _ ← PyReads.dictFind (Value.obj 0) k h fun _ => pure false
    pure Value.none : PyM σ .reads true Value)

/-- `requireDefined` of an unassigned value while `x` is being handled. -/
@[dyn_sem PyT.requireIn, expose]
public def requireIn (x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    PyWrites.setHandled x
    Proto.requireDefined (Value.undef "y") "y" "NameError" "m" : PyM σ .writes true Value)

/-- A lookup whose `__eq__` changes the found entry's value: the result is the new value.  The
key is an object of a class that is not built in (the `builtins` dict stands for it), so that
the lookup compares it through `eq`. -/
@[dyn_sem PyT.eqVal, expose] public def eqVal (x : Value) : Sem ε E Value :=
  runTotal "pt.eqVal" #[] (do
    let d ← PyPure.allocDict
    let k ← PyPure.allocExc (Value.obj 0) #[] #[] x
    let k' ← PyPure.allocExc (Value.obj 0) #[] #[] x
    PyNew.dictSetNew d k (Value.ofString "old") (some (.exact 7)) fun _ => pure false
    let r ← PyReads.dictFind d k' (some (.exact 7)) fun _ => do
      PyNew.dictSetNew d k (Value.ofString "new") (some (.exact 7)) fun _ => pure false
      pure true
    pure (r.getD Value.none) : PyM σ .calls false Value)

/-- `x`, after reading the start only when `x` is an object: `runRuleIf`, which the command
proves. -/
@[dyn_sem PyT.pick, expose] public def pick (x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleIf (x matches .obj _) err #[] (pure x : PyM σ .pure false Value)
    (pure x : PyM σ .pure true Value)

/-- An entry of a dict's entry array as a value: its key and value, or `'hole'` or `'past'`. -/
public def atValue : EntryAt Value → Value
  | .entry k v _ => .tuple #[k, v]
  | .hole => .ofString "hole"
  | .past => .ofString "past"

/-- A slot of a set's table as a value: its key, or `'hole'` or `'past'`. -/
public def slotValue : SlotAt Value → Value
  | .entry k _ => k
  | .hole => .ofString "hole"
  | .past => .ofString "past"

/-- The dict primitives that the operations of this piece don't reach, on `{1: 'a', 2: 'b', 3: 'c'}`:
delete `2`, read positions 1 and 3, the array's size and the deletion flag, pop the last entry,
read the size again (CPython's `dk_nentries`, which keeps the hole), and copy the entries at
position 0. -/
@[dyn_sem PyT.dictPrims, expose] public def dictPrims (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let d ← PyPure.allocDict
    for (k, v) in [(1, "a"), (2, "b"), (3, "c")] do
      PyNew.dictSetNew d (Value.int k) (Value.ofString v) none fun _ => pure false
    let del ← PyNew.dictDeleteNew d (Value.int 2) none fun _ => pure false
    let at1 ← PyReads.dictEntryAt d 1
    let at3 ← PyReads.dictEntryAt d 3
    let n ← PyReads.dictEntriesSize d
    let (deleted, _) ← PyReads.dictFlags d
    let pop ← PyNew.dictPopitemNew d
    let n' ← PyReads.dictEntriesSize d
    let c ← PyReads.allocDictFrom d (· == 0)
    let ce ← PyReads.dictEntries c
    pure (Value.tuple #[del.getD .none, atValue at1, atValue at3, .int n, .bool deleted,
      (pop.map fun (k, v) => Value.tuple #[k, v]).getD .none, .int n', .tuple (ce.map (·.1))])
    : PyM σ .reads false Value)

/-- The set primitives that the operations of this piece don't reach, on `{1, 9}`: slots 0, 1, 6
and 8, then three pops; `setTrim` on a set with two dummies; and `setReserve` on an empty set. -/
@[dyn_sem PyT.setPrims, expose] public def setPrims (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let s ← PyPure.allocSet false false
    for k in [1, 9] do PyNew.setAddNew s (Value.int k) none fun _ => pure false
    let slots ← [0, 1, 6, 8].mapM (PyReads.setSlotAt s)
    let p1 ← PyNew.setPopNew s
    let p2 ← PyNew.setPopNew s
    let p3 ← PyNew.setPopNew s
    -- Ten members grow the table to 32 slots; with nine of them deleted, the dummies fill more
    -- than a quarter of it, and `setTrim` shrinks it to 8 slots: slot 31 is past the end.
    let t ← PyPure.allocSet false false
    for k in List.range 10 do PyNew.setAddNew t (Value.int k) none fun _ => pure false
    for k in List.range 9 do discard <| PyNew.setDiscardNew t (Value.int k) none fun _ => pure false
    let before ← PyReads.setSlotAt t 31
    PyNew.setTrimNew t
    let after ← PyReads.setSlotAt t 31
    -- `setReserve` for 10 more members grows 8 slots to 32: slot 31 exists.
    let r ← PyPure.allocSet false false
    PyNew.setReserveNew r 10
    let at31 ← PyReads.setSlotAt r 31
    pure (Value.tuple ((slots.map slotValue).toArray ++ #[p1.getD .none, p2.getD .none, p3.getD .none,
      slotValue before, slotValue after, slotValue at31]))
    : PyM σ .reads false Value)

/-- `setSlotAt` on a set whose layout is inexact: `{'a'}`. -/
@[dyn_sem PyT.slotInexact, expose] public def slotInexact (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let s ← PyPure.allocSet false false
    PyNew.setAddNew s (Value.ofString "a") none fun _ => pure false
    let _ ← PyReads.setSlotAt s 0
    pure Value.none : PyM σ .reads false Value)

/-- `pop` of a set whose layout is inexact, with the `str` members of `["a", "b"]` up to `n`. -/
@[dyn_sem PyT.popInexact, expose] public def popInexact (n : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let s ← PyPure.allocSet false false
    for x in ["a", "b"].take n.toNat do
      PyNew.setAddNew s (Value.ofString x) none fun _ => pure false
    pure ((← PyNew.setPopNew s).getD .none) : PyM σ .reads false Value)

/-- The resize counter of a new list after `listReserveNew` with `0`, then with `3`. -/
@[dyn_sem PyT.listPrims, expose] public def listPrims (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let l ← PyPure.allocList #[]
    PyNew.listReserveNew l 0
    let r0 ← PyReads.listView l
    PyNew.listReserveNew l 3
    let r1 ← PyReads.listView l
    pure (Value.tuple #[.int ((r0.map (·.2)).getD 9), .int ((r1.map (·.2)).getD 9)])
    : PyM σ .reads false Value)

/-- The primitives on any dict or set, which the operations of this piece don't reach, on objects
made first: `dictPopitem` and `dictClear` on `{1: 'a', 2: 'b'}`; `setDiscard` of 1 and two
`setPop`s on `{1, 9}`; `setTrim` after nine `setDiscard`s on a set of ten members; and `setClear`
on `{5}`. -/
@[dyn_sem PyT.oldPrims, expose] public def oldPrims (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let d ← PyPure.allocDict
    for (k, v) in [(1, "a"), (2, "b")] do
      PyNew.dictSetNew d (Value.int k) (Value.ofString v) none fun _ => pure false
    let pop ← PyWrites.dictPopitem d
    PyWrites.dictClear d
    let n ← PyReads.dictEntriesSize d
    let (deleted, _) ← PyReads.dictFlags d
    let s ← PyPure.allocSet false false
    for k in [1, 9] do PyNew.setAddNew s (Value.int k) none fun _ => pure false
    let found ← PyWrites.setDiscard s (Value.int 1) none fun _ => pure false
    let p1 ← PyWrites.setPop s
    let p2 ← PyWrites.setPop s
    let t ← PyPure.allocSet false false
    for k in List.range 10 do PyNew.setAddNew t (Value.int k) none fun _ => pure false
    for k in List.range 9 do discard <| PyWrites.setDiscard t (Value.int k) none fun _ => pure false
    PyWrites.setTrim t
    let after ← PyReads.setSlotAt t 31
    let c ← PyPure.allocSet false false
    PyNew.setAddNew c (Value.int 5) none fun _ => pure false
    PyWrites.setClear c
    pure (Value.tuple #[(pop.map fun (k, v) => Value.tuple #[k, v]).getD .none, .int n,
      .bool deleted, .bool found, p1.getD .none, p2.getD .none, slotValue after,
      .int (← PyReads.setLen c)])
    : PyM σ .writes false Value)

/-- `setReplaceNew` of `{1, 9}` with the table of `{'a'}`, which is inexact, then `setClearNew`,
which makes it exact again; `dictHasUser` of `{1: 2}`; and the views of a subclass instance's
built-in part on plain values, which have none. -/
@[dyn_sem PyT.newPrims, expose] public def newPrims (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let u ← PyPure.allocSet false false
    for k in [1, 9] do PyNew.setAddNew u (Value.int k) none fun _ => pure false
    let v ← PyPure.allocSet false false
    PyNew.setAddNew v (Value.ofString "a") none fun _ => pure false
    PyNew.setReplaceNew u v
    let n1 ← PyReads.setLen u
    let exact1 := (← PyReads.setView u).any (·.exact)
    PyNew.setClearNew u
    let n2 ← PyReads.setLen u
    let exact2 := (← PyReads.setView u).any (·.exact)
    let d ← PyPure.allocDict
    PyNew.dictSetNew d (Value.int 1) (Value.int 2) none fun _ => pure false
    let user ← PyReads.dictHasUser d
    let t := Value.tuple #[Value.int 1]
    let views := [(← PyReads.tupleView t).isSome, (← PyReads.strView (Value.ofString "s")).isSome,
      (← PyReads.numView (Value.int 5)).isSome, (← PyReads.bytesView (Value.bytes #[1])).isSome]
    pure (Value.tuple (#[.int n1, .bool exact1, .int n2, .bool exact2, .bool user] ++
      views.toArray.map .bool))
    : PyM σ .reads false Value)

/-- `hash()`'s result for an exact hash if `i` is `0`, and for the address of object 0 otherwise. -/
@[dyn_sem PyT.hashOf, expose] public def hashOf (i : Int) : Sem ε E Value :=
  runTotalFree "pt.hashOf" #[] (PyPure.hashValue (if i == 0 then .exact 5
    else .symbolic (HashSrc.addr 0)) : PyM σ .pure true Value)

/-- `{frozenset({1})} == {frozenset({1})}`: a walk of sets whose members are frozensets, which
compare as `KeyClass.user`, and so stop with a gap here. -/
@[dyn_sem PyT.frozenWalk, expose] public def frozenWalk (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let mk : PyM σ .reads false Value := do
      let f ← PyPure.allocSet true false
      PyNew.setAddNew f (Value.int 1) none fun _ => pure false
      PyNew.setFreezeNew f
      let s ← PyPure.allocSet false false
      PyNew.setAddNew s f (some (← Proto.hash f)) (Proto.keyEq f)
      pure s
    let a ← mk
    let b ← mk
    return Value.bool (← Proto.richCompare .eq a b) : PyM σ .reads false Value)

/-- `s |= t` for `s = {1}` and `t = {frozenset({1})}`: `setMerge`'s path that compares, on a set
whose member may run user code when compared, which stops with a gap here. -/
@[dyn_sem PyT.frozenMerge, expose] public def frozenMerge (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let f ← PyPure.allocSet true false
    PyNew.setAddNew f (Value.int 1) none fun _ => pure false
    PyNew.setFreezeNew f
    let t ← PyPure.allocSet false false
    PyNew.setAddNew t f (some (← Proto.hash f)) (Proto.keyEq f)
    let s ← PyPure.allocSet false false
    PyNew.setAddNew s (Value.int 1) none fun _ => pure false
    PyNew.setMergeNew s t Proto.memberEq
    pure Value.none : PyM σ .reads false Value)

/-- `PyWrites.setAdd` on a frozenset: the old-object writes refuse it, since a frozenset is
immutable. -/
@[dyn_sem PyT.frozenAdd, expose] public def frozenAdd (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let f ← PyPure.allocSet true false
    PyWrites.setAdd f (Value.int 1) none fun _ => pure false
    pure Value.none : PyM σ .writes true Value)

/-- A frozenset's open and closed states: with `k = 0`, a hash of an open frozenset; with `k = 1`, a write to a closed one; with `k = 2`, the hashes of what each maker gives for `frozenset({1})` and
`frozenset({1, 2})` (`|`, `&`, `-`, `^` and a copy), which are closed. -/
@[dyn_sem PyT.frozenSeal, expose] public def frozenSeal (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (do
    let mk (xs : List Int) : PyM σ .writes true Value := do
      let f ← PyPure.allocSet true false
      for x in xs do PyNew.setAddNew f (Value.int x) none fun _ => pure false
      pure f
    if k == 0 then
      let f ← mk [1]
      discard <| Proto.hash f
      return Value.none
    if k == 1 then
      let f ← mk [1]
      PyNew.setFreezeNew f
      PyNew.setAddNew f (Value.int 2) none fun _ => pure false
      return Value.none
    let a ← mk [1]
    PyNew.setFreezeNew a
    let b ← mk [1, 2]
    PyNew.setFreezeNew b
    let rs := [← Proto.setUnion true a b, ← Proto.setIntersection true a b,
      ← Proto.setDifference true b a, ← Proto.setSymDifference true a b, ← PyReads.setCopy a true]
    let hs ← rs.mapM fun r => do PyPure.hashValue (← Proto.hash r)
    pure (Value.tuple hs.toArray) : PyM σ .writes true Value)

/-- `x` in `n` nested tuples. -/
public def nest : Nat → Value → Value
  | 0, x => x
  | n + 1, x => .tuple #[nest n x]

/-- The hash of `x` in tuples nested 1000 deep. -/
@[dyn_sem PyT.hashDeep, expose] public def hashDeep (x : Value) : Sem ε E Value :=
  runTotalFree "pt.hashDeep" #[] (do
    let _ ← PyPure.immHash (nest 1000 x)
    pure Value.none : PyM σ .pure true Value)

/-- `f |= {2}` for the frozenset `f = frozenset({1})`: a new frozenset, `f` unchanged, filled at
`PyM σ .writes true`, whose writes to new objects may fill a frozenset. -/
@[dyn_sem PyT.frozenOr, expose] public def frozenOr (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let f ← PyPure.allocSet true false
    PyNew.setAddNew f (Value.int 1) none fun _ => pure false
    PyNew.setFreezeNew f
    let s ← PyPure.allocSet false false
    PyNew.setAddNew s (Value.int 2) none fun _ => pure false
    let r ← Proto.inplaceOp .or f s
    let mr ← Proto.setMembers r
    let mf ← Proto.setMembers f
    pure (Value.tuple #[.bool (r == f), ← PyReads.classOf r,
      .tuple (mr.unordered.map (·.1)), .tuple (mf.unordered.map (·.1))]) : PyM σ .writes true Value)
end

public section
#dyn_sem_table PyTSem for PyT (world := World)
end

/-- The declared effects of `PyT`'s instructions. -/
def ptEffect : String → Effects.Level
  | "pt.callNew" => .calls
  | "pt.raiseIn" => .writes
  | "pt.classOfNew" => .reads
  | "pt.probeCase" => .reads
  | "pt.requireIn" => .writes
  | "pt.eqVal" => .calls
  | "pt.setAny" => .writes
  | "pt.dictPrims" | "pt.setPrims" | "pt.slotInexact" | "pt.popInexact" | "pt.listPrims"
  | "pt.newPrims" => .reads
  | "pt.oldPrims" | "pt.frozenSeal" => .writes
  | "pt.frozenOr" | "pt.frozenAdd" => .writes
  | "pt.frozenWalk" | "pt.frozenMerge" => .reads
  | _ => .pure

/-- The tags of `PyLang` in `PyTSem`. -/
def ptTags (σ : Type) [Store σ] : @Tags σ _ ⟨PyTSem.interp σ⟩ :=
  letI : Decode σ := ⟨PyTSem.interp σ⟩
  ⟨⟨PyTSem.T.py.Value, rfl⟩, ⟨Ty.ref PyTSem.T.py.Value, rfl⟩,
    ⟨PyTSem.T.base.Except PyTSem.T.py.Value PyTSem.T.py.Value, rfl⟩⟩

/--
error: #py_rule_theorems: the rule of pt.direct is not a `runRule`, `runTotal`, `runRuleFree`, `runTotalFree` or `runRuleIf` wrapper at an effect no higher than its declared one whose results and exits hold no ref, and has no lemmas StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.okOf.pt.direct and StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.certOf.pt.direct
---
error: #py_rule_theorems: the rule of pt.tooHigh is not a `runRule`, `runTotal`, `runRuleFree`, `runTotalFree` or `runRuleIf` wrapper at an effect no higher than its declared one whose results and exits hold no ref, and has no lemmas StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.okOf.pt.tooHigh and StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.certOf.pt.tooHigh
-/
#guard_msgs in
#py_rule_theorems PyTSem for PyT (effects := ptEffect) (tags := ptTags)

-- The other rules got their theorems: within their effects, and satisfying every spec that has the
-- laws.
example : ImplWithin PyTSem.interp .pure PyTSem.impl.pt.setOld := PyTSem.ok.pt.setOld
example : ImplOK PyTSem.interp ptTags .pure PyTSem.impl.pt.setOld := PyTSem.implOK.pt.setOld
example : ImplWithin PyTSem.interp .calls PyTSem.impl.pt.eqVal := PyTSem.ok.pt.eqVal
example : ImplOK PyTSem.interp ptTags .calls PyTSem.impl.pt.eqVal := PyTSem.implOK.pt.eqVal
example : ImplWithin PyTSem.interp .writes PyTSem.impl.pt.setAny := PyTSem.ok.pt.setAny
example : ImplOK PyTSem.interp ptTags .writes PyTSem.impl.pt.setAny := PyTSem.implOK.pt.setAny
example : ImplWithin PyTSem.interp .pure PyTSem.impl.pt.good := PyTSem.ok.pt.good
example : ImplOK PyTSem.interp ptTags .pure PyTSem.impl.pt.good := PyTSem.implOK.pt.good
example : ImplWithin PyTSem.interp .calls PyTSem.impl.pt.callNew := PyTSem.ok.pt.callNew
example : ImplOK PyTSem.interp ptTags .calls PyTSem.impl.pt.callNew := PyTSem.implOK.pt.callNew
example : ImplWithin PyTSem.interp .writes PyTSem.impl.pt.raiseIn := PyTSem.ok.pt.raiseIn
example : ImplOK PyTSem.interp ptTags .writes PyTSem.impl.pt.raiseIn := PyTSem.implOK.pt.raiseIn
example : ImplWithin PyTSem.interp .reads PyTSem.impl.pt.classOfNew := PyTSem.ok.pt.classOfNew
example : ImplOK PyTSem.interp ptTags .reads PyTSem.impl.pt.classOfNew := PyTSem.implOK.pt.classOfNew

/-- Run `@m.main` of the module `text`, and print its result or its fault; with `excDetail`, an
exception's class, arguments and context instead of its object. -/
def runText (text : String) (excDetail : Bool) : IO Unit := do
  match ← Module.read PyT.env text "t.dyn" with
  | .error e => IO.println s!"read: {e}"
  | .ok m =>
    let o := runModule PyTSem.model m (.str (.str .base "m") "main") #[] 1000
    match o.result, o.read? Value with
    | .ok _, some (.obj id) =>
      if !excDetail then IO.println (reprStr (Value.obj id)) else
      match o.snapshot.world.store.get? id with
      | some { cls, payload := .exc e, .. } =>
        IO.println s!"exception {reprStr cls} {reprStr e.args} context {reprStr e.context}"
      | _ => IO.println s!"object {id}"
    | .ok _, some v => IO.println (reprStr v)
    | .ok _, none => IO.println "a result that is not a value"
    | .fault f, _ => IO.println s!"fault: {repr f}"

/-- Run `@m.main`, whose body ends with `%v.0`, and print its result, or the class, arguments
and context of the exception it raises, or its fault. -/
def run (body : String) : IO Unit :=
  runText s!"module m \{
  func @m.main() -> py.Value \{
    entry.0():
{body}
      ret(%v.0)
    err.0(%e.0 : py.Value):
      ret(%e.0)
  }
}" true

/-- Run `@m.main` of the module `text` and print its result or its fault. -/
def runModule' (text : String) : IO Unit := runText text false

-- An exception raised while another is handled has it as its `__context__`.
/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.ValueError) StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.str { s := "m", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.int 7
-/
#guard_msgs in
#eval run "      %x.0 : py.Value = py.intLit(7)
      %v.0 : py.Value = pt.raiseIn(%x.0) ^err.0()"

-- `type()` of an exception object is read from the store.
/-- info: StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.AssertionError) -/
#guard_msgs in
#eval run "      %x.0 : py.Value = py.assertionError
      %v.0 : py.Value = pt.classOfNew(%x.0) ^err.0()"

-- `probeOf`: a given hash must be the key's own, an object needs its hash, and the keys whose
-- hash is not modelled gap.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: a given hash that differs from the key's own" -/
#guard_msgs in
#eval run "      %g.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %v.0 : py.Value = pt.probeCase(0)"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: an object key without its hash" -/
#guard_msgs in
#eval run "      %g.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %v.0 : py.Value = pt.probeCase(1)"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "an unhashable dict key is not modelled yet" -/
#guard_msgs in
#eval run "      %g.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %v.0 : py.Value = pt.probeCase(2)"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "the hash of this dict key is not modelled yet" -/
#guard_msgs in
#eval run "      %g.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %v.0 : py.Value = pt.probeCase(3)"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "the hash of a key that holds an object is not modelled yet" -/
#guard_msgs in
#eval run "      %g.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %v.0 : py.Value = pt.probeCase(4)"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a key nested deeper than the model follows" -/
#guard_msgs in
#eval run "      %g.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %v.0 : py.Value = pt.probeCase(5)"

-- A key nested 900 deep is looked up (and not found).
/-- info: StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %g.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %v.0 : py.Value = pt.probeCase(6)"

-- A check raised while another exception is handled takes it as its context.
/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.NameError) StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.str { s := "m", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.int 7
-/
#guard_msgs in
#eval run "      %x.0 : py.Value = py.intLit(7)
      %v.0 : py.Value = pt.requireIn(%x.0) ^err.0()"

-- A value that `__eq__` changes during the lookup is read after it, as CPython reads it.
/-- info: StrataPython.Dyn.Sem.Value.str { s := "new", ascii := true, ascii_eq := _ } -/
#guard_msgs in
#eval run "      %g.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %x.0 : py.Value = py.noneLit
      %v.0 : py.Value = pt.eqVal(%x.0)"

-- A write to an own object fails on an older one.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: a write to an object older than the operation" -/
#guard_msgs in
#eval run "      %x.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %v.0 : py.Value = pt.setOld(%x.0)"

-- A write at `writes` changes any dict: it adds a key, and replaces the value of a key.
/-- info: StrataPython.Dyn.Sem.Value.str { s := "set", ascii := true, ascii_eq := _ } -/
#guard_msgs in
#eval run "      %g.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %x.0 : py.Value = py.strLit(\"zz\")
      %v.0 : py.Value = pt.setAny(%x.0)"

/-- info: StrataPython.Dyn.Sem.Value.str { s := "set", ascii := true, ascii_eq := _ } -/
#guard_msgs in
#eval run "      %g.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %x.0 : py.Value = py.strLit(\"len\")
      %v.0 : py.Value = pt.setAny(%x.0)"

-- No object has a class whose values are always immediates.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: an object of a class whose values are immediates" -/
#guard_msgs in
#eval run "      %x.0 : py.Value = py.intLit(7)
      %t.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %v.0 : py.Value = pt.classOfNew(%t.0) ^err.0()"

-- The primitives that the operations don't reach yet.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "b", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "hole", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "past", ascii := true, ascii_eq := _ }, StrataPython.Dyn.Sem.Value.int 3,
    StrataPython.Dyn.Sem.Value.bool true,
    StrataPython.Dyn.Sem.Value.tuple
      #[StrataPython.Dyn.Sem.Value.int 3, StrataPython.Dyn.Sem.Value.str { s := "c", ascii := true, ascii_eq := _ }],
    StrataPython.Dyn.Sem.Value.int 2, StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 1]]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictPrims ^err.0()"

-- `{1, 9}` holds 1 in slot 1 and 9 in slot 6; the pops start at the finger.  Then `setTrim`
-- shrinks a table of 32 slots to 8, and `setReserve` grows one of 8 slots to 32.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "hole", ascii := true, ascii_eq := _ }, StrataPython.Dyn.Sem.Value.int 1,
    StrataPython.Dyn.Sem.Value.int 9, StrataPython.Dyn.Sem.Value.str { s := "past", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.int 9, StrataPython.Dyn.Sem.Value.none,
    StrataPython.Dyn.Sem.Value.str { s := "hole", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "past", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "hole", ascii := true, ascii_eq := _ }]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.setPrims ^err.0()"

-- `popitem` gives the last entry, and `clear` empties the dict and clears its deletion flag; the
-- pops of what is left of `{1, 9}` give 9, then nothing; `setTrim` shrinks 32 slots to 8;
-- `clear` empties the set.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.tuple
      #[StrataPython.Dyn.Sem.Value.int 2, StrataPython.Dyn.Sem.Value.str { s := "b", ascii := true, ascii_eq := _ }],
    StrataPython.Dyn.Sem.Value.int 0, StrataPython.Dyn.Sem.Value.bool false, StrataPython.Dyn.Sem.Value.bool true,
    StrataPython.Dyn.Sem.Value.int 9, StrataPython.Dyn.Sem.Value.none,
    StrataPython.Dyn.Sem.Value.str { s := "past", ascii := true, ascii_eq := _ }, StrataPython.Dyn.Sem.Value.int 0]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.oldPrims ^err.0()"

-- The replaced set has one member and the inexact layout of `{'a'}`; cleared, it has none and an
-- exact layout.  `{1: 2}` has no key that runs user code, and an immediate has no view (only an instance of a subclass has one).
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.bool false, StrataPython.Dyn.Sem.Value.int 0,
    StrataPython.Dyn.Sem.Value.bool true, StrataPython.Dyn.Sem.Value.bool false, StrataPython.Dyn.Sem.Value.bool false,
    StrataPython.Dyn.Sem.Value.bool false, StrataPython.Dyn.Sem.Value.bool false, StrataPython.Dyn.Sem.Value.bool false]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.newPrims ^err.0()"

-- A frozenset is a value only once closed: hashing an open one, or writing to a closed one, is a
-- model invariant; every maker closes what it makes.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: a read of the frozenset 2, which is still open" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.frozenSeal(0) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: a write to the closed frozenset 2" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.frozenSeal(1) ^err.0()"

-- The makers' results hash as CPython 3.12's do.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.int (-1826646154956904602), StrataPython.Dyn.Sem.Value.int (-558064481276695278),
    StrataPython.Dyn.Sem.Value.int 4774279697163166305, StrataPython.Dyn.Sem.Value.int 4774279697163166305,
    StrataPython.Dyn.Sem.Value.int (-558064481276695278)]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.frozenSeal(2) ^err.0()"

-- `pop` of an inexact set of two members gives a member that depends on the hash seed: a gap. With
-- one member, it has one answer.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "set.pop of a set whose order is not CPython's is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.popInexact(2) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.str { s := "a", ascii := true, ascii_eq := _ } -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.popInexact(1) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a slot of a set whose layout is inexact" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.slotInexact ^err.0()"

-- A preallocation of `0` doesn't move the resize counter; one of `3` does.
/-- info: StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 0, StrataPython.Dyn.Sem.Value.int 1] -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.listPrims ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.int 5 -/
#guard_msgs in
#eval run "      %h.0 : py.Value = pt.hashOf(0)
      %v.0 : py.Value = pt.pick(%h.0) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "hash(x) depends on an address" -/
#guard_msgs in
#eval run "      %h.0 : py.Value = pt.hashOf(1)
      %v.0 : py.Value = pt.pick(%h.0) ^err.0()"

-- A hash of a value nested deeper than the model follows is a gap.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "a hash of values nested deeper than the model follows" -/
#guard_msgs in
#eval run "      %i.0 : py.Value = py.intLit(0)
      %h.0 : py.Value = pt.hashDeep(%i.0)
      %v.0 : py.Value = pt.pick(%h.0) ^err.0()"

-- A walk of sets whose members are frozensets stops with a gap: a frozenset key may run user
-- code when compared.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "a walk of a set whose comparisons may run user code is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.frozenWalk ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a walk of a set whose comparisons may run user code is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.frozenMerge ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: a write to the frozenset 2" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.frozenAdd ^err.0()"

-- A frozenset's `|=` makes a new frozenset, `frozenset({1, 2})`, and leaves the old one as it is.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.bool false, StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.frozenset),
    StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.int 2],
    StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 1]]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.frozenOr ^err.0()"

-- A closure made by `mkClosure` runs its code on the cells it captured: late binding reads the
-- cell when the call runs (`c = 1`, then `c = 2`, then the call gives `2`).
/-- info: StrataPython.Dyn.Sem.Value.int 2 -/
#guard_msgs in
#eval runModule' "module m {
  func @m.g(%c.0 : base.Ref(py.Value), %args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%c.0 : base.Ref(py.Value), %args.0 : py.Value, %kwargs.0 : py.Value):
      %x.0 : py.Value = base.refGet[py.Value](%c.0)
      %r.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%x.0)
      ret(%r.0)
  }
  func @m.main() -> py.Value {
    entry.0():
      %i.0 : py.Value = py.intLit(1)
      %c.0 : base.Ref(py.Value) = base.refNew[py.Value](%i.0)
      %f.0 : py.Value = py.mkClosure[[base.Ref(py.Value)]](@m.g, \"g\", \"m\", %c.0)
      %j.0 : py.Value = py.intLit(2)
      %s.0 : base.Unit = base.refSet[py.Value](%c.0, %j.0)
      %v.0 : py.Value = pt.callNew(%f.0) ^err.0()
      ret(%v.0)
    err.0(%e.0 : py.Value):
      ret(%e.0)
  }
}"

-- Two cells are bound in operand order: the code gets `(1, 2)`.
/--
info: StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.int 2]
-/
#guard_msgs in
#eval runModule' "module m {
  func @m.g(%a.0 : base.Ref(py.Value), %b.0 : base.Ref(py.Value), %args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%a.0 : base.Ref(py.Value), %b.0 : base.Ref(py.Value), %args.0 : py.Value, %kwargs.0 : py.Value):
      %x.0 : py.Value = base.refGet[py.Value](%a.0)
      %y.0 : py.Value = base.refGet[py.Value](%b.0)
      %t.0 : py.Value = py.mkTuple(%x.0, %y.0)
      %r.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%t.0)
      ret(%r.0)
  }
  func @m.main() -> py.Value {
    entry.0():
      %i.0 : py.Value = py.intLit(1)
      %j.0 : py.Value = py.intLit(2)
      %a.0 : base.Ref(py.Value) = base.refNew[py.Value](%i.0)
      %b.0 : base.Ref(py.Value) = base.refNew[py.Value](%j.0)
      %f.0 : py.Value = py.mkClosure[[base.Ref(py.Value), base.Ref(py.Value)]](@m.g, \"g\", \"m\", %a.0, %b.0)
      %v.0 : py.Value = pt.callNew(%f.0) ^err.0()
      ret(%v.0)
    err.0(%e.0 : py.Value):
      ret(%e.0)
  }
}"

-- A call of a value or object that is not a function object is not modelled yet.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "a call of a value other than a function object is not modelled yet" -/
#guard_msgs in
#eval run "      %x.0 : py.Value = py.noneLit
      %v.0 : py.Value = pt.callNew(%x.0) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a call of an object that is not a function object is not modelled yet" -/
#guard_msgs in
#eval run "      %d.0 : py.Value = py.mkDict ^err.0()
      %v.0 : py.Value = pt.callNew(%d.0) ^err.0()"

/--
error: failed to synthesize instance of type class
  PyWrites (PyM σ Effects.Level.reads true) ?m.5

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {σ : Type} [Store σ] [Decode σ] : PyM σ .reads true Unit := PyWrites.write "x"

-- Every instruction of `Py` has a rule, but the contract operations, whose rules come with the
-- semantics of contracts.
/--
error: Py is not fully covered: no rule for py.argOf, py.extraKwargs, py.bindsTo, py.stdClass, py.isInstance, py.typeIsSubclass, py.len, py.reSearch, py.strIsOneOf, py.intIsOneOf, py.isImmutableScalar, py.dictKeysWithin, py.allIn, py.anyIn, py.allItems, py.anyItems, py.attrLoc, py.itemLoc, py.objLoc, py.reachLoc, py.instanceState
-/
#guard_msgs in
#dyn_coverage Py (complete)

end StrataPython.Dyn.Sem.RuleTheoremsTest
