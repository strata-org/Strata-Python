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
  of its own, fails `#py_rule_theorems`; so does a `PyM` rule above its declared effect, and one
  that runs a region whose parameter is a ref (`pt.regionCell`; `pt.regionValue`, its twin on a
  `Value`, gets its theorem).
* A computation at `reads` can't use a `writes` primitive: Lean finds no instance.
* `#dyn_coverage Py (complete)` names what has no rule yet: the quantifiers of the contracts.
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
  insn nextView (^err (exc : Value)) : Value
  insn setUpdateSub (^err (exc : Value)) : Value
  insn frozenSeal (k : base.Int) (^err (exc : Value)) : Value
  insn nativeDepth (k : base.Int) (^err (exc : Value)) : Value
  insn nativeGapped (k : base.Int) (^err (exc : Value)) : Value
  insn classDescr (k : base.Int) (^err (exc : Value)) : Value
  insn startCheck (k : base.Int) (^err (exc : Value)) : Value
  insn hooks (k : base.Int) (^err (exc : Value)) : Value
  insn partHooks (k : base.Int) (^err (exc : Value)) : Value
  insn staticDescr (k : base.Int) (^err (exc : Value)) : Value
  insn heapAttrs (k : base.Int) (^err (exc : Value)) : Value
  insn dictProxyCase (k : base.Int) (^err (exc : Value)) : Value
  insn viewOps (k : base.Int) (^err (exc : Value)) : Value
  insn viewBare (k : base.Int) (^err (exc : Value)) : Value
  insn setExactCase (^err (exc : Value)) : Value
  insn stubHooks (k : base.Int) (^err (exc : Value)) : Value
  insn stubIssubclass (k : base.Int) (^err (exc : Value)) : Value
  insn callableOpaque (^err (exc : Value)) : Value
  insn callableTpNew (^err (exc : Value)) : Value
  insn sequenceCheckProxy (^err (exc : Value)) : Value
  insn regionValue (c : cell) (&body (x : Value) : raising base.Unit) (^err (exc : Value)) : Value
  insn regionCell (c : cell) (&body (r : cell) : raising base.Unit) (^err (exc : Value)) : Value
  insn regionArity (k : base.Int) (&body (x : Value) : raising base.Unit) (^err (exc : Value)) : Value
  insn listPrims (^err (exc : Value)) : Value
  insn oldPrims (^err (exc : Value)) : Value
  insn newPrims (^err (exc : Value)) : Value
  insn hashOf (i : base.Int) : Value
  insn frozenOr (^err (exc : Value)) : Value
  insn hashDeep (x : Value) : Value
  insn frozenWalk (^err (exc : Value)) : Value
  insn frozenMerge (^err (exc : Value)) : Value
  insn frozenAdd (^err (exc : Value)) : Value
  insn importGaps (k : base.Int) (^err (exc : Value)) : Value
  insn groupLenHint (^err (exc : Value)) : Value
  insn objPrims (^err (exc : Value)) : Value
  insn dictWalkSub (k : base.Int) (^err (exc : Value)) : Value
  insn nativeWrite (k : base.Int) (^err (exc : Value)) : Value
  insn immutableWrite (^err (exc : Value)) : Value
  insn strSubArg (k : base.Int) (^err (exc : Value)) : Value
  insn mkSubInst (j : base.Int) (^err (exc : Value)) : Value
  insn mkExc (j : base.Int) (^err (exc : Value)) : Value
  insn subclassCases (f : Value) (g : Value) (k : base.Int) (^err (exc : Value)) : Value
  insn buildClassName (f : Value) (k : base.Int) (^err (exc : Value)) : Value
  insn dictOrSub (k : base.Int) (^err (exc : Value)) : Value
  insn kwargsStrSub (^err (exc : Value)) : Value
  insn bindCase (i : base.Int) (^err (exc : Value)) : Value
  insn subclassOps (^err (exc : Value)) : Value
  insn subclassContainers (^err (exc : Value)) : Value
  insn seqSlotSub (k : base.Int) (^err (exc : Value)) : Value
  insn seqSlotCleared (k : base.Int) (^err (exc : Value)) : Value
  insn strSetSubOps (k : base.Int) (^err (exc : Value)) : Value
  insn resumeCase (f : Value) (^err (exc : Value)) : Value
  insn callInst (^err (exc : Value)) : Value
  insn cTypeStep (k : base.Int) (^err (exc : Value)) : Value
  insn callLevelStep (^err (exc : Value)) : Value
  insn resumeDirect (^err (exc : Value)) : Value
  insn resumeNoFit (^err (exc : Value)) : Value
  insn foreignIter (^err (exc : Value)) : Value
  insn foreignLen (^err (exc : Value)) : Value
  insn strSubIter (^err (exc : Value)) : Value
  insn iterBounds (^err (exc : Value)) : Value
  insn zipNext (^err (exc : Value)) : Value
  insn enumNext (^err (exc : Value)) : Value
  insn revNext (^err (exc : Value)) : Value
  insn listRevNext (^err (exc : Value)) : Value
  insn dictRevNext (^err (exc : Value)) : Value
  insn startZero (^err (exc : Value)) : Value
  insn staleSlice (^err (exc : Value)) : Value
  insn tpNewNoLeak (^err (exc : Value)) : Value
  insn sortInts (^err (exc : Value)) : Value
  insn sortNaN (^err (exc : Value)) : Value
  insn strLowerSigma (^err (exc : Value)) : Value
  insn maketransRule (^err (exc : Value)) : Value
  insn decodeBytearray (^err (exc : Value)) : Value
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

/-- The import rules' gaps: an import after `builtins.__import__` was replaced (`k = 0`) or deleted
(`k = 1`); a reference into another module than `builtins` (`2`) and to a name that `builtins`
lacks (`3`); and `from builtins import __dict__` (otherwise). -/
@[dyn_sem PyT.importGaps, expose] public def importGaps (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (do
    let imp := Value.ofString "__import__"
    if k == 0 then
      PyWrites.dictSet (Value.obj 0) imp Value.none none fun _ => pure false
      return ← Proto.importModule "builtins"
    if k == 1 then
      discard <| PyWrites.dictDelete (Value.obj 0) imp none fun _ => pure false
      return ← Proto.importFrom "builtins" "len"
    if k == 2 then return ← Proto.qualifiedRef "math" "pi"
    if k == 3 then return ← Proto.qualifiedRef "builtins" "nope"
    Proto.importFrom "builtins" "__dict__"
    : PyM σ .writes true Value)

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

/-- `checkKwargs` of a kwargs dict whose key is an instance of a subclass of `str`, which CPython
accepts: a gap. -/
@[dyn_sem PyT.kwargsStrSub, expose] public def kwargsStrSub (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let ns ← PyPure.allocDict
    let c ← PyPure.allocObj (.builtin .type) (.cls
      { name := "S", qualname := "S", «module» := "m", bases := #[.builtin .str],
        mroTail := #[.builtin .str, .builtin .object], ns, solidBase := .builtin .str })
    let k ← PyReads.allocInstance c (.str (.ofString "a")) #[] #[]
    let kw ← PyPure.allocDict
    PyWrites.dictSet kw k (.int 1) (some (.exact 7)) fun _ => pure false
    Proto.checkKwargs kw
    pure Value.none
    : PyM σ .writes true Value)

/-- `|` and `|=` of dicts with an instance `d` of a subclass `D` of `dict` that holds one entry:
`{} | d` (`0`) and `e |= d` (`1`) when `D` sets `__iter__`, which makes CPython's merge take its
slow path; `d | {}` with that `D` (`2`); `{} | d` when `D` sets `keys` (`3`) or
`__getattribute__` (`4`), which CPython's lookup of `keys` runs; `d | {}` when `D` sets
`__getattribute__`, which `PyDict_Copy` doesn't look at (`5`); and `{} | d` when `D` keeps
dict's reads (`6`). The cases that read the entries directly give the result's length. -/
@[dyn_sem PyT.dictOrSub, expose] public def dictOrSub (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let ns ← PyPure.allocDict
    let set? : Option String := match k with
      | 0 | 1 | 2 => some "__iter__"
      | 3 => some "keys"
      | 4 | 5 => some "__getattribute__"
      | _ => none
    if let some n := set? then
      PyNew.dictSetNew ns (Value.ofString n) (.builtin .tuple) none fun _ => pure false
    let c ← PyPure.allocObj (.builtin .type) (.cls
      { name := "D", qualname := "D", «module» := "m", bases := #[.builtin .dict],
        mroTail := #[.builtin .dict, .builtin .object], ns, solidBase := .builtin .dict })
    let d ← PyReads.allocInstance c .dict #[] #[]
    PyWrites.dictSet d (.int 1) (.int 10) none fun _ => pure false
    let e ← PyPure.allocDict
    let r ← match k with
      | 1 => Builtins.dictIorBody e (.tuple #[d]) (← PyPure.allocDict)
      | 2 | 5 => Builtins.dictOrBody "__or__" false d (.tuple #[e]) (← PyPure.allocDict)
      | _ => Builtins.dictOrBody "__or__" false e (.tuple #[d]) (← PyPure.allocDict)
    pure (Value.int (← PyReads.dictLen r))
    : PyM σ .writes true Value)

/-- A write of `__name__` (`0`) and of a plain name (`1`), a deletion of a plain name (`2`), and
`object.__setattr__` (`3`) and `object.__delattr__` (`4`) of a plain name, on a native function:
each stops with a gap. -/
@[dyn_sem PyT.nativeWrite, expose] public def nativeWrite (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let f ← PyPure.allocObj (.builtin .function) (.native
      { key := "k", kind := .function, name := "cast", qualname := "cast", «module» := "typing" })
    match k with
    | 0 => Proto.setAttr f "__name__" (some (Value.ofString "z"))
    | 1 => Proto.setAttr f "foo" (some (.int 1))
    | 2 => Proto.setAttr f "foo" none
    | 3 => discard <| Builtins.objectSetattr f (.tuple #[Value.ofString "foo", .int 1]) (← PyPure.allocDict)
    | _ => discard <| Builtins.objectDelattr f (.tuple #[Value.ofString "foo"]) (← PyPure.allocDict)
    pure Value.none
    : PyM σ .writes true Value)

/-- A write of a plain name to `int`, an immutable built-in type: CPython's `TypeError`. (The
message of a type whose C name differs from its name is `pt.hooks(31)`'s.) -/
@[dyn_sem PyT.immutableWrite, expose] public def immutableWrite (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    Proto.setAttr (.builtin .int) "x" (some (.int 1))
    pure Value.none
    : PyM σ .writes true Value)

/-- `guardDictWalk` of an empty dict into an instance of a subclass of `dict`, which it reads as a
dict: `None` when the instance is empty (`0`), and the gap of a walk that may run user code when
it holds a key of a user class with an exact hash (`1`). -/
@[dyn_sem PyT.dictWalkSub, expose] public def dictWalkSub (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let ns ← PyPure.allocDict
    let c ← PyPure.allocObj (.builtin .type) (.cls
      { name := "D", qualname := "D", «module» := "m", bases := #[.builtin .dict],
        mroTail := #[.builtin .dict, .builtin .object], ns, solidBase := .builtin .dict })
    let d ← PyReads.allocInstance c .dict #[] #[]
    if k == 1 then
      let kns ← PyPure.allocDict
      let kc ← PyPure.allocObj (.builtin .type) (.cls
        { name := "K", qualname := "K", «module» := "m", bases := #[.builtin .object],
          mroTail := #[.builtin .object], ns := kns, solidBase := .builtin .object })
      let key ← PyReads.allocInstance kc .plain #[] #[]
      PyNew.dictSetNew d key (.int 1) (some (.exact 7)) fun _ => pure false
    Proto.guardDictWalk (← PyPure.allocDict) d
    pure Value.none
    : PyM σ .reads false Value)

/-- The object primitives that the operations of this piece don't reach, or reach only in part, on
a new class `C` with the slots `a` and `b` and no instance dict, and an instance of it: set slot 1,
read slots 1 and 0, delete slot 1 and read it again; the instance's `__dict__` (none); rename the
class `D`; give it the MRO `(D, int, object)`; add a module `mm` and read it back; and set and
read the count of running `__build_class__` calls; and the bytes of an instance of a class
`B(bytes)`. -/
@[dyn_sem PyT.objPrims, expose] public def objPrims (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let object := Value.builtin .object
    let c ← PyPure.allocObj (.builtin .type) (.cls
      { name := "C", qualname := "C", «module» := "m", bases := #[object], mroTail := #[object],
        ns := ← PyPure.allocDict, solidBase := .none, instanceDict := false, slots := #["a", "b"] })
    let o ← PyReads.allocInstance c .plain #[] #[none, none]
    PyWrites.slotSet o 1 (.int 7)
    let s1 ← PyReads.slotGet o 1
    let s0 ← PyReads.slotGet o 0
    PyWrites.slotDel o 1
    let s1' ← PyReads.slotGet o 1
    let d ← PyReads.objDict o
    PyWrites.classSetName c "D" "D"
    PyNew.classSetMroNew c #[.builtin .int, object]
    let some cd ← Proto.classData? c | pure (Value.ofString "not a class")
    let mo ← PyPure.allocObj (.builtin .module) (.module "mm" #[] false #[])
    PyReads.moduleAdd "mm" mo
    let back ← PyReads.moduleGet "mm"
    let bytes := Value.builtin .bytes
    let bc ← PyPure.allocObj (.builtin .type) (.cls
      { name := "B", qualname := "B", «module» := "m", bases := #[bytes], mroTail := #[bytes, object],
        ns := ← PyPure.allocDict, solidBase := bytes })
    let bv ← PyReads.bytesView (← PyReads.allocInstance bc (.bytes #[1]) #[] #[])
    pure (Value.tuple #[s1.getD (.ofString "unset"), s0.getD (.ofString "unset"),
      s1'.getD (.ofString "unset"), .bool d.isSome, .ofString cd.name, .ofString cd.qualname,
      .tuple cd.mroTail, .bool (back == some mo), .bool (bv == some #[1])])
    : PyM σ .writes false Value)

/-- A signature for the binder's tests. -/
public def sigOf (name qualname : String) (style : Builtins.BindStyle) (posonly minpos maxpos : Nat)
    (kwnames : Array String := #[]) : Builtins.BuiltinSig :=
  { name, qualname, style, posonly, minpos, maxpos, kwnames }

/-- The signature of `sum`, with the message style of Argument Clinic with keywords. -/
public def sumSig : Builtins.BuiltinSig := sigOf "sum" "sum" .keywords 1 1 2 #["start"]

/-- The binder's case `i`: a built-in's signature, positional arguments and keywords, as in
CPython 3.12's calls `[].append()`, `[].append(x=1)`, `"a".upper(1)`, `[].pop(1, 2)`,
`divmod(1)`, `getattr(1)`, `sum()`, `sum(1, 2, 3)`, `sum([], x=1)`, `"a".split(" ", sep=" ")`,
`round()`, `[].sort(1)`, `"a".splitlines(1, 2)`, `(1).__add__()`, `(1).__add__(x=1)`,
`sum(a=1, b=2, c=3)` and `sum([1], start=5)`. -/
public def bindArgsOf (i : Int) : Builtins.BuiltinSig × Array Value × Array (String × Value) :=
  let one := Value.int 1
  let append := sigOf "append" "list.append" .methO 0 0 0
  let add := sigOf "__add__" "int.__add__" .wrapper 0 0 1
  match i with
  | 0 => (append, #[], #[])
  | 1 => (append, #[], #[("x", one)])
  | 2 => (sigOf "upper" "str.upper" .noArgs 0 0 0, #[one], #[])
  | 3 => (sigOf "pop" "list.pop" .posOnly 1 0 1, #[one, one], #[])
  | 4 => (sigOf "divmod" "divmod" .posOnly 2 2 2, #[one], #[])
  | 5 => (sigOf "getattr" "getattr" .posOnly 3 2 3, #[one], #[])
  | 6 => (sumSig, #[], #[])
  | 7 => (sumSig, #[one, one, one], #[])
  | 8 => (sumSig, #[one], #[("x", one)])
  | 9 => (sigOf "split" "str.split" .keywords 0 0 2 #["sep", "maxsplit"], #[.ofString " "],
      #[("sep", .ofString " ")])
  | 10 => (sigOf "round" "round" .keywords 0 1 2 #["number", "ndigits"], #[], #[])
  | 11 => (sigOf "sort" "list.sort" .keywords 0 0 0 #["key", "reverse"], #[one], #[])
  | 12 => (sigOf "splitlines" "str.splitlines" .keywords 0 0 1 #["keepends"], #[one, one], #[])
  | 13 => (add, #[], #[])
  | 14 => (add, #[], #[("x", one)])
  | 15 => (sumSig, #[], #[("a", one), ("b", one), ("c", one)])
  | _ => (sumSig, #[.tuple #[one]], #[("start", .int 5)])

/-- The binder on case `i` of `bindArgsOf`: the bound parameters (`'unset'` for one not given)
and the collected positional arguments, or the binder's `TypeError`. -/
@[dyn_sem PyT.bindCase, expose] public def bindCase (i : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let (sig, xs, kws) := bindArgsOf i
    let kw ← PyPure.allocDict
    for (k, v) in kws do PyNew.dictSetNew kw (Value.ofString k) v none fun _ => pure false
    let b ← Builtins.bindBuiltinArgs sig (Value.tuple xs) kw
    pure (Value.tuple #[.tuple (b.params.map (·.getD (.ofString "unset"))), .tuple b.rest])
    : PyM σ .reads false Value)

/-- The operators on `x = I(5)` for a class `I(int)` with no dunders of its own, which run
`int`'s slots on its built-in part: `x + 1`, `1 + x`, `x == 5`, `hash(x)`, `-x`, `bool(x)`, and
`t[x]` for a tuple `t` of six elements, as CPython gives them. -/
@[dyn_sem PyT.subclassOps, expose] public def subclassOps (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let int := Value.builtin .int
    let object := Value.builtin .object
    let i ← PyPure.allocObj (.builtin .type) (.cls
      { name := "I", qualname := "I", «module» := "m", bases := #[int], mroTail := #[int, object],
        ns := ← PyPure.allocDict, solidBase := int })
    let x ← PyReads.allocInstance i (.int 5) #[] #[]
    let one := Value.int 1
    let t := Value.tuple ((List.range 6).toArray.map (Value.int ∘ Int.ofNat))
    pure (Value.tuple #[← Proto.binaryOp .add x one, ← Proto.binaryOp .add one x,
      .bool (← Proto.richCompare .eq x (.int 5)), ← PyPure.hashValue (← Proto.hash x),
      ← Proto.unaryOp .neg x, .bool (← Proto.truthy x), ← Proto.getItem t x])
    : PyM σ .calls false Value)

/-- A class `name(base)` with no dunders of its own. -/
public def subclassOf (name : String) (base : Builtin) : PyM σ .writes false Value := do
  PyPure.allocObj (.builtin .type) (.cls
    { name, qualname := name, «module» := "m", bases := #[.builtin base],
      mroTail := #[.builtin base, .builtin .object], ns := ← PyPure.allocDict,
      solidBase := .builtin base.info.solidBase })

/-- A class `T(tuple)` whose namespace binds `name` to `list`'s slot wrapper, and an instance of
it holding `(1,)`. -/
public def foreignSlot (name : String) : PyM σ .writes false Value := do
  let c ← subclassOf "T" .tuple
  let some cd ← Proto.classData? c | PyM.gap "not a class"
  PyWrites.dictSet cd.ns (.ofString name) (.descr .list name .slotWrapper) none fun _ => pure false
  PyReads.allocInstance c (.tuple #[.int 1]) #[] #[]

/-- `iter(T((1,)))` where `T.__iter__ = list.__iter__`: the fast path doesn't apply, and the
dispatch checks the slot wrapper's type. -/
@[dyn_sem PyT.foreignIter, expose] public def foreignIter (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do Proto.getIter (← foreignSlot "__iter__") : PyM σ .writes false Value)

/-- `BaseExceptionGroup("m", T((1,)))` where `T.__len__` is another type's: CPython's
`PySequence_Tuple` would call it for a length hint. -/
@[dyn_sem PyT.groupLenHint, expose] public def groupLenHint (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let c ← subclassOf "T" .tuple
    let some cd ← Proto.classData? c | PyM.gap "not a class"
    PyWrites.dictSet cd.ns (.ofString "__len__") (.descr .str "__len__" .slotWrapper) none fun _ => pure false
    let inst ← PyReads.allocInstance c (.tuple #[.int 1]) #[] #[]
    Proto.callN 5 (.builtin .BaseExceptionGroup) (.tuple #[.ofString "m", inst]) (← PyPure.allocDict)
    : PyM σ .writes false Value)

/-- `len(T((1,)))` where `T.__len__ = list.__len__`, as `foreignIter`. -/
@[dyn_sem PyT.foreignLen, expose] public def foreignLen (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    pure (Value.int (← Proto.pyLen (← foreignSlot "__len__"))) : PyM σ .writes false Value)

/-- The type of `iter(S("ab"))` for a class `S(str)`: `str_iterator`, as CPython makes for an
ASCII instance of a subclass of `str`. -/
@[dyn_sem PyT.strSubIter, expose] public def strSubIter (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let v ← PyReads.allocInstance (← subclassOf "S" .str) (.str (.ofString "ab")) #[] #[]
    let some it ← Proto.builtinIter? v | PyM.gap "no iterator"
    PyReads.classOf it : PyM σ .writes false Value)

/-- A list of the ints `xs`. -/
public def intList (xs : List Int) : PyM σ .writes true Value :=
  PyPure.allocList (xs.toArray.map Value.int)

/-- The walk bounds of iterators made directly: a `zip` over list iterators with 3 and 2 items
left, an empty `zip`, a `zip` of that `zip`, a `zip` over a value that is no built-in iterator, an
`enumerate`, a `reversed` and a `list_reverseiterator` at index 2, a `reversed` at index -1, a
dict reverse iterator over 2 entries; and a nest of `zip`s with a budget of one visit and with a
depth of one. -/
@[dyn_sem PyT.iterBounds, expose] public def iterBounds (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let l3 ← intList [1, 2, 3]
    let l2 ← intList [1, 2]
    let i3 ← Proto.newIter .list_iterator (.seq .list_iterator l3 0)
    let i2 ← Proto.newIter .list_iterator (.seq .list_iterator l2 0)
    let z ← Proto.newIter .zip (.zip #[i3, i2] false)
    let ze ← Proto.newIter .zip (.zip #[] false)
    let zz ← Proto.newIter .zip (.zip #[z] false)
    let zu ← Proto.newIter .zip (.zip #[i3, .none] false)
    let e ← Proto.newIter .enumerate (.enumerate i3 0)
    let r ← Proto.newIter .reversed (.reversed .reversed l3 2)
    let lr ← Proto.newIter .list_reverseiterator (.reversed .list_reverseiterator l3 2)
    let rm ← Proto.newIter .reversed (.reversed .reversed l3 (-1))
    let d ← PyPure.allocDict
    PyWrites.dictSet d (.int 1) (.int 1) none fun _ => pure false
    PyWrites.dictSet d (.int 2) (.int 2) none fun _ => pure false
    let dr ← Proto.newIter .dict_reversekeyiterator (.dictReversed .dict_reversekeyiterator d 1 2 0 2)
    let bounds ← [z, ze, zz, zu, e, r, lr, rm, dr].mapM fun it => Proto.walkBound it
    let small ← (Proto.walkBoundIn 64 1 zz : PyM σ .writes true _)
    let shallow ← (Proto.walkBoundIn 1 64 zz : PyM σ .writes true _)
    pure (.tuple ((bounds ++ [small.1, shallow.1]).toArray.map fun n => Value.int (Int.ofNat n))) :
    PyM σ .writes true Value)

/-- The next item of an iterator of the state `st` and the type `kind`, made directly: the call of
its type's `__next__`. -/
public def nextOf (kind : Builtin) (st : Value → IterState) : PyM σ .writes true Value := do
  let it ← Proto.newIter kind (st (← intList [1, 2, 3]))
  match ← Proto.iterStep it with
  | some v => pure v
  | none => pure (.ofString "end")

@[dyn_sem PyT.zipNext, expose] public def zipNext (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let it ← Proto.getIter (m := PyM σ .writes true) (← intList [1, 2, 3])
    nextOf .zip fun _ => .zip #[it] false)

@[dyn_sem PyT.enumNext, expose] public def enumNext (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let it ← Proto.getIter (m := PyM σ .writes true) (← intList [1, 2, 3])
    nextOf .enumerate fun _ => .enumerate it 0)

@[dyn_sem PyT.revNext, expose] public def revNext (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (nextOf .reversed fun l => .reversed .reversed l 2)

@[dyn_sem PyT.listRevNext, expose] public def listRevNext (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (nextOf .list_reverseiterator fun l => .reversed .list_reverseiterator l 2)

@[dyn_sem PyT.dictRevNext, expose] public def dictRevNext (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (do
    let d ← PyPure.allocDict
    nextOf .dict_reversekeyiterator fun _ => .dictReversed .dict_reversekeyiterator d (-1) 0 0 0)

/-- A slice assignment `l[-1:] = [7]` on `[1, 2, 3]`, given the stale elements `[1]`, as when the
list changed while its items were read: the slice is fitted to the list as it is, and the rule
returns the list's elements after the write. -/
@[dyn_sem PyT.staleSlice, expose] public def staleSlice (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let l ← intList [1, 2, 3]
    let key := PyPure.imm (m := PyM σ .writes true) (.slice (.int (-1)) .none .none)
    Proto.listSetItem l #[(.int 1)] key (← intList [7])
    let some xs ← Proto.listOf? l | pure .none
    pure (.tuple xs))

/-- `machinesStart` with no fuel left. -/
@[dyn_sem PyT.startZero, expose] public def startZero (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    discard <| machinesStart 0 .none (.tuple #[]) (← PyPure.allocDict)
    pure .none)

/-- An instance of a subclass of `str` where CPython asks for a `str` and accepts the instance, for
a class `S(str)` and `q = S("C")`: `type("C", (), ns)` with `q` as the `__qualname__` in `ns`
(`0`), with an instance of a class `M(Quitter, str)` instead, whose MRO starts with another
built-in type (`1`), with `q` as the name (`3`), as an item of `__slots__` (`4`) or as the
`__module__` (`5`); `object.__setattr__` (`6`), `object.__delattr__` (`7`) and
`object.__getattribute__` (`8`) with `q` as the name; the `repr` of a class whose `__module__` is
`q` (`9`); and a keyword `q` of a built-in's call (`10`). The other side of the check: an
instance of a class `B(bytes)` as the `__qualname__` (`2`), which CPython rejects. -/
@[dyn_sem PyT.strSubArg, expose] public def strSubArg (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let q ← PyReads.allocInstance (← subclassOf "S" .str) (.str (.ofString "C")) #[] #[]
    let arg ← match k with
      | 1 => do
        let mixin ← PyPure.allocObj (.builtin .type) (.cls
          { name := "M", qualname := "M", «module» := "m",
            bases := #[.builtin .«_sitebuiltins.Quitter», .builtin .str],
            mroTail := #[.builtin .«_sitebuiltins.Quitter», .builtin .str, .builtin .object],
            ns := ← PyPure.allocDict, solidBase := .builtin .str })
        PyReads.allocInstance mixin (.str (.ofString "C")) #[] #[]
      | 2 => PyReads.allocInstance (← subclassOf "B" .bytes) (.bytes #[67]) #[] #[]
      | _ => pure q
    let ns ← PyPure.allocDict
    let setNs (n : String) (v : Value) : PyM σ .writes false Unit :=
      PyWrites.dictSet ns (.ofString n) v none fun _ => pure false
    let newClass (name : Value) : PyM σ .writes false Value := do
      Builtins.typeNew (.builtin .type) (.tuple #[.builtin .type, name, .tuple #[], ns])
        (← PyPure.allocDict)
    match k with
    | 0 | 1 | 2 => setNs "__module__" (.ofString "m"); setNs "__qualname__" arg; newClass (.ofString "C")
    | 3 => setNs "__module__" (.ofString "m"); newClass q
    | 4 => setNs "__module__" (.ofString "m"); setNs "__slots__" (.tuple #[q]); newClass (.ofString "C")
    | 5 => setNs "__module__" q; newClass (.ofString "C")
    | 6 => Builtins.objectSetattr q (.tuple #[q, .int 1]) (← PyPure.allocDict)
    | 7 => Builtins.objectDelattr q (.tuple #[q]) (← PyPure.allocDict)
    | 8 => Builtins.objectGetattribute q (.tuple #[q]) (← PyPure.allocDict)
    | 9 => do
      setNs "__module__" q
      let c ← PyPure.allocObj (.builtin .type) (.cls
        { name := "C", qualname := "C", «module» := "m", bases := #[.builtin .object],
          mroTail := #[.builtin .object], ns, solidBase := .builtin .object })
      pure (Value.ofString (← Proto.typeRepr c))
    | _ => do
      let kw ← PyPure.allocDict
      PyWrites.dictSet kw q (.int 1) (some (.exact 7)) fun _ => pure false
      pure (Value.int (← Builtins.kwPairs kw).size)
    : PyM σ .writes false Value)

/-- A value for a function of the tests to give: an instance of a class `I(int)` that holds `9`
(`0`), an instance of a class `E(str)` that holds `""` (`1`), the `str` `"x"` (`2`), or an instance
of a class `F(float)` that holds `1.5` (`3`). -/
@[dyn_sem PyT.mkSubInst, expose] public def mkSubInst (j : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    match j with
    | 0 => PyReads.allocInstance (← subclassOf "I" .int) (.int 9) #[] #[]
    | 1 => PyReads.allocInstance (← subclassOf "E" .str) (.str (.ofString "")) #[] #[]
    | 2 => pure (Value.ofString "x")
    | _ => PyReads.allocInstance (← subclassOf "F" .float) (.float 0x3FF8000000000000) #[] #[]
    : PyM σ .writes false Value)

/-- A new `TypeError("t")` (`0`) or `ValueError("v")` (`1`), not raised. -/
@[dyn_sem PyT.mkExc, expose] public def mkExc (j : Int) (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    tryCatch (Proto.raiseBuiltin (if j == 0 then "TypeError" else "ValueError") (if j == 0 then "t" else "v"))
      pure
    : PyM σ .writes false Value)

/-- Instances of subclasses of built-in types where CPython accepts them, with `f` a function of
no arguments that gives `pt.mkSubInst`'s value and `g` one that raises `pt.mkExc`'s exception:
`hash(o)` for an `o` whose class's `__hash__` is `f`, with `f` giving an instance of a class
`I(int)` holding `9` (`0`, CPython's `9`), the `str` `"x"` (`8`) or an instance of a class
`F(float)` (`9`), both CPython's `TypeError`; `S({5}) in {frozenset({5})}` for a class `S(set)` (`1`,
CPython's `True`, through its frozenset copy), the same with `S.__hash__ = f` (`2`, CPython's
`False`, since the hash `9` finds nothing), with an `S.__hash__` that raises `ValueError` (`6`,
which CPython lets out), and `S({5}) in {9, frozenset({5})}` with `S.__hash__ = f` and an
`S.__eq__` that raises `TypeError`, which the comparison with `9` reaches (`7`, CPython's `True`,
through the copy); for a class `T(str)` and `x = T("abc")`, `format(x, "s")` (`3`) and `x % ()`
(`4`), each of which CPython gives as `x` itself; and `format(i, "")` for an instance `i` of a class
`J(int)` whose `__str__` is `f`, giving an instance of a class `E(str)` holding `""` (`5`,
CPython's exact `''`). -/
@[dyn_sem PyT.subclassCases, expose] public def subclassCases (f g : Value) (k : Int)
    (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    match k with
    | 0 | 8 | 9 => do
      let ns ← PyPure.allocDict
      PyWrites.dictSet ns (.ofString "__hash__") f none fun _ => pure false
      let c ← PyPure.allocObj (.builtin .type) (.cls
        { name := "C", qualname := "C", «module» := "m", bases := #[.builtin .object],
          mroTail := #[.builtin .object], ns, solidBase := .builtin .object })
      let o ← PyReads.allocInstance c .plain #[] #[]
      match ← Proto.hash o with
      | .exact h => pure (Value.int h)
      | _ => pure (Value.ofString "not an exact hash")
    | 1 | 2 | 6 | 7 => do
      let ns ← PyPure.allocDict
      if k == 2 || k == 7 then PyWrites.dictSet ns (.ofString "__hash__") f none fun _ => pure false
      if k == 6 then PyWrites.dictSet ns (.ofString "__hash__") g none fun _ => pure false
      if k == 7 then PyWrites.dictSet ns (.ofString "__eq__") g none fun _ => pure false
      let c ← PyPure.allocObj (.builtin .type) (.cls
        { name := "S", qualname := "S", «module» := "m", bases := #[.builtin .set],
          mroTail := #[.builtin .set, .builtin .object], ns, solidBase := .builtin .set })
      let x ← PyReads.allocInstance c .set #[] #[]
      PyWrites.setAdd x (Value.int 5) none fun _ => pure false
      let fz ← PyPure.allocSet true false
      PyNew.setAddNew fz (Value.int 5) none fun _ => pure false
      PyNew.setFreezeNew fz
      let t ← PyPure.allocSet false false
      if k == 7 then PyNew.setAddNew t (Value.int 9) none fun _ => pure false
      PyNew.setAddNew t fz (some (← Proto.hash fz)) fun _ => pure false
      pure (Value.bool (← Proto.containsCore x t))
    | 5 => do
      let ns ← PyPure.allocDict
      PyWrites.dictSet ns (.ofString "__str__") f none fun _ => pure false
      let c ← PyPure.allocObj (.builtin .type) (.cls
        { name := "J", qualname := "J", «module» := "m", bases := #[.builtin .int],
          mroTail := #[.builtin .int, .builtin .object], ns, solidBase := .builtin .int })
      Proto.formatOf (← PyReads.allocInstance c (.int 9) #[] #[]) (.ofString "")
    | _ => do
      let x ← PyReads.allocInstance (← subclassOf "T" .str) (.str (.ofString "abc")) #[] #[]
      let r ← if k == 3 then Proto.formatOf x (.ofString "s")
        else Builtins.strModBody "__mod__" false x (.tuple #[.tuple #[]]) (← PyPure.allocDict)
      pure (Value.tuple #[r, Value.bool (r == x)])
    : PyM σ .writes false Value)

/-- `__build_class__(f, name)` for a class body `f`, with an instance of a class `S(str)` as the
name (`0`), which CPython accepts, and with `3` (`1`), which it rejects. -/
@[dyn_sem PyT.buildClassName, expose] public def buildClassName (f : Value) (k : Int)
    (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let name ← if k == 0 then
        PyReads.allocInstance (← subclassOf "S" .str) (.str (.ofString "C")) #[] #[]
      else pure (Value.int 3)
    Builtins.buildClass .none (.tuple #[f, name]) (← PyPure.allocDict)
    : PyM σ .writes false Value)

/-- `m + [3]` for an instance `m` of a class `M(list)` that holds `[1]` and defines `__radd__`
(`0`), `__mul__` (`1`) or `__iadd__` (`2`), and `m * [3]` with `__mul__ = list.__add__` (`3`).
`__radd__` makes CPython's number slot call the list's `+`, which the model doesn't follow, so `0`
stops with a gap, and so does `2`, a conservative gap, since `__iadd__` is a separate in-place
slot; `__mul__` is of the other family, so `1` gives the list's own concatenation, equal to
`[1, 3]`; and `3`, the list's `+` slot found as `__mul__`, which CPython calls, stops with a gap. -/
@[dyn_sem PyT.seqSlotSub, expose] public def seqSlotSub (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let ns ← PyPure.allocDict
    let d := if k == 0 then "__radd__" else if k == 2 then "__iadd__" else "__mul__"
    let v := if k == 3 then Value.descr .list "__add__" .slotWrapper else .builtin .len
    PyWrites.dictSet ns (.ofString d) v none fun _ => pure false
    let c ← PyPure.allocObj (.builtin .type) (.cls
      { name := "M", qualname := "M", «module» := "m", bases := #[.builtin .list],
        mroTail := #[.builtin .list, .builtin .object], ns, solidBase := .builtin .list })
    let x ← PyReads.allocInstance c (.list #[.int 1]) #[] #[]
    let r ← Proto.binaryOp (if k == 3 then .mul else .add) x (← PyPure.allocList #[.int 3])
    pure (Value.bool (← Proto.richCompare .eq r (← PyPure.allocList #[.int 1, .int 3])))
    : PyM σ .writes false Value)

/-- A subclass of a sequence whose own `__add__`, `__mul__` or `__rmul__` gives `NotImplemented`
(`object.__eq__` here), which clears the sequence's concatenation or repetition in CPython:
`T((1,)) + U()` for a plain `U` (`0`), `L([1]) + [2]` (`1`), `M([1]) * 2` (`2`), `TM((1,)) * 2`
(`3`), `x *= 2` for `x = TM((1,))` (`4`), `2 * TR((1,))` with `TR.__rmul__` (`5`), `x *= TR((1,))`
for `x = 2` (`8`) and `S("a") + "b"` for an `S(str)` (`9`), each CPython's `TypeError`; also
`P((1,)) + (2,)` for a `P(tuple)` with no dunders of its own (`6`), CPython's `(1, 2)`; and
`I((1,)) * [5]` for an `I(tuple)` whose `__index__` is `tuple.__len__` (`7`), CPython's
`TypeError`, since only the left operand's repetition runs; and, past the operator's dunders,
the sequence fallback of `LT([1]) + [2]` for an `LT(list)` whose `__add__` is `tuple.__add__`
(`10`) and of `TL((1,)) * 2` for a `TL(tuple)` whose `__rmul__` is `list.__rmul__` (`11`), each
CPython's `TypeError`, since another sequence type's slot clears the slot too. -/
@[dyn_sem PyT.seqSlotCleared, expose] public def seqSlotCleared (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let ns ← PyPure.allocDict
    let (name, base, d) : String × Builtin × String := match k with
      | 0 => ("T", .tuple, "__add__") | 1 => ("L", .list, "__add__") | 2 => ("M", .list, "__mul__")
      | 3 | 4 => ("TM", .tuple, "__mul__") | 5 | 8 => ("TR", .tuple, "__rmul__")
      | 7 => ("I", .tuple, "__index__") | 9 => ("S", .str, "__add__")
      | 10 => ("LT", .list, "__add__") | 11 => ("TL", .tuple, "__rmul__") | _ => ("P", .tuple, "")
    if d == "__index__" then
      PyWrites.dictSet ns (.ofString d) (Value.descr .tuple "__len__" .slotWrapper) none fun _ => pure false
    else if k == 10 then
      PyWrites.dictSet ns (.ofString d) (Value.descr .tuple "__add__" .slotWrapper) none fun _ => pure false
    else if k == 11 then
      PyWrites.dictSet ns (.ofString d) (Value.descr .list "__rmul__" .slotWrapper) none fun _ => pure false
    else if d != "" then
      PyWrites.dictSet ns (.ofString d) (Value.descr .object "__eq__" .slotWrapper) none fun _ => pure false
    let c ← PyPure.allocObj (.builtin .type) (.cls
      { name, qualname := name, «module» := "m", bases := #[.builtin base],
        mroTail := #[.builtin base, .builtin .object], ns, solidBase := .builtin base })
    let part : BuiltinPart Value := match base with
      | .list => .list #[.int 1] | .str => .str (.ofString "a") | _ => .tuple #[.int 1]
    let x ← PyReads.allocInstance c part #[] #[]
    match k with
    | 0 => do
      let u ← PyReads.allocInstance (← subclassOf "U" .object) .plain #[] #[]
      Proto.binaryOp .add x u
    | 1 => Proto.binaryOp .add x (← PyPure.allocList #[.int 2])
    | 2 | 3 => Proto.binaryOp .mul x (.int 2)
    | 4 => Proto.inplaceOp .mul x (.int 2)
    | 5 => Proto.binaryOp .mul (.int 2) x
    | 7 => Proto.binaryOp .mul x (← PyPure.allocList #[.int 5])
    | 8 => Proto.inplaceOp .mul (.int 2) x
    | 9 => Proto.binaryOp .add x (.ofString "b")
    | 10 => Proto.binaryTail "+" .add x (← PyPure.allocList #[.int 2])
    | 11 => Proto.binaryTail "*" .mul x (.int 2)
    | _ => Proto.binaryOp .add x (.tuple #[.int 2])
    : PyM σ .writes false Value)

/-- `in` with an instance of a class `S(str)` and `repr` of an instance of a subclass of `set`:
`S("a") in "ab"` (`0`), `S("ab") in S("ab")` (`1`) and `S("z") in "ab"` (`2`), CPython's `True`,
`True` and `False`; `repr(Q({1}))` for a `Q(set)` that defines `__iter__` (`3`) or `__len__`
(`4`), which CPython's `set_repr` runs through `PySequence_List`, so the model stops with a gap;
`repr(P({1}))` for a `P(set)` with neither (`5`), CPython's `P({1})`; `repr(Q())` for a `Q(set)`
that defines `__iter__` (`6`), CPython's `Q()`, since an empty set lists nothing; `repr(Q({1}))`
for a `Q(M, set)` whose user base `M` defines `__iter__` (`7`), a gap; and `I(1) in "ab"` for a
class `I(int)` (`8`), CPython's `TypeError`. -/
@[dyn_sem PyT.strSetSubOps, expose] public def strSetSubOps (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let sc ← subclassOf "S" .str
    let mk (t : String) : PyM σ .writes false Value :=
      PyReads.allocInstance sc (.str (.ofString t)) #[] #[]
    match k with
    | 0 => pure (Value.bool (← Proto.contains (← mk "a") (.ofString "ab")))
    | 1 => pure (Value.bool (← Proto.contains (← mk "ab") (← mk "ab")))
    | 2 => pure (Value.bool (← Proto.contains (← mk "z") (.ofString "ab")))
    | 8 => do
      let i ← PyReads.allocInstance (← subclassOf "I" .int) (.int 1) #[] #[]
      pure (Value.bool (← Proto.contains i (.ofString "ab")))
    | _ => do
      let ns ← PyPure.allocDict
      if k == 3 || k == 6 then
        PyWrites.dictSet ns (.ofString "__iter__") (.builtin .len) none fun _ => pure false
      if k == 4 then PyWrites.dictSet ns (.ofString "__len__") (.builtin .len) none fun _ => pure false
      let name := if k == 5 then "P" else "Q"
      let c ← if k == 7 then do
          let mns ← PyPure.allocDict
          PyWrites.dictSet mns (.ofString "__iter__") (.builtin .len) none fun _ => pure false
          let mc ← PyPure.allocObj (.builtin .type) (.cls
            { name := "M", qualname := "M", «module» := "m", bases := #[.builtin .object],
              mroTail := #[.builtin .object], ns := mns, solidBase := .builtin .object })
          PyPure.allocObj (.builtin .type) (.cls
            { name, qualname := name, «module» := "m", bases := #[mc, .builtin .set],
              mroTail := #[mc, .builtin .set, .builtin .object], ns, solidBase := .builtin .set })
        else PyPure.allocObj (.builtin .type) (.cls
          { name, qualname := name, «module» := "m", bases := #[.builtin .set],
            mroTail := #[.builtin .set, .builtin .object], ns, solidBase := .builtin .set })
      let x ← PyReads.allocInstance c .set #[] #[]
      if k != 6 then PyWrites.setAdd x (Value.int 1) none fun _ => pure false
      Proto.reprOf x
    : PyM σ .writes false Value)

/-- The operators on instances of classes `L(list)`, `T(tuple)` and `D(dict)` with no dunders of
their own, which run the built-in type's slots on the built-in part: for `l = L([1, 2])`,
`t = T((1, 2))` and `d = D({1: 'a'})`, the results of `(l + [3])[2]`, `l == [1, 2]`, `bool(l)`,
`2 in l`, `l[0] = 9` then `l[0]`, `(t * 2)[3]`, `t == (1, 2)`, `t < (1, 3)`, `d[1]`, `1 in d`, and
`d == {1: 'a'}`, and, for `s = {1}` and `t = S2({2})` with a class `S2(set)`, whether `s |= t`
gives `s` itself and `2 in s`, as CPython gives them. -/
@[dyn_sem PyT.subclassContainers, expose] public def subclassContainers (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let one := Value.int 1
    let two := Value.int 2
    let l ← PyReads.allocInstance (← subclassOf "L" .list) (.list #[one, two]) #[] #[]
    let t ← PyReads.allocInstance (← subclassOf "T" .tuple) (.tuple #[one, two]) #[] #[]
    let d ← PyReads.allocInstance (← subclassOf "D" .dict) .dict #[] #[]
    PyWrites.dictSet d one (.ofString "a") none fun _ => pure false
    let l3 ← Proto.binaryOp .add l (← PyPure.allocList #[.int 3])
    let r1 ← Proto.getItem l3 two
    let r2 ← Proto.richCompare .eq l (← PyPure.allocList #[one, two])
    let r3 ← Proto.truthy l
    let r4 ← Proto.contains two l
    Proto.setItem l (.int 0) (.int 9)
    let r5 ← Proto.getItem l (.int 0)
    let r6 ← Proto.getItem (← Proto.binaryOp .mul t two) (.int 3)
    let r7 ← Proto.richCompare .eq t (.tuple #[one, two])
    let r8 ← Proto.richCompare .lt t (.tuple #[one, .int 3])
    let r9 ← Proto.getItem d one
    let r10 ← Proto.contains one d
    let e ← PyPure.allocDict
    PyNew.dictSetNew e one (.ofString "a") none fun _ => pure false
    let r11 ← Proto.richCompare .eq d e
    -- `s |= t` with `t = S2({2})` for a class `S2(set)` changes `s` in place.
    let st ← PyPure.allocSet false false
    PyNew.setAddNew st one none fun _ => pure false
    let t2 ← PyReads.allocInstance (← subclassOf "S2" .set) .set #[] #[]
    PyWrites.setAdd t2 two none fun _ => pure false
    let r12 ← Proto.inplaceOp .or st t2
    let r13 ← Proto.contains two st
    pure (Value.tuple #[r1, .bool r2, .bool r3, .bool r4, r5, r6, .bool r7, .bool r8, r9,
      .bool r10, .bool r11, .bool ((← PyPure.identical r12 st) == .yes), .bool r13])
    : PyM σ .writes false Value)

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

/-- The body of the native `selfcall`: a call of itself. -/
public def selfcallBody : BuiltinImpl := fun self args kwargs => PyCalls.callBuiltin self args kwargs

/-- A table of bodies that holds only `selfcall`'s. -/
public def selfcallImpls : Impls :=
  { native := fun key => if key == "selfcall" then some selfcallBody else none }

/-- A native whose body calls itself, of kind `function` if `k` is `0` and of a built-in kind
otherwise, called through a table that holds only its body. -/
@[dyn_sem PyT.nativeDepth, expose] public def nativeDepth (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let impls := selfcallImpls
    let f ← PyPure.allocObj (.builtin .function) (.native
      { key := "selfcall", kind := if k == 0 then .function else .builtinFunctionOrMethod,
        name := "f", qualname := "f", «module» := "m" })
    callBuiltinWith impls 5000 f (.tuple #[]) (← PyPure.allocDict)
    : PyM σ .writes true Value)

/-- A read of the attribute `__class__` (`k = 0`) or `__doc__` (otherwise) of a native whose
`__doc__` read gaps. -/
@[dyn_sem PyT.nativeGapped, expose] public def nativeGapped (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let f ← PyPure.allocObj (.builtin .function) (.native
      { key := "selfcall", kind := .function, name := "f", qualname := "f", «module» := "m",
        gapped := #["__doc__"] })
    Proto.getAttr f (if k == 0 then "__class__" else "__doc__")
    : PyM σ .writes true Value)

/-- The class-method descriptor `dict.__dict__["fromkeys"]`: called on `(list, (1,))` (`0`), on
`(5, (1,))` (`1`) and on no argument (`2`); its `__get__` on `(None, list)` (`3`), on `(5, None)`
(`4`) and on `(None, dict)` (`5`). -/
@[dyn_sem PyT.classDescr, expose] public def classDescr (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let fk : Value := .descr .dict "fromkeys" .classMethod
    let l : Value := .tuple #[.int 1]
    let none₁ := Value.none
    match k with
    | 0 => Proto.callN 5 fk (.tuple #[.builtin .list, l]) (← PyPure.allocDict)
    | 1 => Proto.callN 5 fk (.tuple #[.int 5, l]) (← PyPure.allocDict)
    | 2 => Proto.callN 5 fk (.tuple #[]) (← PyPure.allocDict)
    | 3 => Proto.descrGetN 5 fk none (.builtin .list)
    | 4 => Proto.descrGetN 5 fk (some (.int 5)) none₁
    | _ => Proto.descrGetN 5 fk none (.builtin .dict)
    : PyM σ .writes true Value)

/-- A body that returns `7`. -/
public def sevenBody : BuiltinImpl := fun {m} {_} [_] [_] _ _ _ => pure (PyPure.imm (m := m) (.int 7))

/-- A table of bodies that holds only a body for `importHook "m"`, `sevenBody`. -/
public def hookImpls : Impls :=
  { method := fun t name => if t == .module && name == importHook "m" then some sevenBody else none }

/-- The hooks that a piece of the built-in library fills, run with this piece's part alone
(`opsImpls`), so that each still stops with the gap of a hook without a body: `isinstance(1, o)` for
an object `o` with opaque state whose class has no `__instancecheck__`, which asks the union hook
(`0`); `type[int]` (`1`) and `list[int]` (`2`); `int | None`, which asks `type.__or__` (`3`); and
`list[int]` at C depth 9000 (`4`), whose call of `list.__class_getitem__` counts a level past the
limit. -/
@[dyn_sem PyT.partHooks, expose] public def partHooks (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    letI : PyWrites (PyM σ .writes true) Value :=
      writesRecord (callBuiltinWith opsImpls.withNewCheck 5000)
    match k with
    | 0 => do
      let ns ← PyPure.allocDict
      let a ← PyPure.allocObj (.builtin .type) (.cls
        { name := "A", qualname := "A", «module» := "m", bases := #[.builtin .object],
          mroTail := #[.builtin .object], ns, solidBase := .builtin .object })
      let o ← PyPure.allocObj a (.opaque "u" #[])
      pure (.bool (← Builtins.isinstanceN 5 (.int 1) o))
    | 1 => Proto.getItem (.builtin .type) (.builtin .int)
    | 2 => Proto.getItem (.builtin .list) (.builtin .int)
    | 3 => Proto.binaryTail "|" .or (.builtin .int) .none
    | _ => PyReads.withDepth 9000 (Proto.getItem (.builtin .list) (.builtin .int))
    : PyM σ .writes true Value)

/-- A body that returns its arguments. -/
public def argsBody : BuiltinImpl := fun {_} {_} [_] [_] _ args _ => pure args

/-- A table of bodies that holds only a body for `str.maketrans`, `argsBody`. -/
public def staticImpls : Impls :=
  { method := fun t name => if t == .str && name == "maketrans" then some argsBody else none }

/-- The static method `str.maketrans`, called on `("a", "b")` through the class (`0`), through
the instance `"x"` (`1`), and as the descriptor `str.__dict__["maketrans"]` (`2`): each runs the
body on `("a", "b")`, with no `self`.  It is also one value per type and name, so two lookups of
it are identical (`3`), also through an instance (`7`), two types' are not (`4`), two lookups are
equal (`6`), and it works as a dict key (`5`). -/
@[dyn_sem PyT.staticDescr, expose] public def staticDescr (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    letI : PyWrites (PyM σ .writes true) Value :=
      writesRecord (callBuiltinWith staticImpls 5000)
    do
      if k ≥ 3 then
        -- `str.maketrans is str.maketrans` (`3`), `str.maketrans is bytes.maketrans` (`4`),
        -- `str.maketrans` as a dict key, read by a second lookup of it (`5`),
        -- `str.maketrans == str.maketrans` (`6`), and `"x".maketrans is str.maketrans` (`7`).
        let a ← Proto.getAttr (if k == 7 then Value.ofString "x" else .builtin .str) "maketrans"
        let b ← Proto.getAttr (.builtin (if k == 4 then .bytes else .str)) "maketrans"
        if k == 5 then
          let d ← Proto.mkDict #[]
          Proto.setItem d a (.int 7)
          return ← Proto.getItem d b
        if k == 6 then return ← Proto.richCompareV .eq a b
        return .bool (← Proto.isOp a b)
      let f ← match k with
        | 0 => Proto.getAttr (.builtin .str) "maketrans"
        | 1 => Proto.getAttr (Value.ofString "x") "maketrans"
        | _ => pure (.descr .str "maketrans" .staticMethod)
      Proto.callN 5 f (.tuple #[Value.ofString "a", Value.ofString "b"]) (← PyPure.allocDict)
    : PyM σ .writes true Value)

/-- The attributes that stop with a gap where a built-in type is a heap type, not a static one, or
where a class's namespace has no dict under `__annotations__`: `ExceptionGroup.__annotations__`, a heap
type's (`0`); `B.__annotations__` for a class `B` whose namespace has no entry (`1`) and whose entry
is `1` (`2`); `BuiltinImporter.create_module`, a static method of a Python function (`3`); and
`ExceptionGroup.x = 1` (`4`), which CPython sets, since `ExceptionGroup` is not an immutable type. -/
@[dyn_sem PyT.heapAttrs, expose] public def heapAttrs (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let cls (ann : Option Value) : PyM σ .writes true Value := do
      let ns ← PyPure.allocDict
      if let some a := ann then
        PyWrites.dictSet ns (Value.ofString "__annotations__") a none fun _ => pure false
      PyPure.allocObj (.builtin .type) (.cls
        { name := "B", qualname := "B", «module» := "m", bases := #[.builtin .object],
          mroTail := #[.builtin .object], ns, solidBase := .builtin .object })
    match k with
    | 0 => Proto.getAttr (.builtin .ExceptionGroup) "__annotations__"
    | 1 => Proto.getAttr (← cls none) "__annotations__"
    | 2 => Proto.getAttr (← cls (some (.int 1))) "__annotations__"
    | 3 => Proto.getAttr (.builtin .BuiltinImporter) "create_module"
    | _ => do Proto.setAttr (.builtin .ExceptionGroup) "x" (some (.int 1)); pure .none
    : PyM σ .writes true Value)

/-- A test body of a dict view's table entry `name`: a keys view's `__len__` gives `7` and its
`__contains__` `True`; its `__and__`, `__rand__`, `__or__` and `__ror__` the str of their name
without the underscores; its `__eq__` the str "eq" for a set and `NotImplemented` otherwise, and
its `__lt__` `NotImplemented`; its `mapping` getset the str "mp"; a values view's `__iter__` an
iterator over `(1, 2)`. -/
public def viewBody (name : String) : BuiltinImpl := fun {m} {_} [_] [_] _ args _ => do
  let other : m _ := do
    let some (.tuple xs) ← PyPure.immView args | PyPure.modelInvariant "an args tuple"
    let some x := xs[0]? | PyPure.modelInvariant "an argument"
    pure x
  match name with
  | "__len__" => pure (PyPure.imm (m := m) (.int 7))
  | "__contains__" => pure (PyPure.imm (m := m) (.bool true))
  | "__and__" | "__rand__" | "__or__" | "__ror__" =>
    pure (PyPure.imm (m := m) (.str (.ofString ((name.drop 2).dropEnd 2).toString)))
  | "__eq__" =>
    if (← Proto.anySet? (← other)).isSome then pure (PyPure.imm (m := m) (.str (.ofString "eq")))
    else pure (PyPure.imm (m := m) .notImplemented)
  | "__iter__" => Proto.getIter (PyPure.imm (m := m) (.tuple #[PyPure.imm (m := m) (.int 1),
      PyPure.imm (m := m) (.int 2)]))
  | "<getset mapping>" => pure (PyPure.imm (m := m) (.str (.ofString "mp")))
  | _ => pure (PyPure.imm (m := m) .notImplemented)

/-- This piece's table of bodies (`opsImpls`), with the test bodies of the dict views
(`viewBody`): `dict_keys`' `__len__`, `__contains__`, `__and__`, `__rand__`, `__or__`, `__ror__`,
`__eq__`, `__lt__` and `mapping`, and `dict_values`' `__iter__`. -/
public def viewImpls : Impls :=
  let base := opsImpls.withNewCheck
  { base with
    method := fun t name =>
      if t == .«dict_keys» && ["__len__", "__contains__", "__and__", "__rand__", "__or__",
          "__ror__", "__eq__", "__lt__", getsetHook "mapping"].contains name then some (viewBody name)
      else if t == .«dict_values» && name == "__iter__" then some (viewBody name)
      else base.method t name }

/-- The dict views' operations through their tables, on a keys view `k` and a values view
`w` of a dict `d`, with the test bodies of `viewImpls` (`pt.viewOps`) or with this piece's part
alone (`pt.viewBare`): `len(k)` (`0`), `bool(k)` (`1`), `1 in k` (`2`) and `1 in w`, by iteration
(`3`); `k & {1}` (`4`) and `{1} & k`, by `k`'s `__rand__` (`5`); `k == {1}` (`6`), `{1} == k` (`7`)
and `k < 1` (`8`); `-k` (`9`), `k + 1` (`10`) and `3 *= k` (`11`); `{1} |= k` (`12`), `k &= {1}`
(`13`), `k *= 2` (`14`) and `k *= (1,)` (`15`); `k == mp` and `mp | k` for a mappingproxy `mp`
(`16`, `17`); `next(k)` (`18`), `hash(k)` (`19`) and `hash(w)` (`20`); `k.mapping` (`21`) and a
call of the getset descriptor (`22`); `iter(w) is w` (`23`); `k == E()` and `E() == iter(())`
for a class `E` whose `__eq__` and `__ror__` are `len` (`24`, `25`); `w == w` (`26`) and `w`
against another values view of `d` (`27`); `k @ 1` (`28`); `len` of an items view (`29`);
`k | E()` and `k |= E()`, which `k`'s `__or__` answers (`30`, `31`); `w != w` (`32`) and
`k != {1}` (`33`); `k.__class__` (`34`) and `isinstance(k, set)` (`35`); `k |= mp` (`36`) and
`k == mp` as a condition (`37`). -/
public def viewCase {m : Type → Type 1} [PyWrites m Value] [PyNew m Value] (k : Int) : m Value := do
  let d ← PyPure.allocDict
  let kv ← Proto.newIter .«dict_keys» (.view .«dict_keys» d)
  let wv ← Proto.newIter .«dict_values» (.view .«dict_values» d)
  let iv ← Proto.newIter .«dict_items» (.view .«dict_items» d)
  let one := Value.int 1
  let s1 ← Proto.mkSet #[one]
  let ns ← PyPure.allocDict
  PyNew.dictSetNew ns (Value.ofString "__eq__") (.builtin .len) none fun _ => pure false
  PyNew.dictSetNew ns (Value.ofString "__ror__") (.builtin .len) none fun _ => pure false
  let e ← PyPure.allocObj (.builtin .type) (.cls
    { name := "E", qualname := "E", «module» := "m", bases := #[.builtin .object],
      mroTail := #[.builtin .object], ns, solidBase := .builtin .object })
  let mp ← PyPure.allocObj (.builtin .mappingproxy) (.mappingProxy d e)
  let boolV (b : Bool) : Value := .bool b
  match k with
  | 0 => return .int (← Proto.pyLen kv)
  | 1 => return boolV (← Proto.truthy kv)
  | 2 => return boolV (← Proto.contains one kv)
  | 3 => return boolV (← Proto.contains one wv)
  | 4 => return ← Proto.binaryOp .and kv s1
  | 5 => return ← Proto.binaryOp .and s1 kv
  | 6 => return ← Proto.richCompareV .eq kv s1
  | 7 => return ← Proto.richCompareV .eq s1 kv
  | 8 => return boolV (← Proto.richCompare .lt kv one)
  | 9 => return ← Proto.unaryOp .neg kv
  | 10 => return ← Proto.binaryOp .add kv one
  | 11 => return ← Proto.inplaceOp .mul (.int 3) kv
  | 12 => return ← Proto.inplaceOp .or s1 kv
  | 13 => return ← Proto.inplaceOp .and kv s1
  | 14 => return ← Proto.inplaceOp .mul kv (.int 2)
  | 15 => return ← Proto.inplaceOp .mul kv (.tuple #[one])
  | 16 => return ← Proto.richCompareV .eq kv mp
  | 17 => return ← Proto.binaryOp .or mp kv
  | 18 => return ← Builtins.nextFn .none (.tuple #[kv]) (← PyPure.allocDict)
  | 19 => do discard <| Proto.hashN 5 kv; return .none
  | 20 => do discard <| Proto.hashN 5 wv; return .none
  | 21 => return ← Proto.getAttr kv "mapping"
  | 22 => return ← Proto.callN 5 (.descr .«dict_keys» "mapping" .getset) (.tuple #[kv]) (← PyPure.allocDict)
  | 23 => return boolV ((← PyPure.identical (← Proto.getIter wv) wv) == .yes)
  | 24 => return ← Proto.richCompareV .eq kv (← PyReads.allocInstance e .plain #[] #[])
  | 25 => do
    let x ← PyReads.allocInstance e .plain #[] #[]
    let it ← Proto.getIter (.tuple #[])
    return ← Proto.richCompareV .eq x it
  | 26 => return ← Proto.richCompareV .eq wv wv
  | 27 => return ← Proto.richCompareV .eq wv (← Proto.newIter .«dict_values» (.view .«dict_values» d))
  | 28 => return ← Proto.matMultOp kv one
  | 29 => return .int (← Proto.pyLen iv)
  | 30 => return ← Proto.binaryOp .or kv (← PyReads.allocInstance e .plain #[] #[])
  | 31 => return ← Proto.inplaceOp .or kv (← PyReads.allocInstance e .plain #[] #[])
  | 32 => return ← Proto.richCompareV .ne wv wv
  | 33 => return ← Proto.richCompareV .ne kv s1
  | 34 => return ← Proto.getAttr kv "__class__"
  | 35 => return boolV (← Builtins.isinstanceN 5 kv (.builtin .«set»))
  | 36 => return ← Proto.inplaceOp .or kv mp
  | _ => return boolV (← Proto.richCompare .eq kv mp)

/-- `viewCase k` with the test bodies of `viewImpls`. -/
@[dyn_sem PyT.viewOps, expose] public def viewOps (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    letI : PyWrites (PyM σ .writes true) Value := writesRecord (callBuiltinWith viewImpls 5000)
    viewCase (m := PyM σ .writes true) k
    : PyM σ .writes true Value)

/-- `viewCase k` with this piece's part alone, whose dict views have no bodies. -/
@[dyn_sem PyT.viewBare, expose] public def viewBare (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    letI : PyWrites (PyM σ .writes true) Value :=
      writesRecord (callBuiltinWith opsImpls.withNewCheck 5000)
    viewCase (m := PyM σ .writes true) k
    : PyM σ .writes true Value)

/-- A mappingproxy of a plain dict `d = {1: 2}` (`allocMappingProxy`): `p[1]` (`0`), `p[9]` (`1`),
`p[[1]]` (`2`), `type(p)` (`3`), `p == p` (`4`), and `p[3]` after `d[3] = 4` (`5`); and `p[1]` for
a proxy of an instance of a subclass of `dict` (`6`). -/
@[dyn_sem PyT.dictProxyCase, expose] public def dictProxyCase (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let d ← Proto.mkDict #[.int 1, .int 2]
    let p ← Proto.allocMappingProxy d
    match k with
    | 0 => Proto.getItem p (.int 1)
    | 1 => Proto.getItem p (.int 9)
    | 2 => do Proto.getItem p (← PyPure.allocList #[.int 1])
    | 3 => PyReads.classOf p
    | 4 => return .bool (← Proto.richCompare .eq p p)
    | 5 => do
        Proto.setItem d (.int 3) (.int 4)
        Proto.getItem p (.int 3)
    | _ => do
        let ns ← PyPure.allocDict
        let c ← PyPure.allocObj (.builtin .type) (.cls
          { name := "D", qualname := "D", «module» := "m", bases := #[.builtin .dict],
            mroTail := #[.builtin .dict, .builtin .object], ns, solidBase := .builtin .dict })
        let sd ← PyReads.allocInstance c .dict #[] #[]
        Proto.getItem (← Proto.allocMappingProxy sd) (.int 1)
    : PyM σ .writes true Value)

/-- The hooks that pieces of the built-in library fill, and the class flag `asBase`: the import hook
called through a table with its body (`0`) and without (`1`); `isinstance(1, l)` for a list `l`,
which doesn't ask the union hook (`19`); `import t` of a module without attributes that a piece
made, which imports (`18`); a class whose `asBase` is `notAcceptable` (`5`) or `gap` (`6`) as the
base of a new class; an attribute of a module that a body made (`7`); `import nosuch` (`8`); a call
of a C type that a piece makes (`10`); a call of an object with opaque state, whose class's
`__call__` is `len` (`11`); a native wrapper descriptor of a class `A` bound to `1` (`12`) and to an
instance of `A`, whose type's name is given (`13`); the `tp_name` of such a class in `len()`'s
message (`14`); its `__module__`, which its namespace doesn't hold (`15`); its `__dict__`
subscripted by a name it holds (`16`), by one it doesn't (`17`), and by `__dict__` (`24`); a native
method descriptor bound to `1` (`20`); `object.__new__` of the class (`21`); the class `|` its
`__dict__` (`22`); the `__dict__` of a class that gaps the name `g`, subscripted by `g` (`23`); the
class's `__new__`, which is `object.__new__` (`25`); the wrapper descriptor bound to no object,
which gives the descriptor back (`26`); `object.__getattribute__` of the object with opaque state
(`27`); its `__dict__` subscripted by `1` (`28`); and, for an immutable class `B` whose `tp_name` is
`types.B`, the messages that name it: a call of an instance (`29`), a missing attribute (`30`), an
attribute write (`31`) and `object.__new__(B, 1)` (`32`); and a native function's names (`33`) and
the type of what it binds to `1`, a method (`34`), and of an attribute read of it on an instance of
a class that holds it (`35`), and itself when bound to no object (`36`); and the `__dict__` of the
class that gaps `g`, subscripted by `1` (`37`). -/
@[dyn_sem PyT.hooks, expose] public def hooks (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let hook : Value := .bound .none .module (importHook "m") .method
    let newClass (rule : BaseRule) : PyM σ .writes true Value := do
      let ns ← PyPure.allocDict
      let u ← PyPure.allocObj (.builtin .type) (.cls
        { name := "U", qualname := "U", «module» := "m", bases := #[.builtin .object],
          mroTail := #[.builtin .object], ns, solidBase := .builtin .object, asBase := rule })
      let ns2 ← PyPure.allocDict
      PyNew.dictSetNew ns2 (Value.ofString "__module__") (Value.ofString "m") none fun _ => pure false
      Proto.callN 5 (.builtin .type) (.tuple #[Value.ofString "X", .tuple #[u], ns2])
        (← PyPure.allocDict)
    match k with
    | 0 => callBuiltinWith hookImpls 5000 hook (.tuple #[]) (← PyPure.allocDict)
    | 1 => callBuiltinWith {} 5000 hook (.tuple #[]) (← PyPure.allocDict)
    | 5 => newClass .notAcceptable
    | 6 => newClass .gap
    | 7 => do
      let mod ← PyPure.allocObj (.builtin .module) (.module "m" #[] false #[("a", .int 3)])
      Proto.getAttr mod "a"
    | 8 => Proto.importModule "nosuch"
    | 18 => do
      let mod ← PyPure.allocObj (.builtin .module) (.module "t" #[] false #[])
      PyReads.moduleAdd "t" mod
      Proto.importModule "t"
    | 19 => do
      let l ← PyPure.allocList #[.builtin .int]
      pure (.bool (← Builtins.isinstanceN 5 (.int 1) l))
    | _ => do
      let ns ← PyPure.allocDict
      PyNew.dictSetNew ns (Value.ofString "__call__") (.builtin .len) none fun _ => pure false
      let a ← PyPure.allocObj (.builtin .type) (.cls
        { name := "A", qualname := "A", «module» := "m", bases := #[.builtin .object],
          mroTail := #[.builtin .object], ns, solidBase := .builtin .object,
          tpName := some "types.A", cType := true })
      let wrapper ← PyPure.allocObj (.builtin .«wrapper_descriptor») (.native
        { key := "k", kind := .wrapperDescriptor, name := "__eq__", qualname := "A.__eq__",
          «module» := "m", owner := some a })
      let method ← PyPure.allocObj (.builtin .«method_descriptor») (.native
        { key := "k", kind := .methodDescriptor, name := "m", qualname := "A.m", «module» := "m",
          owner := some a })
      let o ← PyPure.allocObj a (.opaque "a" #[])
      match k with
      | 10 => Proto.callN 5 a (.tuple #[]) (← PyPure.allocDict)
      | 11 => Proto.callN 5 o (.tuple #[]) (← PyPure.allocDict)
      | 12 => Proto.descrGetN 5 wrapper (some (.int 1)) (.builtin .int)
      | 13 => do
        let b ← Proto.descrGetN 5 wrapper (some o) a
        pure (Value.ofString (← Proto.typeName b))
      | 14 => Builtins.lenFn .none (.tuple #[o]) (← PyPure.allocDict)
      | 15 => Proto.getAttr a "__module__"
      | 20 => Proto.descrGetN 5 method (some (.int 1)) (.builtin .int)
      | 21 => Builtins.objectNew .none (.tuple #[a]) (← PyPure.allocDict)
      | 22 => Proto.binaryTail "|" .or a (← Proto.getAttr a "__dict__")
      | 25 => Proto.getAttr a "__new__"
      | 26 => do
        let d ← Proto.descrGetN 5 wrapper none a
        pure (.bool ((← PyPure.identical d wrapper) matches .yes))
      | 27 => Builtins.objectGetattribute o (.tuple #[Value.ofString "x"]) (← PyPure.allocDict)
      | 33 | 34 | 35 | 36 => do
        let f ← PyPure.allocObj (.builtin .function) (.native
          { key := "k", kind := .function, name := "cast", qualname := "cast", «module» := "typing" })
        match k with
        | 33 => do
          let names ← ["__name__", "__qualname__", "__module__"].mapM (Proto.getAttr f)
          pure (.tuple names.toArray)
        | 34 => pure (Value.ofString (← Proto.typeName (← Proto.descrGetN 5 f (some (.int 1)) (.builtin .int))))
        | 36 => pure (.bool ((← PyPure.identical (← Proto.descrGetN 5 f none (.builtin .int)) f) matches .yes))
        | _ => do
          let ns ← PyPure.allocDict
          PyNew.dictSetNew ns (Value.ofString "m") f none fun _ => pure false
          let c ← PyPure.allocObj (.builtin .type) (.cls
            { name := "C", qualname := "C", «module» := "m", bases := #[.builtin .object],
              mroTail := #[.builtin .object], ns, solidBase := .builtin .object })
          let i ← PyReads.allocInstance c .plain #[] #[]
          pure (Value.ofString (← Proto.typeName (← Proto.getAttr i "m")))
      | 28 => Proto.getItem (← Proto.getAttr a "__dict__") (.int 1)
      | 29 | 30 | 31 | 32 => do
        let ns ← PyPure.allocDict
        let b ← PyPure.allocObj (.builtin .type) (.cls
          { name := "B", qualname := "B", «module» := "m", bases := #[.builtin .object],
            mroTail := #[.builtin .object], ns, solidBase := .builtin .object,
            tpName := some "types.B", immutable := true })
        match k with
        | 29 => Proto.callN 5 (← PyReads.allocInstance b .plain #[] #[]) (.tuple #[]) (← PyPure.allocDict)
        | 30 => Proto.getAttr b "nope"
        | 31 => do Proto.setAttr b "x" (some (.int 1)); pure .none
        | _ => Builtins.objectNew .none (.tuple #[b, .int 1]) (← PyPure.allocDict)
      | 23 | 37 => do
        let ns ← PyPure.allocDict
        let g ← PyPure.allocObj (.builtin .type) (.cls
          { name := "G", qualname := "G", «module» := "m", bases := #[.builtin .object],
            mroTail := #[.builtin .object], ns, solidBase := .builtin .object, gapped := #["g"] })
        Proto.getItem (← Proto.getAttr g "__dict__") (if k == 23 then Value.ofString "g" else .int 1)
      | _ => do
        let d ← Proto.getAttr a "__dict__"
        let key := if k == 16 then "__call__" else if k == 17 then "nope" else "__dict__"
        Proto.getItem d (Value.ofString key)
    : PyM σ .writes true Value)

/-- `setExact` beside `setView`'s `exact`, on a set whose order is known (`{1, 2}`), on one whose
order isn't (a set made inexact), on a list and on an `int`: pairs of the two answers. -/
@[dyn_sem PyT.setExactCase, expose] public def setExactCase (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let s ← PyPure.allocSet false false
    for k in [1, 2] do PyNew.setAddNew s (Value.int k) none fun _ => pure false
    let t ← PyPure.allocSet false true
    PyNew.setAddNew t (Value.int 1) none fun _ => pure false
    let l ← PyPure.allocList #[.int 1]
    let mut out : Array Value := #[]
    for v in [s, t, l, .int 1] do
      let view := ((← PyReads.setView v).map (·.exact)).getD false
      out := out.push (.tuple #[.bool (← PyReads.setExact v), .bool view])
    pure (Value.tuple out)
    : PyM σ .reads false Value)

/-- Stub bodies for the hooks: the union hook gives `(str, int)`, or `None` if `unionNone`;
`type.__or__` and `type.__ror__` give `NotImplemented`; and the import of `q` makes a module with
the attribute `a = 3`; the import of `g` a module whose only attribute is a `__getattr__`; the
import of `h` a module that gaps `__getattr__`; the imports of `p` and `p.s` a package, whose body
binds `s = 1`, and its submodule; the import of `z.s`, but not of `z`, a module; and the import of
`r` a body that adds its module to the table and then raises `ValueError`, of `r2` a body that
raises `ValueError` without adding it, and of `o` a package whose attribute `p` is its submodule
`o.p`, which the body adds to the table, and of `w` a body that adds one module to the table and
returns another. -/
public def stubImpls (unionNone : Bool) : Impls :=
  { method := fun t name =>
      if t == .object && name == unionArgsHook then
        some fun {m} {_} [_] [_] _ _ _ => pure (if unionNone then PyPure.imm (m := m) .none else
          PyPure.imm (m := m) (.tuple #[PyPure.imm (m := m) (.builtin .str),
            PyPure.imm (m := m) (.builtin .int)]))
      else if t == .type && (name == "__or__" || name == "__ror__") then
        some fun {m} {_} [_] [_] _ _ _ => pure (PyPure.imm (m := m) .notImplemented)
      else if t == .module && name == importHook "q" then
        some fun {m} {_} [_] [_] _ _ _ => do
          let mod ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
            (.module "q" #[] false #[("a", PyPure.imm (m := m) (.int 3))])
          PyReads.moduleAdd "q" mod
          pure mod
      else if t == .module && name == importHook "h" then
        some fun {m} {_} [_] [_] _ _ _ =>
          PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
            (.module "h" #["__getattr__"] false #[])
      else if let some mod := (["p", "p.s", "z.s"].find? (importHook · == name)).filter
          (fun _ => t == .module) then
        some fun {m} {_} [_] [_] _ _ _ =>
          PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
            (.module mod #[] false #[("s", PyPure.imm (m := m) (.int 1))])
      else if t == .module && name == importHook "r" then
        some fun {m} {_} [_] [_] _ _ _ => do
          let mod ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
            (.module "r" #[] false #[])
          PyReads.moduleAdd "r" mod
          Proto.raiseBuiltin "ValueError" "r"
      else if t == .module && name == importHook "r2" then
        some fun {_} {_} [_] [_] _ _ _ => Proto.raiseBuiltin "ValueError" "r2"
      else if t == .module && name == importHook "o" then
        some fun {m} {_} [_] [_] _ _ _ => do
          let sub ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
            (.module "o.p" #[] false #[])
          PyReads.moduleAdd "o.p" sub
          PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
            (.module "o" #[] false #[("p", sub)])
      else if t == .module && name == importHook "w" then
        some fun {m} {_} [_] [_] _ _ _ => do
          let kept ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
            (.module "w" #[] false #[])
          PyReads.moduleAdd "w" kept
          PyPure.allocObj (PyPure.imm (m := m) (.builtin .module)) (.module "w" #[] false #[])
      else if t == .module && name == importHook "g" then
        some fun {m} {_} [_] [_] _ _ _ =>
          PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
            (.module "g" #[] false #[("__getattr__", PyPure.imm (m := m) (.builtin .len))])
      else none }

/-- The paths that run once a part gives a hook's body, with the bodies of `stubImpls`:
`isinstance(1, u)` for an object `u` with opaque state, whose union arguments are `(str, int)` (`0`)
or `None` (`1`); `int | str`, which both slots decline (`2`); `from q import a` (`3`) and `from q
import b` (`4`); whether two imports of `q` give one module (`5`); `q.__name__`, which CPython's
import sets but the body didn't (`6`); `q.b` (`7`); `g.x`, which CPython gets from `g`'s
`__getattr__` (`8`), and `h.x` (`9`); `p.s` after `import p.s`, which CPython's import sets on `p`
over the body's `s` (`10`); `import z.s`, which imports `z` first (`11`); `p.s.s`, read on the
module that `import p.s` gives (`12`); and `import r`, whose body raises after it added its module
(`13`); `import r2`, whose body raises before it adds its module (`14`); and whether `o.p` is the
module that `import o.p` gives (`15`); whether two imports of `w` give one module, the one in the
table (`16`); and, for a C type `T` that a piece made, `T.__dict__["__doc__"]` (`17`) and
`T.__dict__["x"]` (`18`), and `T.__doc__` (`19`); and, for a class `U` that a piece made, which
isn't a C type, `U.__dict__["__doc__"]` (`20`), `U.__doc__` when `U` holds and gaps `__doc__`
(`21`), the `__doc__` of an instance of `U` (`22`), `U.__module__` (`23`) and
`U.__dict__["__module__"]` (`24`); and the `__module__` of an instance of `T` (`25`). -/
@[dyn_sem PyT.stubHooks, expose] public def stubHooks (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    letI : PyWrites (PyM σ .writes true) Value :=
      writesRecord (callBuiltinWith (stubImpls (k == 1)) 5000)
    match k with
    | 0 | 1 => do
      let ns ← PyPure.allocDict
      let a ← PyPure.allocObj (.builtin .type) (.cls
        { name := "U", qualname := "U", «module» := "m", bases := #[.builtin .object],
          mroTail := #[.builtin .object], ns, solidBase := .builtin .object })
      let u ← PyPure.allocObj a (.opaque "u" #[])
      pure (.bool (← Builtins.isinstanceN 5 (.int 1) u))
    | 2 => Proto.binaryTail "|" .or (.builtin .int) (.builtin .str)
    | 3 => Proto.importFrom "q" "a"
    | 4 => Proto.importFrom "q" "b"
    | 6 => do Proto.getAttr (← Proto.importModule "q") "__name__"
    | 7 => do Proto.getAttr (← Proto.importModule "q") "b"
    | 8 => do Proto.getAttr (← Proto.importModule "g") "x"
    | 9 => do Proto.getAttr (← Proto.importModule "h") "x"
    | 10 => do
      discard <| Proto.importModule "p.s"
      Proto.getAttr (← Proto.importModule "p") "s"
    | 11 => Proto.importModule "z.s"
    | 12 => do Proto.getAttr (← Proto.importModule "p.s") "s"
    | 13 => Proto.importModule "r"
    | 14 => Proto.importModule "r2"
    | 15 => do
      let sub ← Proto.importModule "o.p"
      let p ← Proto.getAttr (← Proto.importModule "o") "p"
      pure (.bool ((← PyPure.identical p sub) matches .yes))
    | 16 => do
      let w1 ← Proto.importModule "w"
      let w2 ← Proto.importModule "w"
      pure (.bool ((← PyPure.identical w1 w2) matches .yes))
    | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 => do
      let ns ← PyPure.allocDict
      -- `U` of case 21 holds a `__doc__`, which it also gaps.
      if k == 21 then
        PyNew.dictSetNew ns (Value.ofString "__doc__") .none none fun _ => pure false
      let c ← PyPure.allocObj (.builtin .type) (.cls
        { name := if k ≤ 19 || k == 25 then "T" else "U", qualname := "T", «module» := "m",
          bases := #[.builtin .object], mroTail := #[.builtin .object], ns,
          solidBase := .builtin .object, cType := k ≤ 19 || k == 25,
          gapped := if k == 21 then #["__doc__"] else #[] })
      if k == 19 || k == 21 then return ← Proto.getAttr c "__doc__"
      if k == 22 then return ← Proto.getAttr (← PyReads.allocInstance c .plain #[] #[]) "__doc__"
      if k == 23 then return ← Proto.getAttr c "__module__"
      if k == 25 then return ← Proto.getAttr (← PyReads.allocInstance c .plain #[] #[]) "__module__"
      let key := Value.ofString
        (if k == 18 then "x" else if k == 24 then "__module__" else "__doc__")
      Proto.getItem (← Proto.getAttr c "__dict__") key
    | _ => do
      let q1 ← Proto.importModule "q"
      let q2 ← Proto.importModule "q"
      pure (.bool ((← PyPure.identical q1 q2) matches .yes))
    : PyM σ .writes true Value)

/-- The bodies of `stubIssubclass`'s case `k`: none for `2`, else `stubImpls`. -/
public def stubIssubclassImpls (k : Int) : Impls :=
  if k == 2 then {} else stubImpls (k == 1)

/-- `issubclass(bool, u)` for an object `u` with opaque state, through the union hook of
`stubImpls`: the hook gives `(str, int)` (`0`), so the result is `True`; it gives `None` (`1`), so
the call goes on to `recursive_issubclass`, which raises `TypeError` for `u`, an object without
`__bases__`; and with no body for the hook (`2`), the call stops with the hook's gap. -/
@[dyn_sem PyT.stubIssubclass, expose] public def stubIssubclass (k : Int)
    (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    letI : PyWrites (PyM σ .writes true) Value :=
      writesRecord (callBuiltinWith (stubIssubclassImpls k) 5000)
    do
      let ns ← PyPure.allocDict
      let a ← PyPure.allocObj (.builtin .type) (.cls
        { name := "U", qualname := "U", «module» := "m", bases := #[.builtin .object],
          mroTail := #[.builtin .object], ns, solidBase := .builtin .object })
      let u ← PyPure.allocObj a (.opaque "u" #[])
      pure (.bool (← Library.issubclassN 5 (.builtin .bool) u))
    : PyM σ .writes true Value)

/-- `callable(u)` for an object `u` with opaque state, which no built-in of `Library` makes: it
stops with a gap. -/
@[dyn_sem PyT.callableOpaque, expose] public def callableOpaque (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let ns ← PyPure.allocDict
    let a ← PyPure.allocObj (.builtin .type) (.cls
      { name := "U", qualname := "U", «module» := "m", bases := #[.builtin .object],
        mroTail := #[.builtin .object], ns, solidBase := .builtin .object })
    let u ← PyPure.allocObj a (.opaque "u" #[])
    pure (.bool (← Library.isCallable u))
    : PyM σ .reads false Value)

/-- `callable(f)` for a class call's own callee, `int.__new__` bound to `int` as `tp_new`, which no
attribute lookup gives: a model invariant, as for its unbound form. -/
@[dyn_sem PyT.callableTpNew, expose] public def callableTpNew (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    pure (.bool (← Library.isCallable (Value.bound (.builtin .int) .int "__new__" .tpNew)))
    : PyM σ .reads false Value)

/-- `PySequence_Check` of a `mappingproxy`, a built-in type whose `__getitem__` is not one of the
five sequence types': it stops with a gap. -/
@[dyn_sem PyT.sequenceCheckProxy, expose] public def sequenceCheckProxy (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    letI : PyWrites (PyM σ .writes true) Value := writesRecord (callBuiltinWith {} 5000)
    do
      let d ← PyPure.allocDict
      let p ← PyPure.allocObj (.builtin .mappingproxy) (.mappingProxy d d)
      pure (.bool (← Library.sequenceCheck p))
    : PyM σ .writes true Value)

/-- Region `0` on `1`, with a cell operand that it doesn't pass: a region whose parameter holds no
ref, which `#py_rule_theorems` proves. -/
@[dyn_sem PyT.regionValue, expose] public def regionValue (_c : Ref σ Value)
    (body : Region ε [Value] (Except Value Unit)) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[regionHandle body oneValue fun _ => .none] (do
    discard <| PyPure.region 0 #[.int 1]
    pure Value.none
    : PyM σ .pure true Value)

/-- Region `0`, which takes one value, on no values (`0`), on two (`1`), and on one (`2`): a
handle given values that its input doesn't take stops with a model-invariant gap. -/
@[dyn_sem PyT.regionArity, expose] public def regionArity (k : Int)
    (body : Region ε [Value] (Except Value Unit)) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[regionHandle body oneValue fun _ => .none] (do
    discard <| PyPure.region 0 (match k with
      | 0 => #[]
      | 1 => #[.int 1, .int 2]
      | _ => #[.int 1])
    pure Value.none
    : PyM σ .pure true Value)

/-- Region `0` on the cell `c`: a region whose parameter is a ref, which `#py_rule_theorems`
rejects. -/
@[dyn_sem PyT.regionCell, expose] public def regionCell (c : Ref σ Value)
    (body : Region ε [Ref σ Value] (Except Value Unit)) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[regionHandle body (fun _ => some c) fun _ => .none] (do
    discard <| PyPure.region 0 #[]
    pure Value.none
    : PyM σ .pure true Value)

/-- `startChecks`, which runs before a step machine starts, on a call of `tuple.__new__` on
`(int, (1,))` (`0`), of `list.extend` on `(5, (1,))` (`1`), of `dict.__dict__["fromkeys"]` on
`(list, (1,))` (`2`), and of `tuple.__new__` on `(tuple, (1,))` (`3`); and the start of a machine
for `tuple.__new__` on `(int, (1,))` (`4`), which runs them; and a call of a `tp_new` value
(`DescrKind.tpNew`) outside a class call (`5`). -/
@[dyn_sem PyT.startCheck, expose] public def startCheck (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let l : Value := .tuple #[.int 1]
    let new : Value := .bound (.builtin .tuple) .tuple "__new__" .method
    match k with
    | 0 => startChecks new (.tuple #[.builtin .int, l])
    | 1 => startChecks (.descr .list "extend" .method) (.tuple #[.int 5, l])
    | 2 => startChecks (.descr .dict "fromkeys" .classMethod) (.tuple #[.builtin .list, l])
    | 3 => startChecks new (.tuple #[.builtin .tuple, l])
    | 4 => discard <| machinesStart (σ := σ) 5 new (.tuple #[.builtin .int, l]) (← PyPure.allocDict)
    | _ => do
      let f := Value.bound (.builtin .tuple) .tuple "__new__" .tpNew
      discard <| Proto.callN 5 f (Value.tuple #[.builtin .tuple, l]) (← PyPure.allocDict)
    pure Value.none
    : PyM σ .writes true Value)

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
compare as `KeyClass.user`, so the walk follows the live table. -/
@[dyn_sem PyT.frozenWalk, expose] public def frozenWalk (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let mk : PyM σ .calls false Value := do
      let f ← PyPure.allocSet true false
      PyNew.setAddNew f (Value.int 1) none fun _ => pure false
      PyNew.setFreezeNew f
      let s ← PyPure.allocSet false false
      PyNew.setAddNew s f (some (← Proto.hash f)) (Proto.keyEq f)
      pure s
    let a ← mk
    let b ← mk
    return Value.bool (← Proto.richCompare .eq a b) : PyM σ .calls false Value)

/-- `s |= t` for `s = {1}` and `t = {frozenset({1})}`: `setMerge`'s path that compares, on a set
whose member may run user code when compared: the primitive gaps, since it walks `t` as it was
(`setMergeWith` walks the live table instead). -/
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
    pure Value.none : PyM σ .calls false Value)

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

/-- `{*S}` for an instance of `S(set)` holding `{1}`, whose `__iter__` is `list`'s slot wrapper:
`set_update_internal` merges a set subclass's table without calling its `__iter__`. -/
@[dyn_sem PyT.setUpdateSub, expose] public def setUpdateSub (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let c ← subclassOf "S" .set
    let some cd ← Proto.classData? c | PyM.gap "not a class"
    PyWrites.dictSet cd.ns (.ofString "__iter__") (.descr .list "__iter__" .slotWrapper) none
      fun _ => pure false
    let x ← PyReads.allocInstance c .set #[] #[]
    PyWrites.setAdd x (Value.int 1) none fun _ => pure false
    let s ← PyPure.allocSet false false
    match ← Proto.setUpdateStep s x none with
    | .done () => pure (.tuple ((← Proto.setMembers s).unordered.map (·.1)))
    | .more _ => PyM.gap "more than one activation" : PyM σ .writes false Value)

/-- `next(d.keys())` for an empty dict `d`: a view, though held as an iterator's state, is not an
iterator. -/
@[dyn_sem PyT.nextView, expose] public def nextView (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let d ← PyPure.allocDict
    let v ← Proto.newIter .dict_keys (.view .dict_keys d)
    Builtins.nextFn .none (.tuple #[v]) (← PyPure.allocDict) : PyM σ .writes true Value)

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
/-- The frames of the test-only step machines: `count k`, a machine at its step `k` that gives
`k` after its third step, and `initCount k`, the same machine as an `__init__`, which gives `1`,
so that `type.__call__` raises its `TypeError` on the resumed result; and this piece's frames. -/
public inductive TState where
  | count (k : Nat)
  | initCount (k : Nat)
  | depthAt
  | ops (s : Proto.OpsLoopState Value)

public instance : HasLoopPart TState (Proto.OpsLoopState Value) where
  inj := .ops
  proj | .ops s => some s | _ => none
  proj_inj _ := rfl
  inj_of_proj s p h := by cases s <;> simp at h; cases h; rfl

mutual
/-- The test machines' first steps, with the fuel `n`: `sum` itself, `tuple.__new__` (reached
through a call of `tuple`) and `object.__init__` (reached through a call of `object`) are machines;
`min`'s first step calls `sum` through `callResumable`, and gives its step. -/
public def tStart : Nat → Value → Value → Value → PyM σ .writes true (Option (CallStep TState Value))
  | 0, _, _, _ => PyM.gap "test calls nested too deep"
  | n + 1, f, args, kwargs =>
    letI : PyMachines (PyM σ .writes true) Value TState :=
      { startStep := tStart n, resume := tResume n }
    match f with
    | .builtin .sum | .bound _ .tuple "__new__" _ => pure (some (.suspend [.count 1]))
    | .bound _ .object "__init__" _ => pure (some (.suspend [.initCount 1]))
    | .bound _ .list "__new__" _ => pure (some (.suspend [.depthAt]))
    | .builtin .min => some <$> Proto.callResumable 5 (.builtin .sum) args kwargs []
    | _ => pure none

/-- The test machines' resume entry, with the fuel `n`. -/
public def tResume : Nat → TState → List TState → PyM σ .writes true (CallStep TState Value)
  | 0, _, _ => PyM.gap "test frames resumed too deep"
  | n + 1, s, rest =>
    letI : PyMachines (PyM σ .writes true) Value TState :=
      { startStep := tStart n, resume := tResume n }
    match s with
    | .count k => pure (if k < 3 then .suspend [.count (k + 1)] else .done (.int k))
    | .initCount k => pure (if k < 3 then .suspend [.initCount (k + 1)] else .done (.int 1))
    | .depthAt => return .done (.int (← PyReads.depthC))
    | .ops f => Proto.opsResume f rest
end

public instance : PyMachines (PyM σ .writes true) Value TState :=
  { startStep := tStart 100, resume := tResume 100 }

/-- One activation of a call of `f` with no arguments, through `callResumable` at the test state. -/
public def testCallStep (f : Value) (st : Option (List TState)) :
    PyM σ .writes true (LoopStep (List TState) Value) := do
  Proto.callStep (S := TState) f (Value.tuple #[]) (← PyPure.allocDict) st

/-- A call of `f` that the test machines may suspend, over as many activations as they need. -/
@[dyn_sem PyT.resumeCase, expose]
public def resumeCase (f : Value) (err : Target E [Value]) (st : Option (List TState))
    (again : Again E (List TState)) : Sem ε E Value :=
  runLoopFree err again st #[] (testCallStep f)

/-- An instance of a class `C` whose `__call__` is `sum`, which the test machines suspend: calling it
suspends as a `callLevel` frame over `sum`'s. -/
@[dyn_sem PyT.callInst, expose] public def callInst (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (do
    let object := Value.builtin .object
    let ns ← PyPure.allocDict
    PyNew.dictSetNew ns (Value.ofString "__call__") (.builtin .sum) none fun _ => pure false
    let c ← PyPure.allocObj (.builtin .type) (.cls
      { name := "C", qualname := "C", «module» := "m", bases := #[object], mroTail := #[object],
        ns, solidBase := object })
    PyReads.allocInstance c .plain #[] #[]
    : PyM σ .writes true Value)

/-- A call's step as a value: `("done", v)` or `("suspend", the number of frames)`. -/
public def showStep : CallStep TState Value → Value
  | .done v => .tuple #[.ofString "done", v]
  | .suspend fs => .tuple #[.ofString "suspend", .int fs.length]

/-- One step of a call of `pt.callInst`'s instance: the instance's `callLevel` frame over `sum`'s. -/
@[dyn_sem PyT.callLevelStep, expose] public def callLevelStep (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let object := Value.builtin .object
    let ns ← PyPure.allocDict
    PyNew.dictSetNew ns (Value.ofString "__call__") (.builtin .sum) none fun _ => pure false
    let c ← PyPure.allocObj (.builtin .type) (.cls
      { name := "C", qualname := "C", «module» := "m", bases := #[object], mroTail := #[object],
        ns, solidBase := object })
    let inst ← PyReads.allocInstance c .plain #[] #[]
    pure (showStep (← Proto.callResumable (S := TState) 5 inst (.tuple #[]) (← PyPure.allocDict) []))
    : PyM σ .writes true Value)

/-- One step of a call through `callResumable`, as `py.call` makes it, of a C type `A` that a piece
makes (`0`), and of an object with opaque state whose class `A`'s `__call__` is `len` (`1`). -/
@[dyn_sem PyT.cTypeStep, expose] public def cTypeStep (k : Int) (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    let ns ← PyPure.allocDict
    PyNew.dictSetNew ns (Value.ofString "__call__") (.builtin .len) none fun _ => pure false
    let a ← PyPure.allocObj (.builtin .type) (.cls
      { name := "A", qualname := "A", «module» := "m", bases := #[.builtin .object],
        mroTail := #[.builtin .object], ns, solidBase := .builtin .object,
        tpName := some "types.A", cType := true })
    let f ← if k == 0 then pure a else PyPure.allocObj a (.opaque "a" #[])
    pure (showStep (← Proto.callResumable (S := TState) 5 f (.tuple #[]) (← PyPure.allocDict) []))
    : PyM σ .writes true Value)

/-- The values that a frame of `py.call`'s loop state holds. -/
public def frameValues : PyLoopState Value → List Value
  | .ops (.typeNew cls args kwargs) => [cls, args, kwargs]
  | .ops (.typeInit obj) => [obj]
  | .ops .callLevel => []
  | .library (.collect (.list self it)) => [self, it]
  | .library (.collect (.tuple cls acc it)) => [cls, acc, it]
  | .library (.collect (.set self it)) => [self, it]
  | .library (.collect (.frozenset self it)) => [self, it]
  | .library (.collect (.dictKeys self other it kwargs acc)) => [self, other, it, kwargs, acc]
  | .library (.collect (.dictKeysList self other keys kwargs _)) => [self, other, keys, kwargs]
  | .library (.collect (.dictPairs self it kwargs _ inner)) =>
    [self, it, kwargs] ++ (inner.map fun (p, got) => [p, got]).getD []
  | .library (.collect (.bytes cls acc it)) => [cls, acc, it]
  | .library (.anyAll _ it) => [it]
  | .library (.sum it _) => [it]
  | .library (.minMax _ it key dflt best pending) =>
    [it] ++ key.toList ++ dflt.toList ++ (best.map fun (a, b) => [a, b]).getD [] ++ pending.toList
  | .library (.strJoin sep acc it) => [sep, acc, it]
  | .library (.listScan s) => [s.self, s.value]
  | .library (.sortKeys s _) => [s.self, s.items, s.keys, s.result] ++ s.key.toList
  | .library (.sortedCollect acc it kwargs) => [acc, it, kwargs]
  | .library (.fromKeys s) => [s.d, s.it, s.value]
  | .library (.setWalk s) => [s.self, s.target, s.so, s.it] ++ s.rest

/-- A call of each container constructor over an iterator that gives one item per activation
(`iter(li.__next__, 99)` over a list iterator `li`), resumed until it ends: for each, the number
of activations, and whether a frame or the result held a value of the internal kind `.tpNew`. -/
public def tpNewNoLeakM : PyM σ .writes true Value := do
  -- A value of the kind `.tpNew`, also inside a tuple or a list, one level down.
  let isTpNew (v : Value) : PyM σ .writes true Bool := do
    let one (w : Value) : PyM σ .writes true Bool := do
      return (← PyPure.immViewAll w) matches some (.bound _ _ _ .tpNew)
    if ← one v then return true
    let inner ← match ← PyPure.immViewAll v with
      | some (.tuple xs) => pure xs
      | _ => pure ((← Proto.listOf? (m := PyM σ .writes true) v).getD #[])
    inner.anyM one
  -- A user subclass of `tuple`, whose call goes through `type.__call__`'s `typeNew` frame.
  let tup := Value.builtin .tuple
  let sub ← PyPure.allocObj (.builtin .type) (.cls
    { name := "T", qualname := "T", «module» := "m", bases := #[tup],
      mroTail := #[tup, .builtin .object], ns := ← PyPure.allocDict, solidBase := tup })
  let mut out : Array Value := #[]
  for t in [Value.builtin .tuple, .builtin .frozenset, .builtin .bytes, .builtin .list,
      .builtin .set, sub] do
    let li ← Proto.getIter (m := PyM σ .writes true) (← intList [65, 66, 67])
    let nxt ← Proto.getAttr (m := PyM σ .writes true) li "__next__"
    let cit ← Proto.newIter (m := PyM σ .writes true) .callable_iterator (.callable nxt (.int 99))
    let kw ← PyPure.allocDict
    let mut saved : List (PyLoopState Value) := []
    let mut steps := 0
    let mut leaked := false
    let mut done := false
    for _ in [0:20] do
      if done then break
      steps := steps + 1
      match ← Proto.callResumable (S := PyLoopState Value) 5 t (.tuple #[cit]) kw saved with
      | .done v =>
        leaked := leaked || (← isTpNew v)
        done := true
      | .suspend fs =>
        for fr in fs do
          for v in frameValues fr do leaked := leaked || (← isTpNew v)
        saved := fs
    out := out.push (.tuple #[.int steps, .bool leaked])
  pure (.tuple out)

@[dyn_sem PyT.tpNewNoLeak, expose]
public def tpNewNoLeak (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] tpNewNoLeakM

/-- `l.sort()` on the list `xs`, and the list after it. -/
public def sortedItems (xs : Array Value) : PyM σ .writes true Value := do
  let l ← PyPure.allocList xs
  discard <| Library.sortBody (m := PyM σ .writes true) l (.tuple #[]) (← PyPure.allocDict)
  let some ys ← Proto.listOf? (m := PyM σ .writes true) l | pure (.ofString "not a list")
  pure (.tuple ys)

/-- `[3, 1, True, 2, 1.0].sort()`: the fast path, stable among the equal keys. -/
@[dyn_sem PyT.sortInts, expose] public def sortInts (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (sortedItems #[.int 3, .int 1, .bool true, .int 2, .float 0x3FF0000000000000])

/-- `[2.0, nan, 1.0].sort()`: a NaN takes CPython's port, which keeps the list as it is. -/
@[dyn_sem PyT.sortNaN, expose] public def sortNaN (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[]
    (sortedItems #[.float 0x4000000000000000, .float 0x7FF8000000000000, .float 0x3FF0000000000000])

/-- `str.maketrans('ab', 'cd', 'e')` and `str.maketrans({'a': 1, 98: 'x'})`, as the pairs of the
two dicts. -/
@[dyn_sem PyT.maketransRule, expose]
public def maketransRule (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let pairs (d : Value) : PyM σ .writes true Value := do
      pure (.tuple ((← PyReads.dictEntries d).map fun (k, v, _) => .tuple #[k, v]))
    let a ← Library.maketransFn (m := PyM σ .writes true) .none
      (.tuple #[.ofString "ab", .ofString "cd", .ofString "e"]) (← PyPure.allocDict)
    let d ← PyPure.allocDict
    PyNew.dictSetNew d (Value.ofString "a") (.int 1) none fun _ => pure false
    PyNew.dictSetNew d (.int 98) (.ofString "x") none fun _ => pure false
    let b ← Library.maketransFn (m := PyM σ .writes true) .none (.tuple #[d]) (← PyPure.allocDict)
    pure (.tuple #[← pairs a, ← pairs b]))

/-- `UnicodeDecodeError('utf-8', bytearray(), 0, 1, 'r')`: a bytes-like object other than `bytes`
stops with a gap. -/
@[dyn_sem PyT.decodeBytearray, expose]
public def decodeBytearray (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let e ← PyReads.allocInstance (.builtin .UnicodeDecodeError) (.exc #[]) #[] #[]
    let ba ← PyReads.allocInstance (.builtin .bytearray) .plain #[] #[]
    Library.unicodeErrorInit (m := PyM σ .writes true) true e
      (.tuple #[.ofString "utf-8", ba, .int 0, .int 1, .ofString "r"]) (← PyPure.allocDict))

/-- `'ΑΣ'.lower()`, with the final sigma. -/
@[dyn_sem PyT.strLowerSigma, expose]
public def strLowerSigma (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    Library.textMethod (m := PyM σ .writes true) Library.Signatures.str_lower Library.Unicode.lower
      (.ofString "ΑΣ") (.tuple #[]) (← PyPure.allocDict))

/-- `callResumable` with saved frames resumes the frame's machine with no dispatch of the callee
(here `None`). -/
public def resumeDirectM : PyM σ .writes true Value := do
  let kw ← PyPure.allocDict
  let r1 ← Proto.callResumable (S := TState) 5 .none (.tuple #[]) kw [.count 2]
  let r2 ← Proto.callResumable (S := TState) 5 .none (.tuple #[]) kw [.count 3]
  pure (.tuple #[showStep r1, showStep r2])

@[dyn_sem PyT.resumeDirect, expose]
public def resumeDirect (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] resumeDirectM

/-- A `typeInit` frame with no inner frame doesn't fit, and stops with a gap. -/
public def resumeNoFitM : PyM σ .writes true Value := do
  discard <| Proto.opsResume (S := TState) (.typeInit (.int 1)) []
  pure .none

@[dyn_sem PyT.resumeNoFit, expose]
public def resumeNoFit (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] resumeNoFitM

end

public section
-- The compiler specializes every piece's step machines into `py.call`'s implementation, which
-- takes more than the default budget.
set_option maxHeartbeats 1000000 in
#dyn_sem_table PyTSem for PyT (world := World)
end

/-- The declared effects of `PyT`'s instructions. -/
def ptEffect : String → Effects.Level
  | "pt.callNew" => .calls
  | "pt.raiseIn" => .writes
  | "pt.classOfNew" | "pt.dictWalkSub" => .reads
  | "pt.nativeWrite" | "pt.immutableWrite" | "pt.strSubArg" | "pt.mkSubInst" | "pt.mkExc" | "pt.subclassCases" | "pt.buildClassName" | "pt.dictOrSub" | "pt.kwargsStrSub" => .writes
  | "pt.probeCase" => .reads
  | "pt.requireIn" => .writes
  | "pt.importGaps" => .writes
  | "pt.groupLenHint" => .writes
  | "pt.eqVal" => .calls
  | "pt.setAny" => .writes
  | "pt.dictPrims" | "pt.setPrims" | "pt.slotInexact" | "pt.popInexact" | "pt.listPrims"
  | "pt.newPrims" | "pt.bindCase" | "pt.setExactCase" => .reads
  | "pt.oldPrims" | "pt.frozenSeal" | "pt.nativeDepth" | "pt.nativeGapped" | "pt.nextView" | "pt.setUpdateSub" | "pt.classDescr" | "pt.startCheck" | "pt.hooks" | "pt.partHooks" | "pt.staticDescr" | "pt.heapAttrs" | "pt.dictProxyCase" | "pt.viewOps" | "pt.viewBare" | "pt.cTypeStep" | "pt.stubHooks" | "pt.stubIssubclass" => .writes
  | "pt.sequenceCheckProxy" => .writes
  | "pt.callableOpaque" | "pt.callableTpNew" => .reads
  | "pt.frozenOr" | "pt.frozenAdd" | "pt.objPrims" => .writes
  | "pt.frozenWalk" | "pt.frozenMerge" | "pt.subclassOps" => .calls
  | "pt.subclassContainers" | "pt.seqSlotSub" | "pt.seqSlotCleared" | "pt.strSetSubOps" | "pt.callInst" | "pt.callLevelStep" | "pt.resumeCase" | "pt.resumeDirect" | "pt.resumeNoFit"
  | "pt.foreignIter" | "pt.foreignLen" | "pt.strSubIter" | "pt.iterBounds" | "pt.zipNext"
  | "pt.enumNext" | "pt.revNext" | "pt.listRevNext" | "pt.dictRevNext" | "pt.startZero"
  | "pt.staleSlice" | "pt.tpNewNoLeak" | "pt.sortInts" | "pt.sortNaN" | "pt.strLowerSigma"
  | "pt.maketransRule" | "pt.decodeBytearray" => .writes
  | _ => .pure

/-- The tags of `PyLang` in `PyTSem`. -/
def ptTags (σ : Type) [Store σ] : @Tags σ _ ⟨PyTSem.interp σ⟩ :=
  letI : Decode σ := ⟨PyTSem.interp σ⟩
  ⟨⟨PyTSem.T.py.Value, rfl⟩, ⟨Ty.ref PyTSem.T.py.Value, rfl⟩,
    ⟨PyTSem.T.base.Except PyTSem.T.py.Value PyTSem.T.py.Value, rfl⟩, [PyTSem.T.py.Value]⟩

/--
error: #py_rule_theorems: the rule of pt.direct is not a `runRule`, `runTotal`, `runRuleFree`, `runTotalFree`, `runRuleIf`, `runLoop` or `runLoopFree` wrapper at an effect no higher than its declared one, whose results and exits hold no ref and whose handles are `regionHandle`s of regions whose parameters hold no ref, and has no lemmas StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.okOf.pt.direct and StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.certOf.pt.direct
---
error: #py_rule_theorems: the rule of pt.tooHigh is not a `runRule`, `runTotal`, `runRuleFree`, `runTotalFree`, `runRuleIf`, `runLoop` or `runLoopFree` wrapper at an effect no higher than its declared one, whose results and exits hold no ref and whose handles are `regionHandle`s of regions whose parameters hold no ref, and has no lemmas StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.okOf.pt.tooHigh and StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.certOf.pt.tooHigh
---
error: #py_rule_theorems: the rule of pt.regionCell is not a `runRule`, `runTotal`, `runRuleFree`, `runTotalFree`, `runRuleIf`, `runLoop` or `runLoopFree` wrapper at an effect no higher than its declared one, whose results and exits hold no ref and whose handles are `regionHandle`s of regions whose parameters hold no ref, and has no lemmas StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.okOf.pt.regionCell and StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.certOf.pt.regionCell
-/
#guard_msgs in
#py_rule_theorems PyTSem for PyT (effects := ptEffect) (tags := ptTags)

-- `#py_part_writers` passes on a table whose rules write `Depth` only through the trusted primitives
-- (`PartWritersTest` has the writes it rejects).
#guard_msgs in
#py_part_writers PyTSem (lang := PyLang)
  (forbidden := [World.instHasPart_depth, PyLang.depth, World.mk])
  (trusted := [Prim.bracketed, Prim.callClosureT, Prim.withDepth, Prim.withPyDepth, Prim.depthGet,
    World.instHasPart_depth, World.instHasPart_store, World.instHasPart_modules,
    World.instHasPart_handled, World.instHasPart_guard, World.instHasPart_out])

-- The other rules got their theorems: within their effects, and satisfying every spec that has the
-- laws.
example : ImplWithin PyTSem.interp .pure PyTSem.impl.pt.setOld := PyTSem.ok.pt.setOld
example : ImplOK PyTSem.interp ptTags .pure PyTSem.impl.pt.setOld := PyTSem.implOK.pt.setOld
example : ImplWithin PyTSem.interp .calls PyTSem.impl.pt.eqVal := PyTSem.ok.pt.eqVal
example : ImplOK PyTSem.interp ptTags .calls PyTSem.impl.pt.eqVal := PyTSem.implOK.pt.eqVal
example : ImplWithin PyTSem.interp .writes PyTSem.impl.pt.setAny := PyTSem.ok.pt.setAny
example : ImplOK PyTSem.interp ptTags .writes PyTSem.impl.pt.setAny := PyTSem.implOK.pt.setAny
example : ImplOK PyTSem.interp ptTags .pure PyTSem.impl.pt.regionValue :=
  PyTSem.implOK.pt.regionValue
example : ImplOK PyTSem.interp ptTags .pure PyTSem.impl.pt.regionArity :=
  PyTSem.implOK.pt.regionArity
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
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.int 7, StrataPython.Dyn.Sem.Value.str { s := "unset", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "unset", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.bool false, StrataPython.Dyn.Sem.Value.str { s := "D", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "D", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.tuple
      #[StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.int),
        StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.object)],
    StrataPython.Dyn.Sem.Value.bool true, StrataPython.Dyn.Sem.Value.bool true]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.objPrims ^err.0()"

-- A walk into a dict subclass instance reads its dict part.
/-- info: StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictWalkSub(0) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a walk of a dict whose comparisons may run user code is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictWalkSub(1) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "an attribute write to the function cast is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.nativeWrite(0) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "an attribute write to the function cast is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.nativeWrite(1) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "an attribute write to the function cast is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.nativeWrite(2) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "an attribute write to the function cast is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.nativeWrite(3) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "an attribute write to the function cast is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.nativeWrite(4) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "cannot set 'x' attribute of immutable type 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.immutableWrite() ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a class __qualname__ that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(0) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a class __qualname__ that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(1) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "type __qualname__ must be a str, not B", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(2) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a class name that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(3) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a __slots__ item that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(4) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a class __module__ that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(5) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "an attribute name that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(6) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "an attribute name that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(7) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "an attribute name that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(8) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a class __module__ that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(9) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a keyword that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubArg(10) ^err.0()"

/-- A module whose `main` runs `pt.buildClassName` with a class body and the case `k`. -/
def buildClassModule (k : Nat) : String := s!"module m \{
  func @m.body(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) \{
    entry.0(%args.0 : py.Value, %kwargs.0 : py.Value):
      %n.0 : py.Value = py.intLit(0)
      %r.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%n.0)
      ret(%r.0)
  }
  func @m.main() -> py.Value \{
    entry.0():
      %f.0 : py.Value = py.mkClosure[[]](@m.body, \"<body>\", \"m\")
      %v.0 : py.Value = pt.buildClassName(%f.0, {k}) ^err.0()
      ret(%v.0)
    err.0(%e.0 : py.Value):
      ret(%e.0)
  }
}"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a class name that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval runModule' (buildClassModule 0)

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "__build_class__: name is not a string", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval runText (buildClassModule 1) true

/-- A module whose `main` runs `pt.subclassCases` with the case `k`, a function of no arguments
that gives `pt.mkSubInst j`'s value, and one that raises `pt.mkExc e`'s exception, each captured in
a cell. -/
def subclassModule (k : Nat) (j e : Nat := 0) : String := s!"module m \{
  func @m.f(%c.0 : base.Ref(py.Value), %args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) \{
    entry.0(%c.0 : base.Ref(py.Value), %args.0 : py.Value, %kwargs.0 : py.Value):
      %x.0 : py.Value = base.refGet[py.Value](%c.0)
      %r.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%x.0)
      ret(%r.0)
  }
  func @m.g(%c.0 : base.Ref(py.Value), %args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) \{
    entry.0(%c.0 : base.Ref(py.Value), %args.0 : py.Value, %kwargs.0 : py.Value):
      %x.0 : py.Value = base.refGet[py.Value](%c.0)
      %r.0 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%x.0)
      ret(%r.0)
  }
  func @m.main() -> py.Value \{
    entry.0():
      %i.0 : py.Value = pt.mkSubInst({j}) ^err.0()
      %c.0 : base.Ref(py.Value) = base.refNew[py.Value](%i.0)
      %f.0 : py.Value = py.mkClosure[[base.Ref(py.Value)]](@m.f, \"f\", \"m\", %c.0)
      %x.0 : py.Value = pt.mkExc({e}) ^err.0()
      %d.0 : base.Ref(py.Value) = base.refNew[py.Value](%x.0)
      %g.0 : py.Value = py.mkClosure[[base.Ref(py.Value)]](@m.g, \"g\", \"m\", %d.0)
      %v.0 : py.Value = pt.subclassCases(%f.0, %g.0, {k}) ^err.0()
      ret(%v.0)
    err.0(%e.0 : py.Value):
      ret(%e.0)
  }
}"

/-- info: StrataPython.Dyn.Sem.Value.int 9 -/
#guard_msgs in
#eval runText (subclassModule 0) true

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval runText (subclassModule 1) true

/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval runText (subclassModule 2) true

/-- info: fault: Strata.Dyn.Exec.Fault.gap "str.__format__ of an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval runText (subclassModule 3) true

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a % format that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval runText (subclassModule 4) true

/-- info: StrataPython.Dyn.Sem.Value.str { s := "", ascii := true, ascii_eq := _ } -/
#guard_msgs in
#eval runText (subclassModule 5 1 0) true

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.ValueError) StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.str { s := "v", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval runText (subclassModule 6 0 1) true

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval runText (subclassModule 7 0 0) true

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "__hash__ method should return an integer", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval runText (subclassModule 8 2 0) true

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "__hash__ method should return an integer", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval runText (subclassModule 9 3 0) true

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a | of a dict whose class overrides how its entries are read is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictOrSub(0) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a | of a dict whose class overrides how its entries are read is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictOrSub(1) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a | of a dict whose class overrides how its entries are read is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictOrSub(2) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a | of a dict whose class overrides how its entries are read is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictOrSub(3) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a | of a dict whose class overrides how its entries are read is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictOrSub(4) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.int 1 -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictOrSub(5) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.int 1 -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictOrSub(6) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a keyword that is an instance of a subclass of str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.kwargsStrSub ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "list.append() takes exactly one argument (0 given)", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(0) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "list.append() takes no keyword arguments", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(1) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "str.upper() takes no arguments (1 given)", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(2) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "pop expected at most 1 argument, got 2", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(3) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "divmod expected 2 arguments, got 1", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(4) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "getattr expected at least 2 arguments, got 1", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(5) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "sum() takes at least 1 positional argument (0 given)", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(6) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "sum() takes at most 2 arguments (3 given)", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(7) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "'x' is an invalid keyword argument for sum()", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(8) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "argument for split() given by name ('sep') and position (1)", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(9) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "round() missing required argument 'number' (pos 1)", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(10) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "sort() takes no positional arguments", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(11) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "splitlines() takes at most 1 argument (2 given)", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(12) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "expected 1 argument, got 0", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(13) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "wrapper __add__() takes no keyword arguments", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(14) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "sum() takes at most 2 keyword arguments (3 given)", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(15) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.tuple
      #[StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 1], StrataPython.Dyn.Sem.Value.int 5],
    StrataPython.Dyn.Sem.Value.tuple #[]]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.bindCase(16) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.int 6, StrataPython.Dyn.Sem.Value.int 6, StrataPython.Dyn.Sem.Value.bool true,
    StrataPython.Dyn.Sem.Value.int 5, StrataPython.Dyn.Sem.Value.int (-5), StrataPython.Dyn.Sem.Value.bool true,
    StrataPython.Dyn.Sem.Value.int 5]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.subclassOps ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.int 3, StrataPython.Dyn.Sem.Value.bool true, StrataPython.Dyn.Sem.Value.bool true,
    StrataPython.Dyn.Sem.Value.bool true, StrataPython.Dyn.Sem.Value.int 9, StrataPython.Dyn.Sem.Value.int 2,
    StrataPython.Dyn.Sem.Value.bool true, StrataPython.Dyn.Sem.Value.bool true,
    StrataPython.Dyn.Sem.Value.str { s := "a", ascii := true, ascii_eq := _ }, StrataPython.Dyn.Sem.Value.bool true,
    StrataPython.Dyn.Sem.Value.bool true, StrataPython.Dyn.Sem.Value.bool true, StrataPython.Dyn.Sem.Value.bool true]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.subclassContainers ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a list slot on an instance of a subclass of list with its own __radd__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotSub(0) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotSub(1) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a list slot on an instance of a subclass of list with its own __iadd__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotSub(2) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a list slot found as __mul__ on an instance of a subclass of list is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotSub(3) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for +: 'T' and 'U'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(0) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for +: 'L' and 'list'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(1) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for *: 'M' and 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(2) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for *: 'TM' and 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(3) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for *=: 'TM' and 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(4) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for *: 'int' and 'TR'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(5) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.int 2] -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(6) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "can't multiply sequence by non-int of type 'list'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(7) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for *=: 'int' and 'TR'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(8) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for +: 'S' and 'str'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(9) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for +: 'LT' and 'list'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(10) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for *: 'TL' and 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.seqSlotCleared(11) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSetSubOps(0) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSetSubOps(1) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSetSubOps(2) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the repr of a set whose class defines __iter__ or __len__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSetSubOps(3) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the repr of a set whose class defines __iter__ or __len__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSetSubOps(4) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.str { s := "P({1})", ascii := true, ascii_eq := _ } -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSetSubOps(5) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.str { s := "Q()", ascii := true, ascii_eq := _ } -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSetSubOps(6) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the repr of a set whose class defines __iter__ or __len__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSetSubOps(7) ^err.0()"

/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "'in <string>' requires string as left operand, not I", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSetSubOps(8) ^err.0()"

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

-- A native of kind `function` is a Python frame: its own recursion stops at the Python depth limit.
-- A native of another kind counts none, and stops at the bound of nested built-in calls.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "Python call depth over 900" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.nativeDepth(0) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "built-in calls nested deeper than the model follows" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.nativeDepth(1) ^err.0()"

-- A native's gapped attribute stops with a gap when it is read; its other attributes read as usual.
/-- info: StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.function) -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.nativeGapped(0) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute __doc__ of the built-in f is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.nativeGapped(1) ^err.0()"

-- A class-method descriptor checks its class, called and in `__get__`, as CPython 3.12 does.
/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "descriptor 'fromkeys' requires a subtype of 'dict' but received 'list'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.classDescr(0) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "descriptor 'fromkeys' for type 'dict' needs a type, not a 'int' as arg 2", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.classDescr(1) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "descriptor 'fromkeys' of 'dict' object needs an argument", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.classDescr(2) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "descriptor 'fromkeys' requires a subtype of 'dict' but received 'list'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.classDescr(3) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "descriptor 'fromkeys' requires a subtype of 'dict' but received 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.classDescr(4) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bound
  (StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.dict))
  (StrataPython.Dyn.Sem.Builtin.dict)
  "fromkeys"
  (StrataPython.Dyn.Sem.DescrKind.classMethod)
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.classDescr(5) ^err.0()"

-- `{*S}` merges a set subclass's members without calling its `__iter__`.
/-- info: StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 1] -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.setUpdateSub ^err.0()"

-- The checks that run before a step machine starts raise CPython 3.12's `TypeError`s.
/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "tuple.__new__(int): int is not a subtype of tuple", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.startCheck(0) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "descriptor 'extend' for 'list' objects doesn't apply to a 'int' object", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.startCheck(1) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "descriptor 'fromkeys' requires a subtype of 'dict' but received 'list'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.startCheck(2) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.startCheck(3) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "tuple.__new__(int): int is not a subtype of tuple", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.startCheck(4) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: a type's tp_new outside a class call" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.startCheck(5) ^err.0()"

/-- No entry of a built-in type's table is a `tp_new`: `AttrKind.descr?`, which gives the kind of
each descriptor that `builtinEntry` makes, never gives `.tpNew`. -/
example (k : AttrKind) : k.descr? ≠ some .tpNew := by
  cases k <;> simp [AttrKind.descr?]

-- The hooks that pieces of the built-in library fill (`pt.hooks`).
/--
info: fault: Strata.Dyn.Exec.Fault.gap "union args is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.partHooks(0) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "subscripting the class type is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.partHooks(1) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method list.__class_getitem__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.partHooks(2) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "built-in method type.__or__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.partHooks(3) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a C recursion depth over 9000" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.partHooks(4) ^err.0()"

-- The static method `str.maketrans`, through the class and through an instance (`pt.staticDescr`).
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "a", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "b", ascii := true, ascii_eq := _ }]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.staticDescr(0) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "a", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "b", ascii := true, ascii_eq := _ }]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.staticDescr(1) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "a", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "b", ascii := true, ascii_eq := _ }]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.staticDescr(2) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.staticDescr(3) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.staticDescr(4) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.int 7 -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.staticDescr(5) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.staticDescr(6) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.staticDescr(7) ^err.0()"

-- The attributes of heap types and of class namespaces, and a write to a type that is not immutable,
-- which stop with a gap (`pt.heapAttrs`).
/--
info: fault: Strata.Dyn.Exec.Fault.gap "the __annotations__ of the heap type ExceptionGroup is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.heapAttrs(0) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the __annotations__ of a class whose namespace has none is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.heapAttrs(1) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "a class's __annotations__ entry that is not a dict is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.heapAttrs(2) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the attribute BuiltinImporter.create_module is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.heapAttrs(3) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "an attribute write to the mutable built-in type ExceptionGroup is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.heapAttrs(4) ^err.0()"

-- The dict views' operations through their tables, with test bodies (`pt.viewOps`) and without
-- (`pt.viewBare`).
/--
info: StrataPython.Dyn.Sem.Value.int 7
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(0) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool true
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(1) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool true
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(2) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool true
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(3) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "and", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(4) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "rand", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(5) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "eq", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(6) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "eq", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(7) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "'<' not supported between instances of 'dict_keys' and 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(8) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "bad operand type for unary -: 'dict_keys'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(9) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for +: 'dict_keys' and 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(10) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for *=: 'int' and 'dict_keys'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(11) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "ror", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(12) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "and", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(13) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for *=: 'dict_keys' and 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(14) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for *=: 'dict_keys' and 'tuple'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(15) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the operators of this built-in type are not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(16) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the operators of this built-in type are not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(17) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "'dict_keys' object is not an iterator", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(18) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "unhashable type: 'dict_keys'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(19) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the hash of a dict_values is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(20) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "mp", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(21) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.mapping is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(22) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool false
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(23) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.int 7
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(24) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "object of type 'tuple_iterator' has no len()", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(25) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool true
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(26) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool false
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(27) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.__len__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(0) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.__len__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(1) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.__contains__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(2) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.__and__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(4) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.__rand__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(5) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.__eq__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(6) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "getset mapping is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(21) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool true
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(26) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool false
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(27) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for @: 'dict_keys' and 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(28) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_items.__len__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(29) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "or", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(30) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "or", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(31) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool false
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(32) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.__ne__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(33) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.dict_keys)
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(34) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool false
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(35) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the operators of this built-in type are not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(36) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the operators of this built-in type are not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewOps(37) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.__ror__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(12) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.__and__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(13) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_items.__len__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(29) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool false
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(32) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_keys.__ne__ is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.viewBare(33) ^err.0()"

-- A mappingproxy of a plain dict (`pt.dictProxyCase`).
/--
info: StrataPython.Dyn.Sem.Value.int 2
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictProxyCase(0) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.KeyError) StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 9] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictProxyCase(1) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "unhashable type: 'list'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictProxyCase(2) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.mappingproxy)
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictProxyCase(3) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the operators of this built-in type are not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictProxyCase(4) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.int 4
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictProxyCase(5) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "a mappingproxy of an instance of a subclass of dict is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictProxyCase(6) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.int 7
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(0) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "import of module m is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(1) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "type 'U' is not an acceptable base type", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(5) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "a subclass of U is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(6) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.int 3
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(7) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "import of module nosuch is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(8) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "object.__new__ of the C type types.A is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(10) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "len() takes exactly one argument (0 given)", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(11) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a slot wrapper bound to an object of another type is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(12) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "method-wrapper", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(13) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "object of type 'types.A' has no len()", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(14) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.str { s := "types", ascii := true, ascii_eq := _ } -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(15) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.len) -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(16) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.KeyError) StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.str { s := "nope", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(17) ^err.0()"

/-- info: object 2 -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(18) ^err.0()"

-- `import m` in the translated program `m`, whose globals are cells, stops with a gap.
/--
info: fault: Strata.Dyn.Exec.Fault.gap "import of the translated module m is not modelled yet"
-/
#guard_msgs in
#eval run "      %c.0 : base.Ref(py.Value) = py.globalCell(\"m\", \"x\")
      %v.0 : py.Value = py.importModule(\"m\") ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "isinstance() arg 2 must be a type, a tuple of types, or a union", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(19) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "descriptor 'm' for 'types.A' objects doesn't apply to a 'int' object", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(20) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "object.__new__ of the C type types.A is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(21) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the operators of this built-in type are not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(22) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the attribute G.g is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(23) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the __dict__ that a user class's namespace holds is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(24) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "object.__new__ of the C type types.A is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(25) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool true
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(26) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.AttributeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "'types.A' object has no attribute 'x'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(27) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "a class's __dict__ subscripted by a key that is not a str is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(28) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "'types.B' object is not callable", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(29) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.AttributeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "type object 'types.B' has no attribute 'nope'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(30) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "cannot set 'x' attribute of immutable type 'types.B'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(31) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "types.B() takes no arguments", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(32) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "cast", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "cast", ascii := true, ascii_eq := _ },
    StrataPython.Dyn.Sem.Value.str { s := "typing", ascii := true, ascii_eq := _ }]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(33) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.str { s := "method", ascii := true, ascii_eq := _ }
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(34) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.str { s := "method", ascii := true, ascii_eq := _ } -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(35) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(36) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a class's __dict__ subscripted by a key that is not a str is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.hooks(37) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool true
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(0) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "isinstance with a second argument that is an object, not a class"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(1) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool true
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubIssubclass(0) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "issubclass() arg 2 must be a class, a tuple of classes, or a union", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubIssubclass(1) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "union args is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubIssubclass(2) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "callable() of this object is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.callableOpaque ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "whether a mappingproxy is a sequence is not modelled"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.sequenceCheckProxy ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: callable() of a class call's own callee"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.callableTpNew ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str
      { s := "unsupported operand type(s) for |: 'type' and 'type'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(2) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.int 3
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(3) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "from q import b of a name that the module lacks is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(4) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.bool true
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(5) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute q.__name__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(6) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.AttributeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "module 'q' has no attribute 'b'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(7) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute g.x is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(8) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute h.x is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(9) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute p.s is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(10) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "import of module z is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(11) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.int 1 -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(12) ^err.0()"

/--
info: fault: Strata.Dyn.Exec.Fault.gap "the failed import of r is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(13) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.ValueError) StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.str { s := "r2", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(14) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(15) ^err.0()"

/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(16) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute T.__doc__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(17) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.KeyError) StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.str { s := "x", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(18) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute T.__doc__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(19) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute U.__doc__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(20) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute U.__doc__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(21) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute U.__doc__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(22) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute U.__module__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(23) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute U.__module__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(24) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the attribute T.__module__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.stubHooks(25) ^err.0()"

/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.bool true, StrataPython.Dyn.Sem.Value.bool true],
    StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.bool false, StrataPython.Dyn.Sem.Value.bool false],
    StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.bool false, StrataPython.Dyn.Sem.Value.bool false],
    StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.bool false, StrataPython.Dyn.Sem.Value.bool false]]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.setExactCase ^err.0()"

-- `next()` of a dict view raises CPython's `TypeError`: its class has no `__next__`.
/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "'dict_keys' object is not an iterator", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.nextView ^err.0()"

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

-- A walk of sets whose members are frozensets, which may run user code when compared, walks the
-- live table.
/-- info: StrataPython.Dyn.Sem.Value.bool true -/
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

-- Every instruction of `Py` has a rule, but the quantifiers of the contracts.
-- `BaseExceptionGroup.__new__` stops with a gap where CPython would run a user length hint.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "a length hint of user code inside BaseExceptionGroup.__new__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.groupLenHint ^err.0()"

-- The import rules stop with a gap where CPython would call a replaced `__import__`, or read a
-- module that the model doesn't hold.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "an import after builtins.__import__ was replaced is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.importGaps(0) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "an import after builtins.__import__ was deleted is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.importGaps(1) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a reference into module math is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.importGaps(2) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "builtins.nope is missing" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.importGaps(3) ^err.0()"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "from builtins import __dict__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.importGaps(4) ^err.0()"

/--
error: Py is not fully covered: no rule for py.allIn, py.anyIn, py.allItems, py.anyItems
-/
#guard_msgs in
#dyn_coverage Py (complete)

-- A step machine that the call dispatch reaches suspends and resumes across activations: `sum`
-- directly; `tuple.__new__` through `tuple()`, with a `typeNew` frame; and `object.__init__`
-- through `object()`, with a `typeInit` frame, whose result `1` raises `type.__call__`'s
-- `TypeError` after the last resume.
/-- info: StrataPython.Dyn.Sem.Value.int 3 -/
#guard_msgs in
#eval run "      %f.0 : py.Value = py.qualifiedRef(\"builtins\", \"sum\") ^err.0()
      %v.0 : py.Value = pt.resumeCase(%f.0) ^err.0()"
/-- info: StrataPython.Dyn.Sem.Value.int 3 -/
#guard_msgs in
#eval run "      %f.0 : py.Value = py.qualifiedRef(\"builtins\", \"tuple\") ^err.0()
      %v.0 : py.Value = pt.resumeCase(%f.0) ^err.0()"
-- A resumed `__new__` runs one C level deeper, as the class call that suspended it: the test
-- machine for `list.__new__` gives the C depth that it resumes at.
/-- info: StrataPython.Dyn.Sem.Value.int 1 -/
#guard_msgs in
#eval run "      %f.0 : py.Value = py.qualifiedRef(\"builtins\", \"list\") ^err.0()
      %v.0 : py.Value = pt.resumeCase(%f.0) ^err.0()"
/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "__init__() should return None, not 'int'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %f.0 : py.Value = py.qualifiedRef(\"builtins\", \"object\") ^err.0()
      %v.0 : py.Value = pt.resumeCase(%f.0) ^err.0()"
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.tuple
      #[StrataPython.Dyn.Sem.Value.str { s := "suspend", ascii := true, ascii_eq := _ },
        StrataPython.Dyn.Sem.Value.int 1],
    StrataPython.Dyn.Sem.Value.tuple
      #[StrataPython.Dyn.Sem.Value.str { s := "done", ascii := true, ascii_eq := _ }, StrataPython.Dyn.Sem.Value.int 3]]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.resumeDirect ^err.0()"

-- One step of it gives two frames: the `callLevel` frame of the instance's call, over `sum`'s.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "suspend", ascii := true, ascii_eq := _ }, StrataPython.Dyn.Sem.Value.int 2]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.callLevelStep ^err.0()"

-- Through `callResumable`, a call of a C type that a piece makes stops with the gap of a C type's
-- `object.__new__`, and a call of an object with opaque state goes through its class's `__call__`.
/--
info: fault: Strata.Dyn.Exec.Fault.gap "object.__new__ of the C type types.A is not modelled yet"
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.cTypeStep(0) ^err.0()"

/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.str { s := "len() takes exactly one argument (0 given)", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.cTypeStep(1) ^err.0()"

-- A call of an instance whose `__call__` is a machine suspends as a `callLevel` frame, and resumes
-- through it to the machine's result.
/-- info: StrataPython.Dyn.Sem.Value.int 3 -/
#guard_msgs in
#eval run "      %f.0 : py.Value = pt.callInst ^err.0()
      %v.0 : py.Value = pt.resumeCase(%f.0) ^err.0()"

-- A `typeInit` frame without the frame of its inner call stops with a gap.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: a frame list that doesn't fit the call" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.resumeNoFit ^err.0()"

-- A first step that calls through `callResumable` reaches a second machine that suspends: `min`'s
-- first step calls `sum`, whose machine runs over the activations.
/-- info: StrataPython.Dyn.Sem.Value.int 3 -/
#guard_msgs in
#eval run "      %f.0 : py.Value = py.qualifiedRef(\"builtins\", \"min\") ^err.0()
      %v.0 : py.Value = pt.resumeCase(%f.0) ^err.0()"

-- A slice assignment fits the slice to the list as it is after the items are read.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.int 2, StrataPython.Dyn.Sem.Value.int 7]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.staleSlice ^err.0()"

-- The container constructors' machines keep no callee of the internal kind `.tpNew` in their
-- frames or results (nor in a tuple or a list there), over the activations that an iterator of
-- one item per activation needs; the last call is of a subclass of `tuple`.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 4, StrataPython.Dyn.Sem.Value.bool false],
    StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 4, StrataPython.Dyn.Sem.Value.bool false],
    StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 4, StrataPython.Dyn.Sem.Value.bool false],
    StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 4, StrataPython.Dyn.Sem.Value.bool false],
    StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 4, StrataPython.Dyn.Sem.Value.bool false],
    StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 4, StrataPython.Dyn.Sem.Value.bool false]]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.tpNewNoLeak ^err.0()"

-- `machinesStart` with no fuel left stops with a gap.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "a call dispatch nested deeper than the model follows" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.startZero ^err.0()"

-- The walk bounds of `zip`, `enumerate` and the reverse iterators, and of a nest past the budget
-- or the depth.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.int 3, StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.int 3,
    StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.int 4, StrataPython.Dyn.Sem.Value.int 4,
    StrataPython.Dyn.Sem.Value.int 4, StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.int 3,
    StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.int 1]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.iterBounds ^err.0()"

-- `zip`, `enumerate` and the reverse iterators step by their type's `__next__`: a `zip` and an
-- `enumerate` over `iter([1, 2, 3])` give `(1,)` and `(0, 1)`, the reverse iterators the list's
-- last item, and the one over an empty dict ends.
/-- info: StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 1] -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.zipNext ^err.0()"
/-- info: StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 0, StrataPython.Dyn.Sem.Value.int 1] -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.enumNext ^err.0()"
/-- info: StrataPython.Dyn.Sem.Value.int 3 -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.revNext ^err.0()"
/-- info: StrataPython.Dyn.Sem.Value.int 3 -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.listRevNext ^err.0()"
/--
info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.StopIteration) StrataPython.Dyn.Sem.Value.tuple #[] context StrataPython.Dyn.Sem.Value.none
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.dictRevNext ^err.0()"

-- A built-in container's fast paths run only for its own type's `__iter__` and `__len__`.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "a slot wrapper bound to an object of another type is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.foreignIter ^err.0()"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "a slot wrapper bound to an object of another type is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.foreignLen ^err.0()"
/-- info: StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.str_iterator) -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strSubIter ^err.0()"

-- A region handle stops with a model-invariant gap on values that its region doesn't take, and
-- runs the region on the values that it takes.
/-- A run of `pt.regionArity k`, whose body returns at once. -/
def regionArityRun (k : Nat) : IO Unit :=
  run s!"      %v.0 : py.Value = pt.regionArity({k}) ^err.0() \{
        body.0(%x.0 : py.Value):
          %unit.0 : base.Unit = base.unit
          %ok.0 : base.Except(py.Value, base.Unit) = base.ok[py.Value, base.Unit](%unit.0)
          ret(%ok.0)
      }"

/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: a region called with 0 values, which it doesn't take" -/
#guard_msgs in
#eval regionArityRun 0

/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: a region called with 2 values, which it doesn't take" -/
#guard_msgs in
#eval regionArityRun 1

/-- info: StrataPython.Dyn.Sem.Value.none -/
#guard_msgs in
#eval regionArityRun 2

-- The rules of `list.sort` and `str.lower` on Lean values, as CPython 3.12 gives them:
-- `[1, True, 1.0, 2, 3]`, `[2.0, nan, 1.0]` and `'ας'`.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.int 1, StrataPython.Dyn.Sem.Value.bool true,
    StrataPython.Dyn.Sem.Value.float 4607182418800017408, StrataPython.Dyn.Sem.Value.int 2,
    StrataPython.Dyn.Sem.Value.int 3]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.sortInts ^err.0()"
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.float 4611686018427387904, StrataPython.Dyn.Sem.Value.float 9221120237041090560,
    StrataPython.Dyn.Sem.Value.float 4607182418800017408]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.sortNaN ^err.0()"
/-- info: StrataPython.Dyn.Sem.Value.str { s := "ας", ascii := false, ascii_eq := _ } -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.strLowerSigma ^err.0()"
-- `{97: 99, 98: 100, 101: None}` and `{97: 1, 98: 'x'}`; and the gap of a bytearray.
/--
info: StrataPython.Dyn.Sem.Value.tuple
  #[StrataPython.Dyn.Sem.Value.tuple
      #[StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 97, StrataPython.Dyn.Sem.Value.int 99],
        StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 98, StrataPython.Dyn.Sem.Value.int 100],
        StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 101, StrataPython.Dyn.Sem.Value.none]],
    StrataPython.Dyn.Sem.Value.tuple
      #[StrataPython.Dyn.Sem.Value.tuple #[StrataPython.Dyn.Sem.Value.int 97, StrataPython.Dyn.Sem.Value.int 1],
        StrataPython.Dyn.Sem.Value.tuple
          #[StrataPython.Dyn.Sem.Value.int 98,
            StrataPython.Dyn.Sem.Value.str { s := "x", ascii := true, ascii_eq := _ }]]]
-/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.maketransRule ^err.0()"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "a UnicodeDecodeError of a bytes-like object other than bytes is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.decodeBytearray ^err.0()"

end StrataPython.Dyn.Sem.RuleTheoremsTest
