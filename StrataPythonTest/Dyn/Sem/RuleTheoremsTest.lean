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
  insn nextView (^err (exc : Value)) : Value
  insn setUpdateSub (^err (exc : Value)) : Value
  insn frozenSeal (k : base.Int) (^err (exc : Value)) : Value
  insn nativeDepth (k : base.Int) (^err (exc : Value)) : Value
  insn nativeGapped (k : base.Int) (^err (exc : Value)) : Value
  insn classDescr (k : base.Int) (^err (exc : Value)) : Value
  insn startCheck (k : base.Int) (^err (exc : Value)) : Value
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
  insn resumeCase (f : Value) (^err (exc : Value)) : Value
  insn callInst (^err (exc : Value)) : Value
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

/-- A write of a plain name to `types.GenericAlias`, an immutable built-in type whose C name differs
from its name: CPython's `TypeError` names it by its C name. -/
@[dyn_sem PyT.immutableWrite, expose] public def immutableWrite (err : Target E [Value]) :
    Sem ε E Value :=
  runRule err #[] (do
    Proto.setAttr (.builtin .«types.GenericAlias») "x" (some (.int 1))
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
    let mo ← PyPure.allocObj (.builtin .module) (.module "mm" #[] false)
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
  runRuleFree err #[] (nextOf .zip fun l => .zip #[l] false)

@[dyn_sem PyT.enumNext, expose] public def enumNext (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (nextOf .enumerate fun l => .enumerate l 0)

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
  | "pt.newPrims" | "pt.bindCase" => .reads
  | "pt.oldPrims" | "pt.frozenSeal" | "pt.nativeDepth" | "pt.nativeGapped" | "pt.nextView" | "pt.setUpdateSub" | "pt.classDescr" | "pt.startCheck" => .writes
  | "pt.frozenOr" | "pt.frozenAdd" | "pt.objPrims" => .writes
  | "pt.frozenWalk" | "pt.frozenMerge" | "pt.subclassOps" => .calls
  | "pt.subclassContainers" | "pt.seqSlotSub" | "pt.callInst" | "pt.callLevelStep" | "pt.resumeCase" | "pt.resumeDirect" | "pt.resumeNoFit"
  | "pt.foreignIter" | "pt.foreignLen" | "pt.strSubIter" | "pt.iterBounds" | "pt.zipNext"
  | "pt.enumNext" | "pt.revNext" | "pt.listRevNext" | "pt.dictRevNext" | "pt.startZero"
  | "pt.staleSlice" => .writes
  | _ => .pure

/-- The tags of `PyLang` in `PyTSem`. -/
def ptTags (σ : Type) [Store σ] : @Tags σ _ ⟨PyTSem.interp σ⟩ :=
  letI : Decode σ := ⟨PyTSem.interp σ⟩
  ⟨⟨PyTSem.T.py.Value, rfl⟩, ⟨Ty.ref PyTSem.T.py.Value, rfl⟩,
    ⟨PyTSem.T.base.Except PyTSem.T.py.Value PyTSem.T.py.Value, rfl⟩⟩

/--
error: #py_rule_theorems: the rule of pt.direct is not a `runRule`, `runTotal`, `runRuleFree`, `runTotalFree`, `runRuleIf`, `runLoop` or `runLoopFree` wrapper at an effect no higher than its declared one whose results and exits hold no ref, and has no lemmas StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.okOf.pt.direct and StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.certOf.pt.direct
---
error: #py_rule_theorems: the rule of pt.tooHigh is not a `runRule`, `runTotal`, `runRuleFree`, `runTotalFree`, `runRuleIf`, `runLoop` or `runLoopFree` wrapper at an effect no higher than its declared one whose results and exits hold no ref, and has no lemmas StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.okOf.pt.tooHigh and StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.certOf.pt.tooHigh
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
      { s := "cannot set 'x' attribute of immutable type 'types.GenericAlias'", ascii := true, ascii_eq := _ }] context StrataPython.Dyn.Sem.Value.none
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

-- Every instruction of `Py` has a rule, but the contract operations, whose rules come with the
-- semantics of contracts.
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
error: Py is not fully covered: no rule for py.argOf, py.extraKwargs, py.bindsTo, py.stdClass, py.isInstance, py.typeIsSubclass, py.len, py.reSearch, py.strIsOneOf, py.intIsOneOf, py.isImmutableScalar, py.dictKeysWithin, py.allIn, py.anyIn, py.allItems, py.anyItems, py.attrLoc, py.itemLoc, py.objLoc, py.reachLoc, py.instanceState
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

-- `zip`, `enumerate` and the reverse iterators step by their type's `__next__`, a body that this
-- piece's tables don't have.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "built-in method zip.__next__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.zipNext ^err.0()"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "built-in method enumerate.__next__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.enumNext ^err.0()"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "built-in method reversed.__next__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.revNext ^err.0()"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "built-in method list_reverseiterator.__next__ is not modelled yet" -/
#guard_msgs in
#eval run "      %v.0 : py.Value = pt.listRevNext ^err.0()"
/-- info: fault: Strata.Dyn.Exec.Fault.gap "built-in method dict_reversekeyiterator.__next__ is not modelled yet" -/
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

end StrataPython.Dyn.Sem.RuleTheoremsTest
