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
* `#dyn_coverage Py (complete)` names what has no rule yet: `py.mkClosure` and the contract
  operations.
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
    Proto.requireDefined (Value.undef "y") "NameError" "m" : PyM σ .writes true Value)

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
  | _ => .pure

/-- The tags of `PyLang` in `PyTSem`. -/
def ptTags (σ : Type) [Store σ] : @Tags σ _ ⟨PyTSem.interp σ⟩ :=
  letI : Decode σ := ⟨PyTSem.interp σ⟩
  ⟨⟨PyTSem.T.py.Value, rfl⟩, ⟨Ty.ref PyTSem.T.py.Value, rfl⟩,
    ⟨PyTSem.T.base.Except PyTSem.T.py.Value PyTSem.T.py.Value, rfl⟩⟩

/--
error: #py_rule_theorems: the rule of pt.direct is not a `runRule`, `runTotal`, `runRuleFree` or `runTotalFree` wrapper at an effect no higher than its declared one whose results and exits hold no ref, and has no lemmas StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.okOf.pt.direct and StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.certOf.pt.direct
---
error: #py_rule_theorems: the rule of pt.tooHigh is not a `runRule`, `runTotal`, `runRuleFree` or `runTotalFree` wrapper at an effect no higher than its declared one whose results and exits hold no ref, and has no lemmas StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.okOf.pt.tooHigh and StrataPython.Dyn.Sem.RuleTheoremsTest.PyTSem.certOf.pt.tooHigh
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

/-- Run `@m.main`, whose body ends with `%v.0`, and print its result, or the class, arguments
and context of the exception it raises, or its fault. -/
def run (body : String) : IO Unit := do
  let text := s!"module m \{
  func @m.main() -> py.Value \{
    entry.0():
{body}
      ret(%v.0)
    err.0(%e.0 : py.Value):
      ret(%e.0)
  }
}"
  match ← Module.read PyT.env text "t.dyn" with
  | .error e => IO.println s!"read: {e}"
  | .ok m =>
    let o := runModule PyTSem.model m (.str (.str .base "m") "main") #[] 1000
    match o.result, o.read? Value with
    | .ok _, some (.obj id) => match o.snapshot.world.store.get? id with
      | some { cls, payload := .exc e, .. } =>
        IO.println s!"exception {reprStr cls} {reprStr e.args} context {reprStr e.context}"
      | _ => IO.println s!"object {id}"
    | .ok _, some v => IO.println (reprStr v)
    | .ok _, none => IO.println "a result that is not a value"
    | .fault f, _ => IO.println s!"fault: {repr f}"

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

/--
error: Py is not fully covered: no rule for py.mkClosure, py.argOf, py.extraKwargs, py.bindsTo, py.stdClass, py.isInstance, py.typeIsSubclass, py.len, py.reSearch, py.strIsOneOf, py.intIsOneOf, py.isImmutableScalar, py.dictKeysWithin, py.allIn, py.anyIn, py.allItems, py.anyItems, py.attrLoc, py.itemLoc, py.objLoc, py.reachLoc, py.instanceState
-/
#guard_msgs in
#dyn_coverage Py (complete)

end StrataPython.Dyn.Sem.RuleTheoremsTest
