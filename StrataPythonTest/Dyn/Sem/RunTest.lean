/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.Table
import StrataDyn.DDMRead
import StrataDyn.Exec.Run
meta import StrataPython.Dyn.Sem.Table
meta import StrataDyn.DDMRead
meta import StrataDyn.Exec.Run

set_option autoImplicit false

/-!
# Running Python's rules

Small modules in the IR's text, run with `PySem`: globals, `loadGlobal` through the `builtins`
dict, the checks, `is`, dict displays, and the gaps.
-/

namespace StrataPython.Dyn.Sem.RunTest

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn.Sem

/-- A short text of a value, for the tests' output. -/
def showV : Value → String
  | .none => "None"
  | .bool b => if b then "True" else "False"
  | .int i => toString i
  | .str s => Format.strRepr s.s
  | .float bits => Format.floatRepr bits
  | .range a b c => if c == 1 then s!"range({a}, {b})" else s!"range({a}, {b}, {c})"
  | .builtin b => b.info.name
  | .tuple xs => "(" ++ ", ".intercalate (xs.attach.toList.map fun ⟨x, _⟩ => showV x) ++
      (if xs.size == 1 then ",)" else ")")
  | .obj id => s!"<object {id}>"
  | .traceback => "<traceback>"
  | v => reprStr v

/-- Run `@m.main` of the module `text`, and print its result or its fault. -/
def run (text : String) : IO Unit := do
  match ← Module.read Py.env text "t.dyn" with
  | .error e => IO.println s!"read: {e}"
  | .ok m =>
    let o := runModule PySem.model m (.str (.str .base "m") "main") #[] 1000
    match o.result with
    | .ok _ => match o.read? Value with
      | some (.obj id) => match o.snapshot.world.store.get? id with
        | some { cls, payload := .exc e, .. } =>
          IO.println s!"exception {showV cls}{showV e.args}, context {showV e.context}, \
            traceback {showV e.traceback}, fields {e.fields.toList.map fun (n, v) => (n, showV v)}"
        | some { cls, payload := .dict t, .. } =>
          IO.println s!"{showV cls} {(t.live.map fun (e, v) => s!"{showV e.key}: {showV v}").toList}"
        | _ => IO.println s!"object {id}"
      | some v => IO.println (showV v)
      | none => IO.println "a result that is not a value"
    | .fault f => IO.println s!"fault: {repr f}"

/-- info: 3 -/
#guard_msgs in
#eval run "module m {
  func @m.main() -> py.Value {
    entry.0():
      %c.0 : base.Ref(py.Value) = py.globalCell(\"m\", \"x\")
      %i.0 : py.Value = py.intLit(3)
      %s.0 : base.Unit = base.refSet[py.Value](%c.0, %i.0)
      %v.0 : py.Value = py.loadGlobal(\"m\", \"x\") ^err.0()
      ret(%v.0)
    err.0(%e.0 : py.Value):
      ret(%e.0)
  }
}"

/-- A module whose `main` returns `body`'s value `%v.0`, or the exception it raises. -/
def main (body : String) : String := s!"module m \{
  func @m.main() -> py.Value \{
    entry.0():
{body}
      ret(%v.0)
    err.0(%e.0 : py.Value):
      ret(%e.0)
  }
}"

/-- A module whose `main` returns `body`'s value `%v.0`, and raises nothing. -/
def mainTotal (body : String) : String := s!"module m \{
  func @m.main() -> py.Value \{
    entry.0():
{body}
      ret(%v.0)
  }
}"

-- A name that no global binds is read from the `builtins` dict.
/-- info: len -/
#guard_msgs in
#eval run (main "      %v.0 : py.Value = py.loadGlobal(\"m\", \"len\") ^err.0()")

-- `None` in `builtins` is the immediate.
/-- info: None -/
#guard_msgs in
#eval run (main "      %v.0 : py.Value = py.loadGlobal(\"m\", \"None\") ^err.0()")

-- A global cell that holds `undef` falls back to `builtins`, as after `del`.
/-- info: print -/
#guard_msgs in
#eval run (main "      %c.0 : base.Ref(py.Value) = py.globalCell(\"m\", \"print\")
      %v.0 : py.Value = py.loadGlobal(\"m\", \"print\") ^err.0()")

-- An unbound name raises `NameError`, with no exception being handled.
/-- info: exception NameError("name 'nope' is not defined",), context None, traceback <traceback>, fields [(name, 'nope')] -/
#guard_msgs in
#eval run (main "      %v.0 : py.Value = py.loadGlobal(\"m\", \"nope\") ^err.0()")

-- `requireDefined` gives a defined value back, and raises for `undef`, with the message as it is.
/-- info: 7 -/
#guard_msgs in
#eval run (main "      %i.0 : py.Value = py.intLit(7)
      %v.0 : py.Value = py.requireDefined(%i.0, \"UnboundLocalError\", \"x {}\") ^err.0()")

/-- info: exception UnboundLocalError('x {}',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %u.0 : py.Value = py.undef(\"x\")
      %v.0 : py.Value = py.requireDefined(%u.0, \"UnboundLocalError\", \"x {}\") ^err.0()")

-- A `NameError` from `requireDefined` has no `name` field yet: the operation carries no name.
/-- info: exception NameError('x',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %u.0 : py.Value = py.undef(\"x\")
      %v.0 : py.Value = py.requireDefined(%u.0, \"NameError\", \"x\") ^err.0()")

-- `is` on singletons is exact; on two equal ints it depends on CPython's caching, so it gaps.
/-- info: True -/
#guard_msgs in
#eval run (mainTotal "      %a.0 : py.Value = py.noneLit
      %b.0 : py.Value = py.noneLit
      %v.0 : py.Value = py.is(%a.0, %b.0)")

/-- info: True -/
#guard_msgs in
#eval run (mainTotal "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.noneLit
      %v.0 : py.Value = py.isNot(%a.0, %b.0)")

/-- info: fault: Strata.Dyn.Exec.Fault.gap "is on two equal immediates depends on CPython's caching" -/
#guard_msgs in
#eval run (mainTotal "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(1)
      %v.0 : py.Value = py.is(%a.0, %b.0)")

-- A dict display keeps the first key's position and the last value.
/-- info: dict ['a': 3, 'b': 2] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.strLit(\"a\")
      %b.0 : py.Value = py.strLit(\"b\")
      %i.0 : py.Value = py.intLit(1)
      %j.0 : py.Value = py.intLit(2)
      %k.0 : py.Value = py.intLit(3)
      %v.0 : py.Value = py.mkDict(%a.0, %i.0, %b.0, %j.0, %a.0, %k.0) ^err.0()")

-- Keys equal under `==` are one key, as in CPython 3.12: `{1: 1, True: 2}` is `{1: 2}`,
-- `{0.0: 'a', -0.0: 'b'}` is `{0.0: 'b'}`.  `ValuesTest` checks the equality of tuples and ranges.
/-- info: dict [1: 2] -/
#guard_msgs in
#eval run (main "      %i.0 : py.Value = py.intLit(1)
      %j.0 : py.Value = py.intLit(2)
      %t.0 : py.Value = py.boolLit(true)
      %v.0 : py.Value = py.mkDict(%i.0, %i.0, %t.0, %j.0) ^err.0()")

/-- info: dict [0.0: 'b'] -/
#guard_msgs in
#eval run (main "      %z.0 : py.Value = py.floatLit(0.0)
      %n.0 : py.Value = py.floatLit(-0.0)
      %a.0 : py.Value = py.strLit(\"a\")
      %b.0 : py.Value = py.strLit(\"b\")
      %v.0 : py.Value = py.mkDict(%z.0, %a.0, %n.0, %b.0) ^err.0()")

-- An int and a float key are not compared yet.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "comparing these dict keys is not modelled yet" -/
#guard_msgs in
#eval run (main "      %i.0 : py.Value = py.intLit(1)
      %f.0 : py.Value = py.floatLit(1.0)
      %v.0 : py.Value = py.mkDict(%i.0, %i.0, %f.0, %i.0) ^err.0()")

-- An odd count of a display's operands, and a key that is an object, gap.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: mkDict: operand assumption failed" -/
#guard_msgs in
#eval run (main "      %i.0 : py.Value = py.intLit(1)
      %v.0 : py.Value = py.mkDict(%i.0) ^err.0()")

/-- info: fault: Strata.Dyn.Exec.Fault.gap "a dict key that is an object is not modelled yet" -/
#guard_msgs in
#eval run (main "      %i.0 : py.Value = py.intLit(1)
      %d.0 : py.Value = py.mkDict ^err.0()
      %v.0 : py.Value = py.mkDict(%d.0, %i.0) ^err.0()")

-- `unsupported` names the construct, and gaps.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "construct not translated: yield" -/
#guard_msgs in
#eval run (mainTotal "      %n.0 : py.Value = py.strLit(\"yield\")
      %v.0 : py.Value = py.unsupported(%n.0)")

/-- info: fault: Strata.Dyn.Exec.Fault.gap "model invariant: py.unsupported: operand assumption failed" -/
#guard_msgs in
#eval run (mainTotal "      %n.0 : py.Value = py.noneLit
      %v.0 : py.Value = py.unsupported(%n.0)")

-- A bytes literal, and an operation that is not modelled yet.
/-- info: StrataPython.Dyn.Sem.Value.bytes #[97, 255] -/
#guard_msgs in
#eval run (mainTotal "      %v.0 : py.Value = py.bytesLit(\"a\\u00ff\")")

/-- info: fault: Strata.Dyn.Exec.Fault.gap "not modelled yet: py.add" -/
#guard_msgs in
#eval run (main "      %i.0 : py.Value = py.intLit(1)
      %v.0 : py.Value = py.add(%i.0, %i.0) ^err.0()")

end StrataPython.Dyn.Sem.RunTest
