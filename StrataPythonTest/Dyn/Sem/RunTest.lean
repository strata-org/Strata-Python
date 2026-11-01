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
dict, the checks, `is`, dict displays, operators, containers, and the gaps.  The expected outputs
are CPython 3.12's, except where the model stops with a gap.
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
        | some { cls, payload := .func f, .. } =>
          IO.println s!"{showV cls} {f.name} of {showV f.module}"
        | some { payload := .list xs n, .. } =>
          IO.println s!"list [{", ".intercalate (xs.toList.map showV)}], resizes {n}"
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
      %v.0 : py.Value = py.requireDefined(%i.0, \"x\", \"UnboundLocalError\", \"x {}\") ^err.0()")

/-- info: exception UnboundLocalError('x {}',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %u.0 : py.Value = py.undef(\"x\")
      %v.0 : py.Value = py.requireDefined(%u.0, \"x\", \"UnboundLocalError\", \"x {}\") ^err.0()")

-- A `NameError` from `requireDefined` carries the variable's name, as CPython's does for a free
-- variable; an `UnboundLocalError` (above) and a `RuntimeError` carry none.
/-- info: exception NameError("cannot access free variable 'w'",), context None, traceback <traceback>, fields [(name, 'w')] -/
#guard_msgs in
#eval run (main "      %u.0 : py.Value = py.undef(\"w\")
      %v.0 : py.Value = py.requireDefined(%u.0, \"w\", \"NameError\", \"cannot access free variable 'w'\") ^err.0()")

/-- info: exception RuntimeError('super(): empty __class__ cell',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %u.0 : py.Value = py.undef(\"__class__\")
      %v.0 : py.Value = py.requireDefined(%u.0, \"__class__\", \"RuntimeError\", \"super(): empty __class__ cell\") ^err.0()")

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

-- An int key and an equal float key are one key: `{1: 1, 1.0: 1}` is `{1: 1}`.
/-- info: dict [1: 1] -/
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

/-- info: fault: Strata.Dyn.Exec.Fault.gap "not modelled yet: py.attr" -/
#guard_msgs in
#eval run (main "      %i.0 : py.Value = py.intLit(1)
      %v.0 : py.Value = py.attr(%i.0, \"x\") ^err.0()")


-- Operators on built-in values, against CPython 3.12.
/-- info: -4 -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(-7)
      %b.0 : py.Value = py.intLit(2)
      %v.0 : py.Value = py.floorDiv(%a.0, %b.0) ^err.0()")

/-- info: -2 -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(7)
      %b.0 : py.Value = py.intLit(-3)
      %v.0 : py.Value = py.mod(%a.0, %b.0) ^err.0()")

/-- info: 0.5 -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(2)
      %b.0 : py.Value = py.intLit(-1)
      %v.0 : py.Value = py.pow(%a.0, %b.0) ^err.0()")

/-- info: exception ZeroDivisionError('division by zero',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(0)
      %v.0 : py.Value = py.div(%a.0, %b.0) ^err.0()")

/-- info: exception ValueError('negative shift count',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(-1)
      %v.0 : py.Value = py.lShift(%a.0, %b.0) ^err.0()")

/-- info: 2 -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.boolLit(true)
      %b.0 : py.Value = py.boolLit(true)
      %v.0 : py.Value = py.add(%a.0, %b.0) ^err.0()")

/-- info: 2.5 -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.floatLit(1.5)
      %b.0 : py.Value = py.intLit(1)
      %v.0 : py.Value = py.add(%a.0, %b.0) ^err.0()")

/-- info: 'abc' -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.strLit(\"ab\")
      %b.0 : py.Value = py.strLit(\"c\")
      %v.0 : py.Value = py.add(%a.0, %b.0) ^err.0()")

/-- info: 'abab' -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.strLit(\"ab\")
      %b.0 : py.Value = py.intLit(2)
      %v.0 : py.Value = py.mult(%a.0, %b.0) ^err.0()")

/-- info: exception TypeError("unsupported operand type(s) for +: 'int' and 'str'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.strLit(\"a\")
      %v.0 : py.Value = py.add(%a.0, %b.0) ^err.0()")

/-- info: exception TypeError("unsupported operand type(s) for <<: 'float' and 'int'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.floatLit(1.5)
      %b.0 : py.Value = py.intLit(1)
      %v.0 : py.Value = py.lShift(%a.0, %b.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.floatLit(2.5)
      %v.0 : py.Value = py.lt(%a.0, %b.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.strLit(\"a\")
      %b.0 : py.Value = py.strLit(\"b\")
      %v.0 : py.Value = py.lt(%a.0, %b.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.noneLit
      %b.0 : py.Value = py.noneLit
      %v.0 : py.Value = py.eq(%a.0, %b.0) ^err.0()")

/-- info: False -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.strLit(\"1\")
      %v.0 : py.Value = py.eq(%a.0, %b.0) ^err.0()")

/-- info: exception TypeError("'<' not supported between instances of 'int' and 'str'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.strLit(\"a\")
      %v.0 : py.Value = py.lt(%a.0, %b.0) ^err.0()")

/-- info: exception TypeError("'<' not supported between instances of 'NoneType' and 'NoneType'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.noneLit
      %b.0 : py.Value = py.noneLit
      %v.0 : py.Value = py.lt(%a.0, %b.0) ^err.0()")

/-- info: 1.4142135623730951 -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(2)
      %b.0 : py.Value = py.floatLit(0.5)
      %v.0 : py.Value = py.pow(%a.0, %b.0) ^err.0()")

/-- info: exception TypeError("bad operand type for unary -: 'str'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.strLit(\"a\")
      %v.0 : py.Value = py.uSub(%a.0) ^err.0()")

/-- info: exception TypeError("bad operand type for unary ~: 'float'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.floatLit(1.5)
      %v.0 : py.Value = py.invert(%a.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.strLit(\"\")
      %v.0 : py.Value = py.not(%a.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.floatLit(0.0)
      %v.0 : py.Value = py.not(%a.0) ^err.0()")

-- The truth of `NotImplemented` warns in CPython, and the warning records itself in the module's
-- `__warningregistry__`: a gap.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "the truth of NotImplemented, which warns, is not modelled yet" -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.loadGlobal(\"m\", \"NotImplemented\") ^err.0()
      %v.0 : py.Value = py.not(%a.0) ^err.0()")

/-- info: False -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(3)
      %v.0 : py.Value = py.not(%a.0) ^err.0()")

-- Tuples compare member by member, the first unequal members deciding.
/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(2)
      %c.0 : py.Value = py.intLit(3)
      %x.0 : py.Value = py.mkTuple(%a.0, %b.0)
      %y.0 : py.Value = py.mkTuple(%a.0, %c.0)
      %v.0 : py.Value = py.lt(%x.0, %y.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(2)
      %x.0 : py.Value = py.mkTuple(%a.0)
      %y.0 : py.Value = py.mkTuple(%a.0, %b.0)
      %v.0 : py.Value = py.lt(%x.0, %y.0) ^err.0()")

/-- info: (1, 1, 1) -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %n.0 : py.Value = py.intLit(3)
      %x.0 : py.Value = py.mkTuple(%a.0)
      %v.0 : py.Value = py.mult(%n.0, %x.0) ^err.0()")

-- Containers on built-in values: item access and slices.
/-- info: (1, 2) -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %s.0 : py.Value = py.getSlice(%l.0, %n1.0, %n3.0, %none.0) ^err.0()
      %v.0 : py.Value = py.listToTuple(%s.0)")

/-- info: 'olh' -/
#guard_msgs in
#eval run (main "      %s.0 : py.Value = py.strLit(\"hello\")
      %none.0 : py.Value = py.noneLit()
      %m.0 : py.Value = py.intLit(-2)
      %v.0 : py.Value = py.getSlice(%s.0, %none.0, %none.0, %m.0) ^err.0()")

/-- info: 2 -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(2)
      %t.0 : py.Value = py.boolLit(true)
      %l.0 : py.Value = py.mkList(%a.0, %b.0)
      %v.0 : py.Value = py.getItem(%l.0, %t.0) ^err.0()")

/-- info: exception TypeError('tuple indices must be integers or slices, not str',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %k.0 : py.Value = py.strLit(\"a\")
      %t.0 : py.Value = py.mkTuple(%a.0, %a.0)
      %v.0 : py.Value = py.getItem(%t.0, %k.0) ^err.0()")

/-- info: exception IndexError("cannot fit 'int' into an index-sized integer",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %k.0 : py.Value = py.intLit(18446744073709551616)
      %l.0 : py.Value = py.mkList(%a.0)
      %v.0 : py.Value = py.getItem(%l.0, %k.0) ^err.0()")

/-- info: exception IndexError('string index out of range',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %s.0 : py.Value = py.strLit(\"ab\")
      %k.0 : py.Value = py.intLit(-3)
      %v.0 : py.Value = py.getItem(%s.0, %k.0) ^err.0()")

/-- info: exception TypeError("'NoneType' object is not subscriptable",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.noneLit()
      %v.0 : py.Value = py.getItem(%a.0, %a.0) ^err.0()")

/-- info: exception ValueError('slice step cannot be zero',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %v.0 : py.Value = py.getSlice(%l.0, %none.0, %none.0, %n0.0) ^err.0()")

-- A zero step raises before the start and the stop are converted: `[1][None:'a':0]`.
/-- info: exception ValueError('slice step cannot be zero',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %l.0 : py.Value = py.mkList(%n1.0)
      %none.0 : py.Value = py.noneLit()
      %a.0 : py.Value = py.strLit(\"a\")
      %v.0 : py.Value = py.getSlice(%l.0, %none.0, %a.0, %n0.0) ^err.0()")

-- Writes to a list. A write that changes the length moves `resizes`.
/-- info: list [0, 1, 2, 9, 3, 4], resizes 1 -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %x.0 : py.Value = py.intLit(9)
      %y.0 : py.Value = py.mkList(%x.0)
      %k.0 : py.Value = py.mkSlice(%n3.0, %n1.0, %none.0)
      %u.0 : base.Unit = py.setItem(%l.0, %k.0, %y.0) ^err.0()
      %v.0 : py.Value = py.iMult(%l.0, %n1.0) ^err.0()")

/-- info: (0, 7, 2, 7, 4) -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %x.0 : py.Value = py.intLit(7)
      %y.0 : py.Value = py.mkTuple(%x.0, %x.0)
      %k.0 : py.Value = py.mkSlice(%n1.0, %none.0, %n2.0)
      %u.0 : base.Unit = py.setItem(%l.0, %k.0, %y.0) ^err.0()
      %v.0 : py.Value = py.listToTuple(%l.0)")

/-- info: exception ValueError('attempt to assign sequence of size 2 to extended slice of size 3',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %y.0 : py.Value = py.mkTuple(%n0.0, %n0.0)
      %k.0 : py.Value = py.mkSlice(%none.0, %none.0, %n2.0)
      %u.0 : base.Unit = py.setItem(%l.0, %k.0, %y.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: exception TypeError('must assign iterable to extended slice',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %k.0 : py.Value = py.mkSlice(%n1.0, %n2.0, %none.0)
      %u.0 : base.Unit = py.setItem(%l.0, %k.0, %n1.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: (1, 3) -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %m.0 : py.Value = py.intLit(-2)
      %k.0 : py.Value = py.mkSlice(%none.0, %none.0, %m.0)
      %u.0 : base.Unit = py.delItem(%l.0, %k.0) ^err.0()
      %v.0 : py.Value = py.listToTuple(%l.0)")

/-- info: exception IndexError('list assignment index out of range',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %k.0 : py.Value = py.intLit(5)
      %u.0 : base.Unit = py.setItem(%l.0, %k.0, %n1.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: exception TypeError('list indices must be integers or slices, not str',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %k.0 : py.Value = py.strLit(\"x\")
      %u.0 : base.Unit = py.delItem(%l.0, %k.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: exception TypeError("'tuple' object doesn't support item deletion",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %t.0 : py.Value = py.mkTuple(%a.0)
      %u.0 : base.Unit = py.delItem(%t.0, %a.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: exception TypeError("'int' object does not support item deletion",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %u.0 : base.Unit = py.delItem(%a.0, %a.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: exception TypeError("'str' object does not support item assignment",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %s.0 : py.Value = py.strLit(\"a\")
      %u.0 : base.Unit = py.setItem(%s.0, %a.0, %a.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

-- `+=` and `*=` change a list in place and give it back.
/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %l.0 : py.Value = py.mkList(%a.0)
      %t.0 : py.Value = py.strLit(\"xy\")
      %r.0 : py.Value = py.iAdd(%l.0, %t.0) ^err.0()
      %v.0 : py.Value = py.is(%r.0, %l.0)")

/-- info: list [0, 'x', 'y'], resizes 1 -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %l.0 : py.Value = py.mkList(%a.0)
      %t.0 : py.Value = py.strLit(\"xy\")
      %v.0 : py.Value = py.iAdd(%l.0, %t.0) ^err.0()")

/-- info: (0, 1, 0, 1) -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %b.0 : py.Value = py.intLit(1)
      %n.0 : py.Value = py.intLit(2)
      %l.0 : py.Value = py.mkList(%a.0, %b.0)
      %r.0 : py.Value = py.iMult(%l.0, %n.0) ^err.0()
      %v.0 : py.Value = py.listToTuple(%l.0)")

/-- info: exception TypeError("'int' object is not iterable",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %l.0 : py.Value = py.mkList(%a.0)
      %v.0 : py.Value = py.iAdd(%l.0, %a.0) ^err.0()")

/-- info: exception TypeError("unsupported operand type(s) for -=: 'int' and 'str'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %s.0 : py.Value = py.strLit(\"x\")
      %v.0 : py.Value = py.iSub(%a.0, %s.0) ^err.0()")

/-- info: exception TypeError("unsupported operand type(s) for **=: 'int' and 'str'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %s.0 : py.Value = py.strLit(\"x\")
      %v.0 : py.Value = py.iPow(%a.0, %s.0) ^err.0()")

-- Operators on lists, and the messages of `+` and `*` on sequences.
/-- info: list [1, 2, 1, 2], resizes 0 -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(2)
      %l.0 : py.Value = py.mkList(%a.0, %b.0)
      %v.0 : py.Value = py.mult(%l.0, %b.0) ^err.0()")

/-- info: exception TypeError("unsupported operand type(s) for -: 'list' and 'list'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %l.0 : py.Value = py.mkList(%a.0)
      %v.0 : py.Value = py.sub(%l.0, %l.0) ^err.0()")

/-- info: exception TypeError('can only concatenate list (not "tuple") to list',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %l.0 : py.Value = py.mkList(%a.0)
      %t.0 : py.Value = py.mkTuple(%a.0)
      %v.0 : py.Value = py.add(%l.0, %t.0) ^err.0()")

/-- info: exception TypeError('can only concatenate str (not "int") to str',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %s.0 : py.Value = py.strLit(\"a\")
      %v.0 : py.Value = py.add(%s.0, %a.0) ^err.0()")

/-- info: exception TypeError("can't concat str to bytes",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %b.0 : py.Value = py.bytesLit(\"a\")
      %s.0 : py.Value = py.strLit(\"a\")
      %v.0 : py.Value = py.add(%b.0, %s.0) ^err.0()")

/-- info: exception TypeError("can't multiply sequence by non-int of type 'float'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %f.0 : py.Value = py.floatLit(1.5)
      %s.0 : py.Value = py.strLit(\"a\")
      %v.0 : py.Value = py.mult(%f.0, %s.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(2)
      %c.0 : py.Value = py.intLit(3)
      %x.0 : py.Value = py.mkList(%a.0, %b.0)
      %y.0 : py.Value = py.mkList(%a.0, %c.0)
      %v.0 : py.Value = py.lt(%x.0, %y.0) ^err.0()")

/-- info: False -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %x.0 : py.Value = py.mkList(%a.0)
      %y.0 : py.Value = py.mkTuple(%a.0)
      %v.0 : py.Value = py.eq(%x.0, %y.0) ^err.0()")

/-- info: exception TypeError("'<' not supported between instances of 'list' and 'tuple'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %x.0 : py.Value = py.mkList(%a.0)
      %y.0 : py.Value = py.mkTuple(%a.0)
      %v.0 : py.Value = py.lt(%x.0, %y.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %l.0 : py.Value = py.mkList()
      %v.0 : py.Value = py.not(%l.0) ^err.0()")

-- Two dicts compare entry by entry.
/-- info: True -/
#guard_msgs in
#eval run (main "      %d.0 : py.Value = py.mkDict() ^err.0()
      %v.0 : py.Value = py.eq(%d.0, %d.0) ^err.0()")

-- Membership.
/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(2)
      %l.0 : py.Value = py.mkList(%a.0, %b.0)
      %v.0 : py.Value = py.in(%b.0, %l.0) ^err.0()")

/-- info: False -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.strLit(\"bc\")
      %b.0 : py.Value = py.strLit(\"abc\")
      %v.0 : py.Value = py.notIn(%a.0, %b.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %t.0 : py.Value = py.boolLit(true)
      %b.0 : py.Value = py.bytesLit(\"\\u0001\")
      %v.0 : py.Value = py.in(%t.0, %b.0) ^err.0()")

/-- info: exception TypeError("'in <string>' requires string as left operand, not int",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %s.0 : py.Value = py.strLit(\"a\")
      %v.0 : py.Value = py.in(%a.0, %s.0) ^err.0()")

/-- info: exception TypeError("argument of type 'int' is not iterable",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %v.0 : py.Value = py.in(%a.0, %a.0) ^err.0()")

-- Unpacking.
/-- info: exception ValueError('not enough values to unpack (expected 2, got 1)',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %l.0 : py.Value = py.mkList(%a.0)
      %v.0 : py.Value = py.unpackSeq(%l.0, 2) ^err.0()")

/-- info: exception ValueError('too many values to unpack (expected 2)',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %s.0 : py.Value = py.strLit(\"abc\")
      %v.0 : py.Value = py.unpackSeq(%s.0, 2) ^err.0()")

/-- info: exception TypeError('cannot unpack non-iterable int object',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %v.0 : py.Value = py.unpackSeq(%a.0, 2) ^err.0()")

/-- info: exception ValueError('not enough values to unpack (expected at least 2, got 1)',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %l.0 : py.Value = py.mkList(%a.0)
      %v.0 : py.Value = py.unpackEx(%l.0, 1, 1) ^err.0()")

/-- info: (2, 3) -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %u.0 : py.Value = py.unpackEx(%l.0, 2, 1) ^err.0()
      %m.0 : py.Value = py.tupleGet(%u.0, 2)
      %v.0 : py.Value = py.listToTuple(%m.0)")

/-- info: 4 -/
#guard_msgs in
#eval run (main "      %n0.0 : py.Value = py.intLit(0)
      %n1.0 : py.Value = py.intLit(1)
      %n2.0 : py.Value = py.intLit(2)
      %n3.0 : py.Value = py.intLit(3)
      %n4.0 : py.Value = py.intLit(4)
      %l.0 : py.Value = py.mkList(%n0.0, %n1.0, %n2.0, %n3.0, %n4.0)
      %none.0 : py.Value = py.noneLit()
      %u.0 : py.Value = py.unpackEx(%l.0, 2, 1) ^err.0()
      %v.0 : py.Value = py.tupleGet(%u.0, 3)")

-- `*x` in a list display.
/-- info: list [1, 'x', 'y'], resizes 1 -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %s.0 : py.Value = py.strLit(\"xy\")
      %v.0 : py.Value = py.mkList(%a.0)
      %u.0 : base.Unit = py.listExtend(%v.0, %s.0) ^err.0()")

-- The truth and the hash of an undefined value stop with plain gaps, not model invariants: a
-- consumer that checks a contract's requires one at a time may reach them.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "the truth of an undefined value" -/
#guard_msgs in
#eval run (main "      %u.0 : py.Value = py.undef(\"x\")
      %v.0 : py.Value = py.not(%u.0) ^err.0()")

/-- info: fault: Strata.Dyn.Exec.Fault.gap "the hash of an undefined value" -/
#guard_msgs in
#eval run (main "      %u.0 : py.Value = py.undef(\"x\")
      %v.0 : py.Value = py.mkSet(%u.0) ^err.0()")

-- A set display of constants is `py.constSet`, whose layout the semantics doesn't assume: iterating
-- it stops with a gap, while `in` and `==` give CPython's results.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "iterating a set whose order is not CPython's" -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(7)
      %b.0 : py.Value = py.intLit(15)
      %s.0 : py.Value = py.constSet(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.mkList()
      %w.0 : base.Unit = py.listExtend(%v.0, %s.0) ^err.0()")

/-- info: (True, True) -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(7)
      %b.0 : py.Value = py.intLit(15)
      %s.0 : py.Value = py.constSet(%a.0, %b.0) ^err.0()
      %t.0 : py.Value = py.mkSet(%b.0, %a.0) ^err.0()
      %q.0 : py.Value = py.eq(%s.0, %t.0) ^err.0()
      %i.0 : py.Value = py.in(%a.0, %s.0) ^err.0()
      %v.0 : py.Value = py.mkTuple(%q.0, %i.0)")

/-- info: exception TypeError('Value after * must be an iterable, not int',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %l.0 : py.Value = py.mkList(%a.0)
      %u.0 : base.Unit = py.listExtend(%l.0, %a.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: list [1, 2], resizes 1 -/
#guard_msgs in
#eval run (mainTotal "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(2)
      %v.0 : py.Value = py.mkList(%a.0)
      %u.0 : base.Unit = py.listAppend(%v.0, %b.0)")


-- Dicts.
/-- info: 'a' -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %v.0 : py.Value = py.getItem(%d.0, %k1.0) ^err.0()")

/-- info: exception KeyError(2,), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %k.0 : py.Value = py.intLit(2)
      %v.0 : py.Value = py.getItem(%d.0, %k.0) ^err.0()")

/-- info: 'a' -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %k.0 : py.Value = py.floatLit(1.0)
      %v.0 : py.Value = py.getItem(%d.0, %k.0) ^err.0()")

/-- info: exception TypeError("unhashable type: 'list'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %l.0 : py.Value = py.mkList()
      %v.0 : py.Value = py.getItem(%d.0, %l.0) ^err.0()")

/-- info: exception TypeError("unhashable type: 'list'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %l.0 : py.Value = py.mkList()
      %t.0 : py.Value = py.mkTuple(%k1.0, %l.0)
      %v.0 : py.Value = py.in(%t.0, %d.0) ^err.0()")

/-- info: 'x' -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.intLit(2)
      %x.0 : py.Value = py.strLit(\"x\")
      %t.0 : py.Value = py.mkTuple(%a.0, %b.0)
      %u.0 : py.Value = py.mkTuple(%a.0, %b.0)
      %d.0 : py.Value = py.mkDict(%t.0, %x.0) ^err.0()
      %v.0 : py.Value = py.getItem(%d.0, %u.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %t.0 : py.Value = py.boolLit(true)
      %v.0 : py.Value = py.in(%t.0, %d.0) ^err.0()")

/-- info: dict [1: 'b', 3: 'b', 'a': 1] -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %u.0 : base.Unit = py.setItem(%d.0, %k1.0, %sb.0) ^err.0()
      %w.0 : base.Unit = py.dictSet(%d.0, %sa.0, %k1.0) ^err.0()
      %v.0 : py.Value = py.iBitOr(%d.0, %d.0) ^err.0()")

/-- info: dict [3: 'b'] -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %u.0 : base.Unit = py.delItem(%d.0, %k1.0) ^err.0()
      %v.0 : py.Value = py.iBitOr(%d.0, %d.0) ^err.0()")

/-- info: exception KeyError(2,), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %k.0 : py.Value = py.intLit(2)
      %u.0 : base.Unit = py.delItem(%d.0, %k.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %f.0 : py.Value = py.mkDict(%k3.0, %sb.0, %k1.0, %sa.0) ^err.0()
      %v.0 : py.Value = py.eq(%d.0, %f.0) ^err.0()")

/-- info: False -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %f.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sa.0) ^err.0()
      %v.0 : py.Value = py.eq(%d.0, %f.0) ^err.0()")

/-- info: exception TypeError("'<' not supported between instances of 'dict' and 'dict'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %v.0 : py.Value = py.lt(%d.0, %d.0) ^err.0()")

/-- info: exception TypeError("unsupported operand type(s) for +: 'dict' and 'dict'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %v.0 : py.Value = py.add(%d.0, %d.0) ^err.0()")

/-- info: dict [1: 'a', 3: 'a', 2: 'b'] -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %k2.0 : py.Value = py.intLit(2)
      %f.0 : py.Value = py.mkDict(%k3.0, %sa.0, %k2.0, %sb.0) ^err.0()
      %v.0 : py.Value = py.bitOr(%d.0, %f.0) ^err.0()")

/-- info: False -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %k2.0 : py.Value = py.intLit(2)
      %f.0 : py.Value = py.mkDict(%k2.0, %sb.0) ^err.0()
      %o.0 : py.Value = py.bitOr(%d.0, %f.0) ^err.0()
      %v.0 : py.Value = py.is(%o.0, %d.0)")

/-- info: (1, 3) -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%d.0, 2) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %d.0 : py.Value = py.mkDict() ^err.0()
      %v.0 : py.Value = py.not(%d.0) ^err.0()")

/-- info: None -/
#guard_msgs in
#eval run (main "      %d.0 : py.Value = py.mkDict() ^err.0()
      %k.0 : py.Value = py.strLit(\"x\")
      %n.0 : py.Value = py.noneLit()
      %v.0 : py.Value = py.getOptionalItem(%d.0, %k.0, %n.0) ^err.0()")

/-- info: 'a' -/
#guard_msgs in
#eval run (main "      %k1.0 : py.Value = py.intLit(1)
      %k3.0 : py.Value = py.intLit(3)
      %sa.0 : py.Value = py.strLit(\"a\")
      %sb.0 : py.Value = py.strLit(\"b\")
      %d.0 : py.Value = py.mkDict(%k1.0, %sa.0, %k3.0, %sb.0) ^err.0()
      %n.0 : py.Value = py.noneLit()
      %v.0 : py.Value = py.getOptionalItem(%d.0, %k1.0, %n.0) ^err.0()")

/-- info: (0, 1, 1, 2, 2) -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %b.0 : py.Value = py.intLit(1)
      %c.0 : py.Value = py.intLit(2)
      %n.0 : py.Value = py.noneLit()
      %l.0 : py.Value = py.mkList(%a.0, %b.0, %c.0)
      %d.0 : py.Value = py.mkDict(%b.0, %a.0, %c.0, %a.0) ^err.0()
      %u.0 : base.Unit = py.setItem(%l.0, %c.0, %c.0) ^err.0()
      %k.0 : py.Value = py.mkSlice(%c.0, %c.0, %n.0)
      %w.0 : base.Unit = py.setItem(%l.0, %k.0, %d.0) ^err.0()
      %v.0 : py.Value = py.listToTuple(%l.0)")


-- Sets: a display adds its elements in order, and the table is CPython's.
/-- info: (1, 33, 2, 9, 17, 25) -/
#guard_msgs in
#eval run (main "      %i1.0 : py.Value = py.intLit(1)
      %i2.0 : py.Value = py.intLit(9)
      %i3.0 : py.Value = py.intLit(17)
      %i4.0 : py.Value = py.intLit(25)
      %i5.0 : py.Value = py.intLit(33)
      %i6.0 : py.Value = py.intLit(2)
      %s.0 : py.Value = py.mkSet(%i1.0, %i2.0, %i3.0, %i4.0, %i5.0, %i6.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 6) ^err.0()")

/-- info: (17, 9, 1) -/
#guard_msgs in
#eval run (main "      %i7.0 : py.Value = py.intLit(17)
      %i8.0 : py.Value = py.intLit(9)
      %i9.0 : py.Value = py.intLit(1)
      %s.0 : py.Value = py.mkSet(%i7.0, %i8.0, %i9.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 3) ^err.0()")

/-- info: (2, 3) -/
#guard_msgs in
#eval run (main "      %i10.0 : py.Value = py.intLit(1)
      %i11.0 : py.Value = py.intLit(2)
      %i12.0 : py.Value = py.intLit(3)
      %a.0 : py.Value = py.mkSet(%i10.0, %i11.0, %i12.0) ^err.0()
      %i13.0 : py.Value = py.intLit(3)
      %i14.0 : py.Value = py.intLit(2)
      %i15.0 : py.Value = py.intLit(9)
      %b.0 : py.Value = py.mkSet(%i13.0, %i14.0, %i15.0) ^err.0()
      %s.0 : py.Value = py.bitAnd(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 2) ^err.0()")

-- `s & s` is a copy of `s`, whose table order differs from a walk's.
/-- info: (1, 33, 2, 17, 9, 25) -/
#guard_msgs in
#eval run (main "      %i16.0 : py.Value = py.intLit(1)
      %i17.0 : py.Value = py.intLit(9)
      %i18.0 : py.Value = py.intLit(17)
      %i19.0 : py.Value = py.intLit(25)
      %i20.0 : py.Value = py.intLit(33)
      %i21.0 : py.Value = py.intLit(2)
      %a.0 : py.Value = py.mkSet(%i16.0, %i17.0, %i18.0, %i19.0, %i20.0, %i21.0) ^err.0()
      %s.0 : py.Value = py.bitAnd(%a.0, %a.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 6) ^err.0()")

/-- info: (1, 2, 33, 9, 17, 25) -/
#guard_msgs in
#eval run (main "      %i22.0 : py.Value = py.intLit(1)
      %i23.0 : py.Value = py.intLit(9)
      %i24.0 : py.Value = py.intLit(17)
      %i25.0 : py.Value = py.intLit(25)
      %i26.0 : py.Value = py.intLit(33)
      %i27.0 : py.Value = py.intLit(2)
      %a.0 : py.Value = py.mkSet(%i22.0, %i23.0, %i24.0, %i25.0, %i26.0, %i27.0) ^err.0()
      %i28.0 : py.Value = py.intLit(1)
      %i29.0 : py.Value = py.intLit(9)
      %i30.0 : py.Value = py.intLit(17)
      %i31.0 : py.Value = py.intLit(25)
      %i32.0 : py.Value = py.intLit(33)
      %i33.0 : py.Value = py.intLit(2)
      %b.0 : py.Value = py.mkSet(%i28.0, %i29.0, %i30.0, %i31.0, %i32.0, %i33.0) ^err.0()
      %s.0 : py.Value = py.bitAnd(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 6) ^err.0()")

/-- info: (1, 2, 3, 17, 9) -/
#guard_msgs in
#eval run (main "      %i34.0 : py.Value = py.intLit(1)
      %i35.0 : py.Value = py.intLit(2)
      %i36.0 : py.Value = py.intLit(3)
      %a.0 : py.Value = py.mkSet(%i34.0, %i35.0, %i36.0) ^err.0()
      %i37.0 : py.Value = py.intLit(9)
      %i38.0 : py.Value = py.intLit(17)
      %b.0 : py.Value = py.mkSet(%i37.0, %i38.0) ^err.0()
      %s.0 : py.Value = py.bitOr(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 5) ^err.0()")

/-- info: (1, 2, 4, 5, 6, 7, 8, 9) -/
#guard_msgs in
#eval run (main "      %i39.0 : py.Value = py.intLit(1)
      %i40.0 : py.Value = py.intLit(2)
      %i41.0 : py.Value = py.intLit(3)
      %i42.0 : py.Value = py.intLit(4)
      %i43.0 : py.Value = py.intLit(5)
      %i44.0 : py.Value = py.intLit(6)
      %i45.0 : py.Value = py.intLit(7)
      %i46.0 : py.Value = py.intLit(8)
      %i47.0 : py.Value = py.intLit(9)
      %a.0 : py.Value = py.mkSet(%i39.0, %i40.0, %i41.0, %i42.0, %i43.0, %i44.0, %i45.0, %i46.0, %i47.0) ^err.0()
      %i48.0 : py.Value = py.intLit(3)
      %b.0 : py.Value = py.mkSet(%i48.0) ^err.0()
      %s.0 : py.Value = py.sub(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 8) ^err.0()")

/-- info: (1, 2) -/
#guard_msgs in
#eval run (main "      %i49.0 : py.Value = py.intLit(1)
      %i50.0 : py.Value = py.intLit(2)
      %i51.0 : py.Value = py.intLit(3)
      %a.0 : py.Value = py.mkSet(%i49.0, %i50.0, %i51.0) ^err.0()
      %i52.0 : py.Value = py.intLit(3)
      %i53.0 : py.Value = py.intLit(4)
      %b.0 : py.Value = py.mkSet(%i52.0, %i53.0) ^err.0()
      %s.0 : py.Value = py.sub(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 2) ^err.0()")

/-- info: (1, 2, 4) -/
#guard_msgs in
#eval run (main "      %i54.0 : py.Value = py.intLit(1)
      %i55.0 : py.Value = py.intLit(2)
      %i56.0 : py.Value = py.intLit(3)
      %a.0 : py.Value = py.mkSet(%i54.0, %i55.0, %i56.0) ^err.0()
      %i57.0 : py.Value = py.intLit(3)
      %i58.0 : py.Value = py.intLit(4)
      %b.0 : py.Value = py.mkSet(%i57.0, %i58.0) ^err.0()
      %s.0 : py.Value = py.bitXor(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 3) ^err.0()")

/-- info: (8, 16, 0, 24) -/
#guard_msgs in
#eval run (main "      %i59.0 : py.Value = py.intLit(8)
      %i60.0 : py.Value = py.intLit(16)
      %i61.0 : py.Value = py.intLit(0)
      %a.0 : py.Value = py.mkSet(%i59.0, %i60.0, %i61.0) ^err.0()
      %i62.0 : py.Value = py.intLit(24)
      %b.0 : py.Value = py.mkSet(%i62.0) ^err.0()
      %s.0 : py.Value = py.bitOr(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 4) ^err.0()")

-- `&=` replaces the set's table in place.
/-- info: (2, 3) -/
#guard_msgs in
#eval run (main "      %i63.0 : py.Value = py.intLit(1)
      %i64.0 : py.Value = py.intLit(2)
      %i65.0 : py.Value = py.intLit(3)
      %a.0 : py.Value = py.mkSet(%i63.0, %i64.0, %i65.0) ^err.0()
      %i66.0 : py.Value = py.intLit(2)
      %i67.0 : py.Value = py.intLit(3)
      %i68.0 : py.Value = py.intLit(4)
      %b.0 : py.Value = py.mkSet(%i66.0, %i67.0, %i68.0) ^err.0()
      %s.0 : py.Value = py.iBitAnd(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%a.0, 2) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %i69.0 : py.Value = py.intLit(1)
      %i70.0 : py.Value = py.intLit(2)
      %i71.0 : py.Value = py.intLit(3)
      %a.0 : py.Value = py.mkSet(%i69.0, %i70.0, %i71.0) ^err.0()
      %i72.0 : py.Value = py.intLit(2)
      %i73.0 : py.Value = py.intLit(3)
      %i74.0 : py.Value = py.intLit(4)
      %b.0 : py.Value = py.mkSet(%i72.0, %i73.0, %i74.0) ^err.0()
      %s.0 : py.Value = py.iBitAnd(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.is(%s.0, %a.0)")

/-- info: (1, 9, 17) -/
#guard_msgs in
#eval run (main "      %i75.0 : py.Value = py.intLit(1)
      %a.0 : py.Value = py.mkSet(%i75.0) ^err.0()
      %i76.0 : py.Value = py.intLit(9)
      %i77.0 : py.Value = py.intLit(17)
      %b.0 : py.Value = py.mkSet(%i76.0, %i77.0) ^err.0()
      %s.0 : py.Value = py.iBitOr(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%a.0, 3) ^err.0()")

/-- info: (1, 3) -/
#guard_msgs in
#eval run (main "      %i78.0 : py.Value = py.intLit(1)
      %i79.0 : py.Value = py.intLit(2)
      %i80.0 : py.Value = py.intLit(3)
      %a.0 : py.Value = py.mkSet(%i78.0, %i79.0, %i80.0) ^err.0()
      %i81.0 : py.Value = py.intLit(2)
      %b.0 : py.Value = py.mkSet(%i81.0) ^err.0()
      %s.0 : py.Value = py.iSub(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%a.0, 2) ^err.0()")

/-- info: (1, 3) -/
#guard_msgs in
#eval run (main "      %i82.0 : py.Value = py.intLit(1)
      %i83.0 : py.Value = py.intLit(2)
      %a.0 : py.Value = py.mkSet(%i82.0, %i83.0) ^err.0()
      %i84.0 : py.Value = py.intLit(2)
      %i85.0 : py.Value = py.intLit(3)
      %b.0 : py.Value = py.mkSet(%i84.0, %i85.0) ^err.0()
      %s.0 : py.Value = py.iBitXor(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%a.0, 2) ^err.0()")

/-- info: () -/
#guard_msgs in
#eval run (main "      %i86.0 : py.Value = py.intLit(1)
      %i87.0 : py.Value = py.intLit(2)
      %a.0 : py.Value = py.mkSet(%i86.0, %i87.0) ^err.0()
      %s.0 : py.Value = py.iSub(%a.0, %a.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%a.0, 0) ^err.0()")

/-- info: (1, 2, 3) -/
#guard_msgs in
#eval run (main "      %i90.0 : py.Value = py.intLit(1)
      %a.0 : py.Value = py.mkSet(%i90.0) ^err.0()
      %i88.0 : py.Value = py.intLit(3)
      %i89.0 : py.Value = py.intLit(2)
      %t.0 : py.Value = py.mkTuple(%i88.0, %i89.0)
      %u.0 : base.Unit = py.setUpdate(%a.0, %t.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%a.0, 3) ^err.0()")

-- Equal numbers are one member: the first one stays.
/-- info: (1.0,) -/
#guard_msgs in
#eval run (main "      %f.0 : py.Value = py.floatLit(1.0)
      %o.0 : py.Value = py.intLit(1)
      %s.0 : py.Value = py.mkSet(%f.0, %o.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 1) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %i91.0 : py.Value = py.intLit(1)
      %i92.0 : py.Value = py.intLit(2)
      %a.0 : py.Value = py.mkSet(%i91.0, %i92.0) ^err.0()
      %i93.0 : py.Value = py.intLit(1)
      %i94.0 : py.Value = py.intLit(2)
      %i95.0 : py.Value = py.intLit(3)
      %b.0 : py.Value = py.mkSet(%i93.0, %i94.0, %i95.0) ^err.0()
      %v.0 : py.Value = py.lt(%a.0, %b.0) ^err.0()")

/-- info: False -/
#guard_msgs in
#eval run (main "      %i96.0 : py.Value = py.intLit(1)
      %i97.0 : py.Value = py.intLit(2)
      %a.0 : py.Value = py.mkSet(%i96.0, %i97.0) ^err.0()
      %i98.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.mkSet(%i98.0) ^err.0()
      %v.0 : py.Value = py.ltE(%a.0, %b.0) ^err.0()")

/-- info: False -/
#guard_msgs in
#eval run (main "      %i99.0 : py.Value = py.intLit(1)
      %a.0 : py.Value = py.mkSet(%i99.0) ^err.0()
      %v.0 : py.Value = py.gt(%a.0, %a.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %i100.0 : py.Value = py.intLit(1)
      %i101.0 : py.Value = py.intLit(2)
      %a.0 : py.Value = py.mkSet(%i100.0, %i101.0) ^err.0()
      %i102.0 : py.Value = py.intLit(2)
      %i103.0 : py.Value = py.intLit(1)
      %b.0 : py.Value = py.mkSet(%i102.0, %i103.0) ^err.0()
      %v.0 : py.Value = py.eq(%a.0, %b.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %i104.0 : py.Value = py.intLit(1)
      %i105.0 : py.Value = py.intLit(2)
      %a.0 : py.Value = py.mkSet(%i104.0, %i105.0) ^err.0()
      %k.0 : py.Value = py.intLit(2)
      %v.0 : py.Value = py.in(%k.0, %a.0) ^err.0()")

-- A set of strs has an order that depends on the hash seed: `in` works, iterating gaps.
/-- info: True -/
#guard_msgs in
#eval run (main "      %x.0 : py.Value = py.strLit(\"a\")
      %y.0 : py.Value = py.strLit(\"b\")
      %a.0 : py.Value = py.mkSet(%x.0, %y.0) ^err.0()
      %v.0 : py.Value = py.in(%x.0, %a.0) ^err.0()")

/-- info: fault: Strata.Dyn.Exec.Fault.gap "iterating a set whose order is not CPython's" -/
#guard_msgs in
#eval run (main "      %x.0 : py.Value = py.strLit(\"a\")
      %y.0 : py.Value = py.strLit(\"b\")
      %a.0 : py.Value = py.mkSet(%x.0, %y.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%a.0, 2) ^err.0()")

/-- info: exception TypeError("unhashable type: 'list'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %l.0 : py.Value = py.mkList()
      %v.0 : py.Value = py.mkSet(%l.0) ^err.0()")

/-- info: exception TypeError("unsupported operand type(s) for +: 'set' and 'set'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %i106.0 : py.Value = py.intLit(1)
      %a.0 : py.Value = py.mkSet(%i106.0) ^err.0()
      %v.0 : py.Value = py.add(%a.0, %a.0) ^err.0()")

/-- info: exception TypeError("unsupported operand type(s) for |: 'set' and 'list'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %i107.0 : py.Value = py.intLit(1)
      %a.0 : py.Value = py.mkSet(%i107.0) ^err.0()
      %l.0 : py.Value = py.mkList()
      %v.0 : py.Value = py.bitOr(%a.0, %l.0) ^err.0()")

/-- info: True -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.mkSet() ^err.0()
      %v.0 : py.Value = py.not(%a.0) ^err.0()")

-- A set built by walking a set whose order is not CPython's has an inexact order too.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "iterating a set whose order is not CPython's" -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.strLit(\"a\")
      %i101.0 : py.Value = py.intLit(7)
      %i102.0 : py.Value = py.intLit(15)
      %src.0 : py.Value = py.mkSet(%a.0, %i101.0, %i102.0) ^err.0()
      %r.0 : py.Value = py.mkSet(%a.0) ^err.0()
      %u.0 : py.Value = py.iSub(%src.0, %r.0) ^err.0()
      %i103.0 : py.Value = py.intLit(0)
      %t.0 : py.Value = py.mkSet(%i103.0) ^err.0()
      %w.0 : py.Value = py.iBitOr(%t.0, %src.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%t.0, 3) ^err.0()")

/-- info: fault: Strata.Dyn.Exec.Fault.gap "iterating a set whose order is not CPython's" -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.strLit(\"a\")
      %i104.0 : py.Value = py.intLit(7)
      %i105.0 : py.Value = py.intLit(15)
      %src.0 : py.Value = py.mkSet(%a.0, %i104.0, %i105.0) ^err.0()
      %r.0 : py.Value = py.mkSet(%a.0) ^err.0()
      %u.0 : py.Value = py.iSub(%src.0, %r.0) ^err.0()
      %i106.0 : py.Value = py.intLit(0)
      %t.0 : py.Value = py.mkSet(%i106.0) ^err.0()
      %w.0 : py.Value = py.iBitXor(%t.0, %src.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%t.0, 3) ^err.0()")

-- `a | a` is a copy of `a`.
/-- info: (8, 1, 2) -/
#guard_msgs in
#eval run (main "      %i107.0 : py.Value = py.intLit(8)
      %i108.0 : py.Value = py.intLit(1)
      %i109.0 : py.Value = py.intLit(2)
      %a.0 : py.Value = py.mkSet(%i107.0, %i108.0, %i109.0) ^err.0()
      %s.0 : py.Value = py.bitOr(%a.0, %a.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 3) ^err.0()")

-- `-=` resizes the dummies away when they fill more than a quarter of the table.
/-- info: (1, 8) -/
#guard_msgs in
#eval run (main "      %i110.0 : py.Value = py.intLit(8)
      %i111.0 : py.Value = py.intLit(1)
      %i112.0 : py.Value = py.intLit(2)
      %i113.0 : py.Value = py.intLit(3)
      %a.0 : py.Value = py.mkSet(%i110.0, %i111.0, %i112.0, %i113.0) ^err.0()
      %i114.0 : py.Value = py.intLit(2)
      %i115.0 : py.Value = py.intLit(3)
      %b.0 : py.Value = py.mkSet(%i114.0, %i115.0) ^err.0()
      %s.0 : py.Value = py.iSub(%a.0, %b.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%a.0, 2) ^err.0()")

-- A merge into a set that holds only dummies copies the other set's slots.
/-- info: (15, 7) -/
#guard_msgs in
#eval run (main "      %i116.0 : py.Value = py.intLit(1)
      %i117.0 : py.Value = py.intLit(2)
      %i118.0 : py.Value = py.intLit(3)
      %a.0 : py.Value = py.mkSet(%i116.0, %i117.0, %i118.0) ^err.0()
      %i119.0 : py.Value = py.intLit(1)
      %i120.0 : py.Value = py.intLit(2)
      %i121.0 : py.Value = py.intLit(3)
      %b.0 : py.Value = py.mkSet(%i119.0, %i120.0, %i121.0) ^err.0()
      %s.0 : py.Value = py.iBitXor(%a.0, %b.0) ^err.0()
      %i122.0 : py.Value = py.intLit(7)
      %i123.0 : py.Value = py.intLit(15)
      %c.0 : py.Value = py.mkSet(%i122.0, %i123.0) ^err.0()
      %t.0 : py.Value = py.iBitOr(%a.0, %c.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%a.0, 2) ^err.0()")

-- `|` of a class makes a union type, which is not modelled yet.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "`|` of a class, which makes a union type, is not modelled yet" -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %b.0 : py.Value = py.loadGlobal(\"m\", \"str\") ^err.0()
      %v.0 : py.Value = py.bitOr(%a.0, %b.0) ^err.0()")

/-- info: fault: Strata.Dyn.Exec.Fault.gap "`|` of a class, which makes a union type, is not modelled yet" -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.loadGlobal(\"m\", \"int\") ^err.0()
      %b.0 : py.Value = py.noneLit()
      %v.0 : py.Value = py.bitOr(%b.0, %a.0) ^err.0()")

-- A NaN is equal to itself inside a container in CPython; the model doesn't know identity.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "comparing values whose identity is unknown and that are not equal (a NaN)" -/
#guard_msgs in
#eval run (main "      %big.0 : py.Value = py.floatLit(1e308)
      %ten.0 : py.Value = py.floatLit(10.0)
      %inf.0 : py.Value = py.mult(%big.0, %ten.0) ^err.0()
      %x.0 : py.Value = py.sub(%inf.0, %inf.0) ^err.0()
      %l.0 : py.Value = py.mkList(%x.0)
      %m.0 : py.Value = py.mkList(%x.0)
      %v.0 : py.Value = py.eq(%l.0, %m.0) ^err.0()")

/-- info: fault: Strata.Dyn.Exec.Fault.gap "comparing values whose identity is unknown and that are not equal (a NaN)" -/
#guard_msgs in
#eval run (main "      %big.0 : py.Value = py.floatLit(1e308)
      %ten.0 : py.Value = py.floatLit(10.0)
      %inf.0 : py.Value = py.mult(%big.0, %ten.0) ^err.0()
      %x.0 : py.Value = py.sub(%inf.0, %inf.0) ^err.0()
      %l.0 : py.Value = py.mkList(%x.0)
      %v.0 : py.Value = py.in(%x.0, %l.0) ^err.0()")

/-- info: False -/
#guard_msgs in
#eval run (main "      %big.0 : py.Value = py.floatLit(1e308)
      %ten.0 : py.Value = py.floatLit(10.0)
      %inf.0 : py.Value = py.mult(%big.0, %ten.0) ^err.0()
      %x.0 : py.Value = py.sub(%inf.0, %inf.0) ^err.0()
      %o.0 : py.Value = py.intLit(1)
      %l.0 : py.Value = py.mkList(%x.0)
      %m.0 : py.Value = py.mkList(%o.0, %o.0)
      %v.0 : py.Value = py.eq(%l.0, %m.0) ^err.0()")

-- A repetition count beyond a C index raises `OverflowError`; an empty sequence stays empty.
/-- info: exception OverflowError("cannot fit 'int' into an index-sized integer",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %s.0 : py.Value = py.strLit(\"a\")
      %n.0 : py.Value = py.intLit(-1267650600228229401496703205376)
      %v.0 : py.Value = py.mult(%s.0, %n.0) ^err.0()")

/-- info: exception OverflowError("cannot fit 'int' into an index-sized integer",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %s.0 : py.Value = py.strLit(\"\")
      %n.0 : py.Value = py.intLit(1267650600228229401496703205376)
      %v.0 : py.Value = py.mult(%s.0, %n.0) ^err.0()")

/-- info: list [], resizes 0 -/
#guard_msgs in
#eval run (main "      %l.0 : py.Value = py.mkList()
      %n.0 : py.Value = py.intLit(1099511627776)
      %v.0 : py.Value = py.mult(%l.0, %n.0) ^err.0()")

/-- info: list [], resizes 0 -/
#guard_msgs in
#eval run (main "      %v.0 : py.Value = py.mkList()
      %n.0 : py.Value = py.intLit(1099511627776)
      %r.0 : py.Value = py.iMult(%v.0, %n.0) ^err.0()")

-- Item deletion and assignment on a tuple convert an index key first.
/-- info: exception TypeError("'tuple' object does not support item deletion",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %t.0 : py.Value = py.mkTuple(%a.0)
      %k.0 : py.Value = py.strLit(\"a\")
      %u.0 : base.Unit = py.delItem(%t.0, %k.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: exception IndexError("cannot fit 'int' into an index-sized integer",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %t.0 : py.Value = py.mkTuple(%a.0)
      %k.0 : py.Value = py.intLit(1267650600228229401496703205376)
      %u.0 : base.Unit = py.setItem(%t.0, %k.0, %a.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: exception IndexError("cannot fit 'int' into an index-sized integer",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %a.0 : py.Value = py.intLit(0)
      %t.0 : py.Value = py.mkTuple(%a.0)
      %k.0 : py.Value = py.intLit(1267650600228229401496703205376)
      %u.0 : base.Unit = py.delItem(%t.0, %k.0) ^err.0()
      %v.0 : py.Value = py.noneLit()")

/-- info: exception TypeError('byte indices must be integers or slices, not str',), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %b.0 : py.Value = py.bytesLit(\"ab\")
      %k.0 : py.Value = py.strLit(\"x\")
      %v.0 : py.Value = py.getItem(%b.0, %k.0) ^err.0()")

-- An ASCII `str` is indexed by byte; another `str` by code point.
/-- info: 'é' -/
#guard_msgs in
#eval run (main "      %s.0 : py.Value = py.strLit(\"aéb\")
      %k.0 : py.Value = py.intLit(-2)
      %v.0 : py.Value = py.getItem(%s.0, %k.0) ^err.0()")

/-- info: 'c' -/
#guard_msgs in
#eval run (main "      %s.0 : py.Value = py.strLit(\"abc\")
      %k.0 : py.Value = py.intLit(2)
      %v.0 : py.Value = py.getItem(%s.0, %k.0) ^err.0()")

-- Only a sequence converts the count: a huge int times a value that is not one is a `TypeError`.
/-- info: exception TypeError("unsupported operand type(s) for *: 'int' and 'NoneType'",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %n.0 : py.Value = py.intLit(1267650600228229401496703205376)
      %x.0 : py.Value = py.noneLit()
      %v.0 : py.Value = py.mult(%n.0, %x.0) ^err.0()")

/-- info: exception OverflowError("cannot fit 'int' into an index-sized integer",), context None, traceback <traceback>, fields [] -/
#guard_msgs in
#eval run (main "      %n.0 : py.Value = py.intLit(1267650600228229401496703205376)
      %a.0 : py.Value = py.intLit(1)
      %l.0 : py.Value = py.mkList(%a.0)
      %v.0 : py.Value = py.mult(%l.0, %n.0) ^err.0()")

-- `{*d}` resizes the set for the dict's size, then adds its keys in order.
/-- info: (17, 1, 2, 3, 4) -/
#guard_msgs in
#eval run (main "      %n.0 : py.Value = py.noneLit()
      %a.0 : py.Value = py.intLit(17)
      %b.0 : py.Value = py.intLit(1)
      %c.0 : py.Value = py.intLit(2)
      %d.0 : py.Value = py.intLit(3)
      %f.0 : py.Value = py.intLit(4)
      %m.0 : py.Value = py.mkDict(%a.0, %n.0, %b.0, %n.0, %c.0, %n.0, %d.0, %n.0, %f.0, %n.0) ^err.0()
      %s.0 : py.Value = py.mkSet() ^err.0()
      %u.0 : base.Unit = py.setUpdate(%s.0, %m.0) ^err.0()
      %v.0 : py.Value = py.unpackSeq(%s.0, 5) ^err.0()")

-- `mkClosure` makes a function object that holds the closure, its `__name__`, and its `__module__`,
-- the module's `__name__` global: `None` here, where the module has none.
/-- info: function f of None -/
#guard_msgs in
#eval run "module m {
  func @m.f(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%args.0 : py.Value, %kwargs.0 : py.Value):
      %r.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%args.0)
      ret(%r.0)
  }
  func @m.main() -> py.Value {
    entry.0():
      %v.0 : py.Value = py.mkClosure[[]](@m.f, \"f\", \"m\")
      ret(%v.0)
  }
}"

-- A closure over a cell is a function object.  The calls of RuleTheoremsTest check that the cell
-- is bound into the code.
/-- info: function g of None -/
#guard_msgs in
#eval run "module m {
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
      %v.0 : py.Value = py.mkClosure[[base.Ref(py.Value)]](@m.g, \"g\", \"m\", %c.0)
      ret(%v.0)
  }
}"

-- After `__name__ = "renamed"`, a new function's `__module__` is `'renamed'`; after `del __name__`
-- (the cell unassigned), it is `None`, as in CPython.
/-- info: function f of 'renamed' -/
#guard_msgs in
#eval run "module m {
  func @m.f(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%args.0 : py.Value, %kwargs.0 : py.Value):
      %r.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%args.0)
      ret(%r.0)
  }
  func @m.main() -> py.Value {
    entry.0():
      %c.0 : base.Ref(py.Value) = py.globalCell(\"m\", \"__name__\")
      %n.0 : py.Value = py.strLit(\"renamed\")
      %s.0 : base.Unit = base.refSet[py.Value](%c.0, %n.0)
      %v.0 : py.Value = py.mkClosure[[]](@m.f, \"f\", \"m\")
      ret(%v.0)
  }
}"

/-- info: function f of None -/
#guard_msgs in
#eval run "module m {
  func @m.f(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%args.0 : py.Value, %kwargs.0 : py.Value):
      %r.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%args.0)
      ret(%r.0)
  }
  func @m.main() -> py.Value {
    entry.0():
      %c.0 : base.Ref(py.Value) = py.globalCell(\"m\", \"__name__\")
      %u.0 : py.Value = py.undef(\"__name__\")
      %s.0 : base.Unit = base.refSet[py.Value](%c.0, %u.0)
      %v.0 : py.Value = py.mkClosure[[]](@m.f, \"f\", \"m\")
      ret(%v.0)
  }
}"

end StrataPython.Dyn.Sem.RunTest
