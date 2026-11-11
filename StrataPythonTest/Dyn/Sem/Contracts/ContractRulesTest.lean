/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.Table
import StrataDyn.DDMRead
import StrataDyn.Exec.Run
import StrataPython.Dyn.Sem.Run
import StrataPythonTest.Util.DynRun
meta import StrataPython.Dyn.Sem.Table
meta import StrataDyn.DDMRead
meta import StrataDyn.Exec.Run
meta import StrataPython.Dyn.Sem.Run
meta import StrataPythonTest.Util.DynRun

set_option autoImplicit false

/-!
# The rules of the contract operations, on built-in values

Small modules in the IR's text, run with `PySem`.  Each applies a contract operation to values
that the module builds, and prints its result, the exception it raises, or its gap.  The
expected outputs follow the operations' docstrings, which differ from the Python an operation
stands for where they say so (e.g. `typeIsSubclass` rejects a tuple that holds a non-class even
when an earlier class matches).  The probes of `StrataPythonTestExtra/ContractProbesTest.lean`
compare the rules with CPython on values that Python programs make, and
`ContractSubclassTest.lean` applies them to instances of subclasses of built-in classes.
-/

namespace StrataPython.Dyn.Sem.ContractRulesTest

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn.Sem

open StrataPython.DynRun (showV runMain)

/-- The text of an exception (its class and arguments) or of a dict, and `none` for any other
object. -/
def showObj : Obj Run → Option String
  | { cls, payload := .exc e, .. } => some s!"raises {showV cls}{showV e.args}"
  | { payload := .dict t, .. } =>
    some s!"dict {(t.live.map fun (e, v) => s!"{showV e.key}: {showV v}").toList}"
  | _ => none

/-- Run `@m.main` of `text`: its result, the class and arguments of its exception, or its
fault. -/
def run : String → IO Unit := runMain showObj

/-- The block `^err.0`, which returns the exception it receives, if `body` reaches it: a function
whose blocks aren't all reachable is not well formed. -/
def errBlock (body : String) : String :=
  if (body.splitOn "^err.0").length > 1 then "    err.0(%e.0 : py.Value):\n      ret(%e.0)\n" else ""

/-- A module whose `main` runs `body`, which ends with `%v.0 : py.Value`, and returns it, or the
exception that `^err.0` receives. -/
def main (body : String) : String := s!"module m \{
  func @m.main() -> py.Value \{
    entry.0():
{body}
      ret(%v.0)
{errBlock body}  }
}"

/-- A module whose `main` runs `body`, which ends with `%b.0 : base.Bool`, and returns it as a
Python `bool`, or the exception that `^err.0` receives. -/
def mainBool (body : String) : String := s!"module m \{
  func @m.main() -> py.Value \{
    entry.0():
{body}
      branch(%b.0) ^yes.0() ^no.0()
    yes.0():
      %yes.0 : py.Value = py.boolLit(true)
      ret(%yes.0)
    no.0():
      %no.0 : py.Value = py.boolLit(false)
      ret(%no.0)
{errBlock body}  }
}"

/-- The values `args = (1, 2)` and `kwargs = {"c": 3, "d": 4}`. -/
def callValues : String := "      %one.0 : py.Value = py.intLit(1)
      %two.0 : py.Value = py.intLit(2)
      %args.0 : py.Value = py.mkTuple(%one.0, %two.0)
      %kc.0 : py.Value = py.strLit(\"c\")
      %kd.0 : py.Value = py.strLit(\"d\")
      %three.0 : py.Value = py.intLit(3)
      %four.0 : py.Value = py.intLit(4)
      %kwargs.0 : py.Value = py.mkDict(%kc.0, %three.0, %kd.0, %four.0) ^err.0()
      %none.0 : py.Value = py.noneLit
"

/-! ## The arguments of a call -/

-- A position in range reads `args`; out of range, the key of `kwargs`; else the default.
/-- info: 2 -/
#guard_msgs in
#eval run (main (callValues ++ "      %v.0 : py.Value = py.argOf(%args.0, %kwargs.0, 1, \"b\", %none.0)"))
/-- info: 3 -/
#guard_msgs in
#eval run (main (callValues ++ "      %v.0 : py.Value = py.argOf(%args.0, %kwargs.0, 2, \"c\", %none.0)"))
/-- info: 3 -/
#guard_msgs in
#eval run (main (callValues ++ "      %v.0 : py.Value = py.argOf(%args.0, %kwargs.0, -1, \"c\", %none.0)"))
/-- info: None -/
#guard_msgs in
#eval run (main (callValues ++ "      %v.0 : py.Value = py.argOf(%args.0, %kwargs.0, 5, \"e\", %none.0)"))
-- `args` counts only if it is exactly a tuple: a list doesn't.
/-- info: 3 -/
#guard_msgs in
#eval run (main (callValues ++ "      %l.0 : py.Value = py.mkList(%one.0, %two.0)
      %v.0 : py.Value = py.argOf(%l.0, %kwargs.0, 0, \"c\", %none.0)"))
-- `kwargs` counts only if it is exactly a dict.
/-- info: None -/
#guard_msgs in
#eval run (main (callValues ++ "      %v.0 : py.Value = py.argOf(%args.0, %args.0, -1, \"c\", %none.0)"))

-- `extraKwargs` drops the named keys, keeps the order, and gives a new dict.
/-- info: dict ['d': 4] -/
#guard_msgs in
#eval run (main (callValues ++ "      %v.0 : py.Value = py.extraKwargs(%kwargs.0, \"c\")"))
/-- info: dict ['c': 3, 'd': 4] -/
#guard_msgs in
#eval run (main (callValues ++ "      %v.0 : py.Value = py.extraKwargs(%kwargs.0)"))
/-- info: dict [] -/
#guard_msgs in
#eval run (main (callValues ++ "      %v.0 : py.Value = py.extraKwargs(%args.0, \"c\")"))

-- `bindsTo` holds for `f(a, b, *, c, d)`, and fails on each of the docstring's `TypeError`s.
/-- info: True -/
#guard_msgs in
#eval run (mainBool (callValues ++ "      %b.0 : base.Bool = py.bindsTo(%args.0, %kwargs.0, 2, false, \"a\", \"b\", \"c\", \"d\")"))
-- Too many positional arguments.
/-- info: False -/
#guard_msgs in
#eval run (mainBool (callValues ++ "      %b.0 : base.Bool = py.bindsTo(%args.0, %kwargs.0, 1, false, \"a\", \"b\", \"c\", \"d\")"))
-- A parameter given both by position and by keyword.
/-- info: False -/
#guard_msgs in
#eval run (mainBool (callValues ++ "      %b.0 : base.Bool = py.bindsTo(%args.0, %kwargs.0, 3, false, \"a\", \"c\", \"x\", \"d\")"))
-- An unexpected keyword without `**kw`, and with it.
/-- info: False -/
#guard_msgs in
#eval run (mainBool (callValues ++ "      %b.0 : base.Bool = py.bindsTo(%args.0, %kwargs.0, 2, false, \"a\", \"b\", \"c\")"))
/-- info: True -/
#guard_msgs in
#eval run (mainBool (callValues ++ "      %b.0 : base.Bool = py.bindsTo(%args.0, %kwargs.0, 2, true, \"a\", \"b\", \"c\")"))
-- No names at all: only an empty call binds.
/-- info: False -/
#guard_msgs in
#eval run (mainBool (callValues ++ "      %b.0 : base.Bool = py.bindsTo(%args.0, %kwargs.0, 0, false)"))

/-! ## The tests -/

/-- info: int -/
#guard_msgs in
#eval run (main "      %v.0 : py.Value = py.stdClass(\"builtins\", \"int\")")
/-- info: complex -/
#guard_msgs in
#eval run (main "      %v.0 : py.Value = py.stdClass(\"builtins\", \"complex\")")
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.stdClass: builtins.len is not a class" -/
#guard_msgs in
#eval run (main "      %v.0 : py.Value = py.stdClass(\"builtins\", \"len\")")
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.stdClass: builtins.NoneType is not a class" -/
#guard_msgs in
#eval run (main "      %v.0 : py.Value = py.stdClass(\"builtins\", \"NoneType\")")
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.stdClass: the module collections.abc is not modelled" -/
#guard_msgs in
#eval run (main "      %v.0 : py.Value = py.stdClass(\"collections.abc\", \"Sequence\")")

-- `typeIsSubclass` by the MRO: `True` is an `int`; a tuple of classes; a non-class raises.
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.boolLit(true)
      %c.0 : py.Value = py.stdClass(\"builtins\", \"int\")
      %b.0 : base.Bool = py.typeIsSubclass(%x.0, %c.0) ^err.0()")
/-- info: False -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.intLit(1)
      %c.0 : py.Value = py.stdClass(\"builtins\", \"bool\")
      %b.0 : base.Bool = py.typeIsSubclass(%x.0, %c.0) ^err.0()")
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.intLit(1)
      %c.0 : py.Value = py.stdClass(\"builtins\", \"str\")
      %d.0 : py.Value = py.stdClass(\"builtins\", \"int\")
      %t.0 : py.Value = py.mkTuple(%c.0, %d.0)
      %b.0 : base.Bool = py.typeIsSubclass(%x.0, %t.0) ^err.0()")
-- Every element is checked first: `(int, 5)` raises, although `int` would match.
/-- info: raises TypeError('typeIsSubclass() arg 2 must be a class or a tuple of classes',) -/
#guard_msgs in
#eval run (main "      %x.0 : py.Value = py.intLit(1)
      %c.0 : py.Value = py.stdClass(\"builtins\", \"int\")
      %five.0 : py.Value = py.intLit(5)
      %t.0 : py.Value = py.mkTuple(%c.0, %five.0)
      %b.0 : base.Bool = py.typeIsSubclass(%x.0, %t.0) ^err.0()
      %v.0 : py.Value = py.boolLit(true)")
-- A nested tuple raises too.
/-- info: raises TypeError('typeIsSubclass() arg 2 must be a class or a tuple of classes',) -/
#guard_msgs in
#eval run (main "      %x.0 : py.Value = py.intLit(1)
      %c.0 : py.Value = py.stdClass(\"builtins\", \"int\")
      %t.0 : py.Value = py.mkTuple(%c.0)
      %u.0 : py.Value = py.mkTuple(%t.0)
      %b.0 : base.Bool = py.typeIsSubclass(%x.0, %u.0) ^err.0()
      %v.0 : py.Value = py.boolLit(true)")
-- An undefined operand stops with a gap, and so does an undefined element of the tuple, even
-- after a non-class.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.typeIsSubclass: an operand is undefined" -/
#guard_msgs in
#eval run (main "      %x.0 : py.Value = py.undef(\"x\")
      %c.0 : py.Value = py.stdClass(\"builtins\", \"int\")
      %b.0 : base.Bool = py.typeIsSubclass(%x.0, %c.0) ^err.0()
      %v.0 : py.Value = py.boolLit(true)")
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.typeIsSubclass: an operand is undefined" -/
#guard_msgs in
#eval run (main "      %x.0 : py.Value = py.intLit(1)
      %five.0 : py.Value = py.intLit(5)
      %u.0 : py.Value = py.undef(\"u\")
      %t.0 : py.Value = py.mkTuple(%five.0, %u.0)
      %b.0 : base.Bool = py.typeIsSubclass(%x.0, %t.0) ^err.0()
      %v.0 : py.Value = py.boolLit(true)")

-- `isInstance` is `isinstance`: `True` is an `int`, and a tuple of classes.
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.boolLit(true)
      %c.0 : py.Value = py.stdClass(\"builtins\", \"int\")
      %b.0 : base.Bool = py.isInstance(%x.0, %c.0) ^err.0()")
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.boolLit(true)
      %c.0 : py.Value = py.stdClass(\"builtins\", \"str\")
      %d.0 : py.Value = py.stdClass(\"builtins\", \"int\")
      %t.0 : py.Value = py.mkTuple(%c.0, %d.0)
      %b.0 : base.Bool = py.isInstance(%x.0, %t.0) ^err.0()")
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.isInstance: an operand is undefined" -/
#guard_msgs in
#eval run (main "      %x.0 : py.Value = py.undef(\"x\")
      %c.0 : py.Value = py.stdClass(\"builtins\", \"int\")
      %b.0 : base.Bool = py.isInstance(%x.0, %c.0) ^err.0()
      %v.0 : py.Value = py.boolLit(true)")

-- `len` is `len`: a list's length, and `TypeError` for an `int`.
/-- info: 2 -/
#guard_msgs in
#eval run (main "      %one.0 : py.Value = py.intLit(1)
      %l.0 : py.Value = py.mkList(%one.0, %one.0)
      %v.0 : py.Value = py.len(%l.0) ^err.0()")
/-- info: raises TypeError("object of type 'int' has no len()",) -/
#guard_msgs in
#eval run (main "      %one.0 : py.Value = py.intLit(1)
      %v.0 : py.Value = py.len(%one.0) ^err.0()")

-- `strIsOneOf` and `intIsOneOf`, with no literals too; a `bool` is no `int`.
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.strLit(\"w\")
      %b.0 : base.Bool = py.strIsOneOf(%x.0, \"r\", \"w\")")
/-- info: False -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.strLit(\"w\")
      %b.0 : base.Bool = py.strIsOneOf(%x.0)")
/-- info: False -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.undef(\"x\")
      %b.0 : base.Bool = py.strIsOneOf(%x.0, \"x\")")
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.intLit(1)
      %b.0 : base.Bool = py.intIsOneOf(%x.0, 0, 1)")
/-- info: False -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.boolLit(true)
      %b.0 : base.Bool = py.intIsOneOf(%x.0, 0, 1)")
/-- info: False -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.intLit(1)
      %b.0 : base.Bool = py.intIsOneOf(%x.0)")

-- `isImmutableScalar`: `None`, `int`, `float`, `bool`, `str` and `bytes` are; a tuple and a list
-- aren't.
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.noneLit
      %b.0 : base.Bool = py.isImmutableScalar(%x.0)")
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.intLit(1)
      %b.0 : base.Bool = py.isImmutableScalar(%x.0)")
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.floatLit(1.5)
      %b.0 : base.Bool = py.isImmutableScalar(%x.0)")
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.boolLit(false)
      %b.0 : base.Bool = py.isImmutableScalar(%x.0)")
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.strLit(\"s\")
      %b.0 : base.Bool = py.isImmutableScalar(%x.0)")
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.bytesLit(\"b\")
      %b.0 : base.Bool = py.isImmutableScalar(%x.0)")
/-- info: False -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.mkTuple()
      %b.0 : base.Bool = py.isImmutableScalar(%x.0)")
/-- info: False -/
#guard_msgs in
#eval run (mainBool "      %x.0 : py.Value = py.mkList()
      %b.0 : base.Bool = py.isImmutableScalar(%x.0)")

-- `dictKeysWithin`: every key among the names; an empty dict; and a non-dict.
/-- info: True -/
#guard_msgs in
#eval run (mainBool (callValues ++ "      %b.0 : base.Bool = py.dictKeysWithin(%kwargs.0, \"c\", \"d\", \"e\")"))
/-- info: False -/
#guard_msgs in
#eval run (mainBool (callValues ++ "      %b.0 : base.Bool = py.dictKeysWithin(%kwargs.0, \"c\")"))
/-- info: True -/
#guard_msgs in
#eval run (mainBool "      %d.0 : py.Value = py.mkDict() ^err.0()
      %b.0 : base.Bool = py.dictKeysWithin(%d.0)")
/-- info: False -/
#guard_msgs in
#eval run (mainBool (callValues ++ "      %b.0 : base.Bool = py.dictKeysWithin(%args.0, \"c\")"))

/-! ## `reSearch` on an undefined subject -/

-- An undefined subject stops with a gap, but only after the pattern is read.
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.reSearch: an operand is undefined" -/
#guard_msgs in
#eval run (main "      %u.0 : py.Value = py.undef(\"u\")
      %b.0 : base.Bool = py.reSearch(\"a\", %u.0) ^err.0()
      %v.0 : py.Value = py.boolLit(true)")
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.reSearch: a pattern outside the modelled subset of re" -/
#guard_msgs in
#eval run (main "      %u.0 : py.Value = py.undef(\"u\")
      %b.0 : base.Bool = py.reSearch(\"(\", %u.0) ^err.0()
      %v.0 : py.Value = py.boolLit(true)")

/-! ## An `int` whose value depends on the hash seed -/

/-- The instructions that make `%h.0 = "a".__hash__()`, whose value depends on the hash seed. -/
def hashA : String := "      %s.0 : py.Value = py.strLit(\"a\")
      %m.0 : py.Value = py.attr(%s.0, \"__hash__\") ^err.0()
      %a.0 : py.Value = py.mkTuple()
      %k.0 : py.Value = py.mkDict() ^err.0()
      %h.0 : py.Value = py.call(%m.0, %a.0, %k.0) ^err.0()
"

-- It is an `int`, so it is an immutable scalar; but whether it is 0 or 1 depends on the seed.
/-- info: True -/
#guard_msgs in
#eval run (mainBool (hashA ++ "      %b.0 : base.Bool = py.isImmutableScalar(%h.0)"))
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.intIsOneOf: an int whose value depends on the hash seed" -/
#guard_msgs in
#eval run (mainBool (hashA ++ "      %b.0 : base.Bool = py.intIsOneOf(%h.0, 0, 1)"))
/-- info: False -/
#guard_msgs in
#eval run (mainBool (hashA ++ "      %b.0 : base.Bool = py.strIsOneOf(%h.0, \"a\")"))

end StrataPython.Dyn.Sem.ContractRulesTest
