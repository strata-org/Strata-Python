/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.IR
public import StrataMantle.Base
-- Constructing an `Env` value needs its representation at code-generation time.
import StrataMantle.Env.WF
import StrataMantle.DSL

set_option autoImplicit false

/-!
# Python's environment

`Py` extends `Base` with `py.Value`, the type of every Python value; `py.Completion`, how a
protected block finished; and one instruction per Python operation.  In every `e` with
`Py.env ⊑ e`:

* `Py.Value.ty`, `Py.Completion.ty`, and the abbreviations `Py.raising.ty a`, `Py.failing.ty`
  and `Py.cell.ty`;
* `Py.o.sig : InsnSig e` and `Py.o : InsnRef e Py.o.sig`, for each operation `o`;
* `Py.Completion.c.sig` and `Py.Completion.c`, for each constructor `c`, and
  `Py.Completion.case`, the terminal operation a dispatch applies;
* `Base`'s declarations, through `Py.toBase`.

`Py.pn` names a declaration in the `py` namespace.

This environment does not model Python's type system: `isinstance`, subtyping and the rest
belong to a predicate layer above the IR.  A base type appears only where a value is not a
Python value:

* `String`, `Int`, `Bool` and `Float64` for what is fixed at translation time, such as an
  attribute name, a literal or a bound.  The translator supplies them as constants.
* `Bool` for what a `branch` inspects, such as the result of `truthy`.
* `Unit` for an operation that only acts.

An operation that can raise declares an `err` successor receiving the exception, and returns
what it produces on success; one without `err` never raises.  A translated Python function
returns `Py.failing`, `Except py.Value py.Value`, so the handler that propagates a failure
returns it as `error`.

## Completions

A `finally` runs however its protected block finished, and then that finishing continues.
So "how it finished" is a value: `py.Completion`, with one constructor per way out.  A
dispatch is one `py.Completion.case`, one successor per constructor, and the value a `return`
carries exists only in the successor reached when it was a `return`.

```
    try:                    entry:        … ^catch()
      return f()                          %c = completionReturn %v; jump ^finally(%c)
    finally:                catch(%e):    %c = completionRaise %e;  jump ^finally(%c)
      g()                   finally(%c):  …;                        jump ^dispatch(%c)
                            dispatch(%c): py.Completion.case %c ^normal() ^return()
                                            ^raise() ^break() ^continue()
```

The `finally` body is emitted once and reached from every exit.  Nested `finally`s forward
a completion outwards instead of acting on it.
-/

namespace StrataPython.Mantle

open Strata.Mantle

/-- Python's environment: the base, `py.Value`, `py.Completion`, and the operations. -/
public environment Py extends Base where
  namespace py
  open base
  /-- Every Python value. -/
  type Value

  /-- How a block a `finally` protects finished.  The constructors are in dispatch order.  Neither
  `completionBreak` nor `completionContinue` carries a target: both bind to the innermost
  enclosing loop, which the dispatch site resolves lexically. -/
  data Completion where
    | /-- Ran to its end: nothing pending. -/ completionNormal
    | /-- Left by `return value`. -/ completionReturn (value : Value)
    | /-- Left by raising `exc`. -/ completionRaise (exc : Value)
    | /-- Left by `break`. -/ completionBreak
    | /-- Left by `continue`. -/ completionContinue

  /-- What an operation that can fail returns: a raised Python exception, or an `a`. -/
  abbrev raising (a) := Except Value a
  /-- Raise, or produce a Python value: what a translated Python function returns. -/
  abbrev failing := raising Value
  /-- A cell holding a Python value: what a local is, and what a closure captures.  It is
  written with `refSet` and read with `refGet`. -/
  abbrev cell := Ref Value

  -- Definedness and checks.

  /-- A value not yet assigned.  `name` is diagnostic only. -/
  insn undef (name : String) : Value
  /-- Whether `val` is assigned, as the `Bool` a `branch` takes. -/
  insn isDefined (val : Value) : Bool
  /-- `bool(val)`, as the `Bool` a `branch` takes.  Raises, because `__bool__` and `__len__`
  are arbitrary code. -/
  insn truthy (val : Value) (^err (exc : Value)) : Bool
  /-- `val`, or a raised `excType(msg)` if it is unassigned: a check without a branch.  A
  `{}` in `msg` is replaced by `repr` of `val`. -/
  insn requireDefined (val : Value) (excType msg : String) (^err (exc : Value)) : Value
  /-- Raises `excType(msg)` if `val` is assigned: the mirror of `requireDefined`.  A `{}` in
  `msg` is replaced by `repr` of `val`. -/
  insn requireUndefined (val : Value) (excType msg : String) (^err (exc : Value)) : Unit
  /-- Raises `excType(msg)` if the integer `val` exceeds `limit`.  A `{}` in `msg` is
  replaced by `repr` of `val`, and a `{was}` by `was` if `val` is 1 and `were` otherwise. -/
  insn requireAtMost (val : Value) (limit : Int) (excType msg : String)
    (^err (exc : Value)) : Unit

  -- Literals: a base constant, boxed into a Python value.

  /-- The Python `int` for `val`. -/
  insn intLit (val : Int) : Value
  /-- The Python `float` for `val`. -/
  insn floatLit (val : Float64) : Value
  /-- The Python `str` for `val`. -/
  insn strLit (val : String) : Value
  /-- `True` or `False`. -/
  insn boolLit (val : Bool) : Value
  /-- The Python `bytes` whose octets are the code units of `val`. -/
  insn bytesLit (val : String) : Value
  /-- `None`. -/
  insn noneLit : Value

  -- Calls and references.

  /-- `func(*args, **kwargs)`, with `args` a tuple and `kwargs` a dict.  Argument binding is
  the callee's prologue, not this operation.  Raises `TypeError` if a key of `kwargs` is not
  a string, as CPython's `_PyStack_UnpackDict` does. -/
  insn call (func args kwargs : Value) (^err (exc : Value)) : Value
  /-- The value `moduleName.name` refers to. -/
  insn qualifiedRef (moduleName name : String) (^err (exc : Value)) : Value
  /-- A callable: `code`, a code pointer, and the `cells` it captures.
  Late binding reads a captured cell; a module-level function captures none.  `call` is its
  `apply`. -/
  insn mkClosure (code : Code) (*cells : Ref Value) : Value
  /-- `obj.name`. -/
  insn attr (obj : Value) (name : String) (^err (exc : Value)) : Value
  /-- `obj.name = val`. -/
  insn setAttr (obj : Value) (name : String) (val : Value) (^err (exc : Value)) : Unit

  -- Globals and imports.  A module name is always fully qualified, such as `"a.b"`.

  /-- The cell of the global `name` of `module`: the same cell for the same arguments, read
  with `refGet` and written with `refSet` as a local is.  It holds `undef` until its first
  assignment, and `del` writes `undef` back.  A read checks `isDefined`; a global that may
  shadow a builtin falls back to `qualifiedRef "builtins" name` when it is not. -/
  insn globalCell (module name : String) : cell
  /-- The module object for `module`, after importing it and each package above it, unless
  already imported.  `import a.b` is `importModule "a.b"` and then `importModule "a"`,
  which binds the package; `import a.b as c` binds this result.
  Raises `ImportError`, or whatever the module's body raises. -/
  insn importModule (module : String) (^err (exc : Value)) : Value
  /-- `from module import name`: imports `module`, then reads its attribute `name`, falling
  back to the submodule `module.name`, as CPython's `IMPORT_FROM` does.  Unlike
  `qualifiedRef`, it runs once, at the import, and its result is a snapshot.  Raises
  `ImportError` if neither exists. -/
  insn importFrom (module name : String) (^err (exc : Value)) : Value

  -- Operators.

  /-- `lhs + rhs`. -/
  insn add (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs - rhs`. -/
  insn sub (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs * rhs`. -/
  insn mult (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs / rhs`. -/
  insn div (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs // rhs`. -/
  insn floorDiv (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs % rhs`. -/
  insn mod (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs ** rhs`. -/
  insn pow (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `not operand`.  Raises, because it consults truthiness. -/
  insn not_ as "not" (operand : Value) (^err (exc : Value)) : Value
  /-- `-operand`. -/
  insn uSub (operand : Value) (^err (exc : Value)) : Value
  /-- `lhs == rhs`. -/
  insn eq (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs != rhs`. -/
  insn notEq (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs < rhs`. -/
  insn lt (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs <= rhs`. -/
  insn ltE (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs > rhs`. -/
  insn gt (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs >= rhs`. -/
  insn gtE (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs is rhs`, which compares identity. -/
  insn is_ as "is" (lhs rhs : Value) : Value
  /-- `lhs is not rhs`. -/
  insn isNot (lhs rhs : Value) : Value
  /-- `lhs in rhs`. -/
  insn in_ as "in" (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs not in rhs`. -/
  insn notIn (lhs rhs : Value) (^err (exc : Value)) : Value

  -- Data structures.

  /-- A dict from `kvs`, keys and values alternating: CPython's `BUILD_MAP`.  The type rules
  do not catch an odd count.  Raises `TypeError` if a key is unhashable, or whatever its
  `__hash__` or `__eq__` raises. -/
  insn mkDict (*kvs : Value) (^err (exc : Value)) : Value
  /-- A call's keyword dict from `kvs`, keys and values alternating, each key a `str` the
  translator supplies.  Total, unlike `mkDict`: hashing and comparing a `str` runs no user
  code. -/
  insn mkKwargs (*kvs : Value) : Value
  /-- A list of `elems`. -/
  insn mkList (*elems : Value) : Value
  /-- A set of `elems`: CPython's `BUILD_SET`.  Raises as `mkDict` does for a key. -/
  insn mkSet (*elems : Value) (^err (exc : Value)) : Value
  /-- A tuple of `elems`. -/
  insn mkTuple (*elems : Value) : Value
  /-- `obj[key]`. -/
  insn getItem (obj key : Value) (^err (exc : Value)) : Value
  /-- `obj[key] = val`. -/
  insn setItem (obj key val : Value) (^err (exc : Value)) : Unit
  /-- `slice(lo, hi, step)`: CPython's `BUILD_SLICE`, for a slice that is not the whole
  subscript, as in `obj[lo:hi, k]`.  An absent bound is `None`. -/
  insn mkSlice (lo hi step : Value) : Value
  /-- `obj[lo:hi:step]`.  An absent bound is `None`, as in Python. -/
  insn getSlice (obj lo hi step : Value) (^err (exc : Value)) : Value
  /-- A tuple of the elements of `list`, a list the emitting code made: CPython's
  `INTRINSIC_LIST_TO_TUPLE`, which ends a tuple display or call with a `*x`. -/
  insn listToTuple (list : Value) : Value
  /-- The positional arguments of `callee(*iterable)`: `tuple(iterable)`, as CPython's
  `CALL_FUNCTION_EX` makes them when `*iterable` is the only positional argument.  Raises a
  `TypeError` naming `callee` if `iterable` is not iterable. -/
  insn argsTuple (callee iterable : Value) (^err (exc : Value)) : Value
  /-- The number of elements of `tup`, as a Python `int`. -/
  insn tupleLen (tup : Value) : Value
  /-- `dict` with `other` merged in, as a fresh dict: the lowering of a `**x` argument.
  CPython's `DICT_MERGE`: a key already present raises a `TypeError` naming `callee`, as does
  an `other` that is not a mapping. -/
  insn dictMerge (callee dict other : Value) (^err (exc : Value)) : Value
  /-- `dict` with `other` merged in, as a fresh dict: the lowering of a `**x` entry in a dict
  display.  CPython's `DICT_UPDATE`: a key already present is overwritten. -/
  insn dictUpdate (dict other : Value) (^err (exc : Value)) : Value
  /-- The number of entries of `dict`, as a Python `int`. -/
  insn dictLen (dict : Value) : Value
  /-- `dict[key]` if present, else `fallback`. -/
  insn dictGet (dict key fallback : Value) : Value
  /-- The first key of `dict` in insertion order, or `fallback` if it is empty. -/
  insn dictFirstKey (dict fallback : Value) : Value
  /-- Removes `key` from `dict`, if it is there. -/
  insn dictDiscard (dict key : Value) : Unit

  -- Accumulating into a container the emitting code made.

  /-- Appends `value` to `list` in place: CPython's `LIST_APPEND`.  Total: `list` is one the
  emitting code made, such as a comprehension's accumulator. -/
  insn listAppend (list value : Value) : Unit
  /-- Appends the elements of `iterable` to `list` in place: CPython's `LIST_EXTEND`, for a `*x`
  element.  Raises `TypeError` if `iterable` is not iterable, or whatever iterating it raises. -/
  insn listExtend (list iterable : Value) (^err (exc : Value)) : Unit
  /-- Adds `value` to `set` in place: CPython's `SET_ADD`.  Raises `TypeError` if `value` is
  unhashable. -/
  insn setAdd (set value : Value) (^err (exc : Value)) : Unit
  /-- Adds the elements of `iterable` to `set` in place: CPython's `SET_UPDATE`, for a `*x`
  element.  Raises as `listExtend` and `setAdd` do. -/
  insn setUpdate (set iterable : Value) (^err (exc : Value)) : Unit
  /-- Stores `value` under `key` in `dict`, in place: CPython's `MAP_ADD`.  Raises `TypeError`
  if `key` is unhashable. -/
  insn dictSet (dict key value : Value) (^err (exc : Value)) : Unit

  -- Iteration.

  /-- `iter(obj)`. -/
  insn getIter (obj : Value) (^err (exc : Value)) : Value
  /-- The next element of `iter`.  Exhaustion raises `StopIteration`, so a `for` loop's exit
  edge is `next`'s `err` successor, to a block that tests it with `isStopIteration`. -/
  insn next (iter : Value) (^err (exc : Value)) : Value
  /-- Whether `exc` is a `StopIteration`, as the `Bool` a `branch` takes: the guard that
  selects a loop's exit edge. -/
  insn isStopIteration (exc : Value) : Bool

  -- Strings and degradation.

  /-- `repr(val)`, without looking up the builtin: an f-string's `!r` (`FORMAT_VALUE`). -/
  insn repr (val : Value) (^err (exc : Value)) : Value
  /-- `str(val)`, without looking up the builtin: an f-string's `!s`. -/
  insn toStr as "str" (val : Value) (^err (exc : Value)) : Value
  /-- `ascii(val)`, without looking up the builtin: an f-string's `!a`. -/
  insn ascii (val : Value) (^err (exc : Value)) : Value
  /-- `format(val, spec)`, without looking up the builtin: an f-string field after its
  conversion (`FORMAT_VALUE`).  Raises what `__format__` raises, or `TypeError` if it does
  not return a `str`. -/
  insn fmtValue (val spec : Value) (^err (exc : Value)) : Value
  /-- The concatenation of `parts`, each a `str`: CPython's `BUILD_STRING`.  Total: joining
  `str`s runs no user code. -/
  insn strConcat (*parts : Value) : Value
  /-- A stand-in for a construct the translator does not handle. -/
  insn unsupported (name : Value) : Value
  end py

namespace Py

/-- `py.<s>`, the name of a declaration in Python's namespace. -/
public abbrev pn (s : String) : Name := .str (.str .base "py") s

end Py

end StrataPython.Mantle
