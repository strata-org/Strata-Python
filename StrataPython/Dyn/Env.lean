/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR
public import StrataDyn.Base
-- Public, so that `Py`'s typed emitters are public.
public import StrataDyn.Build.Typed
-- Constructing an `Env` value needs its representation at code-generation time.
import StrataDyn.Env.WF
import StrataDyn.DSL

set_option autoImplicit false

/-!
# Python's environment

`Py` extends `Base` with `py.Value`, the type of every Python value; `py.Completion`, how a
protected block finished; and one instruction per Python operation.  In every `e` with
`Py.env ≼ e`:

* the handles `Py.Value`, `Py.Completion`, and the abbreviations `Py.raising a`, `Py.failing`
  and `Py.cell`, its types, so the builder writes `Py.raising Base.Unit`;
* `Py.o.sig : InsnSig e` and `Py.o : InsnRef e Py.o.sig`, for each operation `o`;
* `Py.Completion.c.sig` and `Py.Completion.c`, for each constructor `c`, and
  `Py.Completion.case`, the terminal operation a dispatch applies;
* `Base`'s declarations, through `Py.toBase`.

`Py.pn` names a declaration in the `py` namespace.

Every operation is opaque: its docstring states its meaning, with CPython 3.12 as the
reference, and an analyzer, such as Pylate, holds the rules for it.  This holds for Python's type
system too: `isInstance` is an operation like `add`.  A base type appears only where a value is
not a Python value:

* `String`, `Int`, `Bool` and `Float64` for what is fixed at translation time, such as an
  attribute name, a literal or a bound.  The translator supplies them as constants.
* `Bool` for what a `branch` inspects, such as the result of `truthy`, and for what a contract
  clause returns.
* `Unit` for an operation that only acts.

An operation that can raise declares an `err` successor receiving the exception, and returns
what it produces on success; one without `err` never raises.  A translated Python function
returns `Py.failing`, `Except py.Value py.Value`, so the handler that propagates a failure
returns it as `error`.

Each operation declares its effect, an upper bound on what it may do: `pure`, such as a literal
or `is`; `reads`, such as `listToTuple` or `mkClosure` (which reads the module's `__name__`);
`calls`, one that may run code that the IR does not show, such as `add`, `truthy` or
`loadGlobal` (a lookup in the builtins dict may run a key's `__eq__`); or, without a keyword,
`writes`, such as `call`, `setItem`, an in-place operator, or `next`.  A method that an operation
looks up on an operand, or on an object that an operand holds, counts as code that it calls,
whether it is written in Python or built in, such as the `__next__` of a built-in iterator, which
`x in it` advances.  The operation's own fixed computation does not count, such as the search
of `reSearch`.  In doubt, an operation is `writes`.  An operation that raises an exception of its
own reads the exception being handled, which becomes the new exception's `__context__` (below),
so it is never `pure`.

## Operands that an operation assumes

The meaning of some operations assumes something of their operands, such as that an index is in
range.  The translator applies only some of them, and only where the assumption holds.  Where it
fails, the result is not defined, and a contract region that applies the operation there is not
well defined (`docs/Dyn.md`).  These are the operations, with what each assumes.  A tuple, a
dict, a list or a set is an object whose type is exactly `tuple`, `dict`, `list` or `set`, not an
instance of a subclass, unless the item says otherwise.

* a tuple: `tupleGet` (with an index in range), and the `args` of `call`;
* for `bindArgs`: `args` a tuple, `kwargs` a dict, `defaults` a tuple with one entry per name,
  `0 ≤ nPosOnly ≤ nPos ≤` the number of names, and the positional parameters with a default
  after those without;
* a dict: `dictSet`, the `dict` of `dictMerge` and `dictUpdate`, and the `kwargs` of `call`;
* a dict or an instance of a subclass of `dict`: the `obj` of `itemLoc`;
* a list: `listToTuple`, `listAppend` and `listExtend`; a set: `setAdd` and `setUpdate`;
* `str`s: the parts of `strConcat` and the keys of `mkKwargs`;
* an even number of operands: `mkDict` and `mkKwargs`;
* the name of a built-in exception class: the `excType` of `requireDefined`;
* an exception: the `exc` of `pushExcInfo`, `setCause`, `excMatch` and `exitWithExc`;
* the bound `__exit__` of a `with`: the `exit` of `exitWithExc`;
* what `pushExcInfo` or `pushPending` returned: the `prev` of `popExcept`;
* for `reSearch`: a `pattern` that compiles without a warning and without `RecursionError`,
  and an `s` that is a `str` or whose class and its bases define no `__buffer__` in Python;
* a name that CPython 3.12's standard library defines as a class: `stdClass`, which also
  assumes that the program has not run a second time the body of the module that creates that
  class.

## Completions

A `finally` runs however its protected block finished, and then that finishing continues.
So "how it finished" is a value: `py.Completion`, with one constructor per way out.  A
dispatch is one `py.Completion.case`, one successor per constructor, and the value a `return`
carries exists only in the successor reached when it was a `return`.

```
    try:                    entry:        … ^catch()
      return f()                          %c = completionReturn %v; jump ^finally(%c)
    finally:                catch(%e):    %c = completionRaise %e;  jump ^finally(%c)
      g()                   finally(%c):  …;  py.Completion.case %c ^normal() ^return()
                                                ^raise() ^break() ^continue()
```

The `finally` body is emitted once and reached from every exit.  Nested `finally`s forward
a completion outwards instead of acting on it.

## The exception being handled

As in CPython, the run-time state holds the exception being handled: `pushExcInfo` sets it on
entering an `except` handler or a `with`'s exception path, `pushPending` on entering a
`finally` body that a raise reached, and `popExcept` restores the previous one on leaving
them.  `handledExc` reads it.

An exception that an operation raises itself, such as the `KeyError` of `getItem`, gets the
exception being handled as its `__context__`, as CPython's `_PyErr_SetObject` does:

* If the two are the same exception, `__context__` does not change.
* If the handled exception's `__context__` chain already reaches the raised one, that link is
  cut, so no cycle forms.

An exception that comes out of Python code the operation runs, such as a callee or a
`__next__`, keeps its `__context__`.  `toException` sets it too, since `raise e` is
`toException` and then a jump.  `handledExc` does not: a bare `raise` keeps the chain.

## Contracts

A contract of a Python function uses these operations; the translator of Python code does not
emit them.

* The arguments of a call, as a function's parameters `args` and `kwargs` receive them:
  `argOf`, `extraKwargs` and `bindsTo`.
* Tests: `stdClass`, `isInstance`, `typeIsSubclass`, `len`, `reSearch`, `strIsOneOf`,
  `intIsOneOf`, `isImmutableScalar` and `dictKeysWithin`.
* Bounded quantifiers over what a container stores: `allIn`, `anyIn`, `allItems` and `anyItems`.
  The body returns `raising Bool`, so a failure in it can go to a block that passes it on with
  `error`, and the quantifier raises it at its `err` successor.
* Locations, which a frame names and computes at the call: `attrLoc`, `itemLoc`, `objLoc`,
  `reachLoc` and `instanceState`.  A location exists only where CPython lets state change: an
  object whose class is exactly `int`, `float`, `complex`, `str`, `bytes`, `tuple`, `frozenset`,
  `range`, `bool` or `NoneType` has none.

The operations on keywords and on string literals (`argOf`, `extraKwargs`, `bindsTo`,
`strIsOneOf` and `dictKeysWithin`) accept only a key or a value that is exactly a `str`, not an
instance of a subclass, and compare its characters.  A subclass may override `__eq__`: CPython
3.12 binds such a keyword with that `__eq__` in a Python function, and by its characters in a
built-in one.  `bindsTo`, `dictKeysWithin`, `strIsOneOf`, `intIsOneOf`, and `typeIsSubclass`
conjoined with `isInstance` are stricter than the Python they stand for, so
`docs/PythonToDyn.md` (§2) says where a contract may use them.  A declared type's test is
`typeIsSubclass(v, C)` and then `isInstance(v, C)`; `typeIsSubclass` alone is not stricter than
`isinstance`.
-/

namespace StrataPython.Dyn

open Strata.Dyn

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
  pure insn undef (name : String) : Value
  /-- Whether `val` is assigned, as the `Bool` a `branch` takes. -/
  pure insn isDefined (val : Value) : Bool
  /-- `bool(val)`, as the `Bool` a `branch` takes.  Raises, because `__bool__` and `__len__`
  are arbitrary code. -/
  calls insn truthy (val : Value) (^err (exc : Value)) : Bool
  /-- `val`, or a raised `excType(msg)` if it is unassigned: a check without a branch.
  `excType` names a built-in exception class. -/
  reads insn requireDefined (val : Value) (excType msg : String) (^err (exc : Value)) : Value

  -- Literals: a base constant, boxed into a Python value.

  /-- The Python `int` for `val`. -/
  pure insn intLit (val : Int) : Value
  /-- The Python `float` for `val`. -/
  pure insn floatLit (val : Float64) : Value
  /-- The Python `str` for `val`. -/
  pure insn strLit (val : String) : Value
  /-- `True` or `False`. -/
  pure insn boolLit (val : Bool) : Value
  /-- The Python `bytes` whose octets are the code units of `val`. -/
  pure insn bytesLit (val : String) : Value
  /-- `None`. -/
  pure insn noneLit : Value
  /-- `...`, the `Ellipsis` object, even if `builtins.Ellipsis` is rebound: CPython's
  `LOAD_CONST`. -/
  pure insn ellipsisLit : Value

  -- Calls and references.

  /-- `func(*args, **kwargs)`, with `args` a tuple and `kwargs` a dict.  Argument binding is
  not this operation: a translated function's prologue applies `bindArgs`.  Raises `TypeError`
  if a key of `kwargs` is not a string, as CPython's `_PyStack_UnpackDict` does. -/
  insn call (func args kwargs : Value) (^err (exc : Value)) : Value
  /-- Binds the arguments of a call to the parameters `names` of a Python function, as CPython
  3.12's `initialize_locals` does.  `args` is the tuple of positional arguments, and `kwargs` the
  dict of keyword arguments, taken in its order.  The first `nPosOnly` names are
  positional-only, the first `nPos` names are positional (`nPosOnly ≤ nPos`), and the others
  keyword-only.  `varPos` and `varKw` say whether the function has `*args` and `**kw`.
  `defaults` is a tuple with one entry per name: the parameter's default, or `undef` if it has
  none.

  The positional arguments bind to the first `nPos` names, in order.  Each keyword binds to the
  first parameter, other than a positional-only one, that it is or that it equals by `==`.
  Without `**kw`, a keyword that binds to none is an error.  With `**kw`, it goes into the `**kw`
  dict, as does a keyword named like a positional-only parameter.  Then the defaults fill the
  parameters that no argument binds.

  It returns a tuple: one value per name, then the extra positional arguments as a tuple if
  `varPos`, then the remaining keywords as a new dict, in their order, if `varKw`.

  It raises the `TypeError` that CPython raises, in CPython's order.  The text of its
  `TypeError`'s message is not specified.  First, it takes each keyword in order.  A keyword that
  is not a `str` is an error, and so is a keyword that binds to a parameter that is already bound:
  a parameter given twice.  At the first keyword that binds to no parameter, without `**kw`: if
  any keyword of the call names a positional-only parameter, the positional-only error;
  otherwise the unexpected-keyword error.  Then too many positional
  arguments.  Then missing positional arguments, and then missing keyword-only arguments.

  It also raises whatever the user code that binding runs raises: a keyword's `__eq__` and the
  truth test of its result, the keyword's `__hash__` when the `**kw` dict stores it, and the
  keyword's `__str__` when CPython formats an error message. -/
  calls insn bindArgs (args kwargs defaults : Value) (nPosOnly nPos : Int) (varPos varKw : Bool)
    (*names : String) (^err (exc : Value)) : Value
  /-- The value `moduleName.name` refers to. -/
  insn qualifiedRef (moduleName name : String) (^err (exc : Value)) : Value
  /-- The built-in `AssertionError` class, even if `builtins.AssertionError` is rebound:
  CPython's `LOAD_ASSERTION_ERROR`. -/
  pure insn assertionError : Value
  /-- A callable: `code`, a pointer to a translated function that takes the `cells`, of the
  types `cs`, then `args` and `kwargs`, and the cells it captures, one operand each.  Late
  binding reads a captured cell; a module-level function captures none.  `call` is its
  `apply`.  It reads the module's `__name__`, the function's `__module__`. -/
  reads insn mkClosure [(cs : list)] (code : Fn [*cs, Value, Value] failing) (*cells : cs) : Value
  /-- `obj.name`. -/
  calls insn attr (obj : Value) (name : String) (^err (exc : Value)) : Value
  /-- `obj.name = val`. -/
  insn setAttr (obj : Value) (name : String) (val : Value) (^err (exc : Value)) : Unit
  /-- `del obj.name`. -/
  insn delAttr (obj : Value) (name : String) (^err (exc : Value)) : Unit

  -- Globals and imports.  A module name is always fully qualified, such as `"a.b"`.

  /-- The cell of the global `name` of `module`: the same cell for the same arguments,
  written with `refSet` as a local is.  It holds `undef` until its first assignment, and
  `del` writes `undef` back.  A name read is `loadGlobal`; `del` reads the cell with `refGet`
  and `requireDefined`. -/
  pure insn globalCell (module name : String) : cell
  /-- Read the global `name` of `module`, as CPython's `LOAD_GLOBAL` does: the value of
  `globalCell module name` if it is defined, else the entry `name` of the `builtins` module's
  dict (a module that rebinds `__builtins__` is not modelled).  Raises
  `NameError(f"name '{name}' is not defined")` if neither exists.  The lookup in the
  `builtins` dict may run a key's `__eq__`. -/
  calls insn loadGlobal (module name : String) (^err (exc : Value)) : Value
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
  calls insn add (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs - rhs`. -/
  calls insn sub (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs * rhs`. -/
  calls insn mult (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs / rhs`. -/
  calls insn div (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs // rhs`. -/
  calls insn floorDiv (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs % rhs`. -/
  calls insn mod (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs ** rhs`. -/
  calls insn pow (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs @ rhs`. -/
  calls insn matMult (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs << rhs`. -/
  calls insn lShift (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs >> rhs`. -/
  calls insn rShift (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs & rhs`. -/
  calls insn bitAnd (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs | rhs`. -/
  calls insn bitOr (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs ^ rhs`. -/
  calls insn bitXor (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs += rhs`, as CPython's in-place `BINARY_OP`: `lhs.__iadd__(rhs)`, which may update
  `lhs` in place, or `lhs + rhs` if that is missing or returns `NotImplemented`.  The result
  is what `lhs` is rebound to. -/
  insn iAdd (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs -= rhs`, as `iAdd`. -/
  insn iSub (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs *= rhs`, as `iAdd`. -/
  insn iMult (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs @= rhs`, as `iAdd`. -/
  insn iMatMult (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs /= rhs`, as `iAdd`. -/
  insn iDiv (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs //= rhs`, as `iAdd`. -/
  insn iFloorDiv (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs %= rhs`, as `iAdd`. -/
  insn iMod (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs **= rhs`, as `iAdd`. -/
  insn iPow (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs <<= rhs`, as `iAdd`. -/
  insn iLShift (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs >>= rhs`, as `iAdd`. -/
  insn iRShift (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs &= rhs`, as `iAdd`. -/
  insn iBitAnd (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs |= rhs`, as `iAdd`. -/
  insn iBitOr (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs ^= rhs`, as `iAdd`. -/
  insn iBitXor (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `not operand`.  Raises, because it consults truthiness. -/
  calls insn not_ as "not" (operand : Value) (^err (exc : Value)) : Value
  /-- `-operand`. -/
  calls insn uSub (operand : Value) (^err (exc : Value)) : Value
  /-- `+operand`. -/
  calls insn uAdd (operand : Value) (^err (exc : Value)) : Value
  /-- `~operand`. -/
  calls insn invert (operand : Value) (^err (exc : Value)) : Value
  /-- `lhs == rhs`. -/
  calls insn eq (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs != rhs`. -/
  calls insn notEq (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs < rhs`. -/
  calls insn lt (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs <= rhs`. -/
  calls insn ltE (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs > rhs`. -/
  calls insn gt (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs >= rhs`. -/
  calls insn gtE (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs is rhs`, which compares identity. -/
  pure insn is_ as "is" (lhs rhs : Value) : Value
  /-- `lhs is not rhs`. -/
  pure insn isNot (lhs rhs : Value) : Value
  /-- `lhs in rhs`. -/
  calls insn in_ as "in" (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `lhs not in rhs`. -/
  calls insn notIn (lhs rhs : Value) (^err (exc : Value)) : Value

  -- Data structures.

  /-- A dict from `kvs`, an even number of operands, keys and values alternating: CPython's
  `BUILD_MAP`.  The type rules do not catch an odd count.  Raises `TypeError` if a key is
  unhashable, or whatever its `__hash__` or `__eq__` raises. -/
  calls insn mkDict (*kvs : Value) (^err (exc : Value)) : Value
  /-- A call's keyword dict from `kvs`, an even number of operands, keys and values alternating,
  each key a `str` the translator supplies.  Total, unlike `mkDict`: hashing and comparing a
  `str` runs no user code. -/
  pure insn mkKwargs (*kvs : Value) : Value
  /-- A list of `elems`. -/
  pure insn mkList (*elems : Value) : Value
  /-- A set of `elems`: CPython's `BUILD_SET`.  Raises as `mkDict` does for a key. -/
  calls insn mkSet (*elems : Value) (^err (exc : Value)) : Value
  /-- A tuple of `elems`. -/
  pure insn mkTuple (*elems : Value) : Value
  /-- `obj[key]`. -/
  calls insn getItem (obj key : Value) (^err (exc : Value)) : Value
  /-- `obj[key]`, or `fallback` if that raises `KeyError`, as CPython's `LOAD_NAME` reads a
  namespace (`PyMapping_GetOptionalItem` since 3.13). -/
  calls insn getOptionalItem (obj key fallback : Value) (^err (exc : Value)) : Value
  /-- `obj[key] = val`. -/
  insn setItem (obj key val : Value) (^err (exc : Value)) : Unit
  /-- `del obj[key]`. -/
  insn delItem (obj key : Value) (^err (exc : Value)) : Unit
  /-- `slice(lo, hi, step)`: CPython's `BUILD_SLICE`, for a slice that is not the whole
  subscript, as in `obj[lo:hi, k]`.  An absent bound is `None`. -/
  pure insn mkSlice (lo hi step : Value) : Value
  /-- `obj[lo:hi:step]`.  An absent bound is `None`, as in Python. -/
  calls insn getSlice (obj lo hi step : Value) (^err (exc : Value)) : Value
  /-- The elements of `val` as a tuple of exactly `n`: CPython's `UNPACK_SEQUENCE`.  Reads at
  most `n + 1` elements.  Raises `ValueError` if `val` has fewer or more than `n`, `TypeError`
  if it is not iterable, and whatever iterating `val` raises. -/
  insn unpackSeq (val : Value) (n : Int) (^err (exc : Value)) : Value
  /-- The elements of `val` for a target with a starred element: CPython's `UNPACK_EX`.  One
  tuple of `before + 1 + after` items: the first `before` elements, then a list of the
  elements between, then the last `after` elements.  Reads all of `val`.  Raises `ValueError`
  if `val` has fewer than `before + after` elements, `TypeError` if it is not iterable, and
  whatever iterating `val` raises. -/
  insn unpackEx (val : Value) (before after : Int) (^err (exc : Value)) : Value
  /-- A tuple of the elements of `list`, a list the emitting code made: CPython's
  `INTRINSIC_LIST_TO_TUPLE`, which ends a tuple display or call with a `*x`. -/
  reads insn listToTuple (list : Value) : Value
  /-- The positional arguments of `callee(*iterable)`: `tuple(iterable)`, as CPython's
  `CALL_FUNCTION_EX` makes them when `*iterable` is the only positional argument.  Raises a
  `TypeError` naming `callee` if `iterable` is not iterable. -/
  insn argsTuple (callee iterable : Value) (^err (exc : Value)) : Value
  /-- `tup[i]`, for a `tup` that is exactly a tuple and an `i` in range, such as an element of
  `unpackSeq`'s result. -/
  pure insn tupleGet (tup : Value) (i : Int) : Value
  /-- The dict `dict` with `other` merged in, as a fresh dict: the lowering of a `**x` argument.
  CPython's `DICT_MERGE`: a key already present raises a `TypeError` naming `callee`, as does
  an `other` that is not a mapping. -/
  calls insn dictMerge (callee dict other : Value) (^err (exc : Value)) : Value
  /-- The dict `dict` with `other` merged in, as a fresh dict: the lowering of a `**x` entry in a
  dict display.  CPython's `DICT_UPDATE`: a key already present is overwritten. -/
  calls insn dictUpdate (dict other : Value) (^err (exc : Value)) : Value

  -- Accumulating into a container the emitting code made.

  /-- Appends `value` to `list` in place: CPython's `LIST_APPEND`.  Total: `list` is one the
  emitting code made, such as a comprehension's accumulator. -/
  insn listAppend (list value : Value) : Unit
  /-- Appends the elements of `iterable` to the list `list` in place: CPython's `LIST_EXTEND`, for
  a `*x` element.  Raises `TypeError` if `iterable` is not iterable, or whatever iterating it
  raises. -/
  insn listExtend (list iterable : Value) (^err (exc : Value)) : Unit
  /-- Adds `value` to the set `set` in place: CPython's `SET_ADD`.  Raises `TypeError` if `value`
  is unhashable. -/
  insn setAdd (set value : Value) (^err (exc : Value)) : Unit
  /-- Adds the elements of `iterable` to the set `set` in place: CPython's `SET_UPDATE`, for a
  `*x` element.  Raises as `listExtend` and `setAdd` do. -/
  insn setUpdate (set iterable : Value) (^err (exc : Value)) : Unit
  /-- Stores `value` under `key` in the dict `dict`, in place: CPython's `MAP_ADD`.  Raises
  `TypeError` if `key` is unhashable. -/
  insn dictSet (dict key value : Value) (^err (exc : Value)) : Unit

  -- Iteration.

  /-- `iter(obj)`. -/
  insn getIter (obj : Value) (^err (exc : Value)) : Value
  /-- The next element of `iter`.  Exhaustion raises `StopIteration`, so a `for` loop's exit
  edge is `next`'s `err` successor, to a block that tests it with `isStopIteration`. -/
  insn next (iter : Value) (^err (exc : Value)) : Value
  /-- Whether `exc` is a `StopIteration`, as the `Bool` a `branch` takes: the guard that
  selects a loop's exit edge. -/
  reads insn isStopIteration (exc : Value) : Bool
  /-- Runs `body` once per element of `iterable`, in order, as a comprehension's `for` clause
  does: `iter(iterable)`, then `next` until it raises `StopIteration`.  An exception from
  `iter` or `next`, or one `body` returns as `error`, ends the loop and goes to `err`. -/
  insn forEach (iterable : Value) (&body (item : Value) : raising Unit) (^err (exc : Value)) :
    Unit

  -- Exceptions.

  /-- The exception `raise val` raises, as CPython's `RAISE_VARARGS` makes it: `val` if it is
  an exception, or `val()` if it is an exception class, with its `__context__` set as the
  module docstring describes.  Raises `TypeError: exceptions must derive from BaseException`
  otherwise, a `TypeError` if `val()` returns a non-exception, or whatever `val()` raises. -/
  insn toException (val : Value) (^err (e : Value)) : Value
  /-- `raise exc from cause`, for the exception `exc` that `toException` returned: sets
  `exc.__cause__` to `cause`, or to `cause()` if it is an exception class, and
  `exc.__suppress_context__` to `True`.  A `None` cause clears `__cause__`.  Raises
  `TypeError: exception causes must derive from BaseException` for any other `cause`, as CPython
  does, or whatever `cause()` raises.  Unlike CPython, which sets the cause before the context, a
  failure here leaves `exc` with the `__context__` that `toException` set. -/
  insn setCause (exc cause : Value) (^err (e : Value)) : Unit
  /-- Makes the exception `exc` the exception being handled, and returns the one handled before,
  or `None`: CPython's `PUSH_EXC_INFO`, on entering an `except` handler or a `with`'s exception
  path. -/
  insn pushExcInfo (exc : Value) : Value
  /-- On entering a `finally` body: if `pending` is a `raise` completion, makes its exception
  the one being handled, as CPython's `PUSH_EXC_INFO` does on the exceptional path; otherwise
  leaves the exception being handled as it is.  Returns the one handled before, or `None`. -/
  insn pushPending (pending : Completion) : Value
  /-- Makes `prev`, which `pushExcInfo` or `pushPending` returned, the exception being handled
  again: CPython's `POP_EXCEPT`, on every way out of an `except` handler, a `finally` body or
  a `with`'s exception path. -/
  insn popExcept (prev : Value) : Unit
  /-- The exception being handled, which a bare `raise` raises again: CPython's
  `RAISE_VARARGS 0`.  Raises `RuntimeError: No active exception to reraise` if there is
  none. -/
  reads insn handledExc (^err (e : Value)) : Value
  /-- Whether the exception `exc` matches `except type`, as the `Bool` a `branch` takes:
  CPython's `CHECK_EXC_MATCH`.  `type` is an exception class or a tuple of them.  Raises
  `TypeError: catching classes that do not inherit from BaseException is not allowed`
  otherwise. -/
  calls insn excMatch (exc type : Value) (^err (e : Value)) : Bool

  -- `with`: CPython's `BEFORE_WITH`, in its order, and `WITH_EXCEPT_START`.
  /-- `mgr`'s `__enter__`, looked up on its type and bound to it.  Raises `TypeError: 'T'
  object does not support the context manager protocol` if there is none. -/
  calls insn enterMethod (mgr : Value) (^err (exc : Value)) : Value
  /-- `mgr`'s `__exit__`, looked up on its type and bound to it.  Raises `TypeError: 'T'
  object does not support the context manager protocol (missed __exit__ method)` if there is
  none. -/
  calls insn exitMethod (mgr : Value) (^err (exc : Value)) : Value
  /-- `exit(type(exc), exc, exc.__traceback__)`, with `exit` the bound `__exit__` of a `with`
  whose body raised `exc`.  Raises whatever `__exit__` raises. -/
  insn exitWithExc (exit exc : Value) (^err (e : Value)) : Value

  -- Strings and degradation.

  /-- `repr(val)`, without looking up the builtin: an f-string's `!r` (`FORMAT_VALUE`). -/
  calls insn repr (val : Value) (^err (exc : Value)) : Value
  /-- `str(val)`, without looking up the builtin: an f-string's `!s`. -/
  calls insn toStr as "str" (val : Value) (^err (exc : Value)) : Value
  /-- `ascii(val)`, without looking up the builtin: an f-string's `!a`. -/
  calls insn ascii (val : Value) (^err (exc : Value)) : Value
  /-- `format(val, spec)`, without looking up the builtin: an f-string field after its
  conversion (`FORMAT_VALUE`).  Raises what `__format__` raises, or `TypeError` if it does
  not return a `str`. -/
  calls insn fmtValue (val spec : Value) (^err (exc : Value)) : Value
  /-- The concatenation of `parts`, each a `str`: CPython's `BUILD_STRING`.  Total: joining
  `str`s runs no user code. -/
  pure insn strConcat (*parts : Value) : Value
  /-- A stand-in for a construct the translator does not handle. -/
  insn unsupported (name : Value) : Value

  -- Contracts: the arguments of a call.  `args` and `kwargs` are a function's parameters.

  /-- The value that a call binds to the parameter `name` at position `pos`.  It is `args[pos]` if
  `args` is exactly a tuple and `0 ≤ pos < len(args)`.  Otherwise it is the value of the key of
  `kwargs` that is exactly a `str` with the characters of `name`, if `kwargs` is exactly a dict
  with such a key.  Otherwise it is `default`.  So an `args` that is not exactly a tuple counts
  as empty, and so does a `kwargs` that is not exactly a dict.  `pos` is `-1` for a keyword-only
  parameter.  When `bindsTo` holds for the same `args` and `kwargs`, with `name` at position
  `pos` of its names (or among its keyword-only names if `pos` is -1), this is the value that
  CPython binds. -/
  reads insn argOf (args kwargs : Value) (pos : Int) (name : String) (default : Value) : Value
  /-- A new dict of the entries of `kwargs`, in their order, less those whose key is exactly a
  `str` equal to one of `names`.  When `bindsTo` holds for the same `kwargs` and `names`, with
  `varKw` true, it is the dict that CPython binds to the `**kw` parameter.  Empty if `kwargs` is
  not exactly a dict. -/
  reads insn extraKwargs (kwargs : Value) (*names : String) : Value
  /-- Whether binding `args` and `kwargs` to the parameters `names` raises none of these
  `TypeError`s: a parameter given both by position and by keyword, an unexpected keyword when
  there is no `**kw` parameter, or too many positional arguments.  The first `nPos` names are
  positional-or-keyword, and the others keyword-only.  There is no `*args` parameter, and there
  is a `**kw` parameter exactly when `varKw` is true.  It holds exactly when:
  * `args` is exactly a tuple, `kwargs` is exactly a dict, and every key of `kwargs` is exactly a
    `str`;
  * `nPos` is between 0 and the number of `names`, and `args` has at most `nPos` elements;
  * no key of `kwargs` has the characters of a name that an element of `args` binds;
  * if `varKw` is false, every key of `kwargs` has the characters of one of `names`.
  A missing argument is not tested here: `isDefined` of an `argOf` whose default is `undef`
  tests it. -/
  reads insn bindsTo (args kwargs : Value) (nPos : Int) (varKw : Bool) (*names : String) : Bool

  -- Contracts: tests.

  /-- The class that the standard module `module` defines as `name`, such as `builtins.int` or
  `collections.abc.Sequence`, whatever the program rebinds: the class that the first run of the
  body of the module that defines it created.  A program may run that body again, as
  `importlib.reload` does, or as an import does after the module was removed from `sys.modules`.
  That run creates a new class with the same name, and an object of either class is not an
  instance of the other.  A region that applies `stdClass` after such a run, or to a name that
  CPython 3.12's standard library does not define as a class, is not well defined. -/
  pure insn stdClass (module name : String) : Value
  /-- `isinstance(v, cls)`, without looking up the builtin.  `cls` may be a class, a tuple of
  classes, or a union such as `int | str`.  It reads `v.__class__`, which may run user code, such
  as a `__class__` property: `isinstance(Mock(spec=int), int)` is true.  A metaclass's
  `__instancecheck__` may run too.  It gives what `isinstance` gives in the current state, the
  caches of `ABCMeta`'s checks included, but it does not fill those caches.  Raises what
  `isinstance` raises, such as `TypeError` for a TypedDict class or `list[int]`. -/
  calls insn isInstance (v cls : Value) (^err (exc : Value)) : Bool
  /-- Whether `type(v)`, the object's own type and not `v.__class__`, is `cls` or a subclass of it,
  by its MRO or by a registration or a `__subclasshook__` that CPython 3.12's standard library
  defines, such as `list` for `collections.abc.Sequence`.  The MRO is the one that CPython stores
  for the type, which `type.__dict__["__mro__"].__get__(type(v))` gives.  `typeIsSubclass` evaluates
  the MRO and the standard library's hooks over the stored MRO.  It never runs a metaclass's
  `__mro__` property, which `isinstance` runs through such a hook.  A registration or a hook that
  the program makes does not count, the caches of `ABCMeta`'s checks are neither read nor filled,
  and no user code runs.  `cls` is a class or a flat tuple of classes.  It checks every element
  first, and raises `TypeError` for anything else, such as a union, a nested tuple, or a tuple with
  an element that is not a class; the text of the message is not specified.  This is stricter than
  `issubclass`, which accepts nested tuples and stops at the first match:
  `issubclass(int, (int, 5))` is true.  It ignores `v.__class__` and the program's registrations
  and hooks, so `typeIsSubclass(Mock(spec=int), int)` is false.  It does not imply
  `isinstance(v, cls)`: a metaclass's `__instancecheck__` or `__mro__` property, a program's
  `__subclasshook__`, a `__class__` that raises, or an ABC's cache can make `isinstance` false or
  make it raise. -/
  reads insn typeIsSubclass (v cls : Value) (^err (exc : Value)) : Bool
  /-- `len(v)`, without looking up the builtin: a Python `int`.  Raises what `len` raises, such as
  `TypeError` if `v` has no `__len__`, or `ValueError` if `__len__` returns a negative number. -/
  calls insn len (v : Value) (^err (exc : Value)) : Value
  /-- Whether `re.search(pattern, s)` finds a match, with the standard library's `re.search`,
  whatever the program rebinds, and `pattern` in the syntax of Python's `re` module.  It does not
  use the cache of compiled patterns of `re`.  It first compiles `pattern`, and if that fails, it
  raises what `re.compile(pattern)` raises, whatever `s` is: `re.error` for most invalid patterns,
  `ValueError` for incompatible flags such as `(?a)(?u)`, or `OverflowError` for a repetition count
  that is too large.  Otherwise it raises `TypeError` if `s` is not a `str`, and it searches the
  characters of `s`, a `str` or an instance of a subclass of `str`, without running user code.  A
  region that applies it is not well defined in three cases.  Compiling `pattern` emits a warning,
  such as the `FutureWarning` of `"[[a]"`: the warning filters decide whether the warning is raised,
  and the program's `warnings.showwarning` may run.  Compiling `pattern` raises `RecursionError`,
  which depends on the depth of the call stack.  Or `s` is not a `str`, and its class or a base of
  it defines `__buffer__` in Python (PEP 688): CPython runs that method. -/
  reads insn reSearch (pattern : String) (s : Value) (^err (exc : Value)) : Bool
  /-- Whether `v` is exactly a `str`, not an instance of a subclass, with the characters of one
  of `lits`.  It runs no user code.  It implies `v == lits[0] or v == lits[1] or …`, since `==`
  on two `str`s compares their characters. -/
  pure insn strIsOneOf (v : Value) (*lits : String) : Bool
  /-- Whether `v` is exactly an `int`, so neither a `bool` nor an instance of another subclass,
  whose value is one of `lits`.  It implies `v == lits[0] or v == lits[1] or …`. -/
  pure insn intIsOneOf (v : Value) (*lits : Int) : Bool
  /-- Whether the type of `v` is exactly `int`, `float`, `complex`, `bool`, `str`, `bytes` or
  `NoneType`, not a subclass.  Such an object holds no mutable state and no other object, its
  type never changes, and its type's attributes, such as `__eq__`, cannot be changed.  It runs no
  user code. -/
  pure insn isImmutableScalar (v : Value) : Bool
  /-- Whether `d` is exactly a dict whose keys are all exactly `str`s, each with the characters
  of one of `keys`.  False for anything else. -/
  reads insn dictKeysWithin (d : Value) (*keys : String) : Bool

  -- Contracts: bounded quantifiers.

  /-- Whether `body` returns `ok(true)` for every member of `c`.  The members are the objects
  that `c` stores, by identity, read from its own storage: the elements of a `list`, `tuple`,
  `set` or `frozenset`, or the keys of a `dict`, instances of their subclasses included.  A
  subclass that changes how it iterates or reads its members, such as by overriding `__iter__`,
  `items` or `__getitem__`, is still quantified over its storage.  If `body`
  returns an `error` for some member, `allIn` raises the error of the first such member, in
  `c`'s order, whatever the other members give.  Raises `TypeError` for any other `c`, such as a
  `str` or a `range`; the text of the message is not specified. -/
  reads insn allIn (c : Value) (&body (x : Value) : raising Bool) (^err (exc : Value)) : Bool
  /-- Whether `body` returns `ok(true)` for some member of `c`, with the members of `allIn`.  It
  raises as `allIn` does. -/
  reads insn anyIn (c : Value) (&body (x : Value) : raising Bool) (^err (exc : Value)) : Bool
  /-- Whether `body` returns `ok(true)` for every entry, key `k` and value `v`, of the dict `d`,
  an instance of a subclass included, read from its own storage.  It raises the `error` of
  `body` as `allIn` does, and raises `TypeError` if `d` is not a dict; the text of the message
  is not specified. -/
  reads insn allItems (d : Value) (&body (k v : Value) : raising Bool) (^err (exc : Value)) :
    Bool
  /-- Whether `body` returns `ok(true)` for some entry of `d`, with the entries of `allItems`.  It
  raises as `allItems` does. -/
  reads insn anyItems (d : Value) (&body (k v : Value) : raising Bool) (^err (exc : Value)) :
    Bool

  -- Contracts: locations, which a frame computes at the call.

  /-- The attribute `name` of `obj`, whether it is set or not, wherever `obj` stores it, such as
  its `__dict__`, a slot, or a field of a built-in base class (an exception's `args`).  An
  attribute in the `__dict__` is the entry of the dict that is `obj`'s `__dict__` when `attrLoc`
  runs, so `attrLoc(o, "k")` and `itemLoc(vars(o), "k")` are one location.  `__dict__` is an
  attribute too.  The attributes of a module are the contents of its global cells
  (`globalCell`). -/
  reads insn attrLoc (obj : Value) (name : String) : Loc
  /-- The entry for the key `key` of the dict `obj`, an instance of a subclass included, whether
  it is present or not.  It covers every entry of `obj` whose key's hash, as the dict stored it
  when it added the key, is the hash of `key`, whatever the key's type, since `obj[key] = v`
  updates an equal key of any type.  The location
  also holds the entry's place in each order that the dict keeps (an `OrderedDict` keeps two):
  changing the entry may move it, and the other entries keep their order among themselves.  A
  region that applies `itemLoc` to an object whose type is not `dict` or a subclass of it is not
  well defined. -/
  pure insn itemLoc (obj : Value) (key : String) : Loc
  /-- Every location of `obj`: its attributes, as `attrLoc` gives them, its entries or elements,
  its class if `__class__` can be assigned, and any other state it has, such as an iterator's
  position or the buffer of an `io.BytesIO`. -/
  reads insn objLoc (obj : Value) : Loc
  /-- Every location, other than a `__class__`, of `obj` and of every object that `obj` reaches at
  the call.  From an object that is neither a class nor a module, it reaches every object that the
  object stores: the values of its attributes that are locations (those in its `__dict__`, in a
  slot, or in a built-in field that can be set, such as `args` or `__defaults__`), and the elements,
  keys and values that it stores, its internal state included, such as a deque's elements.  It holds
  no attribute of a class or a module, however it is reached, such as an entry of a module's
  `__dict__` or of a class's namespace, and it reaches nothing further from them.  A field that
  cannot be set, such as a function's `__globals__` or `__closure__`, is not a location, and it is
  not followed.  A closure cell's `cell_contents` is not an attribute here either: the IR holds a
  cell's contents in a `base.Ref`, whose location is `base.cellLoc`, and `reachLoc` neither holds
  that location nor follows it. -/
  reads insn reachLoc (obj : Value) : Loc
  /-- Every attribute, other than `__class__`, of every object that is neither a class nor a module,
  and `reachLoc` of the value of each such attribute, at the call.  A closure cell's `cell_contents`
  is not such an attribute (see `reachLoc`), so `instanceState` holds no cell. -/
  reads insn instanceState : Loc
  end py

namespace Py

/-- `py.<s>`, the name of a declaration in Python's namespace. -/
public abbrev pn (s : String) : Name := .str (.str .base "py") s

end Py

end StrataPython.Dyn
