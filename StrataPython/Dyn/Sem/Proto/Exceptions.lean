/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Attrs

set_option autoImplicit false

/-!
# Exceptions and `with`

Generic over the record of primitives, CPython 3.12's raising and catching of exceptions:

* `toException val`, `RAISE_VARARGS`' `do_raise`: an exception instance as it is, an exception
  class called with no arguments, else `TypeError`; then `_PyErr_SetObject`'s implicit chaining
  (`chainContext`), which makes the exception being handled its `__context__` and cuts a link of
  that exception's `__context__` chain that would close a cycle;
* `setCauseOf exc cause`, the `from` clause: `__cause__` and `__suppress_context__`;
* `excMatches exc type`, `CHECK_EXC_MATCH`, with CPython's `TypeError` for a class that is not an
  exception class;
* `enterOf mgr` and `exitOf mgr`, `BEFORE_WITH`'s lookups of `__enter__` and `__exit__` on the
  type, bound to `mgr`, with CPython's two messages.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- `BaseException`, the class of every exception. -/
def baseException [PyPure m V] : V := PyPure.imm (m := m) (.builtin .BaseException)

/-- Whether `v` is an exception: an instance of `BaseException` or of a subclass of it. -/
def isException [PyReads m V] (v : V) : m Bool := do
  if (← PyPure.immView v).isSome || (← PyPure.isUndef v) then return false
  isSubclass (← PyReads.classOf v) (baseException (m := m))

/-- Whether `c` is an exception class: `BaseException` or a subclass of it. -/
def isExceptionClass [PyReads m V] (c : V) : m Bool := do
  if !(← isType c) then return false
  isSubclass c (baseException (m := m))

/-- The state of the exception `e`. -/
def excData [PyReads m V] (e : V) : m (ExcData V) := do
  let some (.exc d) ← PyReads.objView e | PyPure.gap "the state of a value that is not an exception"
  pure d

/-- CPython's `type_repr` of the class `c`: `<class 'module.qualname'>`, or `<class 'tp_name'>`
when the module is `builtins` or not a `str`. -/
def typeRepr [PyReads m V] (c : V) : m String := do
  match ← PyPure.immView c with
  | some (.builtin b) =>
    let mo := b.info.module
    return if mo == "builtins" then s!"<class '{b.info.qualname}'>" else s!"<class '{mo}.{b.info.qualname}'>"
  | _ =>
    match ← classData? c with
    | some cd =>
      let tpName := cd.tpName.getD cd.name
      let some mv ← dictFindStr cd.ns "__module__" | return s!"<class '{tpName}'>"
      match ← strArg? "a class __module__" mv with
      | some mo => return if mo == "builtins" then s!"<class '{tpName}'>" else s!"<class '{mo}.{cd.qualname}'>"
      | none => return s!"<class '{tpName}'>"
    | none => PyPure.gap "the repr of a value that is not a class"

/-- `repr(c)` of the class `c` in a message, `typeRepr`.  A metaclass other than `type` stops with
a gap, since its `__repr__` may run code. -/
def classRepr [PyReads m V] (c : V) : m String := do
  if (← PyPure.immView c).isNone then
    if !((← PyPure.immView (← PyReads.classOf c)) matches some (.builtin .type)) then
      PyPure.gap "the repr of a class whose metaclass is not type is not modelled yet"
  typeRepr c

/-- The `__context__` of the exception `o`, `none` for `None`. -/
def contextOf? [PyReads m V] (o : V) : m (Option V) := do
  let c := (← excData o).context
  if (← PyPure.immView c) matches some .none then return none
  return some c

/-- `_PyErr_SetObject`'s cut of the `__context__` chain from `o` on: the first exception of the
chain whose `__context__` is `e` loses it, so that no cycle forms; a chain that is already a cycle
is walked once, by Floyd's algorithm with CPython's `slow` pointer and toggle. -/
def cutCycle [PyWrites m V] (e : V) : Nat → V → V → Bool → m Unit
  | 0, _, _, _ => PyPure.gap "a __context__ chain longer than the model follows"
  | fuel + 1, o, slow, toggle => do
    let some ctx ← contextOf? o | return
    if (← PyPure.identical ctx e) == .yes then
      return ← PyWrites.excSet o (.context (PyPure.imm (m := m) .none))
    if (← PyPure.identical ctx slow) == .yes then return
    let slow' ← if toggle then (do pure ((← contextOf? slow).getD slow)) else pure slow
    cutCycle e fuel ctx slow' (!toggle)

/-- **`_PyErr_SetObject`'s implicit chaining** of the raised exception `e`: the exception being
handled, if any and other than `e`, becomes `e.__context__`, after the cut of its chain
(`cutCycle`); with none being handled, `e.__context__` stays as it is. -/
def chainContext [PyWrites m V] (e : V) : m Unit := do
  let h ← PyReads.handled
  if (← PyPure.immView h) matches some .none then return
  if (← PyPure.identical h e) == .yes then return
  cutCycle e walkFuel h h false
  PyWrites.excSet e (.context h)

/-- A gap if the metaclass of the class `c` has its own `__subclasscheck__`: `_PyErr_SetObject`
asks it (`PyObject_IsSubclass`) whether the raised exception's class is `c`'s subclass, and calls
`c` again on the exception when it says no. -/
def subclassCheckGap [PyReads m V] (c : V) : m Unit := do
  if let some f ← lookupType (← PyReads.classOf c) "__subclasscheck__" then
    unless (← PyPure.immView f) matches some (.descr .type "__subclasscheck__" _) do
      PyPure.gap "a raise of an exception whose class's metaclass defines __subclasscheck__ is not modelled yet"

/-- **`raise val`**, CPython's `do_raise` and `_PyErr_SetObject`: the exception that it raises,
with its `__context__` chained (`chainContext`) and its traceback set. -/
def toException [PyWrites m V] (val : V) : m V := do
  subclassCheckGap (← if ← isExceptionClass val then pure val else PyReads.classOf val)
  let e ← if ← isException val then pure val
    else if ← isExceptionClass val then do
      let r ← callN dispatchDepth val (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
      if !(← isException r) then
        raiseBuiltin "TypeError"
          s!"calling {← classRepr val} should have returned an instance of BaseException, not {← classRepr (← PyReads.classOf r)}"
      -- `_PyErr_SetObject` calls the class again on an exception of another class.
      if !(← isSubclass (← PyReads.classOf r) val) then
        PyPure.gap "an exception class whose call gives an exception of another class is not modelled yet"
      pure r
    else raiseBuiltin "TypeError" "exceptions must derive from BaseException"
  chainContext e
  PyWrites.excSet e (.traceback (PyPure.imm (m := m) .traceback))
  pure e

/-- **`raise exc from cause`**, after `toException`: `exc.__cause__` is `cause`, an exception or
`None`, and `__suppress_context__` becomes true. A cause that is an exception class, or neither
an exception nor `None`, stops with a gap. -/
def setCauseOf [PyWrites m V] (exc cause : V) : m Unit := do
  -- CPython makes and checks the cause before it chains `exc`'s context, which `toException`
  -- has already done: a call of the cause, or its `TypeError`, would see the other order.
  if (← isExceptionClass cause) ||
      !((← isException cause) || (← PyPure.immView cause) matches some .none) then
    PyPure.gap "a cause that is a class or not an exception is not modelled yet"
  PyWrites.excSet exc (.cause cause)

/-- **`except type`**, CPython's `CHECK_EXC_MATCH`: `TypeError` unless `type` is an exception class
or a tuple of them; then whether the class of `exc` is a subclass of it, or of one of them. -/
def excMatches [PyReads m V] (exc type : V) : m Bool := do
  let msg := "catching classes that do not inherit from BaseException is not allowed"
  let classes ← match ← PyPure.immView type with
    | some (.tuple ts) => pure ts
    | some _ => pure #[type]
    | none =>
      if ← isSubclass (← PyReads.classOf type) (PyPure.imm (m := m) (.builtin .tuple)) then
        PyPure.gap "except with an instance of a subclass of tuple is not modelled yet"
      pure #[type]
  for c in classes do
    if !(← isExceptionClass c) then raiseBuiltin "TypeError" msg
  let t ← PyReads.classOf exc
  for c in classes do
    if ← isSubclass t c then return true
  return false

/-- `mgr`'s special method `name` looked up on its type and bound to it, or `TypeError` with the
message `msg` about the type. -/
def withMethod [PyCalls m V] (mgr : V) (name : String) (msg : String → String) : m V := do
  let t ← PyReads.classOf mgr
  let some f ← lookupType t name | raiseBuiltin "TypeError" (msg (← classNameOf t))
  descrGetN dispatchDepth f (some mgr) t

/-- `BEFORE_WITH`'s `__enter__` of `mgr`. -/
def enterOf [PyCalls m V] (mgr : V) : m V :=
  withMethod mgr "__enter__" fun t => s!"'{t}' object does not support the context manager protocol"

/-- `BEFORE_WITH`'s `__exit__` of `mgr`. -/
def exitOf [PyCalls m V] (mgr : V) : m V :=
  withMethod mgr "__exit__" fun t =>
    s!"'{t}' object does not support the context manager protocol (missed __exit__ method)"

/-- **`exit(type(exc), exc, exc.__traceback__)`**, `WITH_EXCEPT_START`'s call of the bound
`__exit__` of a `with` whose body raised `exc`. -/
def exitWithExc [PyCalls m V] (exit exc : V) : m V := do
  let d ← excData exc
  callN dispatchDepth exit (PyPure.imm (m := m) (.tuple #[← PyReads.classOf exc, exc, d.traceback]))
    (← PyPure.allocDict)


/-- Make `exc`, if any, the exception being handled, and give back the one handled before. -/
def pushHandled [PyWrites m V] (exc : Option V) : m V := do
  let prev ← PyReads.handled
  if let some e := exc then PyWrites.setHandled e
  pure prev

/-- The exception being handled, for a bare `raise`; a raised `RuntimeError` when there is none. -/
def handledExc [PyReads m V] : m V := do
  let h ← PyReads.handled
  if (← PyPure.immViewAll h) matches some .none then
    raiseBuiltin "RuntimeError" "No active exception to reraise"
  pure h

end

end

end StrataPython.Dyn.Sem.Proto
