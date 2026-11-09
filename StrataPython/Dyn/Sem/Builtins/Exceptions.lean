/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Classes
public import StrataPython.Dyn.Sem.Proto.Exceptions

set_option autoImplicit false

/-!
# The built-in exception classes

Generic over the record, the bodies of CPython 3.12's `exceptions.c` for these classes:

* `BaseException.__new__` and `__init__` (`args`, with no keywords), `__str__` and `__repr__` (for
  zero, one or several arguments), and `add_note`;
* the `__init__` of `StopIteration` (`value`), `SystemExit` (`code`), `NameError` (the keyword
  `name`), `AttributeError` (`name`, `obj`) and `ImportError` (`msg`, `name`, `path`,
  `name_from`), and `KeyError.__str__` and `ImportError.__str__`;
* `OSError.__new__`, `__init__` and `__str__`, which parse `errno`, `strerror`, `filename` and
  `filename2` in `__new__`, or in `__init__` for a subclass that overrides `__init__` and not
  `__new__`; `OSError(2, "x")` is a `FileNotFoundError`;
* `BaseExceptionGroup.__new__` with CPython's checks, `message` and `exceptions`, and `__str__`.

A field that is never set is absent from the exception's fields, as CPython's `NULL`: it reads as
`None`, but `OSError.__str__` tells it apart from a field set to `None`. A `str` or a `repr` of an
argument other than `None`, a `bool`, an `int`, a `float` or a `str` stops with a gap, as does
`with_traceback`.
-/

namespace StrataPython.Dyn.Sem.Builtins

open Proto

@[expose] public section

/-- The exception class that the error number `n` names on Linux, CPython's `errnomap`. -/
def errnoClass : Int → Option Builtin
  | 11 | 114 | 115 => some .BlockingIOError
  | 10 => some .ChildProcessError
  | 32 | 108 => some .BrokenPipeError
  | 103 => some .ConnectionAbortedError
  | 111 => some .ConnectionRefusedError
  | 104 => some .ConnectionResetError
  | 17 => some .FileExistsError
  | 2 => some .FileNotFoundError
  | 21 => some .IsADirectoryError
  | 20 => some .NotADirectoryError
  | 4 => some .InterruptedError
  | 1 | 13 => some .PermissionError
  | 3 => some .ProcessLookupError
  | 110 => some .TimeoutError
  | _ => none

section
variable {m : Type → Type 1} {V : Type}

/-- `str(v)` of an argument whose `str` runs no protocol, else a gap. -/
def argStr [PyCalls m V] (v : V) : m String := do
  let some s ← plainStr? v | PyPure.gap "the str of an exception's argument of this type is not modelled yet"
  pure s

/-- The items of the `args` tuple of the exception `e`. -/
def excArgs [PyReads m V] (e : V) : m (Array V) := do tupleItems (← excData e).args

/-- **`BaseException.__new__(cls, *args, **kwargs)`**: a new exception of `cls` with `args`; the
keywords are `__init__`'s to check.  `cls` has passed `tp_new_wrapper`'s check, or a class call's
check that this is its `tp_new` (`Proto.tpNewFor`). -/
def baseExcNew [PyWrites m V] (_self args _kwargs : V) : m V := do
  let xs ← tupleItems args
  let some cls := xs[0]? | PyPure.gap "BaseException.__new__ without a class"
  if !(← isExceptionClass cls) then PyPure.gap "BaseException.__new__ of a class that is not an exception class"
  let some mro ← mroOf cls | PyPure.gap "a class without an MRO"
  let n ← slotCountOf mro.toList
  PyReads.allocInstance cls (.exc (xs.extract 1 xs.size)) #[] (Array.replicate n none)

/-- The name of the class of `self` in the messages of its `__init__`. -/
def excTypeName [PyReads m V] (self : V) : m String := do classNameOf (← PyReads.classOf self)

/-- `_PyArg_NoKeywords(Py_TYPE(self)->tp_name, kwargs)`. -/
def noKeywords [PyReads m V] (self kwargs : V) : m Unit := do
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" s!"{← excTypeName self}() takes no keyword arguments"

/-- **`BaseException.__init__(self, *args)`**: `args`; a keyword raises `TypeError`. -/
def baseExcInit [PyWrites m V] (self args kwargs : V) : m V := do
  noKeywords self kwargs
  PyWrites.excSet self (.args args)
  pure (PyPure.imm (m := m) .none)

/-- `StopIteration.__init__`: `value` is the first argument, else `None`. -/
def stopIterationInit [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| baseExcInit self args kwargs
  let xs ← tupleItems args
  PyWrites.excSet self (.field "value" (some (xs[0]?.getD (PyPure.imm (m := m) .none))))
  pure (PyPure.imm (m := m) .none)

/-- `SystemExit.__init__`: `code` is the argument, or the args tuple for several; with none, it
stays as it is. -/
def systemExitInit [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| baseExcInit self args kwargs
  match ← tupleItems args with
  | #[] => pure ()
  | #[x] => PyWrites.excSet self (.field "code" (some x))
  | _ => PyWrites.excSet self (.field "code" (some args))
  pure (PyPure.imm (m := m) .none)

/-- The `__init__` of `NameError`, `AttributeError` and `ImportError`: `args`, then the
keyword-only fields `names`, each unset unless given. More keywords than `names`, or another
keyword, raise CPython's `TypeError`s, which name the class of the C function, `cname`. -/
def keywordFieldsInit [PyWrites m V] (cname : String) (names : List String) (self args kwargs : V) :
    m V := do
  PyWrites.excSet self (.args args)
  let kws ← kwEntries kwargs
  let n := names.length
  if kws.size > n then
    raiseBuiltin "TypeError"
      s!"{cname}() takes at most {n} keyword argument{if n == 1 then "" else "s"} ({kws.size} given)"
  for (k, _) in kws do
    if !names.contains k then
      raiseBuiltin "TypeError" s!"'{k}' is an invalid keyword argument for {cname}()"
  for n in names do
    PyWrites.excSet self (.field n ((kws.find? (·.1 == n)).map (·.2)))
  pure (PyPure.imm (m := m) .none)

/-- `ImportError.__init__`: the keywords `name`, `path` and `name_from`, and `msg`, the argument
when there is exactly one, else unset. -/
def importErrorInit [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| keywordFieldsInit "ImportError" ["name", "path", "name_from"] self args kwargs
  let msg := match ← tupleItems args with
    | #[x] => some x
    | _ => none
  PyWrites.excSet self (.field "msg" msg)
  pure (PyPure.imm (m := m) .none)

/-- `str` of an exception from its arguments: `""`, the argument's `str`, or the tuple's `repr`. -/
def argsStr [PyCalls m V] (xs : Array V) : m String := do
  match xs with
  | #[] => pure ""
  | #[x] => argStr x
  | _ => return s!"({", ".intercalate (← xs.mapM checkRepr).toList})"

/-- **`BaseException.__str__`**. -/
def baseExcStr [PyWrites m V] (self _args _kwargs : V) : m V := do
  return PyPure.imm (m := m) (.str (.ofString (← argsStr (← excArgs self))))

/-- **`KeyError.__str__`**: the `repr` of a single argument, else `BaseException.__str__`. -/
def keyErrorStr [PyWrites m V] (self args kwargs : V) : m V := do
  match ← excArgs self with
  | #[x] => return PyPure.imm (m := m) (.str (.ofString (← checkRepr x)))
  | _ => baseExcStr self args kwargs

/-- The field `n` of the exception `e`, `none` if it is unset. -/
def excField [PyReads m V] (e : V) (n : String) : m (Option V) := do
  return ((← excData e).fields.find? (·.1 == n)).map (·.2)

/-- **`ImportError.__str__`**: `msg` if it is an exact `str`, else `BaseException.__str__`. -/
def importErrorStr [PyWrites m V] (self args kwargs : V) : m V := do
  if let some msg ← excField self "msg" then
    if (← PyPure.immView msg) matches some (.str _) then return msg
  baseExcStr self args kwargs

/-- **`BaseException.__repr__`**: the class's name, then `(arg)` for one argument or the args
tuple's `repr`. -/
def baseExcRepr [PyWrites m V] (self _args _kwargs : V) : m V := do
  let n ← excTypeName self
  let s ← match ← excArgs self with
    | #[] => pure s!"{n}()"
    | xs =>
      let parts ← xs.mapM checkRepr
      pure s!"{n}({", ".intercalate parts.toList})"
  return PyPure.imm (m := m) (.str (.ofString s))

/-- **`BaseException.add_note(note)`**: `__notes__` read with the attribute protocol, made a new
list and set with it if there is none, then the note appended, as CPython does. -/
def addNote [PyWrites m V] [PyNew m V] (self args kwargs : V) : m V := do
  let sig : BuiltinSig := { name := "add_note", qualname := "BaseException.add_note", style := .methO }
  let b ← bindBuiltinArgs sig args kwargs
  let #[some note] := b.params | PyPure.modelInvariant "add_note: the binder's assumption failed"
  if (← str? note).isNone then
    -- CPython accepts an instance of a subclass of `str`.
    userCheck note note
    raiseBuiltin "TypeError" s!"note must be a str, not '{← typeName note}'"
  addNoteTo self note
  pure (PyPure.imm (m := m) .none)

/-- The class whose C function is the `tp_init` of the built-in exception class `u`. -/
def excInitClass (u : Builtin) : Builtin :=
  ([Builtin.OSError, .ImportError, .BaseExceptionGroup, .StopIteration, .SystemExit, .NameError,
    .AttributeError, .SyntaxError, .UnicodeEncodeError, .UnicodeDecodeError,
    .UnicodeTranslateError].find? u.info.mro.contains).getD .BaseException

/-- The class whose C function the slot `__new__` or `__init__` that a lookup found (`v`) is, for
a built-in exception class's entry; `none` for any other value, such as a user function. -/
def excSlotOwner [PyPure m V] (v : V) (name : String) : m (Option Builtin) := do
  let owner (u : Builtin) : Option Builtin :=
    if !u.info.mro.contains .BaseException then none
    else if name == "__new__" then some (excNewClass u) else some (excInitClass u)
  match ← PyPure.immView v with
  | some (.descr u n _) => pure (if n == name then owner u else none)
  | some (.bound _ u n _) => pure (if n == name then owner u else none)
  | _ => pure none

/-- CPython's `oserror_use_init(cls)`: `cls`'s `tp_init` is not `OSError`'s, and its `tp_new` is
(`tpNewOf`), so that `OSError.__init__` parses the arguments. -/
def osErrorUseInit [PyReads m V] (cls : V) : m Bool := do
  let some i ← lookupType cls "__init__" | return false
  let iOwner ← excSlotOwner i "__init__"
  let newIsOSError := match ← tpNewOf tpNewFuel cls with
    | .builtin b => b.newId == some .OSError
    | .slot _ => false
  return iOwner != some .OSError && newIsOSError

/-- CPython's `oserror_parse_args`: `errno`, `strerror`, `filename`, `winerror` (ignored, as on
Linux) and `filename2`, for two to five arguments. -/
def osErrorParse (xs : Array V) : Option V × Option V × Option V × Option V :=
  if 2 ≤ xs.size && xs.size ≤ 5 then (xs[0]?, xs[1]?, xs[2]?, xs[4]?) else (none, none, none, none)

/-- CPython's `oserror_init` of the exception `e` of the class `cls`, from the arguments `xs`:
`filename` and `filename2` when they are not `None` (`args` then keeps the first two items),
`errno` and `strerror` as parsed. A number as `BlockingIOError`'s third argument, its
`characters_written`, stops with a gap. -/
def osErrorFill [PyWrites m V] (e cls : V) (xs : Array V) : m Unit := do
  let (en, se, f, f2) := osErrorParse xs
  let isNone (v : V) : m Bool := do pure ((← PyPure.immView v) matches some .none)
  let mut args := PyPure.imm (m := m) (.tuple xs)
  if let some f := f then
    if !(← isNone f) then
      if (← PyPure.immView cls) matches some (.builtin .BlockingIOError) then
        if !((← PyPure.immView f) matches some (.str _) || (← PyPure.immView f) matches some (.bytes _)) then
          PyPure.gap "BlockingIOError's characters_written is not modelled yet"
      PyWrites.excSet e (.field "filename" (some f))
      if let some f2 := f2 then
        if !(← isNone f2) then PyWrites.excSet e (.field "filename2" (some f2))
      if 2 ≤ xs.size && xs.size ≤ 5 then args := PyPure.imm (m := m) (.tuple (xs.extract 0 2))
  PyWrites.excSet e (.field "errno" en)
  PyWrites.excSet e (.field "strerror" se)
  PyWrites.excSet e (.args args)

/-- **`OSError.__new__(cls, *args)`**, CPython's `OSError_new`: unless `oserror_use_init(cls)`,
no keywords, the subclass that an `int` error number names when `cls` is `OSError` itself and
there are two to five arguments, and the fields; else an exception with `args` empty. -/
def osErrorNew [PyWrites m V] (self args kwargs : V) : m V := do
  let xs ← tupleItems args
  let some cls := xs[0]? | PyPure.gap "OSError.__new__ without a class"
  let pos := xs.extract 1 xs.size
  if ← osErrorUseInit cls then
    return ← baseExcNew self (PyPure.imm (m := m) (.tuple #[cls])) kwargs
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" s!"{← classNameOf cls}() takes no keyword arguments"
  let (en, _, _, _) := osErrorParse pos
  let cls' ← if (← PyPure.immView cls) matches some (.builtin .OSError) then
      match ← en.mapM PyPure.immView with
      | some (some (.int n)) => pure ((errnoClass n).map (PyPure.imm (m := m) ∘ .builtin) |>.getD cls)
      | some (some (.bool b)) =>
        pure ((errnoClass (if b then 1 else 0)).map (PyPure.imm (m := m) ∘ .builtin) |>.getD cls)
      | some none => match en with
        | some x =>
          if ← isSubclass (← PyReads.classOf x) (PyPure.imm (m := m) (.builtin .int)) then
            PyPure.gap "an error number of a subclass of int is not modelled yet"
          pure cls
        | none => pure cls
      | _ => pure cls
    else pure cls
  let e ← baseExcNew self (PyPure.imm (m := m) (.tuple #[cls'])) kwargs
  osErrorFill e cls' pos
  pure e

/-- **`OSError.__init__`**, CPython's `OSError_init`: nothing unless `oserror_use_init` holds for
the class of `self`; then no keywords, and the fields. -/
def osErrorInit [PyWrites m V] (self args kwargs : V) : m V := do
  let cls ← PyReads.classOf self
  if ← osErrorUseInit cls then
    noKeywords self kwargs
    osErrorFill self cls (← tupleItems args)
  pure (PyPure.imm (m := m) .none)

/-- **`OSError.__str__`**: `[Errno n] strerror: 'filename'` (with ` -> 'filename2'`) when
`filename` is set, `[Errno n] strerror` when both are set, else `BaseException.__str__`; an unset
`errno` or `strerror` prints as `None`. -/
def osErrorStr [PyWrites m V] (self args kwargs : V) : m V := do
  let orNone (v : Option V) : m String := do
    match v with
    | some x => argStr x
    | none => pure "None"
  let en ← excField self "errno"
  let se ← excField self "strerror"
  let s? ← match ← excField self "filename", ← excField self "filename2" with
    | some f, some f2 => pure (some s!"[Errno {← orNone en}] {← orNone se}: {← checkRepr f} -> {← checkRepr f2}")
    | some f, none => pure (some s!"[Errno {← orNone en}] {← orNone se}: {← checkRepr f}")
    | none, _ => match en, se with
      | some x, some y => pure (some s!"[Errno {← argStr x}] {← argStr y}")
      | _, _ => pure none
  match s? with
  | some s => return PyPure.imm (m := m) (.str (.ofString s))
  | none => baseExcStr self args kwargs

/-- **`BaseExceptionGroup.__new__(cls, message, exceptions)`**: CPython's checks of the message and
the sequence of exceptions, an `ExceptionGroup` for `BaseExceptionGroup` when every exception is
an `Exception`, and `TypeError` for an `ExceptionGroup` of other exceptions. A sequence other than
a `tuple` or a `list` stops with a gap. -/
def excGroupNew [PyWrites m V] (self args kwargs : V) : m V := do
  let xs ← tupleItems args
  let some cls := xs[0]? | PyPure.gap "BaseExceptionGroup.__new__ without a class"
  let #[msg, excs] := xs.extract 1 xs.size |
    PyPure.gap "BaseExceptionGroup.__new__ with other than two arguments is not modelled yet"
  if (← str? msg).isNone then
    -- CPython accepts an instance of a subclass of `str`.
    userCheck msg msg
    raiseBuiltin "TypeError" s!"BaseExceptionGroup.__new__() argument 1 must be str, not {← argTypeName msg}"
  -- `PySequence_Tuple`: an instance of a subclass of `list` or `tuple` is iterated by its
  -- `__iter__`, a loop of user code when it overrides `list`'s or `tuple`'s, after its `__len__`
  -- gives a length hint, user code too when it is overridden.
  if ← isUserObject excs then
    let base ← builtinBase? excs
    for (n, gapMsg) in [("__iter__", "a looping built-in was reached inside BaseExceptionGroup.__new__"),
        ("__len__", "a length hint of user code inside BaseExceptionGroup.__new__ is not modelled yet")] do
      if let some f ← lookupType (← PyReads.classOf excs) n then
        -- Only the built-in base's own dunder of that name is no user code.
        let own := match base, ← PyPure.immView f with
          | some b, some (.descr t n' _) => t == b && n' == n
          | _, _ => false
        if !own then PyPure.gap gapMsg
  let items ← match ← PyPure.immView excs with
    | some (.tuple ys) => pure ys
    | _ => match ← listOf? excs with
      | some ys => pure ys
      | none =>
        let notSeq ← match ← PyPure.immView excs with
          | some (.str _) | some (.bytes _) | some (.range ..) => pure false
          | some _ => pure true
          | none => pure ((← classIs excs .dict) || (← classIs excs .set) || (← classIs excs .frozenset))
        if notSeq then raiseBuiltin "TypeError" "second argument (exceptions) must be a sequence"
        PyPure.gap "a sequence of exceptions other than a tuple or a list is not modelled yet"
  if items.isEmpty then
    raiseBuiltin "ValueError" "second argument (exceptions) must be a non-empty sequence"
  let mut allExc := true
  for h : i in [0:items.size] do
    if !(← isException items[i]) then
      raiseBuiltin "ValueError" s!"Item {i} of second argument (exceptions) is not an exception"
    -- `PyObject_IsInstance`, which reads the item's `__class__`.
    if !(← objectIsinstance items[i] (PyPure.imm (m := m) (.builtin .Exception))) then
      allExc := false
  let cls' ← match ← PyPure.immView cls with
    | some (.builtin .BaseExceptionGroup) =>
      pure (if allExc then PyPure.imm (m := m) (.builtin .ExceptionGroup) else cls)
    | some (.builtin .ExceptionGroup) =>
      if !allExc then raiseBuiltin "TypeError" "Cannot nest BaseExceptions in an ExceptionGroup"
      pure cls
    | _ =>
      if (← isSubclass cls (PyPure.imm (m := m) (.builtin .Exception))) && !allExc then
        raiseBuiltin "TypeError" s!"Cannot nest BaseExceptions in '{← classNameOf cls}'"
      pure cls
  let e ← baseExcNew self (PyPure.imm (m := m) (.tuple #[cls', msg, excs])) kwargs
  PyWrites.excSet e (.field "message" (some msg))
  PyWrites.excSet e (.field "exceptions" (some (PyPure.imm (m := m) (.tuple items))))
  pure e

/-- **`BaseExceptionGroup.__str__`**: `message (n sub-exception(s))`. -/
def excGroupStr [PyWrites m V] (self _args _kwargs : V) : m V := do
  let some msg ← excField self "message" | PyPure.gap "an exception group without message"
  let some ex ← excField self "exceptions" | PyPure.gap "an exception group without exceptions"
  let n := (← tupleItems ex).size
  return PyPure.imm (m := m) (.str (.ofString
    s!"{← argStr msg} ({n} sub-exception{if n == 1 then "" else "s"})"))

end

end

end StrataPython.Dyn.Sem.Builtins
