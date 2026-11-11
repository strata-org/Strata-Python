/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Functions
public import StrataPython.Dyn.Sem.Library.Numbers
public import StrataPython.Dyn.Sem.Library.Codecs
public import StrataPython.Dyn.Sem.Builtins.Iter

set_option autoImplicit false

/-!
# The constructors of the scalar types: `int`, `float`, `bool` and `str`

Generic over the record, CPython 3.12's `long_new_impl` with `PyNumber_Long`, `float_new_impl`
with `PyNumber_Float`, `bool_new` and `unicode_new_impl` (`Objects/longobject.c`,
`Objects/floatobject.c`, `Objects/boolobject.c`, `Objects/unicodeobject.c`, `Objects/abstract.c`).
An instance of a user subclass is made with the built-in part of its value. Where CPython 3.12
warns (an `__int__` or `__index__` that gives a `bool` or an `int` subclass, a `__float__` that
gives a `float` subclass, the delegation to `__trunc__`), the warning writes the module's
`__warningregistry__`, so the call stops with a gap.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The gap of a step where CPython 3.12 warns. -/
def warnGap [PyPure m V] {α : Type} (what : String) : m α :=
  PyPure.gap s!"{what} warns, which writes __warningregistry__"

/-- The class argument of `T.__new__(cls, …)` and the other arguments. -/
def classAndArgs [PyReads m V] (t : Builtin) (args : V) : m (V × Array V) := do
  let xs ← tupleItems args
  let some cls := xs[0]? |
    PyPure.modelInvariant s!"{t.info.name}.__new__ called without its class"
  return (cls, xs.extract 1 xs.size)

/-- Whether `cls` is exactly the built-in type `t`. -/
def isExact [PyPure m V] (cls : V) (t : Builtin) : m Bool := do
  match ← PyPure.immView cls with
  | some (.builtin b) => return b == t
  | _ => return false

/-- Whether the class `cls` finds the same entry `name` as the built-in type `t`: CPython's
`type->tp_init == T.tp_init` and `type->tp_new == T.tp_new` tests, which decide whether a
subclass's constructor takes keywords. Two equal bound built-in methods (`list.__new__` is one)
are the same C function, though `is` can't tell for two such values. -/
def sameEntry [PyReads m V] (cls : V) (t : Builtin) (name : String) : m Bool := do
  let a ← lookupType cls name
  let b ← lookupType (PyPure.imm (m := m) (.builtin t)) name
  match a, b with
  | some x, some y =>
    match ← PyPure.identical x y with
    | .yes => return true
    | .no => return false
    | .unknown =>
      -- `.unknown` holds only for two equal values.
      if (← PyPure.immView x) matches some (.bound ..) then return true
      PyPure.gap s!"whether {name} is the entry of {t.info.name} is not known"
  | none, none => return true
  | _, _ => return false

/-- A new instance of the subclass `cls` of a built-in type, with the built-in part `p`. -/
def newSubInstance [PyReads m V] (cls : V) (p : BuiltinPart V) : m V := do
  let some mro ← mroOf cls | PyPure.modelInvariant "a constructor's class has no MRO"
  PyReads.allocInstance cls p #[] (Array.replicate (← slotCountOf mro.toList) none)

/-- The text of a `str`, a subclass included. -/
def strText? [PyReads m V] (v : V) : m (Option String) := do
  if let some s ← str? v then return some s
  return (← PyReads.strView v).map (·.s)

/-- The octets of a `bytes`, a subclass included. -/
def bytesOctets? [PyReads m V] (v : V) : m (Option (Array UInt8)) := do
  match ← PyPure.immView v with
  | some (.bytes b) => return some b
  | some _ => return none
  | none => PyReads.bytesView v

/-- Raise what `Numbers` says CPython raises. -/
def failure [PyCalls m V] {α : Type} : Format.Failure → m α := ofFailure

/-! ## `int` -/

/-- Whether the reading of `s` in `base` stops at the limit on digits, before a NUL (CPython's
`PyLong_FromString` reads up to one). -/
def overDigitLimit (s : String) (base : Nat) : Bool :=
  Numbers.readInt ((Numbers.toAscii s.toList).takeWhile (· != '\x00')) base matches .tooManyDigits _

/-- The `%R` of `o`, an instance of `b` or of a subclass of it, in a conversion's message: the
built-in `repr` of an exact one, which is `exact`, and a subclass instance's own `__repr__`,
which runs. -/
def argRepr [PyWrites m V] (o : V) (b : Builtin) (exact : String) : m String := do
  if ← classIs o b then return exact
  reprTextOf o

/-- `int(o, base)` for a `str` or an instance of a subclass of `str`, `o`, with the text `s`
(`PyLong_FromUnicodeObject`): an invalid literal is named by `o`'s `repr`, cut to 200
characters. -/
def intOfStr [PyWrites m V] (o : V) (s : String) (base : Nat) : m Int := do
  match Numbers.intFromStr s base with
  | .ok n => pure n
  | .error f =>
    if (← classIs o .str) || overDigitLimit s base then return ← failure f
    let r ← reprTextOf o
    raiseBuiltin "ValueError"
      s!"invalid literal for int() with base {base}: {String.ofList (r.toList.take 200)}"

/-- `int(b, base)` for the octets `b` (`_PyLong_FromBytes`): read as ASCII text, with the `repr`
of the octets in the message, cut to 200 characters. A non-ASCII octet before a NUL can't be a
digit or a space, so it makes the text invalid; after a NUL, which ends CPython's reading, it
doesn't matter. -/
def intOfBytes [PyCalls m V] (b : Array UInt8) (base : Nat) : m Int := do
  let invalid : m Int := raiseBuiltin "ValueError"
    s!"invalid literal for int() with base {base}: {String.ofList ((Format.bytesRepr b).toList.take 200)}"
  if (b.toList.takeWhile (· != 0)).any (· ≥ 128) then return ← invalid
  let s := String.ofList (b.toList.map fun o => Char.ofNat o.toNat)
  match Numbers.intFromStr s base with
  | .ok n => pure n
  | .error f =>
    -- Only the limit on digits keeps its own message; any other error is an invalid literal,
    -- named by the octets.
    if overDigitLimit s base then failure f else invalid

/-- **`PyNumber_Long(o)`**: an exact `int` as it is; `__int__` (an `int` subclass's own, or a
`float`'s truncation); `__index__`; `__trunc__`, which warns; a `str` or `bytes` read in base
10; else `TypeError`. -/
def numberLong [PyWrites m V] (o : V) : m V := do
  match ← PyPure.immViewAll o with
  | some (.int _) | some (.symHash _) => return o
  | some (.bool b) => return intValue (m := m) (if b then 1 else 0)
  | some (.float f) =>
    match Arith.floatToInt f with
    | .ok i => return intValue (m := m) i
    | .error e => failure e
  | _ => pure ()
  let t ← PyReads.classOf o
  if let some f ← lookupType t "__int__" then
    let r ← callN dispatchDepth (← descrGetN dispatchDepth f (some o) t)
      (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
    match ← PyPure.immViewAll r with
    | some (.int _) | some (.symHash _) => return r
    | some (.bool _) => return ← warnGap "an __int__ that returns a bool"
    | _ =>
      if (← PyReads.numView r) matches some (.int _) then
        return ← warnGap "an __int__ that returns an instance of a subclass of int"
      raiseBuiltin "TypeError" s!"__int__ returned non-int (type {← typeName r})"
  if (← lookupType t "__index__").isSome then
    let some i ← indexValue? o | PyPure.modelInvariant "an __index__ that indexValue? missed"
    return intValue (m := m) i
  if (← lookupType t "__trunc__").isSome then
    return ← warnGap "int() of an object with __trunc__"
  if let some s ← strText? o then return intValue (m := m) (← intOfStr o s 10)
  if let some b ← bytesOctets? o then return intValue (m := m) (← intOfBytes b 10)
  if (← lookupType t "__buffer__").isSome then
    PyPure.gap "int() of an object with __buffer__ is not modelled yet"
  raiseBuiltin "TypeError"
    s!"int() argument must be a string, a bytes-like object or a real number, not '{← typeName o}'"

/-- The `int` value of `int(x, base)`: `PyNumber_Long` without a base; with one, a `str` or
`bytes` read in that base. -/
def intValueOf [PyWrites m V] (x base : Option V) : m V := do
  match x, base with
  | none, none => return intValue (m := m) 0
  | none, some _ => raiseBuiltin "TypeError" "int() missing string argument"
  | some x, none => numberLong x
  | some x, some b =>
    let some n ← indexValue? b |
      raiseBuiltin "TypeError" s!"'{← typeName b}' object cannot be interpreted as an integer"
    if (n != 0 && n < 2) || n > 36 then
      raiseBuiltin "ValueError" "int() base must be >= 2 and <= 36, or 0"
    if let some s ← strText? x then return intValue (m := m) (← intOfStr x s n.toNat)
    if let some o ← bytesOctets? x then return intValue (m := m) (← intOfBytes o n.toNat)
    raiseBuiltin "TypeError" "int() can't convert non-string with explicit base"

/-- **`int.__new__(cls, x=0, /, base=10)`**: the value, then an instance of `cls` with it for a
subclass. -/
def intNew [PyWrites m V] (_self args kwargs : V) : m V := do
  let (cls, xs) ← classAndArgs .int args
  let sig : BuiltinSig :=
    { name := "int", qualname := "int", style := .keywords, posonly := 1, maxpos := 2,
      kwnames := #["base"] }
  let b ← bindBuiltinArgs sig (PyPure.imm (m := m) (.tuple xs)) kwargs
  let #[x, base] := b.params |
    PyPure.modelInvariant "int: the binder gave a parameter array of another shape"
  let v ← intValueOf x base
  if ← isExact cls .int then return v
  -- `PyNumber_Long` may give a `symHash` back, so the value is read with `immViewAll`.
  match ← PyPure.immViewAll v with
  | some (.int i) => newSubInstance cls (.int i)
  | some (.symHash _) =>
    PyPure.gap "an int subclass instance of an int whose number the model doesn't know"
  | _ => PyPure.modelInvariant "PyNumber_Long gave a value that is not an int"

/-! ## `float` -/

/-- `float(o)` for a `str` or an instance of a subclass of `str`, `o`, with the text `s`: an
error names `o` by its `repr`. -/
def floatOfStr [PyWrites m V] (o : V) (s : String) : m V := do
  match Numbers.floatFromStr s with
  | .ok f => return PyPure.imm (m := m) (.float f)
  | .error f =>
    if ← classIs o .str then return ← failure f
    raiseBuiltin "ValueError" s!"could not convert string to float: {← reprTextOf o}"

/-- **`PyNumber_Float(o)`**: an exact `float` as it is; `__float__` (an `int`'s conversion);
`__index__`; a `float` subclass's value; a `str` or `bytes` read as a float; else `TypeError`. -/
def numberFloat [PyWrites m V] (o : V) : m V := do
  match ← PyPure.immViewAll o with
  | some (.float _) => return o
  | some (.int i) =>
    match Format.intToFloat i with
    | .ok f => return PyPure.imm (m := m) (.float f)
    | .error e => failure e
  | some (.bool b) => return PyPure.imm (m := m) (.float (if b then Arith.one else Arith.zero))
  | some (.symHash _) => PyPure.gap "float() of a hash whose number the model doesn't know"
  | _ => pure ()
  let t ← PyReads.classOf o
  if let some f ← lookupType t "__float__" then
    let r ← callN dispatchDepth (← descrGetN dispatchDepth f (some o) t)
      (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
    match ← PyPure.immView r with
    | some (.float _) => return r
    | _ =>
      if (← PyReads.numView r) matches some (.float _) then
        return ← warnGap "a __float__ that returns an instance of a subclass of float"
      raiseBuiltin "TypeError"
        s!"{← typeName o}.__float__ returned non-float (type {← typeName r})"
  if (← lookupType t "__index__").isSome then
    let some i ← indexValue? o | PyPure.modelInvariant "an __index__ that indexValue? missed"
    match Format.intToFloat i with
    | .ok f => return PyPure.imm (m := m) (.float f)
    | .error e => return ← failure e
  if let some (.float f) ← PyReads.numView o then return PyPure.imm (m := m) (.float f)
  if let some s ← strText? o then return ← floatOfStr o s
  if let some b ← bytesOctets? o then
    let invalid : m V := do
      raiseBuiltin "ValueError"
        s!"could not convert string to float: {← argRepr o .bytes (Format.bytesRepr b)}"
    if b.any (· ≥ 128) then return ← invalid
    match Numbers.floatFromStr (String.ofList (b.toList.map fun o => Char.ofNat o.toNat)) with
    | .ok f => return PyPure.imm (m := m) (.float f)
    | .error _ => return ← invalid
  if (← lookupType t "__buffer__").isSome then
    PyPure.gap "float() of an object with __buffer__ is not modelled yet"
  raiseBuiltin "TypeError"
    s!"float() argument must be a string or a real number, not '{← typeName o}'"

/-- **`float.__new__(cls, x=0.0, /)`**. -/
def floatNew [PyWrites m V] (_self args kwargs : V) : m V := do
  let (cls, xs) ← classAndArgs .float args
  -- A subclass with its own `__init__` passes its keywords on to it.
  if (← PyReads.dictLen kwargs) > 0 then
    if (← isExact cls .float) || (← sameEntry cls .float "__init__") then
      raiseBuiltin "TypeError" "float() takes no keyword arguments"
  if xs.size > 1 then
    raiseBuiltin "TypeError" s!"float expected at most 1 argument, got {xs.size}"
  let v ← match xs[0]? with
    | none => pure (PyPure.imm (m := m) (.float Arith.zero))
    | some x => numberFloat x
  if ← isExact cls .float then return v
  let some (.float f) ← PyPure.immView v |
    PyPure.modelInvariant "PyNumber_Float gave a value that is not a float"
  newSubInstance cls (.float f)

/-! ## `bool` -/

/-- **`bool.__new__(cls, x=False, /)`**: the truth of `x`. -/
def boolNew [PyWrites m V] (_self args kwargs : V) : m V := do
  let (_, xs) ← classAndArgs .bool args
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" "bool() takes no keyword arguments"
  if xs.size > 1 then
    raiseBuiltin "TypeError" s!"bool expected at most 1 argument, got {xs.size}"
  let r ← match xs[0]? with
    | none => pure false
    | some x => truthy x
  return PyPure.imm (m := m) (.bool r)

/-! ## `str` -/

/-- The text of an `encoding` or `errors` argument of `str()` or `bytes()` (Argument Clinic's
`str` converter): a `str` without a NUL. -/
def codecName [PyCalls m V] (fn what : String) : Option V → m (Option String)
  | none => pure none
  | some v => do
    let some s ← strText? v |
      raiseBuiltin "TypeError" s!"{fn}() argument '{what}' must be str, not {← typeName v}"
    if s.toList.contains '\x00' then raiseBuiltin "ValueError" "embedded null character"
    return some s

/-- **`str.__new__(cls, object='', encoding='utf-8', errors='strict')`**: `str(object)` without
a codec name; with one, the decoding of a `bytes`. A decoding error is a `UnicodeDecodeError`,
whose class the model doesn't build yet, so it stops with a gap. -/
def strNew [PyWrites m V] (_self args kwargs : V) : m V := do
  let (cls, xs) ← classAndArgs .str args
  let sig : BuiltinSig :=
    { name := "str", qualname := "str", style := .keywords, maxpos := 3,
      kwnames := #["object", "encoding", "errors"] }
  let b ← bindBuiltinArgs sig (PyPure.imm (m := m) (.tuple xs)) kwargs
  let #[obj, encV, errV] := b.params |
    PyPure.modelInvariant "str: the binder gave a parameter array of another shape"
  -- The parser converts `encoding` and `errors` before the body looks at `object`.
  let enc ← codecName "str" "encoding" encV
  let err ← codecName "str" "errors" errV
  let v ← match obj, encV, errV with
    | none, _, _ => pure (strValue (m := m) "")
    | some o, none, none => strOf o
    | some o, _, _ =>
      if (← strText? o).isSome then
        raiseBuiltin "TypeError" "decoding str is not supported"
      let some octets ← bytesOctets? o | do
        if (← lookupType (← PyReads.classOf o) "__buffer__").isSome then
          PyPure.gap "decoding an object with __buffer__ is not modelled yet"
        raiseBuiltin "TypeError" s!"decoding to str: need a bytes-like object, {← typeName o} found"
      match Codecs.decodeWith enc err octets with
      | .ok s => pure (strValue (m := m) s)
      | .error (.raise c msg) => raiseBuiltin c msg
      | .error (.notModelled what) => PyPure.gap s!"not modelled: {what}"
      | .error (.decode ..) | .error (.encode ..) =>
        PyPure.gap "a UnicodeDecodeError is not modelled yet"
  if ← isExact cls .str then return v
  match ← PyPure.immView v with
  | some (.str t) => newSubInstance cls (.str t)
  | _ => PyPure.modelInvariant "str() gave a value that is not a str"

/-- **`bytes.__bytes__(self)`**: an exact `bytes` itself; a subclass instance's octets as a plain
`bytes`. -/
def bytesBytes [PyWrites m V] (self args kwargs : V) : m V := do
  noArgsMethod .bytes "__bytes__" self args kwargs
  if (← PyPure.immView self) matches some (.bytes _) then return self
  let some o ← bytesOctets? self |
    PyPure.modelInvariant "bytes.__bytes__ of a value that is not a bytes"
  return PyPure.imm (m := m) (.bytes o)

/-- This file's bodies of the constructors' `__new__`. -/
def constructorsMethod : Builtin → String → Option BuiltinImpl
  | .int, "__new__" => some fun {_} {_} [_] [_] => intNew
  | .float, "__new__" => some fun {_} {_} [_] [_] => floatNew
  | .bool, "__new__" => some fun {_} {_} [_] [_] => boolNew
  | .str, "__new__" => some fun {_} {_} [_] [_] => strNew
  | .bytes, "__bytes__" => some fun {_} {_} [_] [_] => bytesBytes
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
