/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Exceptions
public import StrataPython.Dyn.Sem.Library.Codecs
public import StrataPython.Dyn.Sem.Library.Functions

set_option autoImplicit false

/-!
# `UnicodeEncodeError` and `UnicodeDecodeError`

Generic over the record, the exceptions of the codecs, as CPython 3.12's `exceptions.c` builds
them: five arguments, `encoding`, `object`, `start`, `end` and `reason`, kept as the exception's
fields. `raiseCodecError` raises the error that a codec of `Codecs` gives. The classes' `__new__`
is `BaseException`'s; their `__init__` parses the five arguments as `PyArg_ParseTuple` does
(`"UUnnU"`, and `"UOnnU"` with a bytes-like object for decoding), and their `__str__` writes the
codec's message from the fields.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

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

/-- The text of the argument `v`, a `str` (a subclass too), as Argument Clinic's converters take
it; else their `TypeError`, `msg` then the name of `v`'s type, or `None` for `None`
(`_PyArg_BadArgument`). -/
def clinicStrArg [PyReads m V] (msg : String) (v : V) : m String := do
  if let some s ← strText? v then return s
  let t ← if (← PyPure.immView v) matches some .none then pure "None" else typeName v
  raiseBuiltin "TypeError" s!"{msg}{t}"

/-- A plain `bytes` of the octets `b`. -/
def bytesValue [PyPure m V] (b : Array UInt8) : V := PyPure.imm (m := m) (.bytes b)

/-- Raise the exception of the class `cls` with the five arguments of a codec error. -/
def raiseUnicodeError [PyReads m V] {α : Type} (cls : Builtin) (enc : String) (obj : V)
    (start stop : Nat) (reason : String) : m α := do
  let e := strValue (m := m) enc
  let a := intValue (m := m) start
  let b := intValue (m := m) stop
  let r := strValue (m := m) reason
  PyReads.raiseNew (PyPure.imm (m := m) (.builtin cls)) #[e, obj, a, b, r]
    #[("encoding", e), ("object", obj), ("start", a), ("end", b), ("reason", r)]

/-- **Raise the error of a codec**: a `UnicodeEncodeError` or `UnicodeDecodeError` with its
fields, another exception with its message, or a gap for a case that is not modelled. The object
of an encoding error is the `str` being encoded, `source`, an instance of a subclass included;
without it, a plain `str` of the text. -/
def raiseCodecError [PyReads m V] {α : Type} (e : Codecs.Error) (source : Option V := none) :
    m α :=
  match e with
  | .encode enc obj start stop reason =>
    raiseUnicodeError .UnicodeEncodeError enc (source.getD (strValue (m := m) obj)) start stop
      reason
  | .decode enc obj start stop reason =>
    raiseUnicodeError .UnicodeDecodeError enc (bytesValue (m := m) obj) start stop reason
  | .raise cls msg => raiseBuiltin cls msg
  | .notModelled what => PyPure.gap s!"not modelled: {what}"

/-- **`UnicodeEncodeError.__init__(self, encoding, object, start, end, reason)`** (`decode` for
`UnicodeDecodeError`): `BaseException.__init__`, then the five arguments in order, as CPython's
`PyArg_ParseTuple` writes them: `encoding`, `object` and `reason` cleared first, each field set as
soon as it parses, so user code in a later conversion sees the earlier ones, and `encoding`,
`object` and `reason` cleared again when a later argument fails, while `start` and `end` keep
what they parsed. -/
def unicodeErrorInit [PyWrites m V] (decode : Bool) (self args kwargs : V) : m V := do
  discard <| baseExcInit self args kwargs
  let clear : m Unit := do
    for n in ["encoding", "object", "reason"] do PyWrites.excSet self (.field n none)
  clear
  let xs ← tupleItems args
  let #[x0, x1, x2, x3, x4] := xs |
    raiseBuiltin "TypeError" s!"function takes exactly 5 arguments ({xs.size} given)"
  let strAt (i : Nat) (v : V) : m V := do
    if (← strText? v).isNone then
      -- `PyArg_ParseTuple` names `None` as `None`, not by its type.
      let t ← if (← PyPure.immView v) matches some .none then pure "None" else typeName v
      raiseBuiltin "TypeError" s!"argument {i + 1} must be str, not {t}"
    return v
  let set (n : String) (v : V) : m Unit := PyWrites.excSet self (.field n (some v))
  tryCatch (do
      set "encoding" (← strAt 0 x0)
      -- `"UOnnU"` takes any object for decoding, and checks it after the five arguments.
      set "object" (← if decode then pure x1 else strAt 1 x1)
      set "start" (intValue (m := m) (← ssizeArg x2))
      set "end" (intValue (m := m) (← ssizeArg x3))
      set "reason" (← strAt 4 x4)
      if decode then
        -- A `bytes` (a subclass too) stays; another bytes-like object becomes a `bytes`.
        if (← bytesOctets? x1).isNone then
          if (← classIs x1 .bytearray) || (← classIs x1 .memoryview) then
            PyPure.gap "a UnicodeDecodeError of a bytes-like object other than bytes is not modelled yet"
          if (← lookupType (← PyReads.classOf x1) "__buffer__").isSome then
            PyPure.gap "a UnicodeDecodeError of an object with __buffer__ is not modelled yet"
          raiseBuiltin "TypeError" s!"a bytes-like object is required, not '{← typeName x1}'")
    fun e => do clear; throw e
  return PyPure.imm (m := m) .none

/-- **`UnicodeEncodeError.__str__`** (`decode` for `UnicodeDecodeError`): the empty string before
`__init__` set the object; otherwise the codec's message, naming one character (or byte) when
`end` is `start + 1` within the object. -/
def unicodeErrorStr [PyWrites m V] (decode : Bool) (self _args _kwargs : V) : m V := do
  let some obj ← excField self "object" | return strValue (m := m) ""
  let text (n : String) : m String := do
    -- `PyObject_Str` of a field that `__init__` hasn't set yet (CPython's `NULL`) is `<NULL>`.
    match ← excField self n with
    | some v => strTextOf v
    | none => pure "<NULL>"
  let reason ← text "reason"
  let enc ← text "encoding"
  let num (n : String) : m Int := do
    let some v ← excField self n | return 0
    return (← intPart? v).getD 0
  let start ← num "start"
  let stop ← num "end"
  if decode then
    let b := (← bytesOctets? obj).getD #[]
    if 0 ≤ start && start < b.size && 0 ≤ stop && stop ≤ b.size && stop == start + 1 then
      let o := b.getD start.toNat 0
      return strValue (m := m)
        s!"'{enc}' codec can't decode byte 0x{Codecs.hex o.toNat 2} in position {start}: {reason}"
    return strValue (m := m)
      s!"'{enc}' codec can't decode bytes in position {start}-{stop - 1}: {reason}"
  let s := ((← strText? obj).getD "").toList.toArray
  if 0 ≤ start && start < s.size && 0 ≤ stop && stop ≤ s.size && stop == start + 1 then
    let c := s.getD start.toNat ' '
    return strValue (m := m)
      s!"'{enc}' codec can't encode character '{Codecs.escapeChar c.toNat}' in position {start}: {reason}"
  return strValue (m := m)
    s!"'{enc}' codec can't encode characters in position {start}-{stop - 1}: {reason}"

/-- This file's bodies of the methods of the two classes. -/
def unicodeErrorsMethod : Builtin → String → Option BuiltinImpl
  | .UnicodeEncodeError, "__new__" | .UnicodeDecodeError, "__new__" =>
    some fun {_} {_} [_] [_] => baseExcNew
  | .UnicodeEncodeError, "__init__" => some fun {_} {_} [_] [_] => unicodeErrorInit false
  | .UnicodeDecodeError, "__init__" => some fun {_} {_} [_] [_] => unicodeErrorInit true
  | .UnicodeEncodeError, "__str__" => some fun {_} {_} [_] [_] => unicodeErrorStr false
  | .UnicodeDecodeError, "__str__" => some fun {_} {_} [_] [_] => unicodeErrorStr true
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
