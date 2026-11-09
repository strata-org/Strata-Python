/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Dunders
public import StrataPython.Dyn.Sem.Proto.Printf

set_option autoImplicit false

/-!
# `repr`, and the `__repr__`, `__str__`, `__format__` and `%` of the built-in types

The built-in function `repr`, and the bodies of the built-in types' `__repr__`, `__str__` and
`__format__` called as methods (`int.__repr__(5)`, `super().__str__()`), over `Proto/Repr.lean`;
and the `__mod__` and `__rmod__` of `str` and `bytes`, printf-style formatting (`Proto/Printf.lean`).
`stringImpl t name` gives the body of `t.name`, or `none`.
-/

namespace StrataPython.Dyn.Sem.Builtins

open Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- **`repr(x)`**. -/
def reprFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig : BuiltinSig := { name := "repr", qualname := "repr", style := .methO }
  let b ← bindBuiltinArgs sig args kwargs
  let #[some x] := b.params | PyPure.modelInvariant "repr: the binder's assumption failed"
  reprOf x

/-- **`b.__repr__(self)`** of the built-in type `b`. -/
def reprBody [PyWrites m V] (b : Builtin) (self args kwargs : V) : m V := do
  noArg "__repr__" args kwargs
  builtinReprOf b self

/-- **`object.__str__(self)`**: the type's `__repr__` of `self`. -/
def objectStrBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__str__" args kwargs
  reprCoreOf self

/-- **`str.__str__(self)`**: an exact `str` of `self`'s `str` part. -/
def strStrBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__str__" args kwargs
  let some s ← strText? self | PyPure.modelInvariant "str.__str__ of a value that is not a str"
  return strValue (m := m) s

/-- **`bytes.__str__(self)`**: the `repr` of `self`'s `bytes` part. -/
def bytesStrBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__str__" args kwargs
  let some x ← bytesPart? self | PyPure.modelInvariant "bytes.__str__ of a value that is not a bytes"
  return strValue (m := m) (Format.bytesRepr x)

/-- **`b.__format__(self, spec)`** of `object`, `int`, `float` or `str`: one argument, a `str`. -/
def formatBody [PyWrites m V] (b : Builtin) (self args kwargs : V) : m V := do
  let sig : BuiltinSig := { name := "__format__", qualname := s!"{b.info.name}.__format__", style := .methO }
  let r ← bindBuiltinArgs sig args kwargs
  let #[some spec] := r.params | PyPure.modelInvariant "__format__: the binder's assumption failed"
  let some sp ← strText? spec |
    raiseBuiltin "TypeError" s!"__format__() argument must be str, not {← argTypeName spec}"
  let some v ← builtinFormat b self (← PyReads.classOf self) sp |
    PyPure.modelInvariant s!"no __format__ body for {b.info.name}"
  pure v

/-- **`str.__mod__(self, args)`**, and `str.__rmod__` when `reflected`, as `unicode_mod` runs it:
the format is the left operand, which must be a `str`, else `NotImplemented`. -/
def strModBody [PyWrites m V] (name : String) (reflected : Bool) (self args kwargs : V) : m V := do
  let o ← oneArg name args kwargs
  let (fmt, xs) := if reflected then (o, self) else (self, o)
  let some f ← strText? fmt | return PyPure.imm (m := m) .notImplemented
  printfStr f xs

/-- **`bytes.__mod__(self, args)`**, and `bytes.__rmod__` when `reflected`, as `bytes_mod` runs it. -/
def bytesModBody [PyWrites m V] (name : String) (reflected : Bool) (self args kwargs : V) : m V := do
  let o ← oneArg name args kwargs
  let (fmt, xs) := if reflected then (o, self) else (self, o)
  let some f ← bytesPart? fmt | return PyPure.imm (m := m) .notImplemented
  printfBytes f xs

/-- The built-in types whose `__repr__` has a body here. -/
def reprTypes : List Builtin :=
  [.object, .type, .int, .bool, .float, .str, .bytes, .tuple, .list, .dict, .«set», .«frozenset»,
    .range, .slice, .NoneType, .NotImplementedType, .ellipsis, .«classmethod», .«staticmethod»]

/-- The body of the `__repr__`, `__str__`, `__format__`, `__mod__` or `__rmod__` of the built-in type `t`. -/
def stringImpl (t : Builtin) (name : String) : Option BuiltinImpl :=
  match name with
  | "__repr__" => if reprTypes.contains t then some fun {_} {_} [_] [_] => reprBody t else none
  | "__str__" => match t with
    | .object => some fun {_} {_} [_] [_] => objectStrBody
    | .str => some fun {_} {_} [_] [_] => strStrBody
    | .bytes => some fun {_} {_} [_] [_] => bytesStrBody
    | _ => none
  | "__mod__" | "__rmod__" =>
    let reflected := name == "__rmod__"
    match t with
    | .str => some fun {_} {_} [_] [_] => strModBody name reflected
    | .bytes => some fun {_} {_} [_] [_] => bytesModBody name reflected
    | _ => none
  | "__format__" =>
    if [Builtin.object, .int, .float, .str].contains t then some fun {_} {_} [_] [_] => formatBody t
    else none
  | _ => none

end

end

end StrataPython.Dyn.Sem.Builtins
