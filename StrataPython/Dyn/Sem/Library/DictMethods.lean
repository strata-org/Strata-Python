/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.DictViews

set_option autoImplicit false

/-!
# The methods of `dict`

Generic over the record, CPython 3.12's `dict` methods (`Objects/dictobject.c`): `get`,
`setdefault` and `pop` hash their key once, as CPython does, and look it up with the stored
key's `__eq__`; `update` is `dict.__init__`'s merge (`Collections`), and `fromkeys` makes an
instance of its class, then walks its iterable. The walks of `update` and `fromkeys` over a user
iterator are step machines (`Machines`).
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- **`d.get(key, default=None)`**. -/
def dictGetMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .dict self Signatures.dict_get args kwargs
  let k ← req "get" ps 0
  let dflt := (arg (m := m) ps 1).getD (PyPure.imm (m := m) .none)
  return (← PyReads.dictFind self k (some (← hash k)) (keyEq k)).getD dflt

/-- **`d.setdefault(key, default=None)`**: the key hashed once, for the lookup and the
insertion. -/
def dictSetdefaultMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .dict self Signatures.dict_setdefault args kwargs
  let k ← req "setdefault" ps 0
  let dflt := (arg (m := m) ps 1).getD (PyPure.imm (m := m) .none)
  let h ← hash k
  if let some v ← PyReads.dictFind self k (some h) (keyEq k) then return v
  PyWrites.dictSet self k dflt (some h) (keyEq k)
  return dflt

/-- **`d.pop(key[, default])`**: an empty dict gives the default, or `KeyError`, without hashing
the key. -/
def dictPopMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .dict self Signatures.dict_pop args kwargs
  let k ← req "pop" ps 0
  let dflt := arg (m := m) ps 1
  let missing : m V := match dflt with
    | some d => pure d
    | none => raiseKeyError k
  if (← PyReads.dictLen self) == 0 then return ← missing
  match ← PyWrites.dictDelete self k (some (← hash k)) (keyEq k) with
  | some v => return v
  | none => missing

/-- **`d.popitem()`**: the last entry, as a pair. -/
def dictPopitemMethod [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| bound .dict self Signatures.dict_popitem args kwargs
  let some (k, v) ← PyWrites.dictPopitem self |
    raiseBuiltin "KeyError" "popitem(): dictionary is empty"
  return PyPure.imm (m := m) (.tuple #[k, v])

/-- **`d.clear()`**. -/
def dictClearMethod [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| bound .dict self Signatures.dict_clear args kwargs
  PyWrites.dictClear self
  return PyPure.imm (m := m) .none

/-- `PyDict_Copy(d)`: a new plain dict. An empty `d` gives an empty one; a `d` whose type keeps
`dict.__iter__` gives its entries in order, with its deleted slots and its deletion flag, which can
only add gaps (`dictCopy`); otherwise `dict_merge`'s keys protocol, through `d`'s own `keys()` and
`__getitem__`, inside the step, with no probe for `keys` before it. -/
def dictCopyOf [PyWrites m V] [PyNew m V] (d : V) : m V := do
  if (← PyReads.dictLen d) == 0 then return ← PyPure.allocDict
  if ← keepsDictIter d then return ← PyReads.dictCopy d
  let c ← PyPure.allocDict
  match ← dictMergeFirst c d (← PyPure.allocDict) with
  | none => return c
  | some st =>
    match ← collectStep st with
    | .done _ => return c
    | .more _ => midStepGap

/-- **`d.copy()`**: `PyDict_Copy`. -/
def dictCopyMethod [PyWrites m V] [PyNew m V] (self args kwargs : V) : m V := do
  discard <| bound .dict self Signatures.dict_copy args kwargs
  dictCopyOf self

/-- The first step of **`d.update([other], **kwargs)`**: `dict.__init__`'s merge without the
clearing, with `update`'s own count message; the walk left, if any. -/
def dictUpdateFirst [PyWrites m V] (self args kwargs : V) : m (Option (CollectState V)) := do
  let xs ← tupleItems args
  if xs.size > 1 then
    raiseBuiltin "TypeError" s!"update expected at most 1 argument, got {xs.size}"
  match xs[0]? with
  | none =>
    mergeKwargs self kwargs
    return none
  | some x => dictFirst self x kwargs

/-- **`d.update(…)` inside another operation's step**: one walk, which must end. -/
def dictUpdateBody [PyWrites m V] [PyNew m V] (self args kwargs : V) : m V := do
  match ← dictUpdateFirst self args kwargs with
  | none => return PyPure.imm (m := m) .none
  | some st =>
    match ← collectStep st with
    | .done _ => return PyPure.imm (m := m) .none
    | .more _ => midStepGap

/-- The state of `cls.fromkeys(iterable, value)` while it walks the iterator: the new mapping
`d`, the iterator `it`, the value, and whether `d` is an exact dict (keys set directly) or not
(keys set with `d[key] = value`). -/
structure FromKeys (V : Type) where
  d : V
  it : V
  value : V
  exact : Bool

/-- One activation of `fromkeys`'s walk. -/
def fromKeysStep [PyWrites m V] (s : FromKeys V) : m (LoopStep (FromKeys V) V) := do
  match ← forEachItem iterNext s.it () fun k _ => do
      if s.exact then dictPut s.d k s.value else setItem s.d k s.value
      pure (.next ()) with
  | .done _ => return .done s.d
  | .more _ => return .more s

/-- The first step of **`cls.fromkeys(iterable, value=None)`** (`_PyDict_FromKeys`): `cls()`;
for a new exact dict, an exact dict or set's keys at once, with their stored hashes; otherwise
the walk of the iterator. A set whose order the model doesn't know stops with a gap, since the
dict's order would come from it. -/
def fromKeysFirst [PyWrites m V] (cls args kwargs : V) : m (Sum V (FromKeys V)) := do
  let ps ← bound .dict cls Signatures.dict_fromkeys args kwargs
  let x ← req "fromkeys" ps 0
  let value := (arg (m := m) ps 1).getD (PyPure.imm (m := m) .none)
  let d ← callN dispatchDepth cls (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
  let exact ← classIs d .dict
  let empty ← if exact then pure ((← PyReads.dictLen d) == 0) else pure false
  if empty then
    if ← classIs x .dict then
      for (k, _, h) in ← PyReads.dictEntries x do PyWrites.dictSet d k value (some h) (keyEq k)
      return .inl d
    if (← classIs x .set) || (← classIs x .frozenset) then
      let some vw ← PyReads.setView x | PyPure.modelInvariant "fromkeys: a set without a view"
      let some ms := vw.inOrder? |
        PyPure.gap "dict.fromkeys of a set whose order the model doesn't know"
      for (k, h) in ms do PyWrites.dictSet d k value (some h) (keyEq k)
      return .inl d
  let it ← getIter x
  return .inr { d, it, value, exact }

/-- **`cls.fromkeys(…)` inside another operation's step**: one walk, which must end. -/
def fromKeysBody [PyWrites m V] (cls args kwargs : V) : m V := do
  match ← fromKeysFirst cls args kwargs with
  | .inl d => return d
  | .inr s =>
    match ← fromKeysStep s with
    | .done d => return d
    | .more _ => midStepGap

/-- This file's bodies of the methods of `dict`. -/
def dictMethodsMethod : Builtin → String → Option BuiltinImpl
  | .dict, "get" => some fun {_} {_} [_] [_] => dictGetMethod
  | .dict, "setdefault" => some fun {_} {_} [_] [_] => dictSetdefaultMethod
  | .dict, "pop" => some fun {_} {_} [_] [_] => dictPopMethod
  | .dict, "popitem" => some fun {_} {_} [_] [_] => dictPopitemMethod
  | .dict, "clear" => some fun {_} {_} [_] [_] => dictClearMethod
  | .dict, "copy" => some fun {_} {_} [_] [_] => dictCopyMethod
  | .dict, "update" => some fun {_} {_} [_] [_] => dictUpdateBody
  | .dict, "fromkeys" => some fun {_} {_} [_] [_] => fromKeysBody
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
