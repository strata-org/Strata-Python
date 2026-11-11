/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Bind
public import StrataPython.Dyn.Sem.Proto.Iter

set_option autoImplicit false

/-!
# The dunders of the built-in types

Generic over the record, the bodies of the dunders that the operators reach on the built-in types,
as CPython 3.12's slot wrappers run them: `int.__add__`, `float.__eq__`, `int.__neg__` and so on.
Each body takes its `self`, an instance of the type or of a subclass of it, and works on the
built-in part of its operands. A binary or comparison dunder gives `NotImplemented` for an operand
that the type's slot doesn't take: `int.__add__(1, 1.5)` is `NotImplemented`, and so is
`int.__eq__(1, 1.0)`, while `float.__add__(1.5, 1)` is `2.5`.

`dunderImpl t name` gives the body of `t.name`, or `none`, which the call of a built-in method
turns into a gap.
-/

namespace StrataPython.Dyn.Sem.Builtins

open Proto

@[expose] public section

/-- The slot wrapper signature of the dunder `name` with `n` arguments after `self`. -/
def wrapperSig (name : String) (n : Nat) : BuiltinSig :=
  { name, qualname := name, style := .wrapper, maxpos := n }

/-- The binary operator of a numeric dunder (`__add__`, `__radd__`, ...), and whether it is the
reflected form. -/
def numBinaryOf? (name : String) : Option (Arith.BinOp × Bool) :=
  let ops : List (Arith.BinOp × String) :=
    [(.add, "add"), (.sub, "sub"), (.mul, "mul"), (.trueDiv, "truediv"),
      (.floorDiv, "floordiv"), (.mod, "mod"), (.pow, "pow"), (.lshift, "lshift"),
      (.rshift, "rshift"), (.and, "and"), (.or, "or"), (.xor, "xor")]
  ops.findSome? fun (op, n) =>
    if name == s!"__{n}__" then some (op, false)
    else if name == s!"__r{n}__" then some (op, true)
    else none

/-- The comparison of a rich comparison dunder. -/
def cmpOf? (name : String) : Option Arith.CmpOp :=
  [(Arith.CmpOp.eq, "__eq__"), (.ne, "__ne__"), (.lt, "__lt__"), (.le, "__le__"), (.gt, "__gt__"),
    (.ge, "__ge__")].findSome? fun (op, n) => if name == n then some op else none

/-- The unary operator of a numeric dunder (`__abs__` is library's, with `abs`). -/
def unaryOf? (name : String) : Option Arith.UnaryOp :=
  [(Arith.UnaryOp.neg, "__neg__"), (.pos, "__pos__"),
    (.invert, "__invert__")].findSome? fun (op, n) => if name == n then some op else none

section
variable {m : Type → Type 1} {V : Type}

/-- `NotImplemented`. -/
def notImpl [PyPure m V] : V := PyPure.imm (m := m) .notImplemented

/-- The only argument of a slot wrapper's call. -/
def oneArg [PyReads m V] (name : String) (args kwargs : V) : m V := do
  let b ← bindBuiltinArgs (wrapperSig name 1) args kwargs
  let #[some o] := b.params | PyPure.modelInvariant "a slot wrapper: the binder's assumption failed"
  pure o

/-- A slot wrapper's call with no argument. -/
def noArg [PyReads m V] (name : String) (args kwargs : V) : m Unit := do
  discard <| bindBuiltinArgs (wrapperSig name 0) args kwargs

/-- Whether a number of the type `t`'s slots takes the number `x`: an `int` slot takes an `int` or
a `bool`, a `float` slot an `int`, a `bool` or a `float`. -/
def numTakes [PyPure m V] (t : Builtin) (x : V) : m Bool := do
  match ← PyPure.immView x with
  | some (.int _) | some (.bool _) => pure true
  | some (.float _) => pure (t == .float)
  | _ => pure false

/-- `t.name(self, o)` for a binary numeric dunder of the operator `op` (`reflected` for
`__radd__` and the other reflected forms). -/
def numBinBody [PyWrites m V] (t : Builtin) (name : String) (op : Arith.BinOp) (reflected : Bool)
    (self args kwargs : V) : m V := do
  let o ← oneArg name args kwargs
  let some a ← numPart? self | PyPure.gap s!"{name}: the receiver is not a number"
  let some b ← numPart? o | return notImpl (m := m)
  if !(← numTakes t b) then return notImpl (m := m)
  let (x, y) := if reflected then (b, a) else (a, b)
  let some r ← PyReads.numBinary op x y | return notImpl (m := m)
  -- Only `bool`'s own `&`, `|` and `^` give a `bool`: `int.__and__(True, True)` is `1`.
  if t != .bool then
    if let some (.bool v) ← PyPure.immView r then
      return PyPure.imm (m := m) (.int (if v then 1 else 0))
  return r

/-- `t.__pow__(self, o[, mod])` and `t.__rpow__`: a ternary slot wrapper, whose third argument
must be `None` here; a modulus gaps. -/
def numPowBody [PyWrites m V] (t : Builtin) (name : String) (reflected : Bool)
    (self args kwargs : V) : m V := do
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" s!"wrapper {name}() takes no keyword arguments"
  let xs ← tupleItems args
  if xs.size < 1 then raiseBuiltin "TypeError" s!" expected at least 1 argument, got {xs.size}"
  if xs.size > 2 then raiseBuiltin "TypeError" s!" expected at most 2 arguments, got {xs.size}"
  if let some z := xs[1]? then
    if !((← PyPure.immView z) matches some .none) then
      PyPure.gap "pow with a modulus is not modelled yet"
  let some o := xs[0]? | PyPure.modelInvariant "an argument"
  numBinBody t name .pow reflected self (PyPure.imm (m := m) (.tuple #[o]))
    (← PyPure.allocDict)

/-- `t.name(self, o)` for a numeric rich comparison. -/
def numCmpBody [PyWrites m V] (t : Builtin) (name : String) (op : Arith.CmpOp)
    (self args kwargs : V) : m V := do
  let o ← oneArg name args kwargs
  let some a ← numPart? self | PyPure.gap s!"{name}: the receiver is not a number"
  let some b ← numPart? o | return notImpl (m := m)
  if !(← numTakes t b) then return notImpl (m := m)
  match ← PyPure.numCompare op a b with
  | some r => pure (PyPure.imm (m := m) (.bool r))
  | none => pure (notImpl (m := m))

/-- `t.name(self)` for a numeric unary operator. -/
def numUnaryBody [PyWrites m V] (name : String) (op : Arith.UnaryOp) (self args kwargs : V) :
    m V := do
  noArg name args kwargs
  let some a ← numPart? self | PyPure.gap s!"{name}: the receiver is not a number"
  let some r ← PyReads.numUnary op a | PyPure.gap s!"{name}: the operator doesn't apply"
  pure r

/-- `t.__bool__(self)` for a number. -/
def numBoolBody [PyCalls m V] (self args kwargs : V) : m V := do
  noArg "__bool__" args kwargs
  let some a ← numPart? self | PyPure.gap "__bool__: the receiver is not a number"
  pure (PyPure.imm (m := m) (.bool (← truthy a)))

/-- `t.__hash__(self)` for a number: the hash of its value. -/
def numHashBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__hash__" args kwargs
  let some a ← numPart? self | PyPure.gap "__hash__: the receiver is not a number"
  let some h ← PyPure.immHash a | PyPure.gap "__hash__: a number without a hash"
  PyPure.hashValue h

/-- `int.__index__(self)`: the `int` itself, a `bool` as `0` or `1`. -/
def intIndexBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__index__" args kwargs
  let some a ← numPart? self | PyPure.gap "__index__: the receiver is not an int"
  match ← PyPure.immView a with
  | some (.int i) => pure (PyPure.imm (m := m) (.int i))
  | some (.bool b) => pure (PyPure.imm (m := m) (.int (if b then 1 else 0)))
  | _ => PyPure.gap "__index__: the receiver is not an int"

/-- The body of the numeric dunder `name` of `t` (`int`, `bool` or `float`). -/
def numDunder (t : Builtin) (name : String) : Option BuiltinImpl :=
  if name == "__pow__" || name == "__rpow__" then
    some fun {_} {_} [_] [_] => numPowBody t name (name == "__rpow__")
  else if let some (op, reflected) := numBinaryOf? name then
    some fun {_} {_} [_] [_] => numBinBody t name op reflected
  else if let some op := cmpOf? name then
    some fun {_} {_} [_] [_] => numCmpBody t name op
  else if let some op := unaryOf? name then
    some fun {_} {_} [_] [_] => numUnaryBody name op
  else match name with
    | "__bool__" => some fun {_} {_} [_] [_] => numBoolBody
    | "__hash__" => some fun {_} {_} [_] [_] => numHashBody
    | "__index__" => if t == .float then none else some fun {_} {_} [_] [_] => intIndexBody
    | _ => none

/-- The two arguments of a slot wrapper's call. -/
def twoArgs [PyReads m V] (name : String) (args kwargs : V) : m (V × V) := do
  let b ← bindBuiltinArgs (wrapperSig name 2) args kwargs
  let #[some k, some v] := b.params | PyPure.modelInvariant "a slot wrapper: the binder's assumption failed"
  pure (k, v)

/-- `None`. -/
def noneV [PyPure m V] : V := PyPure.imm (m := m) .none

/-- The `str`, `bytes` or `tuple` that `v` is or derives from, as a value: an immediate. -/
def seqPartV [PyReads m V] (v : V) : m (Option V) :=
  return (← seqImm? v).map (PyPure.imm (m := m))

/-- The number of elements of a built-in container `v`, or of the built-in part of an instance of
a subclass of one. -/
def lenCore [PyCalls m V] (v : V) : m Nat := do
  let some n ← builtinLen? v | PyPure.gap "the length of this value is not modelled yet"
  pure n

/-- `t.__len__(self)`. -/
def lenBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__len__" args kwargs
  pure (PyPure.imm (m := m) (.int (← lenCore self)))

/-- `range.__bool__(self)`: whether it has an element. -/
def lenBoolBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__bool__" args kwargs
  -- `range_bool` reads the length as a Python int, so a range longer than a `Py_ssize_t` is true.
  if let some (.range a z c) ← PyPure.immView self then
    return PyPure.imm (m := m) (.bool (rangeLen a z c != 0))
  pure (PyPure.imm (m := m) (.bool ((← lenCore self) != 0)))

/-- `t.__contains__(self, x)`. -/
def containsBody [PyWrites m V] (self args kwargs : V) : m V := do
  let x ← oneArg "__contains__" args kwargs
  pure (PyPure.imm (m := m) (.bool (← containsCore x self)))

/-- `t.__getitem__(self, key)` for a sequence or a range. -/
def getItemBody [PyWrites m V] (self args kwargs : V) : m V := do
  getItemCore self (← oneArg "__getitem__" args kwargs)

/-- `t.__setitem__(self, key, value)`. -/
def setItemBody [PyWrites m V] (self args kwargs : V) : m V := do
  let (k, v) ← twoArgs "__setitem__" args kwargs
  setItemCore self k v
  pure (noneV (m := m))

/-- `t.__delitem__(self, key)`. -/
def delItemBody [PyWrites m V] (self args kwargs : V) : m V := do
  delItemCore self (← oneArg "__delitem__" args kwargs)
  pure (noneV (m := m))

/-- `t.__hash__(self)` for a `str`, `bytes`, `tuple` or `range`: the hash of its value. -/
def valueHashBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__hash__" args kwargs
  let v ← match ← seqPartV self with
    | some v => pure v
    | none => pure self
  PyPure.hashValue (← Proto.hash v)

/-- `t.__add__(self, o)` for a sequence: the concatenation, or CPython's `TypeError`. -/
def seqAddBody [PyWrites m V] (t : Builtin) (self args kwargs : V) : m V := do
  let o ← oneArg "__add__" args kwargs
  if let some r ← concatSeq self o then return r
  if t == .bytes then
    if (← lookupType (← PyReads.classOf o) "__buffer__").isSome then
      PyPure.gap "a bytes concatenation with an object that has __buffer__ is not modelled yet"
    raiseBuiltin "TypeError" s!"can't concat {← typeName o} to bytes"
  let n := t.info.name
  raiseBuiltin "TypeError" s!"can only concatenate {n} (not \"{← typeName o}\") to {n}"

/-- `t.__mul__(self, n)` and `t.__rmul__(self, n)` for a sequence: the repetition, or CPython's
`TypeError` for a count without `__index__`. -/
def seqMulBody [PyWrites m V] (name : String) (self args kwargs : V) : m V := do
  let o ← oneArg name args kwargs
  if let some r ← repeatSeq self o then return r
  raiseBuiltin "TypeError" s!"'{← typeName o}' object cannot be interpreted as an integer"

/-- `t.name(self, o)` for a comparison of a sequence: `NotImplemented` unless `o` is of the same
built-in type or derives from it. -/
def seqCmpBody [PyWrites m V] (t : Builtin) (name : String) (op : Arith.CmpOp)
    (self args kwargs : V) : m V := do
  let o ← oneArg name args kwargs
  if (← builtinBase? o) != some t then return notImpl (m := m)
  let boolV (r : Bool) : V := PyPure.imm (m := m) (.bool r)
  if (← listOf? self).isSome then
    if (← listOf? o).isNone then return notImpl (m := m)
    let eqv (x y : V) : m Bool := do truthy (← richCompareV .eq x y)
    return ← listCompareLive eqv (richCompareV op) boolV op self o
  let a ← (·.getD self) <$> seqPartV self
  let b ← (·.getD o) <$> seqPartV o
  if t == .range && op != .eq && op != .ne then return notImpl (m := m)
  richCompareV op a b

/-- `list.__iadd__(self, it)`: `self` extended by the elements of `it`. -/
def listIaddBody [PyWrites m V] (self args kwargs : V) : m V := do
  let o ← oneArg "__iadd__" args kwargs
  let some xs ← listOf? self | PyPure.gap "__iadd__: the receiver is not a list"
  listExtendWith self xs o fun t => s!"'{t}' object is not iterable"
  pure self

/-- `list.__imul__(self, n)`: `self` repeated in place. -/
def listImulBody [PyWrites m V] (self args kwargs : V) : m V := do
  let o ← oneArg "__imul__" args kwargs
  if (← listOf? self).isNone then PyPure.gap "__imul__: the receiver is not a list"
  let some k ← repeatCount o |
    raiseBuiltin "TypeError" s!"'{← typeName o}' object cannot be interpreted as an integer"
  -- The count's `__index__` may change the list: CPython repeats the list as it is then.
  let some xs ← listOf? self | PyPure.modelInvariant "a list that is no longer a list"
  if xs.size * k > maxRepeat then PyPure.gap "a repetition too large to model"
  PyWrites.listSplice self 0 xs.size (repeatArray xs k)
  pure self

/-- The body of the dunder `name` of the sequence type `t` (`str`, `bytes`, `tuple`, `list` or
`range`). -/
def seqDunder (t : Builtin) (name : String) : Option BuiltinImpl :=
  if let some op := cmpOf? name then some fun {_} {_} [_] [_] => seqCmpBody t name op
  else match name with
    | "__len__" => some fun {_} {_} [_] [_] => lenBody
    | "__contains__" => some fun {_} {_} [_] [_] => containsBody
    | "__getitem__" => some fun {_} {_} [_] [_] => getItemBody
    | "__hash__" => if t == .list then none else some fun {_} {_} [_] [_] => valueHashBody
    | "__add__" => if t == .range then none else some fun {_} {_} [_] [_] => seqAddBody t
    | "__mul__" | "__rmul__" =>
      if t == .range then none else some fun {_} {_} [_] [_] => seqMulBody name
    | "__bool__" => if t == .range then some fun {_} {_} [_] [_] => lenBoolBody else none
    | "__setitem__" => if t == .list then some fun {_} {_} [_] [_] => setItemBody else none
    | "__delitem__" => if t == .list then some fun {_} {_} [_] [_] => delItemBody else none
    | "__iadd__" => if t == .list then some fun {_} {_} [_] [_] => listIaddBody else none
    | "__imul__" => if t == .list then some fun {_} {_} [_] [_] => listImulBody else none
    | _ => none

/-- `dict.__getitem__(self, key)`: the value; for an instance of a subclass, its type's
`__missing__` where the key is absent; else `KeyError`. -/
def dictGetItemBody [PyWrites m V] (self args kwargs : V) : m V := do
  let k ← oneArg "__getitem__" args kwargs
  if let some v ← dictFindKey self k then return v
  if !(← isDict self) then
    if let some r ← callSpecial? self "__missing__" #[k] then return r
  raiseKeyError k

/-- `dict.__eq__` and `dict.__ne__`; the other comparisons give `NotImplemented`. -/
def dictCmpBody [PyWrites m V] (name : String) (op : Arith.CmpOp) (self args kwargs : V) : m V := do
  let o ← oneArg name args kwargs
  if !(← isDictLike o) || (op != .eq && op != .ne) then return notImpl (m := m)
  let same ← dictEqual (richCompare .eq) self o
  pure (PyPure.imm (m := m) (.bool (if op == .eq then same else !same)))

/-- A gap unless CPython reads the dict `o`'s entries directly, running no user code: an exact
dict, or an instance of a subclass of `dict` whose class keeps dict's `__iter__`, which keeps
`dict_merge` and `PyDict_Copy` on their fast path; for an operand that is `merged` into another
dict, also dict's `keys` and `__getattribute__`, since `dict_update_arg` looks `keys` up on it. -/
def dictFastGap [PyReads m V] (o : V) (merged : Bool) : m Unit := do
  if ← classIs o .dict then return
  let t ← PyReads.classOf o
  let keeps (n : String) (b : Builtin) : m Bool := do
    match ← lookupType t n with
    | some f => match ← PyPure.immView f with
      | some (.descr b' n' _) => pure (b' == b && n' == n)
      | _ => pure false
    | none => pure false
  let fast ← if merged then
      pure ((← keeps "__iter__" .dict) && (← keeps "keys" .dict) && (← keeps "__getattribute__" .dict))
    else keeps "__iter__" .dict
  if !fast then
    PyPure.gap "a | of a dict whose class overrides how its entries are read is not modelled yet"

/-- `dict.__or__(self, o)` (`reflected` for `__ror__`): a new dict, the left operand's entries
updated with the right one's. -/
def dictOrBody [PyWrites m V] [PyNew m V] (name : String) (reflected : Bool) (self args kwargs : V) :
    m V := do
  let o ← oneArg name args kwargs
  if !(← isDictLike o) then return notImpl (m := m)
  let (l, r) := if reflected then (o, self) else (self, o)
  dictFastGap l false
  dictFastGap r true
  let c ← PyReads.dictCopy l
  guardDictWalk r c
  for (k, v, h) in ← PyReads.dictEntries r do PyNew.dictSetNew c k v (some h) (keyEq k)
  pure c

/-- `dict.__ior__(self, o)` for a dict `o`: `self` updated with `o`'s entries. -/
def dictIorBody [PyWrites m V] (self args kwargs : V) : m V := do
  let o ← oneArg "__ior__" args kwargs
  if !(← isDictLike o) then PyPure.gap "updating a dict from a value that is not a dict is not modelled yet"
  dictFastGap o true
  guardDictWalk o self
  for (k, v, h) in ← PyReads.dictEntries o do PyWrites.dictSet self k v (some h) (keyEq k)
  pure self

/-- The body of the dunder `name` of `dict`. -/
def dictDunder (name : String) : Option BuiltinImpl :=
  if let some op := cmpOf? name then some fun {_} {_} [_] [_] => dictCmpBody name op
  else match name with
    | "__len__" => some fun {_} {_} [_] [_] => lenBody
    | "__contains__" => some fun {_} {_} [_] [_] => containsBody
    | "__getitem__" => some fun {_} {_} [_] [_] => dictGetItemBody
    | "__setitem__" => some fun {_} {_} [_] [_] => setItemBody
    | "__delitem__" => some fun {_} {_} [_] [_] => delItemBody
    | "__or__" => some fun {_} {_} [_] [_] => dictOrBody name false
    | "__ror__" => some fun {_} {_} [_] [_] => dictOrBody name true
    | "__ior__" => some fun {_} {_} [_] [_] => dictIorBody
    | _ => none

/-- The set operation of a binary dunder of `set` and `frozenset`. -/
def setOpOf? (name : String) : Option (Arith.BinOp × Bool) :=
  match numBinaryOf? name with
  | some (op, r) => if op == .or || op == .and || op == .sub || op == .xor then some (op, r) else none
  | none => none

/-- `t.name(self, o)` for a binary set operator: a new set of the left operand's built-in type,
or `NotImplemented` unless `o` is a set or a frozenset. -/
def setBinBody [PyWrites m V] [PyNew m V] (name : String) (op : Arith.BinOp) (reflected : Bool)
    (self args kwargs : V) : m V := do
  let o ← oneArg name args kwargs
  if (← anySetLike? o).isNone then return notImpl (m := m)
  let (a, b) := if reflected then (o, self) else (self, o)
  let frozen := (← anySetLike? a) == some true
  match op with
  | .or => setUnion frozen a b
  | .and => setIntersection frozen a b
  | .sub => setDifference frozen a b
  | _ => setSymDifference frozen a b

/-- `set.name(self, o)` for an in-place set operator. -/
def setInplaceBody [PyWrites m V] [PyNew m V] (name : String) (op : Arith.BinOp)
    (self args kwargs : V) : m V := do
  let o ← oneArg name args kwargs
  if (← anySetLike? o).isNone then return notImpl (m := m)
  match op with
  | .or => setMergeWith oldSetWrites self o
  | .and => PyWrites.setReplace self (← setIntersection false self o)
  | .sub => setSubtractWith oldSetWrites self o
  | _ => setSymUpdateWith oldSetWrites self o
  pure self

/-- `t.name(self, o)` for a comparison of sets. -/
def setCmpBody [PyWrites m V] (name : String) (op : Arith.CmpOp) (self args kwargs : V) : m V := do
  let o ← oneArg name args kwargs
  if (← anySetLike? o).isNone then return notImpl (m := m)
  pure (PyPure.imm (m := m) (.bool (← setCompare (richCompare .eq) op self o)))

/-- `frozenset.__hash__(self)`. -/
def frozensetHashBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__hash__" args kwargs
  PyPure.hashValue (frozensetHash ((← setMembers self).unordered.toList.map (·.2)))

/-- The body of the dunder `name` of `set` or `frozenset`. -/
def setDunder (t : Builtin) (name : String) : Option BuiltinImpl :=
  if let some op := cmpOf? name then some fun {_} {_} [_] [_] => setCmpBody name op
  else if let some (op, r) := setOpOf? name then some fun {_} {_} [_] [_] => setBinBody name op r
  else match name with
    | "__len__" => some fun {_} {_} [_] [_] => lenBody
    | "__contains__" => some fun {_} {_} [_] [_] => containsBody
    | "__hash__" => if t == .frozenset then some fun {_} {_} [_] [_] => frozensetHashBody else none
    | "__ior__" => if t == .set then some fun {_} {_} [_] [_] => setInplaceBody name .or else none
    | "__iand__" => if t == .set then some fun {_} {_} [_] [_] => setInplaceBody name .and else none
    | "__isub__" => if t == .set then some fun {_} {_} [_] [_] => setInplaceBody name .sub else none
    | "__ixor__" => if t == .set then some fun {_} {_} [_] [_] => setInplaceBody name .xor else none
    | _ => none

/-- **The body of the dunder `t.name`** of a built-in type, if this piece models it. -/
def dunderImpl (t : Builtin) (name : String) : Option BuiltinImpl :=
  match t with
  | .int | .bool | .float => numDunder t name
  | .str | .bytes | .tuple | .list | .range => seqDunder t name
  | .dict => dictDunder name
  | .«set» | .«frozenset» => setDunder t name
  | _ => none

end

end

end StrataPython.Dyn.Sem.Builtins
