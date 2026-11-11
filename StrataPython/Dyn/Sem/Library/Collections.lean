/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Constructors
public import StrataPython.Dyn.Sem.Proto.Mapping

set_option autoImplicit false

/-!
# The constructors of the containers: `list`, `tuple`, `set`, `frozenset` and `dict`

Generic over the record, CPython 3.12's `list___init___impl` with `list_extend`,
`tuple_new_impl` with `PySequence_Tuple`, `set_init` and `make_new_frozenset` with
`set_update_internal`, `dict_init` with `dict_update_arg`, `PyDict_Merge` and
`PyDict_MergeFromSeq2`, and `bytes_new_impl` with `PyBytes_FromObject` (`Objects/listobject.c`,
`Objects/tupleobject.c`, `Objects/setobject.c`, `Objects/dictobject.c`,
`Objects/bytesobject.c`, `Objects/abstract.c`). A loop over a user iterable runs user code at each
item, so each constructor is a step machine, and its frame (`LoopState`) holds the object that it
fills and the iterator. `list`, `set` and `dict` loop in `__init__`; `tuple`, `frozenset` and `bytes`,
whose objects can't change once made, loop in `__new__`.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

/-- The state of a container constructor's loop. -/
inductive CollectState (V : Type) where
  /-- `list.__init__`: the list `self`, filled from the iterator `it`. -/
  | list (self it : V)
  /-- `tuple.__new__(cls, …)`: the items gathered so far into the list `acc` from `it`. -/
  | tuple (cls acc it : V)
  /-- `set.__init__`: the set `self`, filled from `it`. -/
  | set (self it : V)
  /-- `frozenset.__new__`: the frozenset `self` being made, still open, filled from `it`. -/
  | frozenset (self it : V)
  /-- `dict.__init__` by the keys protocol of `other`, while the keys of `keys()` are gathered
  from `it` into the list `acc`; `kwargs` are merged after. -/
  | dictKeys (self other it kwargs acc : V)
  /-- `dict.__init__` by the keys protocol of `other`, at position `i` of the list of keys
  `keys`, which is walked live. -/
  | dictKeysList (self other keys kwargs : V) (i : Nat)
  /-- `dict.__init__` from the pairs of the iterator `it`, at the pair numbered `i`; `inner` is a
  pair's own iterator, still being read, with the list of the items read so far. -/
  | dictPairs (self it kwargs : V) (i : Nat) (inner : Option (V × V))
  /-- `bytes.__new__(cls, …)` over the iterator `it`: the octets so far, as `int`s in the list
  `acc`. -/
  | bytes (cls acc it : V)

section
variable {m : Type → Type 1} {V : Type}

/-- The one argument of a constructor whose parser is `PyArg_UnpackTuple(args, name, 0, 1)` or
`_PyArg_CheckPositional(name, nargs, 0, 1)`, after `_PyArg_NoKeywords(kwName, kwargs)` when
`noKw`: a subclass whose own `__init__` or `__new__` takes the keywords passes them on. -/
def oneOptionalArg [PyReads m V] (name kwName : String) (noKw : Bool) (xs : Array V)
    (kwargs : V) : m (Option V) := do
  if noKw && (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" s!"{kwName}() takes no keyword arguments"
  if xs.size > 1 then raiseBuiltin "TypeError" s!"{name} expected at most 1 argument, got {xs.size}"
  return xs[0]?

/-! ## `list` -/

/-- **`list.__new__(cls, *args, **kwargs)`**, `PyType_GenericNew`: an empty list of `cls`. -/
def listNew [PyWrites m V] (_self args _kwargs : V) : m V := do
  let (cls, _) ← classAndArgs .list args
  if ← isExact cls .list then return ← PyPure.allocList #[]
  newSubInstance cls (.list #[])

/-- One activation of a `list.__init__` walk. -/
def listStep [PyWrites m V] (self it : V) : m (LoopStep V Unit) := do
  match ← forEachItem iterNext it () fun y _ => do
      PyWrites.listAppend self y
      pure (.next ()) with
  | .done _ => return .done ()
  | .more _ => return .more it

/-- The walk of `list_extend(self, x)` over an object that has no fast path: the iterator of
`x`, after the length hint and the reservation it gives. -/
def listExtendIter [PyWrites m V] (self x : V) : m V := do
  let it ← getIter x
  let n ← lengthHint x 8
  hintCheck n
  if n > 0 then PyWrites.listReserve self n
  return it

/-- The first step of `list_extend(self, iterable)`: an exact list or tuple is appended at once;
so is the list itself, its items as they are before the first append, which for an instance of
a subclass `PySequence_Fast` gathers through its iterator first. Otherwise the iterator, after
the length hint and the reservation it gives. -/
def listExtendFirst [PyWrites m V] (self x : V) : m (Option V) := do
  if (← classIs x .list) || (← classIs x .tuple) then
    let items ← match ← listOf? x with
      | some ys => pure ys
      | none => tupleItems x
    for y in items do PyWrites.listAppend self y
    return none
  if (← PyPure.identical self x) == .yes then
    let it ← tryCatch (getIter x) fun e => do
      if ← isTypeErrorExc e then raiseBuiltin "TypeError" "argument must be iterable"
      throw e
    -- `PySequence_List(it)`: a new list, extended by the iterator.
    let acc ← PyPure.allocList #[]
    let it2 ← listExtendIter acc it
    if (← listStep acc it2) matches .more _ then
      PyPure.gap "a list subclass extended by itself through a user iterator is not modelled yet"
    for y in (← listOf? acc).getD #[] do PyWrites.listAppend self y
    return none
  some <$> listExtendIter self x

/-- The first step of `list.__init__(self, iterable)`: the list is cleared, then extended. -/
def listInitFirst [PyWrites m V] (self x : V) : m (Option V) := do
  let some xs ← listOf? self | PyPure.modelInvariant "list.__init__ of a value that is not a list"
  PyWrites.listSplice self 0 xs.size #[]
  listExtendFirst self x

/-! ## `tuple` -/

/-- The first step of `tuple.__new__(cls, iterable)`: an exact tuple as it is for `tuple` itself,
an exact list's items at once, otherwise the iterator after the length hint. The items go into a
new list until the iterator ends. -/
def tupleFirst [PyWrites m V] (cls : V) (x : Option V) : m (Sum V (V × V)) := do
  let some x := x | return .inl (← tupleResult cls #[])
  if (← classIs x .tuple) then
    if ← isExact cls .tuple then return .inl x
    return .inl (← tupleResult cls (← tupleItems x))
  if let some ys ← listOf? x then
    if ← classIs x .list then return .inl (← tupleResult cls ys)
  let it ← getIter x
  hintCheck (← lengthHint x 10)
  return .inr (← PyPure.allocList #[], it)
where
  tupleResult (cls : V) (items : Array V) : m V := do
    if ← isExact cls .tuple then return PyPure.imm (m := m) (.tuple items)
    newSubInstance cls (.tuple items)

/-- One activation of a `tuple.__new__` walk: the tuple once the iterator ends. -/
def tupleStep [PyWrites m V] (cls acc it : V) : m (LoopStep V V) := do
  match ← forEachItem iterNext it () fun y _ => do
      PyWrites.listAppend acc y
      pure (.next ()) with
  | .more _ => return .more it
  | .done _ =>
    let some items ← listOf? acc | PyPure.modelInvariant "a tuple's items that stopped being a list"
    if ← isExact cls .tuple then return .done (PyPure.imm (m := m) (.tuple items))
    return .done (← newSubInstance cls (.tuple items))

/-! ## `set` and `frozenset` -/

/-- The members of the list `l` from position `i` on, added to `s` as CPython's list iterator
gives them: the list is read again at each step. -/
def addListLive [PyWrites m V] (w : SetWrites m V) (s l : V) : Nat → Nat → m Unit
  | 0, _ => PyPure.gap "a walk of a list that doesn't end"
  | fuel + 1, i => do
    let some xs ← listOf? l | PyPure.modelInvariant "a list walked that stopped being a list"
    let some x := xs[i]? | return
    w.add s x (some (← hash x)) (keyEq x)
    addListLive w s l fuel (i + 1)

/-- The first step of `set_update_internal(s, x)`: a set or frozenset (a subclass included)
merged; an exact dict's keys with their stored hashes; an exact built-in sequence's items at
once; otherwise the iterator. -/
def setFirst [PyWrites m V] (w : SetWrites m V) (s x : V) : m (Option V) := do
  if (← anySetLike? x).isSome then
    setMergeWith w s x
    return none
  if ← isDict x then
    guardDictWalk x s
    let es ← PyReads.dictEntries x
    w.reserve s es.size
    for (k, _, h) in es do w.add s k (some h) (keyEq k)
    return none
  if ← exactBuiltinIterable x then
    if (← listOf? x).isSome then
      addListLive w s x walkFuel 0
      return none
    for y in ← (← iterSeq x fun t => s!"'{t}' object is not iterable").items do
      w.add s y (some (← hash y)) (keyEq y)
    return none
  return some (← getIter x)

/-- One activation of a set walk. -/
def setStep [PyWrites m V] (w : SetWrites m V) (s it : V) : m (LoopStep V Unit) := do
  match ← forEachItem iterNext it () fun y _ => do
      w.add s y (some (← hash y)) (keyEq y)
      pure (.next ()) with
  | .done _ => return .done ()
  | .more _ => return .more it

/-- **`set.__new__(cls, *args, **kwargs)`**, `set_new`: an empty set of `cls`, whatever the
arguments; `set.__init__` rejects keywords. -/
def setNew [PyWrites m V] (_self args _kwargs : V) : m V := do
  let (cls, _) ← classAndArgs .set args
  if ← isExact cls .set then return ← PyPure.allocSet false false
  newSubInstance cls .set

/-- A new frozenset of `cls`, still open. -/
def openFrozenset [PyWrites m V] (cls : V) : m V := do
  if ← isExact cls .frozenset then PyPure.allocSet true false
  else newSubInstance cls .frozenset

/-! ## `dict` -/

/-- **`dict.__new__(cls, *args, **kwargs)`**: an empty dict of `cls`. -/
def dictNew [PyWrites m V] (_self args _kwargs : V) : m V := do
  let (cls, _) ← classAndArgs .dict args
  if ← isExact cls .dict then return ← PyPure.allocDict
  newSubInstance cls .dict

/-- `self[k] = v`, as `PyDict_SetItem`. -/
def dictPut [PyWrites m V] (self k v : V) : m Unit := do
  PyWrites.dictSet self k v (some (← hash k)) (keyEq k)

/-- The keywords of `dict(**kwargs)` merged, after `PyArg_ValidateKeywordArguments`. -/
def mergeKwargs [PyWrites m V] (self kwargs : V) : m Unit := do
  let es ← PyReads.dictEntries kwargs
  for (k, _, _) in es do
    if (← strText? k).isNone then raiseBuiltin "TypeError" "keywords must be strings"
  for (k, v, h) in es do PyWrites.dictSet self k v (some h) (keyEq k)

/-- The entries of the dict `x` (a subclass included) set in `self`, `dict_merge`'s fast path,
with a gap when the walk's comparisons may run user code. -/
def copyDict [PyWrites m V] (self x : V) : m Unit := do
  if WalkKinds.mayRunUser [← PyReads.dictWalkKinds x, ← PyReads.dictWalkKinds self] then
    PyPure.gap "a walk of a dict whose comparisons may run user code is not modelled yet"
  for (k, v, h) in ← PyReads.dictEntries x do PyWrites.dictSet self k v (some h) (keyEq k)

/-- Whether the class of `x` keeps `dict.__iter__`, the test of `dict_merge`'s fast path. -/
def keepsDictIter [PyReads m V] (x : V) : m Bool := do
  match ← lookupType (← PyReads.classOf x) "__iter__" with
  | some f => return ((← PyPure.immView f) matches some (.descr .dict "__iter__" _))
  | none => return false

/-- The first step of `PyDict_Merge(self, x)` (`dict_merge`): a dict (a subclass too) that keeps
`dict.__iter__` merged at once; else the keys protocol over the list that `x.keys()` returns, or
over the keys gathered from its iterator (`PyMapping_Keys`), which looks `keys` up once. -/
def dictMergeFirst [PyWrites m V] (self x kwargs : V) : m (Option (CollectState V)) := do
  if (← isDictLike x) && (← keepsDictIter x) then
    copyDict self x
    mergeKwargs self kwargs
    return none
  let keysF ← getAttr x "keys"
  let ks ← callN dispatchDepth keysF (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
  if ← classIs ks .list then return some (.dictKeysList self x ks kwargs 0)
  let it ← tryCatch (getIter ks) fun e => do
    if ← isTypeErrorExc e then
      raiseBuiltin "TypeError"
        s!"{← typeName x}.keys() returned a non-iterable (type {← typeName ks})"
    throw e
  -- `PySequence_List(it)`: `list_extend` takes the iterator of the iterator, and its hint.
  let it2 ← getIter it
  hintCheck (← lengthHint it 8)
  return some (.dictKeys self x it2 kwargs (← PyPure.allocList #[]))

/-- The first step of `dict_update_arg(self, x)`: an exact dict merged at once; for an object
with `keys`, `PyDict_Merge`; otherwise the pairs of its iterator. -/
def dictFirst [PyWrites m V] (self x kwargs : V) : m (Option (CollectState V)) := do
  if ← isDict x then
    copyDict self x
    mergeKwargs self kwargs
    return none
  let hasKeys ← tryCatch (do discard <| getAttr x "keys"; pure true) fun e => do
    if ← isAttributeError e then pure false else throw e
  if hasKeys then return ← dictMergeFirst self x kwargs
  return some (.dictPairs self (← getIter x) kwargs 0 none)

/-- The pair numbered `i`, as `PyDict_MergeFromSeq2` checks it: its length must be 2. -/
def putPair [PyWrites m V] (self : V) (i : Nat) (items : Array V) : m Unit := do
  let #[k, v] := items |
    raiseBuiltin "ValueError"
      s!"dictionary update sequence element #{i} has length {items.size}; 2 is required"
  dictPut self k v

/-- A `TypeError` raised while a pair is turned into a sequence (`PySequence_Fast`) becomes
CPython's message for the pair numbered `i`. -/
def asPairError [PyWrites m V] {α : Type} (i : Nat) (act : m α) : m α :=
  tryCatch act fun e => do
    if ← isTypeErrorExc e then
      raiseBuiltin "TypeError" s!"cannot convert dictionary update sequence element #{i} to a sequence"
    throw e

/-- One activation of `self[k] = other[k]` for the keys of the list `keys` from position `i`:
the list is read again at each step, since `other[k]` may change it, and one activation takes at
most the list's length when it began, and one more. -/
def dictKeysListStep [PyWrites m V] (self other keys kwargs : V) (i : Nat) :
    m (LoopStep (CollectState V) Unit) := do
  let some xs ← listOf? keys | PyPure.modelInvariant "a list of keys that stopped being a list"
  let mut j := i
  for _ in [0:xs.size + 1] do
    let some ys ← listOf? keys | PyPure.modelInvariant "a list of keys that stopped being a list"
    let some k := ys[j]? |
      mergeKwargs self kwargs
      return .done ()
    dictPut self k (← getItem other k)
    j := j + 1
  return .more (.dictKeysList self other keys kwargs j)

/-- One activation of the keys protocol while the keys are gathered into `acc`; once they are
all there, the first activation of the loop over them. -/
def dictKeysStep [PyWrites m V] (self other it kwargs acc : V) :
    m (LoopStep (CollectState V) Unit) := do
  match ← forEachItem iterNext it () fun k _ => do
      PyWrites.listAppend acc k
      pure (.next ()) with
  | .more _ => return .more (.dictKeys self other it kwargs acc)
  | .done _ => dictKeysListStep self other acc kwargs 0

/-- What one pair of the pairs walk does: an exact list or tuple, or another built-in container,
gives its items at once; a user iterable starts its own walk. -/
inductive PairStart (V : Type) where
  | items (xs : Array V)
  | walk (it : V)

/-- The start of the pair `x` numbered `i` (`PySequence_Fast`). -/
def pairStart [PyWrites m V] (i : Nat) (x : V) : m (PairStart V) := asPairError i do
  if let some ys ← listOf? x then
    if ← classIs x .list then return .items ys
  if ← classIs x .tuple then return .items (← tupleItems x)
  if ← exactBuiltinIterable x then
    return .items (← (← iterSeq x fun t => s!"'{t}' object is not iterable").items)
  -- `PySequence_List(iter(x))`: `list_extend` takes the iterator of the iterator, and its hint.
  let pit ← getIter x
  let pit2 ← getIter pit
  hintCheck (← lengthHint pit 8)
  return .walk pit2

/-- One activation of the pairs walk from the pair numbered `i`, with a pending inner walk. -/
def dictPairsStep [PyWrites m V] (self it kwargs : V) (i : Nat) (inner : Option (V × V)) :
    m (LoopStep (CollectState V) Unit) := do
  -- A pending pair's own walk goes on first.
  let i ← match inner with
    | none => pure i
    | some (pit, got) =>
      let walk ← asPairError i (forEachItem iterNext pit () fun y _ => do
        PyWrites.listAppend got y
        pure (.next ()))
      match walk with
      | .more _ => return .more (.dictPairs self it kwargs i (some (pit, got)))
      | .done _ =>
        let some items ← listOf? got |
          PyPure.modelInvariant "a pair's items that stopped being a list"
        putPair self i items
        pure (i + 1)
  let walk ← forEachItem iterNext it (i, (none : Option V)) fun x (i, _) => do
    match ← pairStart i x with
    | .items items =>
      putPair self i items
      pure (.next (i + 1, none))
    | .walk pit => pure (.stop (i, some pit))
  match walk with
  | .more (i, _) => return .more (.dictPairs self it kwargs i none)
  | .done (i, some pit) =>
    return .more (.dictPairs self it kwargs i (some (pit, ← PyPure.allocList #[])))
  | .done (_, none) =>
    mergeKwargs self kwargs
    return .done ()

/-! ## `bytes` -/

/-- The octet of the item `x` of `bytes(…)`: `x` through `PyNumber_AsSsize_t`, in `range(0, 256)`. -/
def octetOf [PyCalls m V] (x : V) : m UInt8 := do
  let some n ← indexValue? x |
    raiseBuiltin "TypeError" s!"'{← typeName x}' object cannot be interpreted as an integer"
  if n < 0 || n ≥ 256 then raiseBuiltin "ValueError" "bytes must be in range(0, 256)"
  return n.toNat.toUInt8

/-- `bytes` of the octets `b` for the class `cls`. -/
def bytesResult [PyReads m V] (cls : V) (b : Array UInt8) : m V := do
  if ← isExact cls .bytes then return PyPure.imm (m := m) (.bytes b)
  newSubInstance cls (.bytes b)

/-- The octets of the list `l`, read live as `_PyBytes_FromList` does: an item's `__index__` may
change the list. -/
def octetsOfListLive [PyCalls m V] (l : V) : Nat → Nat → Array UInt8 → m (Array UInt8)
  | 0, _, _ => PyPure.gap "a walk of a list that doesn't end"
  | fuel + 1, i, acc => do
    let some xs ← listOf? l | PyPure.modelInvariant "a list walked that stopped being a list"
    let some x := xs[i]? | return acc
    octetsOfListLive l fuel (i + 1) (acc.push (← octetOf x))

/-- The first step of `bytes.__new__(cls, source, encoding, errors)`, CPython's `bytes_new_impl`:
the result, or the list that gathers the octets of an iterator and the iterator. -/
def bytesFirst [PyWrites m V] (cls : V) (xs : Array V) (kwargs : V) : m (Sum V (V × V)) := do
  let sig : BuiltinSig :=
    { name := "bytes", qualname := "bytes", style := .keywords, maxpos := 3,
      kwnames := #["source", "encoding", "errors"] }
  let b ← bindBuiltinArgs sig (PyPure.imm (m := m) (.tuple xs)) kwargs
  let #[x, enc, err] := b.params |
    PyPure.modelInvariant "bytes: the binder gave a parameter array of another shape"
  let enc ← codecName "bytes" "encoding" enc
  let err ← codecName "bytes" "errors" err
  let some x := x | do
    if enc.isSome then raiseBuiltin "TypeError" "encoding without a string argument"
    if err.isSome then raiseBuiltin "TypeError" "errors without a string argument"
    return .inl (← bytesResult cls #[])
  let text ← strText? x
  if enc.isSome then
    let some s := text | raiseBuiltin "TypeError" "encoding without a string argument"
    match Codecs.encodeWith enc err s with
    | .ok o => return .inl (← bytesResult cls o)
    | .error e => raiseCodecError e x
  if err.isSome then
    raiseBuiltin "TypeError"
      (if text.isSome then "string argument without an encoding" else "errors without a string argument")
  let t ← PyReads.classOf x
  if let some f ← lookupType t "__bytes__" then
    let r ← callN dispatchDepth (← descrGetN dispatchDepth f (some x) t)
      (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
    let some o ← bytesOctets? r |
      raiseBuiltin "TypeError" s!"__bytes__ returned non-bytes (type {← typeName r})"
    -- `bytes` itself returns what `__bytes__` gave, a subclass's instance too.
    if ← isExact cls .bytes then return .inl r
    return .inl (← bytesResult cls o)
  if text.isSome then raiseBuiltin "TypeError" "string argument without an encoding"
  -- An integer is a size, unless its `__index__` raises `TypeError`.
  if (← lookupType t "__index__").isSome then
    let n? ← tryCatch (some <$> indexValue? x) fun e => do
      if ← isTypeErrorExc e then pure none else throw e
    if let some (some n) := n? then
      if n > (Format.ssizeMax : Int) || n < Arith.ssizeMin then
        raiseBuiltin "OverflowError" s!"cannot fit '{← typeName x}' into an index-sized integer"
      if n < 0 then raiseBuiltin "ValueError" "negative count"
      hintCheck n.toNat
      return .inl (← bytesResult cls (Array.replicate n.toNat 0))
  -- `PyBytes_FromObject`.
  if ← classIs x .bytes then
    if ← isExact cls .bytes then return .inl x
  if let some o ← bytesOctets? x then return .inl (← bytesResult cls o)
  if (← lookupType t "__buffer__").isSome then
    PyPure.gap "bytes() of an object with __buffer__ is not modelled yet"
  if ← classIs x .list then
    return .inl (← bytesResult cls (← octetsOfListLive x walkFuel 0 #[]))
  if ← classIs x .tuple then
    let mut acc : Array UInt8 := #[]
    for y in ← tupleItems x do acc := acc.push (← octetOf y)
    return .inl (← bytesResult cls acc)
  let it? ← tryCatch (some <$> getIter x) fun e => do
    if ← isTypeErrorExc e then pure none else throw e
  let some it := it? |
    raiseBuiltin "TypeError" s!"cannot convert '{← typeName x}' object to bytes"
  hintCheck (← lengthHint x 64)
  return .inr (← PyPure.allocList #[], it)

/-- One activation of a `bytes` walk: each item's octet, until the iterator ends. -/
def bytesStep [PyWrites m V] (cls acc it : V) : m (LoopStep V V) := do
  match ← forEachItem iterNext it () fun y _ => do
      let o ← octetOf y
      PyWrites.listAppend acc (PyPure.imm (m := m) (.int o.toNat))
      pure (.next ()) with
  | .more _ => return .more it
  | .done _ =>
    let some ys ← listOf? acc | PyPure.modelInvariant "the octets of bytes stopped being a list"
    let mut out : Array UInt8 := #[]
    for y in ys do
      let some (.int n) ← PyPure.immView y | PyPure.modelInvariant "an octet that is not an int"
      out := out.push n.toNat.toUInt8
    return .done (← bytesResult cls out)

/-! ## The machines -/

/-- One activation of the machine of the frame `st`: the result once its loop ends (the object
for `tuple` and `frozenset`, `None` for an `__init__`), or the frame to go on from. -/
def collectStep [PyWrites m V] [PyNew m V] : CollectState V → m (LoopStep (CollectState V) V)
  | .list self it => do
    match ← listStep self it with
    | .done _ => return .done (PyPure.imm (m := m) .none)
    | .more it => return .more (.list self it)
  | .tuple cls acc it => do
    match ← tupleStep cls acc it with
    | .done v => return .done v
    | .more it => return .more (.tuple cls acc it)
  | .set self it => do
    match ← setStep oldSetWrites self it with
    | .more it => return .more (.set self it)
    | .done _ => return .done (PyPure.imm (m := m) .none)
  | .frozenset self it => do
    match ← setStep newSetWrites self it with
    | .more it => return .more (.frozenset self it)
    | .done _ =>
      PyNew.setFreezeNew self
      return .done self
  | .dictKeys self other it kwargs acc => do
    match ← dictKeysStep self other it kwargs acc with
    | .done _ => return .done (PyPure.imm (m := m) .none)
    | .more st => return .more st
  | .dictKeysList self other keys kwargs i => do
    match ← dictKeysListStep self other keys kwargs i with
    | .done _ => return .done (PyPure.imm (m := m) .none)
    | .more st => return .more st
  | .dictPairs self it kwargs i inner => do
    match ← dictPairsStep self it kwargs i inner with
    | .done _ => return .done (PyPure.imm (m := m) .none)
    | .more st => return .more st
  | .bytes cls acc it => do
    match ← bytesStep cls acc it with
    | .done v => return .done v
    | .more it => return .more (.bytes cls acc it)

/-- **The first step of a container constructor**: for `list.__init__`, `set.__init__` and
`dict.__init__`, `self` and its arguments; for `tuple.__new__`, `frozenset.__new__` and
`bytes.__new__`, the class and its arguments. Its result, or the frame of its loop. -/
def collectFirst [PyWrites m V] [PyNew m V] (t : Builtin) (name : String) (xs : Array V)
    (kwargs : V) : m (LoopStep (CollectState V) V) := do
  let none' : V := PyPure.imm (m := m) .none
  match t, name with
  | .list, "__init__" =>
    let some self := xs[0]? | PyPure.modelInvariant "list.__init__ without self"
    let t ← PyReads.classOf self
    let noKw := (← classIs self .list) || (← sameEntry t .list "__new__")
    match ← oneOptionalArg "list" "list" noKw (xs.extract 1 xs.size) kwargs with
    | none =>
      let some ys ← listOf? self | PyPure.modelInvariant "list.__init__ of another value"
      PyWrites.listSplice self 0 ys.size #[]
      return .done none'
    | some x =>
      match ← listInitFirst self x with
      | none => return .done none'
      | some it => collectStep (.list self it)
  | .tuple, "__new__" =>
    let (cls, ys) ← classAndArgs .tuple (PyPure.imm (m := m) (.tuple xs))
    let noKw := (← isExact cls .tuple) || (← sameEntry cls .tuple "__init__")
    match ← tupleFirst cls (← oneOptionalArg "tuple" "tuple" noKw ys kwargs) with
    | .inl v => return .done v
    | .inr (acc, it) => collectStep (.tuple cls acc it)
  | .set, "__init__" =>
    let some self := xs[0]? | PyPure.modelInvariant "set.__init__ without self"
    let ys := xs.extract 1 xs.size
    -- The class name is read only for the error, since `classNameOf` may stop with a gap.
    let name ← if ys.size > 1 && !(← classIs self .set) then classNameOf (← PyReads.classOf self)
      else pure "set"
    let x ← oneOptionalArg name "set" true ys kwargs
    PyWrites.setClear self
    let some x := x | return .done none'
    match ← setFirst oldSetWrites self x with
    | none => return .done none'
    | some it => collectStep (.set self it)
  | .frozenset, "__new__" =>
    let (cls, ys) ← classAndArgs .frozenset (PyPure.imm (m := m) (.tuple xs))
    let name ← if ys.size > 1 && !(← isExact cls .frozenset) then classNameOf cls
      else pure "frozenset"
    let noKw := (← isExact cls .frozenset) || (← sameEntry cls .frozenset "__init__")
    let x ← oneOptionalArg name "frozenset" noKw ys kwargs
    if let some x := x then
      if (← isExact cls .frozenset) && (← classIs x .frozenset) then return .done x
    let fs ← openFrozenset cls
    let some x := x | do PyNew.setFreezeNew fs; return .done fs
    match ← setFirst newSetWrites fs x with
    | none =>
      PyNew.setFreezeNew fs
      return .done fs
    | some it => collectStep (.frozenset fs it)
  | .dict, "__init__" =>
    let some self := xs[0]? | PyPure.modelInvariant "dict.__init__ without self"
    let ys := xs.extract 1 xs.size
    if ys.size > 1 then raiseBuiltin "TypeError" s!"dict expected at most 1 argument, got {ys.size}"
    match ys[0]? with
    | none =>
      mergeKwargs self kwargs
      return .done none'
    | some x =>
      match ← dictFirst self x kwargs with
      | none => return .done none'
      | some st => collectStep st
  | .bytes, "__new__" =>
    let (cls, ys) ← classAndArgs .bytes (PyPure.imm (m := m) (.tuple xs))
    match ← bytesFirst cls ys kwargs with
    | .inl v => return .done v
    | .inr (acc, it) => collectStep (.bytes cls acc it)
  | _, _ => PyPure.modelInvariant s!"{t.info.name}.{name} is not a container constructor"

/-- The constructor of a callee, if it is one: its type, `__new__` or `__init__`, and its
arguments with `self` or the class first. -/
def collectCallee [PyReads m V] (f args : V) : m (Option (Builtin × String × Array V)) := do
  let xs ← tupleItems args
  let isCtor (t : Builtin) (n : String) : Bool :=
    (n == "__init__" && [Builtin.list, .set, .dict].contains t) ||
    (n == "__new__" && [Builtin.tuple, .frozenset, .bytes].contains t)
  match ← PyPure.immView f with
  | some (.bound self t n _) =>
    if !isCtor t n then return none
    -- A bound `__init__` has its `self`; a `__new__` gets its class as the first argument.
    return some (t, n, if n == "__init__" then #[self] ++ xs else xs)
  | some (.descr t n _) => return if isCtor t n then some (t, n, xs) else none
  | _ => return none

/-- **A container constructor inside another operation's step**: one walk, which must end. -/
def collectBody [PyWrites m V] [PyNew m V] (t : Builtin) (name : String) (self args kwargs : V) :
    m V := do
  let xs ← tupleItems args
  let xs := if name == "__init__" then #[self] ++ xs else xs
  match ← collectFirst t name xs kwargs with
  | .done v => return v
  | .more _ => midStepGap

/-- This file's bodies of the containers' `__new__` and `__init__`. -/
def collectionsMethod : Builtin → String → Option BuiltinImpl
  | .list, "__new__" => some fun {_} {_} [_] [_] => listNew
  | .set, "__new__" => some fun {_} {_} [_] [_] => setNew
  | .dict, "__new__" => some fun {_} {_} [_] [_] => dictNew
  | .list, "__init__" => some fun {_} {_} [_] [_] => collectBody .list "__init__"
  | .set, "__init__" => some fun {_} {_} [_] [_] => collectBody .set "__init__"
  | .dict, "__init__" => some fun {_} {_} [_] [_] => collectBody .dict "__init__"
  | .tuple, "__new__" => some fun {_} {_} [_] [_] => collectBody .tuple "__new__"
  | .frozenset, "__new__" => some fun {_} {_} [_] [_] => collectBody .frozenset "__new__"
  | .bytes, "__new__" => some fun {_} {_} [_] [_] => collectBody .bytes "__new__"
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
