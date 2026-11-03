/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Iter
public import StrataPython.Dyn.Sem.Library.Iterables

set_option autoImplicit false

/-!
# The lazy iterators: `zip`, `enumerate`, `reversed` and the reverse iterators

Generic over the record, CPython 3.12's `zip`, `enumerate` and `reversed` objects
(`Python/bltinmodule.c`, `Objects/enumobject.c`), `list.__reversed__`'s `list_reverseiterator`
(`Objects/listobject.c`), and `dict.__reversed__`'s reverse iterators, whose `__next__` and
`__length_hint__` also serve the value and item kinds (`dict_reversevalueiterator`,
`dict_reverseitemiterator`, `Objects/dictobject.c`). Each object holds a state of `IterStateG`,
whose kind is its class: `__new__` stops with a gap for a subclass of `zip`, `enumerate` or
`reversed`. Each `__next__` steps its own state, never through `iterStep` on its own object.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The arguments of `T.__new__(cls, …)` after `cls`, once `cls` is checked to be exactly the
built-in type `t`: a subclass stops with a gap. -/
def exactNew [PyWrites m V] (t : Builtin) (args : V) : m (Array V) := do
  let xs ← tupleItems args
  let some cls := xs[0]? |
    PyPure.modelInvariant s!"{t.info.name}.__new__ called without its class"
  let exact := match ← PyPure.immView cls with
    | some (.builtin b) => b == t
    | _ => false
  unless exact do PyPure.gap s!"a subclass of {t.info.name} is not modelled"
  return xs.extract 1 xs.size

/-! ## `zip` -/

/-- **`zip.__new__(cls, *iterables, strict=False)`**, CPython's `zip_new`: the keyword `strict`
(its truth, `p`), then the iterator of each argument, in order. -/
def zipNew [PyWrites m V] (_self args kwargs : V) : m V := do
  let xs ← exactNew .zip args
  let sig : BuiltinSig :=
    { name := "zip", qualname := "zip", style := .keywords, kwnames := #["strict"] }
  let b ← bindBuiltinArgs sig (PyPure.imm (m := m) (.tuple #[])) kwargs
  let #[strict] := b.params |
    PyPure.modelInvariant "zip: the binder gave a parameter array of another shape"
  let strict ← match strict with
    | some v => truthy v
    | none => pure false
  let iters ← xs.mapM getIter
  newIter .zip (.zip iters strict)

/-- The next item of the iterator `it`, `none` when it ends; with `catchStop`, a `StopIteration`
raised by a user `__next__` is an end too. Any other exception propagates, as `tp_iternext`'s
caller sees it. -/
def stepInner [PyWrites m V] (catchStop : Bool) (it : V) : m (Option V) :=
  if catchStop then iterNext it else iterStep it

/-- `"s 1-"` or `" "`: the plural of `zip`'s length messages, which name the arguments before
the `i`-th (from 0) as "argument 1" or "arguments 1-i". -/
def zipPlural (i : Nat) : String := if i == 1 then " " else "s 1-"

/-- The check of `zip(strict=True)` after the `i`-th iterator (from 0) ended: `ValueError` if an
earlier one didn't end, or if a later one still gives an item. -/
def zipStrictCheck [PyWrites m V] (iters : Array V) (i : Nat) : m V := do
  if i > 0 then
    raiseBuiltin "ValueError"
      s!"zip() argument {i + 1} is shorter than argument{zipPlural i}{i}"
  for j in [1:iters.size] do
    if let some it := iters[j]? then
      if (← stepInner true it).isSome then
        raiseBuiltin "ValueError"
          s!"zip() argument {j + 1} is longer than argument{zipPlural j}{j}"
  raiseStop

/-- **`zip.__next__(self)`**, CPython's `zip_next`: a tuple of the next item of each iterator.
When one ends, the zip ends, and its state stays: CPython calls the iterators again at the next
step. Without `strict`, a `StopIteration` that a user `__next__` raised propagates as it is. -/
def zipNext [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__next__" args kwargs
  let some (.iter (.zip iters strict)) ← PyReads.objView self |
    PyPure.modelInvariant "zip.__next__ on an object that is not a zip"
  if iters.isEmpty then raiseStop
  let mut items : Array V := #[]
  for h : i in [0:iters.size] do
    match ← stepInner strict iters[i] with
    | some x => items := items.push x
    | none => if strict then return ← zipStrictCheck iters i else raiseStop
  return PyPure.imm (m := m) (.tuple items)

/-! ## `enumerate` -/

/-- Whether `enumerate_vectorcall` accepts `nargs` positional arguments and the keyword names
`kws`, in their order: it takes the same calls as `enumerate.__new__`'s parser, but raises other
messages for the others. -/
def enumerateVectorcallAccepts (nargs : Nat) (kws : List String) : Bool :=
  match nargs, kws with
  | 1, [] | 2, [] | 1, ["start"] | 0, ["iterable"] => true
  | 0, ["iterable", "start"] | 0, ["start", "iterable"] => true
  | _, _ => false

/-- **`enumerate.__new__(cls, iterable, start=0)`**, CPython's `enum_new_impl`: `start` through
`PyNumber_Index` first, then the iterator of `iterable`. A call of `enumerate` goes through the
type's vectorcall, an explicit `enumerate.__new__` through the argument parser, and a body can't
tell them apart. Both accept the same calls; for the others, both give the same message only
with no keyword and more than two arguments, so every other wrong call stops with a gap. -/
def enumerateNew [PyWrites m V] (_self args kwargs : V) : m V := do
  let xs ← exactNew .enumerate args
  let kws ← (← PyReads.dictEntries kwargs).toList.mapM fun (k, _, _) => do
    match ← str? k with
    | some s => pure s
    | none => PyPure.gap "a keyword argument of enumerate that is not a str"
  unless enumerateVectorcallAccepts xs.size kws do
    unless kws.isEmpty && xs.size > 2 do
      PyPure.gap "the message of this wrong call of enumerate depends on how it is called"
  let sig : BuiltinSig :=
    { name := "enumerate", qualname := "enumerate", style := .keywords, minpos := 1,
      maxpos := 2, kwnames := #["iterable", "start"] }
  let b ← bindBuiltinArgs sig (PyPure.imm (m := m) (.tuple xs)) kwargs
  let #[some iterable, start] := b.params |
    PyPure.modelInvariant "enumerate: the binder gave a parameter array of another shape"
  let count ← match start with
    | none => pure 0
    | some v =>
      match ← indexValue? v with
      | some n => pure n
      | none =>
        raiseBuiltin "TypeError" s!"'{← typeName v}' object cannot be interpreted as an integer"
  let it ← getIter iterable
  newIter .enumerate (.enumerate it count)

/-- **`enumerate.__next__(self)`**, CPython's `enum_next`: the pair of the count and the next
item of the iterator. When the iterator ends, the state stays, as in CPython; a `StopIteration`
that a user `__next__` raised propagates as it is. -/
def enumerateNext [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__next__" args kwargs
  let some (.iter (.enumerate it _)) ← PyReads.objView self |
    PyPure.modelInvariant "enumerate.__next__ on an object that is not an enumerate"
  let some x ← iterStep it | raiseStop
  -- `enum_next` reads the count after the step, which may have stepped this enumerate.
  let some (.iter (.enumerate _ count)) ← PyReads.objView self |
    PyPure.modelInvariant "an enumerate that changed its kind"
  PyWrites.iterSet self (.enumerate it (count + 1))
  return PyPure.imm (m := m) (.tuple #[PyPure.imm (m := m) (.int count), x])

/-! ## `reversed` and the reverse iterators -/

/-- Whether `v` is an instance of `dict` or of a subclass of it (`PyDict_Check`). -/
def isDictInstance [PyReads m V] (v : V) : m Bool := isInstanceOfBuiltin v .dict

/-- **`PySequence_Check(v)`**: not a dict, and its type has `sq_item`. A user class with any
`__getitem__` has it, as `type_new` fills the slot from the name; of the built-in types, a list, a
tuple, a `str`, a `bytes` and a range have it, and another built-in `__getitem__` (a mapping's)
stops with a gap. -/
def sequenceCheck [PyCalls m V] (v : V) : m Bool := do
  if ← isDictInstance v then return false
  match ← lookupType (← PyReads.classOf v) "__getitem__" with
  | none => return false
  | some f =>
    if ← isUserObject v then return true
    match ← PyPure.immView f with
    | some (.descr t "__getitem__" _) =>
      if [Builtin.list, .tuple, .str, .bytes, .range].contains t then return true
      PyPure.gap s!"whether a {t.info.name} is a sequence is not modelled"
    | _ => return true

/-- **`reversed.__new__(cls, seq)`**, CPython's `reversed_new_impl`: `seq.__reversed__()` if its
type has one (`None` means not reversible); else, for a sequence, a `reversed` object from its
last index, which `len(seq)` gives. -/
def reversedNew [PyWrites m V] (_self args kwargs : V) : m V := do
  let xs ← exactNew .reversed args
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" "reversed() takes no keyword arguments"
  let #[seq] := xs |
    raiseBuiltin "TypeError"
      s!"reversed expected 1 argument, got {xs.size}"
  let t ← PyReads.classOf seq
  match ← lookupType t "__reversed__" with
  | some f =>
    -- `_PyObject_LookupSpecial` binds the attribute first, so a `None` that a descriptor gives
    -- counts too.
    let g ← descrGetN dispatchDepth f (some seq) t
    if (← PyPure.immView g) matches some .none then
      raiseBuiltin "TypeError" s!"'{← typeName seq}' object is not reversible"
    callN dispatchDepth g (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
  | none =>
    unless ← sequenceCheck seq do
      raiseBuiltin "TypeError" s!"'{← typeName seq}' object is not reversible"
    let n ← pyLen seq
    newIter .reversed (.reversed .reversed seq ((n : Int) - 1))

/-- **`reversed.__next__(self)`**, CPython's `reversed_next`: `seq[index]`, going down. An
`IndexError` or `StopIteration` from `__getitem__` ends it; any other exception ends it too, and
propagates. Once it ends, it stays ended. -/
def reversedNext [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__next__" args kwargs
  match ← PyReads.objView self with
  | some (.iter (.done _)) => raiseStop
  | some (.iter (.reversed k seq i)) =>
    if i ≥ 0 then
      if ← isUserObject seq then
        if (← lookupType (← PyReads.classOf seq) "__getitem__").isNone then
          PyPure.gap "a reversed whose sequence's class lost __getitem__ is not modelled yet"
      let r ← tryCatch (some <$> getItem seq (PyPure.imm (m := m) (.int i))) fun x => do
        if (← isIndexErrorExc x) || (← isStopIterationExc x) then pure none
        else
          PyWrites.iterSet self (.done k)
          throw x
      if let some v := r then
        -- `__getitem__` may have stepped or ended this iterator: `reversed_next` decrements the
        -- index it holds now, and an ended iterator stays ended.
        if let some (.iter (.reversed _ _ j)) ← PyReads.objView self then
          PyWrites.iterSet self (.reversed k seq (j - 1))
        return v
    PyWrites.iterSet self (.done k)
    raiseStop
  | _ => PyPure.modelInvariant "reversed.__next__ on an object that is not a reversed"

/-- **`reversed.__length_hint__(self)`**, CPython's `reversed_len`: 0 once it ended; else the
items left, `index + 1`, or 0 if `len(seq)` is now smaller. -/
def reversedLengthHint [PyWrites m V] (self args kwargs : V) : m V := do
  noArgsMethod .reversed "__length_hint__" self args kwargs
  match ← PyReads.objView self with
  | some (.iter (.done _)) => return PyPure.imm (m := m) (.int 0)
  | some (.iter (.reversed _ seq _)) =>
    let n ← pyLen seq
    -- `reversed_len` reads the index after `__len__`, which may have stepped or ended the iterator.
    match ← PyReads.objView self with
    | some (.iter (.reversed _ _ i)) =>
      return PyPure.imm (m := m) (.int (if (n : Int) < i + 1 then 0 else i + 1))
    | _ => return PyPure.imm (m := m) (.int 0)
  | _ => PyPure.modelInvariant "reversed.__length_hint__ on an object that is not a reversed"

/-- **`list.__reversed__(self)`**, CPython's `list___reversed___impl`: a `list_reverseiterator`
from the last index. -/
def listReversed [PyWrites m V] (self args kwargs : V) : m V := do
  noArgsMethod .list "__reversed__" self args kwargs
  let some xs ← listOf? self |
    PyPure.modelInvariant "list.__reversed__ of a value that is not a list"
  newIter .list_reverseiterator (.reversed .list_reverseiterator self ((xs.size : Int) - 1))

/-- **`list_reverseiterator.__next__(self)`**, CPython's `listreviter_next`: the item at `index`
while it is below the list's current length, going down. Once it ends, it stays ended. -/
def listRevNext [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__next__" args kwargs
  match ← PyReads.objView self with
  | some (.iter (.done _)) => raiseStop
  | some (.iter (.reversed k l i)) =>
    let some xs ← listOf? l |
      PyPure.modelInvariant "a list_reverseiterator over a value that is not a list"
    if h : 0 ≤ i ∧ i.toNat < xs.size then
      PyWrites.iterSet self (.reversed k l (i - 1))
      return xs[i.toNat]
    PyWrites.iterSet self (.done k)
    raiseStop
  | _ => PyPure.modelInvariant "list_reverseiterator.__next__ on another object"

/-- **`list_reverseiterator.__length_hint__(self)`**, CPython's `listreviter_len`: `index + 1`,
or 0 once it ended or if the list is now shorter. -/
def listRevLengthHint [PyWrites m V] (self args kwargs : V) : m V := do
  noArgsMethod .list_reverseiterator "__length_hint__" self args kwargs
  match ← PyReads.objView self with
  | some (.iter (.done _)) => return PyPure.imm (m := m) (.int 0)
  | some (.iter (.reversed _ l i)) =>
    let some xs ← listOf? l |
      PyPure.modelInvariant "a list_reverseiterator over a value that is not a list"
    return PyPure.imm (m := m) (.int (if (xs.size : Int) < i + 1 then 0 else i + 1))
  | _ => PyPure.modelInvariant "list_reverseiterator.__length_hint__ on another object"

/-- The reverse iterator of the kind `k` over the dict `d`: from its last entry, with its size,
its keys' version and its length (CPython's `dictreviter_new`). -/
def dictRevIter [PyWrites m V] (k : Builtin) (d : V) : m V := do
  let n ← PyReads.dictLen d
  let last : Int := (← PyReads.dictEntriesSize d : Int) - 1
  newIter k (.dictReversed k d last n (← PyReads.dictFlags d).2 n)

/-- **`dict.__reversed__(self)`**: a `dict_reversekeyiterator`. -/
def dictReversed [PyWrites m V] (self args kwargs : V) : m V := do
  noArgsMethod .dict "__reversed__" self args kwargs
  dictRevIter .dict_reversekeyiterator self

/-- The position and the entry of the last entry of the dict `d` at or before `i`, scanning down
over the holes, or none. -/
def dictEntryDownFrom [PyReads m V] (d : V) (i : Int) : m (Option (Int × V × V)) := do
  let mut j := i
  for _ in [0:(i + 1).toNat] do
    match ← PyReads.dictEntryAt d j.toNat with
    | .entry k v _ => return some (j, k, v)
    | .hole | .past => j := j - 1
  return none

/-- **`__next__` of a dict reverse iterator**, CPython's `dictreviter_iternext`: a change of the
dict's size raises `RuntimeError` and stays failed; a change of its keys at the same size stops
with a gap, as the forward iterators do, since the model's entry layout differs from CPython's
then. Once it ends, it stays ended. -/
def dictRevNext [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__next__" args kwargs
  match ← PyReads.objView self with
  | some (.iter (.done _)) => raiseStop
  | some (.iter (.failed _ msg)) => raiseBuiltin "RuntimeError" msg
  | some (.iter (.dictReversed k d i size ver left)) =>
    if (← PyReads.dictLen d) != size then
      let msg := "dictionary changed size during iteration"
      PyWrites.iterSet self (.failed k msg)
      raiseBuiltin "RuntimeError" msg
    if (← PyReads.dictFlags d).2 != ver then
      PyPure.gap
        "a dict whose keys changed at the same size during its iteration is not modelled yet"
    match ← dictEntryDownFrom d i with
    | some (j, key, v) =>
      PyWrites.iterSet self (.dictReversed k d (j - 1) size ver (left - 1))
      return match k with
        | .dict_reversevalueiterator => v
        | .dict_reverseitemiterator => PyPure.imm (m := m) (.tuple #[key, v])
        | _ => key
    | none =>
      PyWrites.iterSet self (.done k)
      raiseStop
  | _ => PyPure.modelInvariant "a dict reverse iterator's __next__ on another object"

/-- The kind of the dict reverse iterator `self`. -/
def dictRevKind [PyReads m V] (self : V) : m Builtin := do
  match ← PyReads.objView self with
  | some (.iter (.dictReversed k ..)) | some (.iter (.done k)) | some (.iter (.failed k _)) =>
    return k
  | _ => PyPure.modelInvariant "a dict reverse iterator's method on another object"

/-- **`__length_hint__` of a dict reverse iterator**, CPython's `dictiter_len`: the items left
while the dict's size is still the one it started with; else 0, also once it ended or failed. -/
def dictRevLengthHint [PyWrites m V] (self args kwargs : V) : m V := do
  noArgsMethod (← dictRevKind self) "__length_hint__" self args kwargs
  match ← PyReads.objView self with
  | some (.iter (.dictReversed _ d _ size _ left)) =>
    let n := if (← PyReads.dictLen d) == size then left else 0
    return PyPure.imm (m := m) (.int n)
  | some (.iter (.done _)) | some (.iter (.failed ..)) => return PyPure.imm (m := m) (.int 0)
  | _ => PyPure.modelInvariant "a dict reverse iterator's __length_hint__ on another object"

/-- The iterator types whose entries this file fills. -/
def lazyIterTypes : List Builtin :=
  [.zip, .enumerate, .reversed, .list_reverseiterator, .dict_reversekeyiterator,
    .dict_reversevalueiterator, .dict_reverseitemiterator]

/-- **The bodies of the entries `t.name`** that this file fills. -/
def iteratorsMethod (t : Builtin) (name : String) : Option BuiltinImpl :=
  match t, name with
  | .zip, "__new__" => some fun {_} {_} [_] [_] => zipNew
  | .zip, "__next__" => some fun {_} {_} [_] [_] => zipNext
  | .enumerate, "__new__" => some fun {_} {_} [_] [_] => enumerateNew
  | .enumerate, "__next__" => some fun {_} {_} [_] [_] => enumerateNext
  | .reversed, "__new__" => some fun {_} {_} [_] [_] => reversedNew
  | .reversed, "__next__" => some fun {_} {_} [_] [_] => reversedNext
  | .reversed, "__length_hint__" => some fun {_} {_} [_] [_] => reversedLengthHint
  | .list, "__reversed__" => some fun {_} {_} [_] [_] => listReversed
  | .list_reverseiterator, "__next__" => some fun {_} {_} [_] [_] => listRevNext
  | .list_reverseiterator, "__length_hint__" => some fun {_} {_} [_] [_] => listRevLengthHint
  | .dict, "__reversed__" => some fun {_} {_} [_] [_] => dictReversed
  | .dict_reversekeyiterator, "__next__" | .dict_reversevalueiterator, "__next__"
  | .dict_reverseitemiterator, "__next__" => some fun {_} {_} [_] [_] => dictRevNext
  | .dict_reversekeyiterator, "__length_hint__" | .dict_reversevalueiterator, "__length_hint__"
  | .dict_reverseitemiterator, "__length_hint__" =>
    some fun {_} {_} [_] [_] => dictRevLengthHint
  | t, "__iter__" => if lazyIterTypes.contains t then some fun {_} {_} [_] [_] => iterSelfBody
    else none
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
