/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Ops

set_option autoImplicit false

/-!
# Containers

Generic over the record of primitives, CPython 3.12's operations on its built-in containers: the
sequences `tuple`, `list`, `str`, `bytes` and `range`, dicts, sets and frozensets.

* `getItem` with an index or a slice, `setItem` and `delItem` on a list, with CPython's
  `IndexError`s and `TypeError`s;
* `containsCore`: membership in a sequence, a substring of a `str`, a byte or a sub-`bytes` of a
  `bytes`, a dict or a set;
* `unpackSeq` and `unpackEx`, with CPython's `ValueError`s;
* `hash`: CPython's `PyObject_Hash` on built-in values;
* dicts: item access, `in`, `==`, `|` and `|=`;
* sets and frozensets: displays, `in`, the subset order, `|`, `&`, `-`, `^` and their in-place
  forms.

A user object, or an instance of a user subclass of a built-in type, goes through its type's
dunders, in the order of CPython's slots.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

/-- A built-in sequence. -/
inductive Seq (V : Type) where
  | tuple (xs : Array V)
  /-- A list, the object `obj`, with its elements as they were when the view was taken: a consumer
  that runs user code in between reads them again. -/
  | list (obj : V) (xs : Array V)
  | str (s : PyStr)
  | bytes (b : Array UInt8)
  | range (start stop step : Int)

/-- The name of a sequence's type in CPython's messages. -/
def Seq.typeName {V : Type} : Seq V → String
  | .tuple _ => "tuple" | .list .. => "list" | .str _ => "str" | .bytes _ => "bytes"
  | .range .. => "range"

/-- The number of elements of a sequence. -/
def Seq.length {V : Type} : Seq V → Nat
  | .tuple xs | .list _ xs => xs.size
  | .str s => s.length
  | .bytes b => b.size
  | .range a b c => rangeLen a b c

section
variable {m : Type → Type 1} {V : Type}

/-- `v` as a built-in sequence, if it is one or an instance of a subclass of one. -/
def seqOf [PyCalls m V] (v : V) : m (Option (Seq V)) := do
  match ← PyPure.immView v with
  | some (.tuple xs) => pure (some (.tuple xs))
  | some (.str s) => pure (some (.str s))
  | some (.bytes b) => pure (some (.bytes b))
  | some (.range a b c) => pure (some (.range a b c))
  | some _ => pure none
  | none =>
    if ← PyPure.isUndef v then return none
    match ← PyReads.listView v with
    | some (xs, _) => pure (some (.list v xs))
    | none => match ← seqImm? v with
      | some (.tuple xs) => pure (some (.tuple xs))
      | some (.str t) => pure (some (.str t))
      | some (.bytes b) => pure (some (.bytes b))
      | _ => pure none

/-- Raise what `Arith` says CPython raises, or stop with a gap where it isn't modelled. -/
def ofFailure [PyCalls m V] {α : Type} : Format.Failure → m α
  | .raise cls msg => raiseBuiltin cls msg
  | .notModelled what => PyPure.gap s!"not modelled: {what}"

/-- `v` as an index, as `PyNumber_Index` converts it (`indexValue?`); `none` for a value whose
type has no `__index__`. -/
def indexOf [PyCalls m V] (v : V) : m (Option Int) := indexValue? v


/-- A bound of a slice: `None`, or an index; otherwise CPython's `TypeError`. -/
def sliceBound [PyCalls m V] (v : V) : m (Option Int) := do
  if (← PyPure.immView v) matches some .none then return none
  match ← indexOf v with
  | some i => pure (some i)
  | none => raiseBuiltin "TypeError" "slice indices must be integers or None or have an __index__ method"

/-- The bounds of the slice `lo:hi:step`, as CPython's `PySlice_Unpack` gives them: the step
converted first, and a zero step a `ValueError` before the start and the stop are converted; each
conversion may run user code. -/
def sliceBounds [PyCalls m V] (lo hi step : V) : m (Option Int × Option Int × Option Int) := do
  let st ← sliceBound step
  if st == some 0 then raiseBuiltin "ValueError" "slice step cannot be zero"
  let a ← sliceBound lo
  let b ← sliceBound hi
  pure (a, b, st)

/-- The indices that the slice bounds `bs` select in a sequence of `n` elements, as CPython's
`PySlice_AdjustIndices` does. -/
def sliceIdxOf [PyCalls m V] (bs : Option Int × Option Int × Option Int) (n : Nat) :
    m Arith.SliceIndices :=
  match Arith.sliceIndices bs.1 bs.2.1 bs.2.2 n with
  | .ok ix => pure ix
  | .error f => ofFailure f

/-- Whether converting `v` to an index or a slice bound may run user code: anything but an `int`, a
`bool` and `None` (an object's `__index__`). -/
def convRunsCode [PyPure m V] (v : V) : m Bool := do
  match ← PyPure.immView v with
  | some (.int _) | some (.bool _) | some .none => pure false
  | _ => pure true

/-- Whether converting the bounds `a`, `b` and `c` of a slice may run user code. -/
def boundsRunCode [PyPure m V] (a b c : V) : m Bool := do
  return (← convRunsCode a) || (← convRunsCode b) || (← convRunsCode c)

/-- Whether an index that is the immediate `kv` (`none` for an object) may run user code when it
is converted: anything but an `int` and a `bool`. -/
def immIndexRunsCode (kv : Option (Imm V)) : Bool :=
  !(kv matches some (.int _) || kv matches some (.bool _))

/-- The elements of the list `l` as they are now. -/
def listElems [PyReads m V] (l : V) : m (Array V) := do
  let some xs ← listOf? l | PyPure.modelInvariant "a list that is no longer a list"
  pure xs

/-- A sequence with a list's elements read again (`listElems`) when `again`, that is, when a
conversion may have run user code; any other sequence as it is, since it can't change. -/
def Seq.refresh [PyReads m V] (again : Bool) : Seq V → m (Seq V)
  | .list l xs => do if again then pure (.list l (← listElems l)) else pure (.list l xs)
  | s => pure s

/-- The positions that slice indices select, in order. -/
def SliceIdx.positions (ix : Arith.SliceIndices) : List Nat :=
  (List.range ix.length).map fun (i : Nat) => (ix.start + (i : Int) * ix.step).toNat

/-- Element `i` of a sequence, `i` in range. -/
def Seq.at [PyPure m V] (s : Seq V) (i : Nat) : V :=
  match s with
  | .tuple xs | .list _ xs => xs.getD i (PyPure.imm (m := m) .none)
  | .str t =>
    -- A `str` is indexed in constant time, after a non-ASCII one's first use builds its characters
    -- (`PyStr.charAt`).
    let ch := t.charAt i
    PyPure.imm (m := m) (.str (.ofString (String.singleton ch)))
  | .bytes b => PyPure.imm (m := m) (.int (b.getD i 0).toNat)
  | .range a _ c => PyPure.imm (m := m) (.int (a + i * c))

/-- The elements of a sequence; a gap for more than `maxRepeat`, where CPython may raise
`MemoryError`. -/
def Seq.items [PyPure m V] (s : Seq V) : m (Array V) := do
  match s with
  | .tuple xs | .list _ xs => pure xs
  | .str t => pure (t.s.toList.toArray.map fun c =>
    PyPure.imm (m := m) (.str (.ofString (String.singleton c))))
  | .bytes b => pure (b.map fun x => PyPure.imm (m := m) (.int x.toNat))
  | .range a b c =>
    let n := rangeLen a b c
    if n > maxRepeat then PyPure.gap "the elements of a range too long to model"
    pure ((List.range n).toArray.map fun (i : Nat) => PyPure.imm (m := m) (.int (a + (i : Int) * c)))

/-- `IndexError` for an index `i`, converted from `key`, that a C `Py_ssize_t` can't hold, as
`PyNumber_AsSsize_t` raises it, naming `key`'s type. -/
def fitIndex [PyCalls m V] (key : V) (i : Int) : m Unit := do
  if i < Arith.ssizeMin ∨ i > (Format.ssizeMax : Int) then
    raiseBuiltin "IndexError" s!"cannot fit '{← typeName key}' into an index-sized integer"

/-- The message of an index out of range of a sequence. -/
def Seq.rangeMsg {V : Type} : Seq V → String
  | .tuple _ => "tuple index out of range" | .list .. => "list index out of range"
  | .str _ => "string index out of range" | .bytes _ => "index out of range"
  | .range .. => "range object index out of range"

/-- The position of the index `i` in a sequence of `n` elements, counting a negative one from
the end, if it is in range. -/
def position (i : Int) (n : Nat) : Option Nat :=
  let j := if i < 0 then i + n else i
  if 0 ≤ j ∧ j < n then some j.toNat else none

/-- A bound of a slice of a range, as `evaluate_slice_index` converts it: `none` for `None`. -/
def rangeSliceIndex [PyCalls m V] (v : V) : m (Option Int) := do
  if (← PyPure.immView v) matches some .none then return none
  let some i ← indexValue? v |
    raiseBuiltin "TypeError" "slice indices must be integers or None or have an __index__ method"
  return some i

/-- **`range(a, z, c)[lo:hi:st]`, CPython's `compute_slice`**: the slice indices of
`_PySlice_GetLongIndices` over the range's length, with no `Py_ssize_t` bound, then the range of
the items at them. -/
def rangeSlice [PyCalls m V] (a z c : Int) (lo hi st : V) : m V := do
  let len : Int := rangeLen a z c
  let step ← match ← rangeSliceIndex st with
    | none => pure 1
    | some 0 => raiseBuiltin "ValueError" "slice step cannot be zero"
    | some s => pure s
  let (lower, upper) := if step < 0 then (-1, len - 1) else (0, len)
  let clamp (i : Int) : Int :=
    if i < 0 then max (i + len) lower else min i upper
  let start := match ← rangeSliceIndex lo with
    | none => if step < 0 then upper else lower
    | some i => clamp i
  let stop := match ← rangeSliceIndex hi with
    | none => if step < 0 then lower else upper
    | some i => clamp i
  pure (PyPure.imm (m := m) (.range (a + start * c) (a + stop * c) (c * step)))

/-- `s[a:b:c]` for a built-in sequence. -/
def sliceOf [PyCalls m V] (s : Seq V) (lo hi step : V) : m V := do
  if let .range a z c := s then return ← rangeSlice a z c lo hi step
  let bs ← sliceBounds lo hi step
  let s ← s.refresh (← boundsRunCode lo hi step)
  let ix ← sliceIdxOf bs s.length
  let ps := SliceIdx.positions ix
  match s with
  | .tuple xs => pure (PyPure.imm (m := m) (.tuple (ps.toArray.map fun p => xs.getD p (PyPure.imm (m := m) .none))))
  | .list _ xs => PyPure.allocList (ps.toArray.map fun p => xs.getD p (PyPure.imm (m := m) .none))
  | .str t =>
    pure (PyPure.imm (m := m) (.str (.ofString (String.ofList (ps.map t.charAt)))))
  | .bytes b => pure (PyPure.imm (m := m) (.bytes (ps.toArray.map fun p => b.getD p 0)))
  | .range a z c => rangeSlice a z c lo hi step

/-- `obj[key]` for a built-in sequence: an index or a slice. -/
def seqGetItem [PyCalls m V] (s : Seq V) (key : V) : m V := do
  let kv ← PyPure.immView key
  if let some (.slice a b c) := kv then return ← sliceOf s a b c
  match ← indexOf key with
  | some i =>
    if !(s matches .range ..) then fitIndex key i
    let s ← s.refresh (immIndexRunsCode kv)
    match position i s.length with
    | some p => pure (s.at (m := m) p)
    | none => raiseBuiltin "IndexError" s.rangeMsg
  | none =>
    let t ← typeName key
    match s with
    | .str _ => raiseBuiltin "TypeError" s!"string indices must be integers, not '{t}'"
    | .bytes _ => raiseBuiltin "TypeError" s!"byte indices must be integers or slices, not {t}"
    | _ => raiseBuiltin "TypeError" s!"{s.typeName} indices must be integers or slices, not {t}"

/-- The built-in types whose instances CPython can't hash. -/
def unhashableTypes : List String := ["list", "dict", "set", "bytearray", "dict_keys", "dict_items"]

/-- CPython's `PyObject_Hash`, with `fuel` the depth of nested tuples left: an immediate's hash, a
tuple's or a slice's from its members', the address hash of an object whose built-in type hashes
by identity, a user object's `__hash__`, and `TypeError` for an instance of an unhashable type.
Any other object stops with a gap. -/
def hashN [PyCalls m V] : Nat → V → m Hash
  | 0, _ => PyPure.gap "a hash of values nested deeper than the model follows"
  | fuel + 1, v => do
    if let some h ← PyPure.immHash v then return h
    match ← PyPure.immView v with
    | some (.tuple xs) => return tupleHash (← xs.toList.mapM (hashN fuel))
    | some (.slice a b c) => return sliceHash [← hashN fuel a, ← hashN fuel b, ← hashN fuel c]
    | some _ => PyPure.gap "the hash of this value is not modelled yet"
    | none =>
      if ← PyPure.isUndef v then PyPure.gap "the hash of an undefined value"
      match ← PyPure.immView (← PyReads.classOf v) with
      | some (.builtin b) =>
        if unhashableTypes.contains b.info.name then
          raiseBuiltin "TypeError" s!"unhashable type: '{← typeName v}'"
        if hashesByAddr b then PyPure.addrHash v
        else if b == .«frozenset» then
          return frozensetHash ((← setMembers v).unordered.toList.map (·.2))
        else PyPure.gap s!"the hash of a {b.info.name} is not modelled yet"
      | _ =>
        -- A user class's `__hash__`: `None` makes it unhashable, `object`'s hashes the address,
        -- and any other must give an `int`.
        match ← lookupType (← PyReads.classOf v) "__hash__" with
        | none => PyPure.addrHash v
        | some f =>
          if (← PyPure.immView f) matches some .none then
            raiseBuiltin "TypeError" s!"unhashable type: '{← typeName v}'"
          if (← PyPure.immView f) matches some (.descr .object "__hash__" _) then
            return ← PyPure.addrHash v
          -- `slot_tp_hash`: an exception raised while the dunder is bound makes the value
          -- unhashable (`PyObject_HashNotImplemented`).
          let t ← PyReads.classOf v
          let g ← tryCatch (descrGetN dispatchDepth f (some v) t) fun _ => do
            raiseBuiltin "TypeError" s!"unhashable type: '{← typeName v}'"
          -- `lookup_maybe_method` binds first: a `__get__` that gives `None` makes it unhashable.
          if (← PyPure.immView g) matches some .none then
            raiseBuiltin "TypeError" s!"unhashable type: '{← typeName v}'"
          let r ← callN dispatchDepth g (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
          match ← PyPure.immViewAll r with
          | some (.int i) =>
            -- CPython keeps a C `Py_ssize_t` as it is, -1 made -2, and hashes a larger `int`.
            if -(2 ^ 63 : Int) ≤ i && i < 2 ^ 63 then
              return .exact (if i == -1 then -2 else i)
            let some h ← PyPure.immHash r | PyPure.gap "the hash of a large int"
            return h
          | some (.bool b) => return .exact (if b then 1 else 0)
          -- A hash that depends on the seed is another value's hash: a `Py_ssize_t` other than
          -- `-1`, which `slot_tp_hash` keeps as it is, so that `hash(x) == hash(y)` when
          -- `x.__hash__()` returns `hash(y)`.
          | some (.symHash n) => return .symbolic n.1
          | _ => raiseBuiltin "TypeError" "__hash__ method should return an integer"

/-- `hash(v)`'s hash. -/
def hash [PyCalls m V] (v : V) : m Hash := hashN compareDepth v

/-- The comparison of a dict's stored key with the key `k`, as CPython makes it: `stored == k`. -/
def keyEq [PyCalls m V] (k : V) : V → m Bool := fun stored => richCompare .eq stored k

/-- Raise `KeyError(k)`. -/
def raiseKeyError [PyCalls m V] {α : Type} (k : V) : m α :=
  PyReads.raiseNew (PyPure.imm (m := m) (.builtin .KeyError)) #[k] #[]

/-- The value of the entry `k` of the dict `d`, `k` hashed first. -/
def dictFindKey [PyCalls m V] (d k : V) : m (Option V) := do
  PyReads.dictFind d k (some (← hash k)) (keyEq k)

/-- The keys and values `kvs` (alternating) inserted into the dict `d`, which the operation made, in
order, each key hashed and compared as CPython's `BUILD_MAP` does, user dunders included. -/
def dictInsertHashed [PyCalls m V] [PyNew m V] (d : V) : List V → m Unit
  | [] => pure ()
  | [_] => PyPure.modelInvariant "mkDict: operand assumption failed"
  | k :: v :: rest => do
    PyNew.dictSetNew d k v (some (← hash k)) (keyEq k)
    dictInsertHashed d rest

/-- A dict of the keys and values `kvs`, alternating, in order: CPython's `BUILD_MAP`. -/
def mkDictHashed [PyCalls m V] [PyNew m V] (kvs : Array V) : m V := do
  let d ← PyPure.allocDict
  dictInsertHashed d kvs.toList
  pure d

/-- `obj[key]` for a built-in `obj`, or an instance of a subclass of a built-in type, as the
built-in type's own `__getitem__` does; otherwise CPython's `TypeError`. -/
def getItemCore [PyCalls m V] (obj key : V) : m V := do
  if ← isType obj then PyPure.gap "subscripting a class is not modelled yet"
  if let some s ← seqOf obj then return ← seqGetItem s key
  if ← isDictLike obj then
    let some v ← dictFindKey obj key | raiseKeyError key
    return v
  match ← PyPure.immView obj with
  | some (.builtin _) => PyPure.gap "subscripting a built-in type or function is not modelled yet"
  | some _ => raiseBuiltin "TypeError" s!"'{← typeName obj}' object is not subscriptable"
  | none => PyPure.gap "subscripting this built-in object is not modelled yet"

/-- `obj[key]`: a user object's `__getitem__` (a class's `__class_getitem__`), a built-in `obj`'s
own; otherwise CPython's `TypeError`. -/
def getItem [PyCalls m V] (obj key : V) : m V := do
  if ← isUserObject obj then
    if let some r ← callSpecial? obj "__getitem__" #[key] then return r
    if !(← isType obj) then
      raiseBuiltin "TypeError" s!"'{← typeName obj}' object is not subscriptable"
  if ← isType obj then
    -- A class's `__class_getitem__`, as `PyObject_GetItem` tries it last.
    if (← PyPure.immView obj) matches some (.builtin _) then
      PyPure.gap "subscripting a built-in class is not modelled yet"
    -- `_PyObject_LookupAttr` reads it with the attribute protocol, which looks at the metaclass
    -- first: a metaclass that defines it, a `__getattr__`, or a `__getattribute__` other than
    -- `type`'s stops with a gap.  A `None` that the lookup gives means none.
    let mt ← PyReads.classOf obj
    if !((← PyPure.immView mt) matches some (.builtin _)) then
      for n in ["__class_getitem__", "__getattr__"] do
        if (← lookupType mt n).isSome then
          PyPure.gap "a __class_getitem__ that a metaclass may give is not modelled yet"
      if let some f ← lookupType mt "__getattribute__" then
        if !((← PyPure.immView f) matches some (.descr .type "__getattribute__" _)) then
          PyPure.gap "a __class_getitem__ that a metaclass may give is not modelled yet"
    if let some f ← lookupType obj "__class_getitem__" then
      -- An `AttributeError` from its `__get__` means none, as `_PyObject_LookupAttr` takes it.
      let g? ← tryCatch (some <$> descrGetN dispatchDepth f none obj) fun x => do
        if ← isAttributeError x then pure none else throw x
      if let some g := g? then
        if !((← PyPure.immView g) matches some .none) then
          return ← callN dispatchDepth g (PyPure.imm (m := m) (.tuple #[key])) (← PyPure.allocDict)
    raiseBuiltin "TypeError" s!"type '{← classNameOf obj}' is not subscriptable"
  getItemCore obj key

/-- `obj[key]`, or `fallback` where a dict has no entry `key`: CPython's
`PyMapping_GetOptionalItem`.  For any other built-in `obj`, it is `getItem`, since only a dict
raises `KeyError`. -/
def getOptionalItem [PyCalls m V] (obj key fallback : V) : m V := do
  if ← isDict obj then return (← dictFindKey obj key).getD fallback
  getItem obj key

/-- Whether `x` is a member of `xs` from position `i` on: `is` first, then `==`; walked by
position, with `fuel` above the positions left. -/
def memberOf [PyCalls m V] (x : V) (xs : Array V) : Nat → Nat → m Bool
  | 0, _ => PyPure.modelInvariant "memberOf: the fuel ran out"
  | fuel + 1, i => do
    let some y := xs[i]? | return false
    pauseStep
    if ← sameOrEq (richCompare .eq) y x then return true
    memberOf x xs fuel (i + 1)

/-- Whether `x` is a member of the list `l` from position `i` on, as CPython's `list_contains`
walks it: `is` first, then `item == x`, the list read again at each step, since an `__eq__` may
change it. -/
def listMemberLive [PyCalls m V] (x l : V) : Nat → Nat → m Bool
  | 0, _ => PyPure.gap "a walk of a list that doesn't end"
  | fuel + 1, i => do
    let some xs ← listOf? l | PyPure.modelInvariant "a list walked that stopped being a list"
    let some y := xs[i]? | return false
    if ← sameOrEq (richCompare .eq) y x then return true
    listMemberLive x l fuel (i + 1)

/-- Whether the list `n` is a contiguous part of `h`. -/
def isInfix {α : Type} [BEq α] (n h : List α) : Bool :=
  match h with
  | [] => n.isEmpty
  | _ :: rest => n.isPrefixOf h || isInfix n rest

/-- `x in s` for a built-in `s`, or an instance of a subclass of a built-in type, as the built-in
type's own `__contains__` does. -/
def containsCore [PyCalls m V] (x s : V) : m Bool := do
  match ← seqOf s with
  | some (.tuple xs) => memberOf x xs (xs.size + 1) 0
  | some (.list l _) => listMemberLive x l walkFuel 0
  | some (.str hay) =>
    match ← PyPure.immView x with
    | some (.str n) => pure (isInfix n.s.toList hay.s.toList)
    | _ => raiseBuiltin "TypeError" s!"'in <string>' requires string as left operand, not {← typeName x}"
  | some (.bytes hay) =>
    match ← PyPure.immViewAll x with
    | some (.bytes n) => pure (isInfix n.toList hay.toList)
    | some (.int _) | some (.bool _) | some (.symHash _) =>
      let some i ← indexOf x | PyPure.modelInvariant "an index"
      if 0 ≤ i ∧ i < 256 then pure (hay.contains i.toNat.toUInt8)
      else raiseBuiltin "ValueError" "byte must be in range(0, 256)"
    | some _ => raiseBuiltin "TypeError" s!"a bytes-like object is required, not '{← typeName x}'"
    | none => PyPure.gap "membership of an object in a bytes is not modelled yet"
  | some (.range a b c) =>
    match ← PyPure.immView x with
    | some (.int i) =>
      pure ((if c > 0 then a ≤ i ∧ i < b else b < i ∧ i ≤ a) && (i - a) % c == 0)
    | some (.str _) | some (.bytes _) | some (.tuple _) | some .none => pure false
    | _ => PyPure.gap "membership of this value in a range is not modelled yet"
  | none =>
    if ← isDictLike s then return (← dictFindKey s x).isSome
    if (← anySetLike? s).isSome then
      -- A set is looked up as a frozenset copy of it, as `set_contains` retries it: the members'
      -- `__eq__` compare with the copy.
      if (← anySet? x) matches some false then
        let fz ← PyReads.setCopy x true
        let h := frozensetHash ((← setMembers x).unordered.toList.map (·.2))
        return ← PyReads.setFind s fz (some h) (keyEq fz)
      return ← PyReads.setFind s x (some (← hash x)) (keyEq x)
    if (← PyPure.immView s).isSome then
      raiseBuiltin "TypeError" s!"argument of type '{← typeName s}' is not iterable"
    PyPure.gap "membership in this container is not modelled yet"

/-- What iterating `v` gives, as a sequence: a built-in sequence itself, a dict's keys in order;
`TypeError` with the message `notIterable t` for an immediate of type `t` that isn't iterable,
and a gap for any other object. -/
def iterSeq [PyCalls m V] (v : V) (notIterable : String → String) : m (Seq V) := do
  if ← isUserObject v then
    if (← lookupType (← PyReads.classOf v) "__iter__").isSome ||
        (← lookupType (← PyReads.classOf v) "__getitem__").isSome then
      PyPure.gap "a looping built-in was reached inside an operation"
    raiseBuiltin "TypeError" (notIterable (← typeName v))
  match ← seqOf v with
  | some s => pure s
  | none =>
    if ← isDict v then return .tuple ((← PyReads.dictEntries v).map (·.1))
    if (← anySet? v).isSome then
      let vw ← setMembers v
      match vw.inOrder? with
      | some ms => return .tuple (ms.map (·.1))
      | none =>
        -- A set of fewer than two members has one order.
        if vw.unordered.size ≥ 2 then PyPure.gap "iterating a set whose order is not CPython's"
        return .tuple (vw.unordered.map (·.1))
    if (← PyPure.immView v).isSome then raiseBuiltin "TypeError" (notIterable (← typeName v))
    PyPure.gap "iterating this built-in object is not modelled yet"

/-- The message of a value that can't be unpacked. -/
def unpackMsg (t : String) : String := s!"cannot unpack non-iterable {t} object"

/-- `a, b, … = v` with `n` targets: a tuple of the `n` elements. -/
def unpackSeq [PyCalls m V] (v : V) (n : Nat) : m V := do
  let s ← iterSeq v unpackMsg
  if s.length < n then
    raiseBuiltin "ValueError" s!"not enough values to unpack (expected {n}, got {s.length})"
  if s.length > n then raiseBuiltin "ValueError" s!"too many values to unpack (expected {n})"
  pure (PyPure.imm (m := m) (.tuple (← s.items)))

/-- `a, *b, c = v` with `before` targets before the star and `after` after it: a tuple of the
`before` elements, a list of the middle ones, and the `after` elements. -/
def unpackEx [PyCalls m V] (v : V) (before after : Nat) : m V := do
  let xs ← (← iterSeq v unpackMsg).items
  if xs.size < before + after then
    raiseBuiltin "ValueError"
      s!"not enough values to unpack (expected at least {before + after}, got {xs.size})"
  let mid ← PyPure.allocList (xs.extract before (xs.size - after))
  pure (PyPure.imm (m := m) (.tuple (xs.extract 0 before ++ #[mid] ++ xs.extract (xs.size - after) xs.size)))

/-- The elements that a slice assignment puts in: CPython's `PySequence_Fast` of `val`. -/
def assignItems [PyCalls m V] (val : V) : m (Array V) := do
  (← iterSeq val fun _ => "must assign iterable to extended slice").items

/-- `l[key] = val` for the list `l` with the elements `xs`, as CPython's `list_ass_subscript`. An
index is converted first, and then checked against the list's size at that point (the list is read
again when the conversion may have run user code). A slice's bounds are converted, then the items
to assign are read, which may run user code, and only then is the slice fitted to the list as it
is (`PySlice_Unpack`, `PySequence_Fast`, then `PySlice_AdjustIndices`). -/
def listSetItem [PyWrites m V] (l : V) (xs : Array V) (key val : V) : m Unit := do
  let kv ← PyPure.immView key
  if let some (.slice a b c) := kv then
    let bs ← sliceBounds a b c
    let ys ← assignItems val
    let xs ← listElems l
    let ix ← sliceIdxOf bs xs.size
    if ix.step == 1 then
      return ← PyWrites.listSplice l ix.start.toNat (ix.start.toNat + ix.length) ys
    if ys.size != ix.length then
      raiseBuiltin "ValueError"
        s!"attempt to assign sequence of size {ys.size} to extended slice of size {ix.length}"
    let xs' := ((SliceIdx.positions ix).zip ys.toList).foldl
      (fun acc (p, y) => acc.setIfInBounds p y) xs
    return ← PyWrites.listSplice l 0 xs.size xs'
  match ← indexOf key with
  | some i =>
    fitIndex key i
    match position i (← if immIndexRunsCode kv then listElems l else pure xs).size with
    | some p => PyWrites.listSet l p val
    | none => raiseBuiltin "IndexError" "list assignment index out of range"
  | none => raiseBuiltin "TypeError" s!"list indices must be integers or slices, not {← typeName key}"

/-- `del l[key]` for the list `l` with the elements `xs`.  As CPython's `list_ass_subscript`, the
index or the slice is converted first, and then checked against the list's size at that point (the
list is read again when the conversion may have run user code). -/
def listDelItem [PyWrites m V] (l : V) (xs : Array V) (key : V) : m Unit := do
  let kv ← PyPure.immView key
  if let some (.slice a b c) := kv then
    let bs ← sliceBounds a b c
    let xs ← if ← boundsRunCode a b c then listElems l else pure xs
    let ix ← sliceIdxOf bs xs.size
    if ix.step == 1 then
      return ← PyWrites.listSplice l ix.start.toNat (ix.start.toNat + ix.length) #[]
    let gone := (SliceIdx.positions ix).foldl (fun acc p => acc.setIfInBounds p true)
      (Array.replicate xs.size false)
    let kept := (List.range xs.size).filterMap fun p => if gone.getD p false then none else xs[p]?
    return ← PyWrites.listSplice l 0 xs.size kept.toArray
  match ← indexOf key with
  | some i =>
    fitIndex key i
    match position i (← if immIndexRunsCode kv then listElems l else pure xs).size with
    | some p => PyWrites.listSplice l p (p + 1) #[]
    | none => raiseBuiltin "IndexError" "list assignment index out of range"
  | none => raiseBuiltin "TypeError" s!"list indices must be integers or slices, not {← typeName key}"

/-- `obj[key] = val` for a built-in `obj`, or an instance of a subclass of a built-in type, as the
built-in type's own `__setitem__` does. -/
def setItemCore [PyWrites m V] (obj key val : V) : m Unit := do
  if let some xs ← listOf? obj then return ← listSetItem obj xs key val
  if ← isDictLike obj then return ← PyWrites.dictSet obj key val (some (← hash key)) (keyEq key)
  if (← seqOf obj).isSome then
    -- A sequence converts an index key first, as `PySequence_SetItem` does.
    if let some i ← indexOf key then fitIndex key i
  if (← PyPure.immView obj).isSome then
    raiseBuiltin "TypeError" s!"'{← typeName obj}' object does not support item assignment"
  PyPure.gap "item assignment on this built-in object is not modelled yet"

/-- `obj[key] = val`: a user object's `__setitem__`, the built-in assignment, or CPython's `AttributeError` when the type has
only `__delitem__`, and its `TypeError` when it has neither. -/
def setItem [PyWrites m V] (obj key val : V) : m Unit := do
  if ← isUserObject obj then
    match ← callSpecial? obj "__setitem__" #[key, val] with
    | some _ => return
    | none =>
      -- One slot serves both dunders: with only `__delitem__`, the slot looks `__setitem__` up.
      if (← lookupType (← PyReads.classOf obj) "__delitem__").isSome then
        raiseBuiltin "AttributeError" "__setitem__"
      -- A class's type has sequence slots, so an index key is converted first.
      if let some i ← indexOf key then fitIndex key i
      raiseBuiltin "TypeError" s!"'{← typeName obj}' object does not support item assignment"
  setItemCore obj key val

/-- `del obj[key]` for a built-in `obj`, or an instance of a subclass of a built-in type, as the
built-in type's own `__delitem__` does. -/
def delItemCore [PyWrites m V] (obj key : V) : m Unit := do
  if let some xs ← listOf? obj then return ← listDelItem obj xs key
  if ← isDictLike obj then
    if (← PyWrites.dictDelete obj key (some (← hash key)) (keyEq key)).isNone then
      raiseKeyError key
    return
  if (← seqOf obj).isSome then
    if let some i ← indexOf key then
      fitIndex key i
      raiseBuiltin "TypeError" s!"'{← typeName obj}' object doesn't support item deletion"
  if (← PyPure.immView obj).isSome then
    raiseBuiltin "TypeError" s!"'{← typeName obj}' object does not support item deletion"
  PyPure.gap "item deletion on this built-in object is not modelled yet"

/-- `del obj[key]` for a built-in `obj`; otherwise CPython's `AttributeError` when the type has only
`__setitem__`, and its `TypeError` when it has neither. -/
def delItem [PyWrites m V] (obj key : V) : m Unit := do
  if ← isUserObject obj then
    match ← callSpecial? obj "__delitem__" #[key] with
    | some _ => return
    | none =>
      if (← lookupType (← PyReads.classOf obj) "__setitem__").isSome then
        raiseBuiltin "AttributeError" "__delitem__"
      -- A class's type has sequence slots: an index key is converted first, and the message is
      -- then `PySequence_DelItem`'s.
      if let some i ← indexOf key then
        fitIndex key i
        raiseBuiltin "TypeError" s!"'{← typeName obj}' object doesn't support item deletion"
      raiseBuiltin "TypeError" s!"'{← typeName obj}' object does not support item deletion"
  delItemCore obj key

/-- Append the elements of the built-in sequence `it` to the list `l` with the elements `xs`; the
message of `TypeError` for an immediate of type `t` that isn't iterable is `notIterable t`. -/
def listExtendWith [PyWrites m V] (l : V) (xs : Array V) (it : V)
    (notIterable : String → String) : m Unit := do
  let ys ← (← iterSeq it notIterable).items
  PyWrites.listSplice l xs.size xs.size ys

/-- The comparison of a set's stored member with a probe, as `keyEq`. -/
def memberEq [PyCalls m V] (probe stored : V) : m Bool := richCompare .eq stored probe

/-- The writes of a set that a walk makes: `PyNew`'s, on a set that the operation made, or
`PyWrites`'s. -/
structure SetWrites (m : Type → Type 1) (V : Type) where
  add : V → V → Option Hash → (V → m Bool) → m Unit
  discard : V → V → Option Hash → (V → m Bool) → m Bool
  reserve : V → Nat → m Unit
  trim : V → m Unit
  merge : V → V → (V → V → m Bool) → m Unit
  subtract : V → V → (V → V → m Bool) → m Unit
  symUpdate : V → V → (V → V → m Bool) → m Unit

/-- `PyNew`'s set writes. -/
def newSetWrites [PyNew m V] : SetWrites m V :=
  ⟨PyNew.setAddNew, PyNew.setDiscardNew, PyNew.setReserveNew, PyNew.setTrimNew,
    PyNew.setMergeNew, PyNew.setSubtractNew, PyNew.setSymUpdateNew⟩

/-- `PyWrites`' set writes. -/
def oldSetWrites [PyWrites m V] : SetWrites m V :=
  ⟨PyWrites.setAdd, PyWrites.setDiscard, PyWrites.setReserve, PyWrites.setTrim,
    PyWrites.setMerge, PyWrites.setSubtract, PyWrites.setSymUpdate⟩

/-- CPython's `set_merge` of the set `src` into the set `s`: when a comparison may run user code,
one resize for `src`'s members, then each member of `src`'s live table added; otherwise the
primitive. -/
def setMergeWith [PyCalls m V] (w : SetWrites m V) (s src : V) : m Unit := do
  if (← PyPure.identical s src) matches .yes then return
  if !(← mayRunUserWalk [src, s]) || (← PyReads.setLen s) == 0 || (← PyReads.setLen src) == 0 then
    return ← w.merge s src memberEq
  w.reserve s (← PyReads.setLen src)
  discard <| setWalkLive src (fun k h => do w.add s k (some h) (keyEq k); pure true) walkFuel 0

/-- Close the new set `r` if it is a frozenset (`frozen`), so that it escapes as a value. -/
def freezeIf [PyPure m V] [PyNew m V] (frozen : Bool) (r : V) : m V := do
  if frozen then PyNew.setFreezeNew r
  pure r

/-- A new set (a frozenset if `frozen`, closed) of the members of the view `vs` that `keep` keeps,
in the view's table order, inexact when the view is: the one reader of `SetView.unordered` that
builds a set, so that no consumer handles the flag. -/
def fillFrom [PyCalls m V] [PyNew m V] (frozen : Bool) (vs : SetView V) (keep : V → Hash → m Bool) :
    m V := do
  let r ← PyPure.allocSet frozen !vs.exact
  for (k, h) in vs.unordered do
    if ← keep k h then PyNew.setAddNew r k (some h) (keyEq k)
  freezeIf frozen r

/-- A copy of the set `a`, a frozenset if `frozen`, still open: a maker that goes on writing to it
closes it itself. -/
def openCopy [PyCalls m V] [PyNew m V] (frozen : Bool) (a : V) : m V := do
  let c ← PyPure.allocSet frozen false
  PyNew.setMergeNew c a memberEq
  pure c

/-- `a & b` for two sets: a copy of `a` if `b` is `a`; else the members of the smaller one that the
larger one has, walked in the smaller one's order, its live table when a comparison may run user
code. -/
def setIntersection [PyCalls m V] [PyNew m V] (frozen : Bool) (a b : V) : m V := do
  if (← PyPure.identical a b) matches .yes then return ← PyReads.setCopy a frozen
  let (big, small) := if (← PyReads.setLen b) > (← PyReads.setLen a) then (b, a) else (a, b)
  if ← mayRunUserWalk [small, big] then
    let r ← PyPure.allocSet frozen false
    discard <| setWalkLive small (fun k h => do
      if ← PyReads.setFind big k (some h) (keyEq k) then PyNew.setAddNew r k (some h) (keyEq k)
      pure true) walkFuel 0
    return ← freezeIf frozen r
  fillFrom frozen (← setMembers small) fun k h => PyReads.setFind big k (some h) (keyEq k)

/-- CPython's `set_difference_update_internal` with a set `src`: each member of `src` discarded
from `s`, then the dummies resized away. When a comparison may run user code, it walks `src`'s
live table, and first replaces a `src` more than 8 times larger than `s` by `s & src`, as CPython
does; otherwise the primitive. -/
def setSubtractWith [PyCalls m V] [PyNew m V] (w : SetWrites m V) (s src : V) : m Unit := do
  if (← PyPure.identical s src) matches .yes || !(← mayRunUserWalk [src, s]) then
    return ← w.subtract s src memberEq
  let src' ← if (← PyReads.setLen src) >>> 3 > (← PyReads.setLen s) then setIntersection false s src
    else pure src
  discard <| setWalkLive src' (fun k h => do
    discard <| w.discard s k (some h) (keyEq k)
    pure true) walkFuel 0
  w.trim s

/-- CPython's `set_symmetric_difference_update` with a set `src`: each member of `src` discarded
from `s` if `s` has it and else added, walking `src`'s live table when a comparison may run user
code; otherwise the primitive. -/
def setSymUpdateWith [PyCalls m V] (w : SetWrites m V) (s src : V) : m Unit := do
  if (← PyPure.identical s src) matches .yes || !(← mayRunUserWalk [src, s]) then
    return ← w.symUpdate s src memberEq
  discard <| setWalkLive src (fun k h => do
    if !(← w.discard s k (some h) (keyEq k)) then w.add s k (some h) (keyEq k)
    pure true) walkFuel 0

/-- `a | b` for two sets: a copy of `a` with `b` merged in. -/
def setUnion [PyCalls m V] [PyNew m V] (frozen : Bool) (a b : V) : m V := do
  if (← PyPure.identical a b) matches .yes then return ← PyReads.setCopy a frozen
  let c ← openCopy frozen a
  setMergeWith newSetWrites c b
  freezeIf frozen c

/-- `a - b` for two sets: a copy of `a` without the members of `b` when `b` is small, else the
members of `a` that `b` doesn't have, as CPython's `set_difference` chooses, walking `a`'s live
table when a comparison may run user code. -/
def setDifference [PyCalls m V] [PyNew m V] (frozen : Bool) (a b : V) : m V := do
  if (← PyReads.setLen a) / 4 > (← PyReads.setLen b) then
    let c ← openCopy frozen a
    setSubtractWith newSetWrites c b
    return ← freezeIf frozen c
  if ← mayRunUserWalk [a, b] then
    let r ← PyPure.allocSet frozen false
    discard <| setWalkLive a (fun k h => do
      if !(← PyReads.setFind b k (some h) (keyEq k)) then PyNew.setAddNew r k (some h) (keyEq k)
      pure true) walkFuel 0
    return ← freezeIf frozen r
  fillFrom frozen (← setMembers a) fun k h => return !(← PyReads.setFind b k (some h) (keyEq k))

/-- `a ^ b` for two sets: a set of `a`'s type made from `b`, updated by `a`. -/
def setSymDifference [PyCalls m V] [PyNew m V] (frozen : Bool) (a b : V) : m V := do
  let r ← PyPure.allocSet frozen !(← setMembers a).exact
  setMergeWith newSetWrites r b
  setSymUpdateWith newSetWrites r a
  freezeIf frozen r

/-- `a op b` for two sets or frozensets: `|`, `&`, `-` and `^` make a new set of `a`'s type;
`none` for any other operands. -/
def setBinary? [PyCalls m V] [PyNew m V] (op : Arith.BinOp) (a b : V) : m (Option V) := do
  let some frozen ← anySet? a | return none
  if (← anySet? b).isNone then return none
  match op with
  | .or => return some (← setUnion frozen a b)
  | .and => return some (← setIntersection frozen a b)
  | .sub => return some (← setDifference frozen a b)
  | .xor => return some (← setSymDifference frozen a b)
  | _ => return none

/-- `a | b`: for two dicts, a copy of `a` updated with the entries of `b` in
order, by their stored hashes; otherwise `binaryOp`. -/
def orOp [PyCalls m V] [PyNew m V] (a b : V) : m V := do
  if (← isUserObject a) || (← isUserObject b) then return ← binaryOp .or a b
  if (← isDict a) && (← isDict b) then
    let c ← PyReads.dictCopy a
    guardDictWalk b c
    for (k, v, h) in ← PyReads.dictEntries b do PyNew.dictSetNew c k v (some h) (keyEq k)
    return c
  binaryOp .or a b

/-- `a op b`, with the operators of two sets, which make a new set; for any
other operands, `orOp` or `binaryOp`. -/
def setOp [PyCalls m V] [PyNew m V] (op : Arith.BinOp) (a b : V) : m V := do
  if (← isUserObject a) || (← isUserObject b) then return ← binaryOp op a b
  if let some r ← setBinary? op a b then return r
  if op == .or then orOp a b else binaryOp op a b

/-- The end of `a *= b`, after the number slots, as `PyNumber_InPlaceMultiply` does: `a`'s own
repetition; `b`'s only when `a`'s type has no sequence slots at all (a number or `None`), since an
instance of a user class, a dict, a set or a range has them without a repetition; else CPython's
`TypeError`. -/
def inplaceRepeat [PyCalls m V] (a b : V) : m V := do
  if let some v ← repeatSeq a b then return v
  if (← seqName? a).isSome then
    raiseBuiltin "TypeError" s!"can't multiply sequence by non-int of type '{← typeName b}'"
  let noSeqSlots ← match ← PyPure.immView a with
    | some (.range ..) => pure false
    | some _ => pure true
    | none =>
      if (← isUserObject a) || (← isDict a) || (← anySet? a).isSome then pure false
      else PyPure.gap "an in-place repetition of an object of this type is not modelled yet"
  if noSeqSlots then
    if let some v ← repeatSeq b a then return v
    if (← seqName? b).isSome then
      raiseBuiltin "TypeError" s!"can't multiply sequence by non-int of type '{← typeName a}'"
  raiseBuiltin "TypeError" s!"unsupported operand type(s) for *=: '{← typeName a}' and '{← typeName b}'"

/-- **`a op= b`**, as CPython's `PyNumber_InPlace*`: `a`'s in-place number slot (a user
`__iadd__`, or a set's `|=`, `&=`, `-=` and `^=` with a set, a dict's `|=` with a dict); then the
binary protocol; then a list's in-place `+=` and `*=`; otherwise what `a op b` does, with the
in-place operator in its messages. -/
def inplaceOp [PyWrites m V] [PyNew m V] (op : Arith.BinOp) (a b : V) : m V := do
  if let some v ← PyReads.numBinary op a b then return v
  symCheck a b
  let user := (← isUserObject a) || (← isUserObject b)
  -- On an instance of a subclass of `list`, the list's in-place slots come in CPython's order
  -- among the subclass's own, which the model doesn't follow.
  if (op == .add || op == .mul) && (← isUserObject a) && (← listOf? a).isSome then
    PyPure.gap "an in-place operator on an instance of a subclass of list is not modelled yet"
  -- `binary_iop1`: `a`'s in-place number slot first.
  if ← isUserObject a then
    let name := "__i" ++ ((binDunders op).1.drop 2).toString
    let t ← PyReads.classOf a
    if let some f ← lookupType t name then
      if !(← isSeqSlot f) then
        let r ← callFound f a t #[b] (← PyPure.allocDict)
        if !(← isNotImpl r) then return r
  else if (← anySet? a) matches some false then
    -- `set_ior` and the others take an instance of a subclass of `set` or `frozenset` too.
    if (← anySetLike? b).isSome then
      match op with
      | .or =>
        setMergeWith oldSetWrites a b
        return a
      | .and =>
        PyWrites.setReplace a (← setIntersection false a b)
        return a
      | .sub =>
        setSubtractWith oldSetWrites a b
        return a
      | .xor =>
        setSymUpdateWith oldSetWrites a b
        return a
      | _ => pure ()
  else if op == .or && (← isDict a) then
    if !(← isDict b) then
      PyPure.gap "updating a dict from a value that is not a dict is not modelled yet"
    guardDictWalk b a
    for (k, v, h) in ← PyReads.dictEntries b do PyWrites.dictSet a k v (some h) (keyEq k)
    return a
  -- Then `binary_op1`.
  if let some r ← printfFirst? op a b then return r
  if user then
    let (fwd, rev) := binDunders op
    if let some r ← binaryDunder fwd rev a b then return r
  else if let some r ← setBinary? op a b then return r
  -- Then a list's in-place concatenation or repetition (`sq_inplace_concat`, `sq_inplace_repeat`).
  if let some xs ← listOf? a then
    match op with
    | .add =>
      listExtendWith a xs b fun t => s!"'{t}' object is not iterable"
      return a
    | .mul =>
      let some k ← repeatCount b |
        raiseBuiltin "TypeError" s!"can't multiply sequence by non-int of type '{← typeName b}'"
      -- The count's `__index__` may change the list: CPython repeats the list as it is then.
      let some xs ← listOf? a | PyPure.modelInvariant "a list that is no longer a list"
      if xs.size * k > maxRepeat then PyPure.gap "a repetition too large to model"
      PyWrites.listSplice a 0 xs.size (repeatArray xs k)
      return a
    | _ => pure ()
  if op == .mul then return ← inplaceRepeat a b
  binaryTail (inplaceSymbol op) op a b

/-- `a @= b`: `a`'s `__imatmul__` first, as `binary_iop1` tries it, then `a @ b`. -/
def inplaceMatMult [PyCalls m V] (a b : V) : m V := do
  if ← isUserObject a then
    let t ← PyReads.classOf a
    if let some f ← lookupType t "__imatmul__" then
      let r ← callFound f a t #[b] (← PyPure.allocDict)
      if !(← isNotImpl r) then return r
  matMultOpAs "@=" a b

/-- `{x, y, …}`: CPython's `BUILD_SET`, each element hashed and added in order. -/
def mkSet [PyCalls m V] [PyNew m V] (elems : Array V) : m V := do
  let s ← PyPure.allocSet false false
  for x in elems do PyNew.setAddNew s x (some (← hash x)) (keyEq x)
  return s

/-- A set display of constants, which CPython's compiler folds into a frozenset constant: a new set
of the elements whose layout is inexact, since the constant's order depends on how the module was
compiled and loaded. -/
def constSet [PyCalls m V] [PyNew m V] (elems : Array V) : m V := do
  let s ← PyPure.allocSet false true
  for x in elems do PyNew.setAddNew s x (some (← hash x)) (keyEq x)
  return s

/-- `s.add(x)` for a set `s`: CPython's `SET_ADD`. -/
def setAddItem [PyWrites m V] (s x : V) : m Unit := do
  PyWrites.setAdd s x (some (← hash x)) (keyEq x)

/-- The members of the list `l` from position `i` on added to the set `s`, as CPython's list
iterator gives them: the list is read again at each step, since a member's `__hash__` or
`__eq__` may change it. -/
def setAddListLive [PyWrites m V] (s l : V) : Nat → Nat → m Unit
  | 0, _ => PyPure.gap "a walk of a list that doesn't end"
  | fuel + 1, i => do
    let some xs ← listOf? l | PyPure.modelInvariant "a list walked that stopped being a list"
    let some x := xs[i]? | return
    setAddItem s x
    setAddListLive s l fuel (i + 1)

/-- `s.update(it)` for a set `s`, as CPython's `SET_UPDATE`: a set or frozenset, or an instance of
a subclass of one, merged in; a
dict's keys added with their stored hashes, after a resize for their number; or the elements of a
built-in sequence added in order. -/
def setUpdate [PyWrites m V] (s it : V) : m Unit := do
  -- `set_update_internal` merges any set or frozenset, an instance of a subclass too, without its
  -- `__iter__`.
  if (← anySetLike? it).isSome then return ← setMergeWith oldSetWrites s it
  if ← isUserObject it then PyPure.gap "a looping built-in was reached inside an operation"
  if ← isDict it then
    guardDictWalk it s
    let es ← PyReads.dictEntries it
    PyWrites.setReserve s es.size
    for (k, _, h) in es do PyWrites.setAdd s k (some h) (keyEq k)
    return
  if (← listOf? it).isSome then return ← setAddListLive s it walkFuel 0
  for x in ← (← iterSeq it fun t => s!"'{t}' object is not iterable").items do setAddItem s x


/-- The tuple of the items of the list `list`. -/
def listToTuple [PyReads m V] (list : V) : m V := do
  let some xs ← listOf? list
    | PyPure.modelInvariant "listToTuple: operand assumption failed"
  pure (PyPure.imm (m := m) (.tuple xs))

/-- `dict[key] = value` on a `dict` of a display, with `key`'s hash. -/
def dictSetHashed [PyWrites m V] (dict key value : V) : m Unit := do
  let h ← hash key
  PyWrites.dictSet dict key value (some h) (keyEq key)

end

end

end StrataPython.Dyn.Sem.Proto
