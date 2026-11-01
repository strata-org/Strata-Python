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
* `contains`: membership in a sequence, a substring of a `str`, a byte or a sub-`bytes` of a
  `bytes`;
* `unpackSeq` and `unpackEx`, with CPython's `ValueError`s;
* `hash`: CPython's `PyObject_Hash` on built-in values;
* dicts: item access, `in`, `==`, `|` and `|=`;
* sets and frozensets: displays, `in`, the subset order, `|`, `&`, `-`, `^` and their in-place
  forms.

A user object, or an instance of a user subclass of a built-in type, stops with a gap until the
dunder lookup of a type exists.
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
  | .str s => if s.ascii then s.s.utf8ByteSize else s.s.length
  | .bytes b => b.size
  | .range a b c => rangeLen a b c

section
variable {m : Type → Type 1} {V : Type}

/-- `v` as a built-in sequence, if it is one. -/
def seqOf [PyReads m V] (v : V) : m (Option (Seq V)) := do
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
    | none => pure none

/-- Raise what `Arith` says CPython raises, or stop with a gap where it isn't modelled. -/
def ofFailure [PyReads m V] {α : Type} : Format.Failure → m α
  | .raise cls msg => raiseBuiltin cls msg
  | .notModelled what => PyPure.gap s!"not modelled: {what}"

/-- `v` as an index: an `int` or a `bool`; `none` for any other value. -/
def indexOf [PyReads m V] (v : V) : m (Option Int) := do
  match ← PyPure.immView v with
  | some (.int i) => pure (some i)
  | some (.bool b) => pure (some (if b then 1 else 0))
  | some (.symHash _) => PyPure.gap "an index whose number depends on the hash seed"
  | _ => pure none

/-- A bound of a slice: `None`, or an index; otherwise CPython's `TypeError`, and a gap for a user
object, which may have `__index__`. -/
def sliceBound [PyReads m V] (v : V) : m (Option Int) := do
  if (← PyPure.immView v) matches some .none then return none
  userCheck v v
  match ← indexOf v with
  | some i => pure (some i)
  | none => raiseBuiltin "TypeError" "slice indices must be integers or None or have an __index__ method"

/-- The indices that the slice `lo:hi:step` selects in a sequence of `n` elements.  As CPython's
`PySlice_Unpack`, the step is converted first, and a zero step is a `ValueError` before the start
and the stop are converted. -/
def sliceIdx [PyReads m V] (lo hi step : V) (n : Nat) : m Arith.SliceIndices := do
  let st ← sliceBound step
  if st == some 0 then raiseBuiltin "ValueError" "slice step cannot be zero"
  let a ← sliceBound lo
  let b ← sliceBound hi
  match Arith.sliceIndices a b st n with
  | .ok ix => pure ix
  | .error f => ofFailure f

/-- The positions that slice indices select, in order. -/
def SliceIdx.positions (ix : Arith.SliceIndices) : List Nat :=
  (List.range ix.length).map fun (i : Nat) => (ix.start + (i : Int) * ix.step).toNat

/-- Element `i` of a sequence, `i` in range. -/
def Seq.at [PyPure m V] (s : Seq V) (i : Nat) : V :=
  match s with
  | .tuple xs | .list _ xs => xs.getD i (PyPure.imm (m := m) .none)
  | .str t =>
    -- An ASCII `str` is indexed by byte, in constant time.
    let ch := if t.ascii then String.Pos.Raw.get t.s ⟨i⟩ else t.s.toList.getD i ' '
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

/-- `IndexError` for an index that a C `Py_ssize_t` can't hold, as `PyNumber_AsSsize_t` raises
it. -/
def fitIndex [PyReads m V] (i : Int) : m Unit := do
  if i < Arith.ssizeMin ∨ i > (Format.ssizeMax : Int) then
    raiseBuiltin "IndexError" "cannot fit 'int' into an index-sized integer"

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

/-- `s[a:b:c]` for a built-in sequence. -/
def sliceOf [PyReads m V] (s : Seq V) (lo hi step : V) : m V := do
  let ix ← sliceIdx lo hi step s.length
  let ps := SliceIdx.positions ix
  match s with
  | .tuple xs => pure (PyPure.imm (m := m) (.tuple (ps.toArray.map fun p => xs.getD p (PyPure.imm (m := m) .none))))
  | .list _ xs => PyPure.allocList (ps.toArray.map fun p => xs.getD p (PyPure.imm (m := m) .none))
  | .str t =>
    let cs := t.s.toList.toArray
    pure (PyPure.imm (m := m) (.str (.ofString (String.ofList (ps.map fun p => cs.getD p ' ')))))
  | .bytes b => pure (PyPure.imm (m := m) (.bytes (ps.toArray.map fun p => b.getD p 0)))
  | .range .. => PyPure.gap "a slice of a range is not modelled yet"

/-- `obj[key]` for a built-in sequence: an index or a slice. -/
def seqGetItem [PyReads m V] (s : Seq V) (key : V) : m V := do
  if let some (.slice a b c) ← PyPure.immView key then return ← sliceOf s a b c
  match ← indexOf key with
  | some i =>
    if !(s matches .range ..) then fitIndex i
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

/-- CPython's `PyObject_Hash` on a built-in value, with `fuel` the depth of nested tuples left:
an immediate's hash, a tuple's or a slice's from its members', the address hash of an object
whose built-in type hashes by identity, and `TypeError` for an instance of an unhashable type.
Any other object stops with a gap. -/
def hashN [PyReads m V] : Nat → V → m Hash
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
      | _ => PyPure.gap userGap

/-- `hash(v)`'s hash, for a built-in value. -/
def hash [PyReads m V] (v : V) : m Hash := hashN compareDepth v

/-- The comparison of a dict's stored key with the key `k`, as CPython makes it: `stored == k`. -/
def keyEq [PyReads m V] (k : V) : V → m Bool := fun stored => richCompare .eq stored k

/-- Raise `KeyError(k)`. -/
def raiseKeyError [PyReads m V] {α : Type} (k : V) : m α :=
  PyReads.raiseNew (PyPure.imm (m := m) (.builtin .KeyError)) #[k] #[]

/-- The value of the entry `k` of the dict `d`, `k` hashed first. -/
def dictFindKey [PyReads m V] (d k : V) : m (Option V) := do
  PyReads.dictFind d k (some (← hash k)) (keyEq k)

/-- `obj[key]` for a built-in `obj`; otherwise CPython's `TypeError`. -/
def getItem [PyReads m V] (obj key : V) : m V := do
  userCheck obj key
  if let some s ← seqOf obj then return ← seqGetItem s key
  if ← isDict obj then
    let some v ← dictFindKey obj key | raiseKeyError key
    return v
  match ← PyPure.immView obj with
  | some (.builtin _) => PyPure.gap "subscripting a built-in type or function is not modelled yet"
  | some _ => raiseBuiltin "TypeError" s!"'{← typeName obj}' object is not subscriptable"
  | none => PyPure.gap "subscripting this built-in object is not modelled yet"

/-- `obj[key]`, or `fallback` where a dict has no entry `key`: CPython's
`PyMapping_GetOptionalItem`.  For any other built-in `obj`, it is `getItem`, since only a dict
raises `KeyError`. -/
def getOptionalItem [PyReads m V] (obj key fallback : V) : m V := do
  userCheck obj key
  if ← isDict obj then return (← dictFindKey obj key).getD fallback
  getItem obj key

/-- Whether `x` is a member of `xs`: `is` first, then `==`. -/
def memberOf [PyReads m V] (x : V) : List V → m Bool
  | [] => pure false
  | y :: ys => do
    if ← sameOrEq (richCompare .eq) y x then return true
    memberOf x ys

/-- Whether the list `n` is a contiguous part of `h`. -/
def isInfix {α : Type} [BEq α] (n h : List α) : Bool :=
  match h with
  | [] => n.isEmpty
  | _ :: rest => n.isPrefixOf h || isInfix n rest

/-- `x in s` for a built-in container; otherwise CPython's `TypeError`. -/
def contains [PyReads m V] (x s : V) : m Bool := do
  userCheck x s
  match ← seqOf s with
  | some (.tuple xs) | some (.list _ xs) => memberOf x xs.toList
  | some (.str hay) =>
    match ← PyPure.immView x with
    | some (.str n) => pure (isInfix n.s.toList hay.s.toList)
    | _ => raiseBuiltin "TypeError" s!"'in <string>' requires string as left operand, not {← typeName x}"
  | some (.bytes hay) =>
    match ← PyPure.immView x with
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
    if ← isDict s then return (← dictFindKey s x).isSome
    if (← anySet? s).isSome then
      -- A set is looked up as the frozenset of its members, as CPython retries it.
      if (← anySet? x) matches some false then
        let h := frozensetHash ((← setMembers x).unordered.toList.map (·.2))
        return ← PyReads.setFind s x (some h) (keyEq x)
      return ← PyReads.setFind s x (some (← hash x)) (keyEq x)
    if (← PyPure.immView s).isSome then
      raiseBuiltin "TypeError" s!"argument of type '{← typeName s}' is not iterable"
    PyPure.gap "membership in this container is not modelled yet"

/-- What iterating `v` gives, as a sequence: a built-in sequence itself, a dict's keys in order;
`TypeError` with the message `notIterable t` for an immediate of type `t` that isn't iterable,
and a gap for any other object. -/
def iterSeq [PyReads m V] (v : V) (notIterable : String → String) : m (Seq V) := do
  userCheck v v
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
def unpackSeq [PyReads m V] (v : V) (n : Nat) : m V := do
  let s ← iterSeq v unpackMsg
  if s.length < n then
    raiseBuiltin "ValueError" s!"not enough values to unpack (expected {n}, got {s.length})"
  if s.length > n then raiseBuiltin "ValueError" s!"too many values to unpack (expected {n})"
  pure (PyPure.imm (m := m) (.tuple (← s.items)))

/-- `a, *b, c = v` with `before` targets before the star and `after` after it: a tuple of the
`before` elements, a list of the middle ones, and the `after` elements. -/
def unpackEx [PyReads m V] (v : V) (before after : Nat) : m V := do
  let xs ← (← iterSeq v unpackMsg).items
  if xs.size < before + after then
    raiseBuiltin "ValueError"
      s!"not enough values to unpack (expected at least {before + after}, got {xs.size})"
  let mid ← PyPure.allocList (xs.extract before (xs.size - after))
  pure (PyPure.imm (m := m) (.tuple (xs.extract 0 before ++ #[mid] ++ xs.extract (xs.size - after) xs.size)))

/-- The elements that a slice assignment puts in: CPython's `PySequence_Fast` of `val`. -/
def assignItems [PyReads m V] (val : V) : m (Array V) := do
  (← iterSeq val fun _ => "must assign iterable to extended slice").items

/-- `l[key] = val` for the list `l` with the elements `xs`. -/
def listSetItem [PyWrites m V] (l : V) (xs : Array V) (key val : V) : m Unit := do
  if let some (.slice a b c) ← PyPure.immView key then
    let ix ← sliceIdx a b c xs.size
    let ys ← assignItems val
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
    fitIndex i
    match position i xs.size with
    | some p => PyWrites.listSet l p val
    | none => raiseBuiltin "IndexError" "list assignment index out of range"
  | none => raiseBuiltin "TypeError" s!"list indices must be integers or slices, not {← typeName key}"

/-- `del l[key]` for the list `l` with the elements `xs`. -/
def listDelItem [PyWrites m V] (l : V) (xs : Array V) (key : V) : m Unit := do
  if let some (.slice a b c) ← PyPure.immView key then
    let ix ← sliceIdx a b c xs.size
    if ix.step == 1 then
      return ← PyWrites.listSplice l ix.start.toNat (ix.start.toNat + ix.length) #[]
    let gone := (SliceIdx.positions ix).foldl (fun acc p => acc.setIfInBounds p true)
      (Array.replicate xs.size false)
    let kept := (List.range xs.size).filterMap fun p => if gone.getD p false then none else xs[p]?
    return ← PyWrites.listSplice l 0 xs.size kept.toArray
  match ← indexOf key with
  | some i =>
    fitIndex i
    match position i xs.size with
    | some p => PyWrites.listSplice l p (p + 1) #[]
    | none => raiseBuiltin "IndexError" "list assignment index out of range"
  | none => raiseBuiltin "TypeError" s!"list indices must be integers or slices, not {← typeName key}"

/-- `obj[key] = val` for a built-in `obj`; otherwise CPython's `TypeError`. -/
def setItem [PyWrites m V] (obj key val : V) : m Unit := do
  userCheck obj key
  if let some xs ← listOf? obj then return ← listSetItem obj xs key val
  if ← isDict obj then return ← PyWrites.dictSet obj key val (some (← hash key)) (keyEq key)
  if (← seqOf obj).isSome then
    -- A sequence converts an index key first, as `PySequence_SetItem` does.
    if let some i ← indexOf key then fitIndex i
  if (← PyPure.immView obj).isSome then
    raiseBuiltin "TypeError" s!"'{← typeName obj}' object does not support item assignment"
  PyPure.gap "item assignment on this built-in object is not modelled yet"

/-- `del obj[key]` for a built-in `obj`; otherwise CPython's `TypeError`, whose wording depends on
whether the type is a sequence and the key an index, which is converted first. -/
def delItem [PyWrites m V] (obj key : V) : m Unit := do
  userCheck obj key
  if let some xs ← listOf? obj then return ← listDelItem obj xs key
  if ← isDict obj then
    if (← PyWrites.dictDelete obj key (some (← hash key)) (keyEq key)).isNone then
      raiseKeyError key
    return
  if (← seqOf obj).isSome then
    if let some i ← indexOf key then
      fitIndex i
      raiseBuiltin "TypeError" s!"'{← typeName obj}' object doesn't support item deletion"
  if (← PyPure.immView obj).isSome then
    raiseBuiltin "TypeError" s!"'{← typeName obj}' object does not support item deletion"
  PyPure.gap "item deletion on this built-in object is not modelled yet"

/-- Append the elements of the built-in sequence `it` to the list `l` with the elements `xs`; the
message of `TypeError` for an immediate of type `t` that isn't iterable is `notIterable t`. -/
def listExtendWith [PyWrites m V] (l : V) (xs : Array V) (it : V)
    (notIterable : String → String) : m Unit := do
  let ys ← (← iterSeq it notIterable).items
  PyWrites.listSplice l xs.size xs.size ys

/-- `l.extend(it)` for a list `l`, as CPython's `LIST_EXTEND`. -/
def listExtend [PyWrites m V] (l it : V) : m Unit := do
  let some xs ← listOf? l | PyPure.modelInvariant "listExtend: operand assumption failed"
  listExtendWith l xs it fun t => s!"Value after * must be an iterable, not {t}"

/-- The comparison of a set's stored member with a probe, as `keyEq`. -/
def memberEq [PyReads m V] (probe stored : V) : m Bool := richCompare .eq stored probe

/-- Close the new set `r` if it is a frozenset (`frozen`), so that it escapes as a value. -/
def freezeIf [PyPure m V] [PyNew m V] (frozen : Bool) (r : V) : m V := do
  if frozen then PyNew.setFreezeNew r
  pure r

/-- A new set (a frozenset if `frozen`, closed) of the members of the view `vs` that `keep` keeps,
in the view's table order, inexact when the view is: the one reader of `SetView.unordered` that
builds a set, so that no consumer handles the flag. -/
def fillFrom [PyReads m V] [PyNew m V] (frozen : Bool) (vs : SetView V) (keep : V → Hash → m Bool) :
    m V := do
  let r ← PyPure.allocSet frozen !vs.exact
  for (k, h) in vs.unordered do
    if ← keep k h then PyNew.setAddNew r k (some h) (keyEq k)
  freezeIf frozen r

/-- A copy of the set `a`, a frozenset if `frozen`, still open: a maker that goes on writing to it
closes it itself. -/
def openCopy [PyReads m V] [PyNew m V] (frozen : Bool) (a : V) : m V := do
  let c ← PyPure.allocSet frozen false
  PyNew.setMergeNew c a memberEq
  pure c

/-- `a | b` for two sets: a copy of `a` (of its type), with `b` merged in unless it is `a`. -/
def setUnion [PyReads m V] [PyNew m V] (frozen : Bool) (a b : V) : m V := do
  if (← PyPure.identical a b) matches .yes then return ← PyReads.setCopy a frozen
  let c ← openCopy frozen a
  PyNew.setMergeNew c b memberEq
  freezeIf frozen c

/-- `a & b` for two sets: a copy of `a` if `b` is `a`; else the members of the smaller one that the
larger one has, walked in the smaller one's order. -/
def setIntersection [PyReads m V] [PyNew m V] (frozen : Bool) (a b : V) : m V := do
  if (← PyPure.identical a b) matches .yes then return ← PyReads.setCopy a frozen
  let (big, small) := if (← PyReads.setLen b) > (← PyReads.setLen a) then (b, a) else (a, b)
  guardWalk [small, big]
  fillFrom frozen (← setMembers small) fun k h => PyReads.setFind big k (some h) (keyEq k)

/-- `a - b` for two sets: a copy of `a` without the members of `b` when `b` is small, else the
members of `a` that `b` doesn't have, as CPython's `set_difference` chooses. -/
def setDifference [PyReads m V] [PyNew m V] (frozen : Bool) (a b : V) : m V := do
  if (← PyReads.setLen a) / 4 > (← PyReads.setLen b) then
    let c ← openCopy frozen a
    PyNew.setSubtractNew c b memberEq
    return ← freezeIf frozen c
  guardWalk [a, b]
  fillFrom frozen (← setMembers a) fun k h => return !(← PyReads.setFind b k (some h) (keyEq k))

/-- `a ^ b` for two sets: a set of `a`'s type made from `b`, updated by `a`. -/
def setSymDifference [PyReads m V] [PyNew m V] (frozen : Bool) (a b : V) : m V := do
  let r ← PyPure.allocSet frozen !(← setMembers a).exact
  PyNew.setMergeNew r b memberEq
  PyNew.setSymUpdateNew r a memberEq
  freezeIf frozen r

/-- `a op b` for two sets or frozensets: `|`, `&`, `-` and `^` make a new set of `a`'s type;
`none` for any other operands. -/
def setBinary? [PyReads m V] [PyNew m V] (op : Arith.BinOp) (a b : V) : m (Option V) := do
  let some frozen ← anySet? a | return none
  if (← anySet? b).isNone then return none
  match op with
  | .or => return some (← setUnion frozen a b)
  | .and => return some (← setIntersection frozen a b)
  | .sub => return some (← setDifference frozen a b)
  | .xor => return some (← setSymDifference frozen a b)
  | _ => return none

/-- `a | b` for built-in values: for two dicts, a copy of `a` updated with the entries of `b` in
order, by their stored hashes; otherwise `binaryOp`. -/
def orOp [PyReads m V] [PyNew m V] (a b : V) : m V := do
  userCheck a b
  if (← isDict a) && (← isDict b) then
    let c ← PyReads.dictCopy a
    for (k, v, h) in ← PyReads.dictEntries b do PyNew.dictSetNew c k v (some h) (keyEq k)
    return c
  binaryOp .or a b

/-- `a op b` for built-in values, with the operators of two sets, which make a new set; for any
other operands, `orOp` or `binaryOp`. -/
def setOp [PyReads m V] [PyNew m V] (op : Arith.BinOp) (a b : V) : m V := do
  userCheck a b
  if let some r ← setBinary? op a b then return r
  if op == .or then orOp a b else binaryOp op a b

/-- `a op= b` for built-in values: a list's `+=` and `*=` change the list in place and give it
back, and so do a dict's `|=` with a dict and a set's `|=`, `&=`, `-=` and `^=` with a set; every
other case is `a op b`, with the in-place operator in its messages. -/
def inplaceOp [PyWrites m V] [PyNew m V] (op : Arith.BinOp) (a b : V) : m V := do
  if let some v ← PyReads.numBinary op a b then return v
  userCheck a b
  if (← anySet? a) matches some false then
    if (← anySet? b).isSome then
      match op with
      | .or =>
        PyWrites.setMerge a b memberEq
        return a
      | .and =>
        PyWrites.setReplace a (← setIntersection false a b)
        return a
      | .sub =>
        PyWrites.setSubtract a b memberEq
        return a
      | .xor =>
        PyWrites.setSymUpdate a b memberEq
        return a
      | _ => pure ()
  if let some r ← setBinary? op a b then return r
  if op == .or && (← isDict a) then
    if !(← isDict b) then
      PyPure.gap "updating a dict from a value that is not a dict is not modelled yet"
    for (k, v, h) in ← PyReads.dictEntries b do PyWrites.dictSet a k v (some h) (keyEq k)
    return a
  if let some xs ← listOf? a then
    match op with
    | .add =>
      listExtendWith a xs b fun t => s!"'{t}' object is not iterable"
      return a
    | .mul =>
      let some k ← repeatCount b |
        raiseBuiltin "TypeError" s!"can't multiply sequence by non-int of type '{← typeName b}'"
      if xs.size * k > maxRepeat then PyPure.gap "a repetition too large to model"
      PyWrites.listSplice a 0 xs.size (repeatArray xs k)
      return a
    | _ => pure ()
  binaryOpAs (inplaceSymbol op) op a b

/-- `a @= b` for built-in values. -/
def inplaceMatMult [PyReads m V] (a b : V) : m V := matMultOpAs "@=" a b

/-- `{x, y, …}`: CPython's `BUILD_SET`, each element hashed and added in order. -/
def mkSet [PyReads m V] [PyNew m V] (elems : Array V) : m V := do
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

/-- `s.update(it)` for a set `s`, as CPython's `SET_UPDATE`: a set or frozenset merged in; a
dict's keys added with their stored hashes, after a resize for their number; or the elements of a
built-in sequence added in order. -/
def setUpdate [PyWrites m V] (s it : V) : m Unit := do
  userCheck it it
  if (← anySet? it).isSome then return ← PyWrites.setMerge s it memberEq
  if ← isDict it then
    let es ← PyReads.dictEntries it
    PyWrites.setReserve s es.size
    for (k, _, h) in es do PyWrites.setAdd s k (some h) (keyEq k)
    return
  for x in ← (← iterSeq it fun t => s!"'{t}' object is not iterable").items do setAddItem s x

end

end

end StrataPython.Dyn.Sem.Proto
