/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Exceptions

set_option autoImplicit false

/-!
# Merging a mapping into a dict

Generic over the record, CPython 3.12's `dict_merge` as `DICT_MERGE` (`f(**m)`, a key already
present is an error) and `DICT_UPDATE` (`{**m}`, a key already present is overwritten) run it,
into a fresh copy of the dict, one activation at a time:

* a dict, or an instance of a subclass of `dict` that keeps `dict`'s `__iter__`, is merged at
  once;
* any other mapping gives its keys by `keys()`: an exact list is walked as it is, live; any other
  result is iterated (a second `iter`, its length hint, then the walk of `forEachItem`, over as
  many activations as it takes), its keys gathered in the state; then each key's value comes from
  `__getitem__`.

A later activation copies the partial dict first, so that no activation writes an object that an
earlier one made. The errors are converted as `format_kwargs_error` and `DICT_UPDATE` do.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

/-- The state of a merge across its activations. -/
inductive MergeState (V : Type) where
  /-- The keys of `keys()` gathered so far from its iterator `it`, into the partial dict
  `merged`. -/
  | keys (merged it : V) (acc : Array V)
  /-- The merge of the keys of the list `l`, walked live, from position `i`. -/
  | itemsList (merged l : V) (i : Nat)
  /-- The merge of the gathered keys `ks`, from position `i`. -/
  | itemsArray (merged : V) (ks : Array V) (i : Nat)

section
variable {m : Type → Type 1} {V : Type}

/-- `merged[k] = v`, or for `DICT_MERGE` (`dup`) CPython's `KeyError(k)` when `k` is already
there, as `dict_merge` checks it before it reads the value. -/
def mergeItem [PyCalls m V] [PyNew m V] (dup : Bool) (merged other k : V) : m Unit := do
  if dup then
    if (← dictFindKey merged k).isSome then
      PyReads.raiseNew (PyPure.imm (m := m) (.builtin .KeyError)) #[k] #[]
  let v ← getItem other k
  let h ← hash k
  PyNew.dictSetNew merged k v (some h) (keyEq k)

/-- The entries of the dict `other` merged into `merged`, as `dict_merge`'s fast path does. -/
def mergeDict [PyCalls m V] [PyNew m V] (dup : Bool) (merged other : V) : m Unit := do
  guardDictWalk other merged
  for (k, v, h) in ← PyReads.dictEntries other do
    if dup then
      if (← PyReads.dictFind merged k (some h) (keyEq k)).isSome then
        PyReads.raiseNew (PyPure.imm (m := m) (.builtin .KeyError)) #[k] #[]
    PyNew.dictSetNew merged k v (some h) (keyEq k)

/-- One activation of `dict_merge` of `other` into a copy of `d`: `dup` for `DICT_MERGE`. -/
def mergeStep [PyCalls m V] [PyNew m V] (dup : Bool) (d other : V) (st : Option (MergeState V)) :
    m (LoopStep (MergeState V) V) := do
  let st ← match st with
    -- The keys phase writes no entry, so only the items phases copy the dict that an earlier
    -- activation made, to write it as their own.
    | some (.keys merged it acc) => pure (MergeState.keys merged it acc)
    | some (.itemsList merged l i) => pure (.itemsList (← PyReads.dictCopy merged) l i)
    | some (.itemsArray merged ks i) => pure (.itemsArray (← PyReads.dictCopy merged) ks i)
    | none =>
      let merged ← PyReads.dictCopy d
      -- `PyDict_Check(b) && Py_TYPE(b)->tp_iter == dict_iter`.
      let keepsIter ← match ← lookupType (← PyReads.classOf other) "__iter__" with
        | some f => pure ((← PyPure.immView f) matches some (.descr .dict "__iter__" _))
        | none => pure false
      if (← isDictLike other) && keepsIter then
        mergeDict dup merged other
        return .done merged
      let keysF ← getAttr other "keys"
      let ks ← callN dispatchDepth keysF (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
      if ← classIs ks .list then pure (.itemsList merged ks 0)
      else
        let it ← tryCatch (getIter ks) fun x => do
          if ← isTypeErrorExc x then
            raiseBuiltin "TypeError"
              s!"{← typeName other}.keys() returned a non-iterable (type {← typeName ks})"
          throw x
        let it2 ← getIter it
        hintCheck (← lengthHint it 8)
        pure (.keys merged it2 #[])
  match st with
  | .keys merged it acc =>
    match ← forEachItem nextCall it acc fun k acc => pure (.next (acc.push k)) with
    | .done ks => return .more (.itemsArray merged ks 0)
    | .more acc => return .more (.keys merged it acc)
  | .itemsArray merged ks i =>
    for k in ks.extract i ks.size do mergeItem dup merged other k
    return .done merged
  | .itemsList merged l i =>
    let some xs ← listOf? l | PyPure.modelInvariant "a list of keys that stopped being a list"
    let mut j := i
    for _ in [i:xs.size] do
      let some xs' ← listOf? l | PyPure.modelInvariant "a list of keys that stopped being a list"
      let some k := xs'[j]? | return .done merged
      mergeItem dup merged other k
      j := j + 1
    let some xs' ← listOf? l | PyPure.modelInvariant "a list of keys that stopped being a list"
    if j < xs'.size then return .more (.itemsList merged l j)
    return .done merged

/-- **`f(**other)` into a copy of `d`, CPython's `DICT_MERGE`**, one activation: `format_kwargs_error`
turns an `AttributeError` into "f() argument after ** must be a mapping, not T", and a `KeyError`
with one argument into "f() got multiple values for keyword argument 'k'". -/
def dictMergeStep [PyCalls m V] [PyNew m V] (f d other : V) (st : Option (MergeState V)) :
    m (LoopStep (MergeState V) V) :=
  tryCatch (mergeStep true d other st) fun x => do
    if ← isAttributeError x then
      raiseBuiltin "TypeError"
        s!"{← calleeName f} argument after ** must be a mapping, not {← typeName other}"
    if let some mro ← mroOf (← PyReads.classOf x) then
      if ← inMro (PyPure.imm (m := m) (.builtin .KeyError)) mro then
        if let #[k] ← tupleItems (← excData x).args then
          let some s ← plainStr? k | PyPure.gap "a duplicate ** key whose str runs a protocol"
          raiseBuiltin "TypeError" s!"{← calleeName f} got multiple values for keyword argument '{s}'"
    throw x

/-- **`{**other}` into a copy of `d`, CPython's `DICT_UPDATE`**, one activation: an
`AttributeError` becomes "'T' object is not a mapping". -/
def dictUpdateStep [PyCalls m V] [PyNew m V] (d other : V) (st : Option (MergeState V)) :
    m (LoopStep (MergeState V) V) :=
  tryCatch (mergeStep false d other st) fun x => do
    if ← isAttributeError x then
      raiseBuiltin "TypeError" s!"'{← typeName other}' object is not a mapping"
    throw x

end

end

end StrataPython.Dyn.Sem.Proto
