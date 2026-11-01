/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Store
public import StrataPython.Dyn.Sem.Imm
public import StrataPython.Dyn.Sem.Arith
public import StrataPython.Dyn.Sem.Invariant

set_option autoImplicit false

/-!
# The record of primitives

The rules are written once over a record of primitives, generic in the monad `m` and the value
type `V`.  The record is split by effect, so that the type of a rule says what it may do:

* `PyPure`: compute on values, allocate, stop with a gap;
* `PyNew`: change objects made since the operation started;
* `PyReads`: also read mutable state, and raise a new exception;
* `PyCalls`: also call Python code;
* `PyWrites`: also change existing state.

No primitive takes or gives a machine cell: a primitive that needs one finds it and uses it
inside itself.  The monads land in `Type 1`, as the rule monad does.  Generic code sees values
only as `V`: it makes immediates with `imm` and views them with `immView`, and never names
`Value`, an object id or a table.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- The answer of `is`: yes, no, or unknown (it depends on CPython's caching). -/
inductive IdResult where
  | yes | no | unknown
  deriving DecidableEq, Repr, Inhabited

/-- Position `i` of a dict's entry array: an entry with its key, its value and its stored hash,
a hole where an entry was deleted, or past the end. -/
inductive EntryAt (V : Type) where
  | entry (key value : V) (hash : Hash)
  | hole
  | past

/-- What a set holds: its members with their stored hashes, whether their order is CPython's,
and the number of distinct hashes of its members by kind (exact, address, other symbolic).  The
members are in table order, which is CPython's only when `exact`: a consumer that depends on
their order reads them with `inOrder?`, and `unordered` only where the order can't matter. -/
structure SetView (V : Type) where
  unordered : Array (V × Hash)
  exact : Bool
  groupCount : Nat × Nat × Nat

/-- The members of a set in CPython's order, if the model knows it. -/
def SetView.inOrder? {V : Type} (vw : SetView V) : Option (Array (V × Hash)) :=
  if vw.exact then some vw.unordered else none

/-- Slot `i` of a set's table: an entry with its key and stored hash, a hole (an empty slot or a
deleted entry), or past the end. -/
inductive SlotAt (V : Type) where
  | entry (key : V) (hash : Hash)
  | hole
  | past

/-- What a `pure` rule may do: make and view immediates, compare identities, make objects with
their final contents, run a region, and stop with a gap. -/
class PyPure (m : Type → Type 1) (V : outParam Type) extends Monad m, MonadExcept V m where
  /-- The value of an immediate. -/
  imm : Imm V → V
  /-- `v` as an immediate; `none` for an object or an unassigned value. -/
  immView : V → m (Option (Imm V))
  /-- Whether `v` is unassigned. -/
  isUndef : V → m Bool
  /-- `is`. -/
  identical : V → V → m IdResult
  /-- The hash of `v`'s address, for `object.__hash__`. -/
  addrHash : V → m Hash
  /-- Stop with a gap that names its case. -/
  gap : {α : Type} → String → m α
  /-- A new exception of the class `cls` with the arguments `args`, the fields of its class
  (`NameError.name`, …) and the `__context__` `context`. -/
  allocExc : V → Array V → Array (String × V) → V → m V
  /-- A new empty dict. -/
  allocDict : m V
  /-- Run region `i` of the operation on `args`: its result, or its exception raised. -/
  region : Nat → Array V → m V
  /-- The hash of an immediate with no object inside, as CPython computes it; `none` for any
  other value. -/
  immHash : V → m (Option Hash)
  /-- `a op b` for two numbers (`bool`, `int` or `float`), exact between an `int` and a `float`;
  `none` when one isn't a number. -/
  numCompare : Arith.CmpOp → V → V → m (Option Bool)
  /-- `hash()`'s result for the hash `h`: an `int`, or one whose number is unknown; a gap for a
  hash over a store object's address. -/
  hashValue : Hash → m V
  /-- A new list of the elements `xs`. -/
  allocList : Array V → m V
  /-- A new empty set, a frozenset if `frozen`, whose order starts inexact if `inexact`. -/
  allocSet : (frozen inexact : Bool) → m V

/-- Stop with a model-invariant gap (`Invariant.lean`): a case that the model's own code rules
out. -/
def PyPure.modelInvariant {m : Type → Type 1} {V : Type} [PyPure m V] {α : Type} (msg : String) :
    m α :=
  PyPure.gap (modelInvariantPrefix ++ msg)

/-- What code may do to an object made since its operation's first activation started, by the
operation or by code that it called: this class's contract.  At `PyM σ e false`, which gets its
activation's start, a write to an object older than that activation stops with a model invariant
(`PyM.failure`).  At `PyM σ .writes true`, which doesn't read the start, the writes aren't checked
against it, and the contract is trusted. -/
class PyNew (m : Type → Type 1) (V : outParam Type) where
  /-- Set the entry `k` of the dict `d` to `v`, as `dictFind` finds `k`. -/
  dictSetNew : V → V → V → Option Hash → (V → m Bool) → m Unit
  /-- Set element `i` of the list `l`, which must exist, to `v`. -/
  listSetNew : V → Nat → V → m Unit
  /-- Append `v` to the list `l`. -/
  listAppendNew : V → V → m Unit
  /-- Replace the elements of the list `l` from `lo` to `hi` (`lo ≤ hi ≤ len(l)`) with `xs`. -/
  listSpliceNew : V → Nat → Nat → Array V → m Unit
  /-- CPython's `list_preallocate_exact` with the length hint `n`: it changes the list's
  `allocated` when `n > 0`, which only `list.sort` sees. -/
  listReserveNew : V → Nat → m Unit
  /-- Delete the entry `k` of the dict `d`, as `dictFind` finds `k`, and give its value; `none`
  if `d` has no entry `k`. -/
  dictDeleteNew : V → V → Option Hash → (V → m Bool) → m (Option V)
  /-- Remove the last entry of the dict `d` and give its key and value; `none` if `d` is empty.
  The entry array then ends at the popped entry's position, as CPython's `dk_nentries` does. -/
  dictPopitemNew : V → m (Option (V × V))
  /-- Add `k` to the set `s`, as `setFind` finds `k`. -/
  setAddNew : V → V → Option Hash → (V → m Bool) → m Unit
  /-- Remove `k` from the set `s`, as `setFind` finds `k`; whether it was there. -/
  setDiscardNew : V → V → Option Hash → (V → m Bool) → m Bool
  /-- `set.pop` of the set `s`: the first member from its finger on; `none` if it is empty. -/
  setPopNew : V → m (Option V)
  /-- CPython's `set_merge` of the set `src` into the set `s`: the members of `src` with their
  stored hashes, `eq k` comparing a stored key with `k` where an insertion compares. -/
  setMergeNew : V → V → (V → V → m Bool) → m Unit
  /-- CPython's `set_difference_update_internal` of the set `src` from the set `s`: each member
  of `src` discarded, then the table resized if dummies fill more than a quarter of it. -/
  setSubtractNew : V → V → (V → V → m Bool) → m Unit
  /-- CPython's `set_symmetric_difference_update` of the set `src` into the set `s`. -/
  setSymUpdateNew : V → V → (V → V → m Bool) → m Unit
  /-- Resize the set `s` for `n` more members, as `set_merge` and `set_update_internal` do
  before they add the members of another set or of a dict. -/
  setReserveNew : V → Nat → m Unit
  /-- Resize the set `s` if its dummies fill more than a quarter of it: the last step of
  `set_difference_update_internal`. -/
  setTrimNew : V → m Unit
  /-- Remove every member of the set `s`; its order is exact again. -/
  setClearNew : V → m Unit
  /-- Give the set `s` the table of the set `t`, `inexact` included, keeping its own finger:
  CPython's `set_swap_bodies`. -/
  setReplaceNew : V → V → m Unit
  /-- Close the frozenset `s`, which `allocSet` made open: a write to a closed frozenset, and a read
  of an open one as a value (`setView`), are model invariants. Every maker of a frozenset closes it
  before it escapes. Its abstract reading is a no-op. -/
  setFreezeNew : V → m Unit

/-- What a `reads` rule may do in addition: read mutable state, and raise a new exception. -/
class PyReads (m : Type → Type 1) (V : outParam Type) extends PyPure m V where
  /-- `type(v)`; for an object, read from the store. -/
  classOf : V → m V
  /-- The exception being handled, `None` if none. -/
  handled : m V
  /-- The value of the global `name` of `module`, if its cell is defined. -/
  globalGet : String → String → m (Option V)
  /-- The entry `name` of the `builtins` module's dict, if any. -/
  builtinGet : String → m (Option V)
  /-- A new exception of the class `cls` with the arguments `args` and the fields of its class,
  its `__context__` the exception being handled; raised. -/
  raiseNew : {α : Type} → V → Array V → Array (String × V) → m α
  /-- The value of the entry `k` of the dict `d`: `h` is the hash of `k` when `k` is an object
  (or holds one), `none` otherwise; `eq` compares `k` with a stored key that may run user code. -/
  dictFind : V → V → Option Hash → (V → m Bool) → m (Option V)
  /-- `a op b` for two numbers, with CPython's result or its exception raised; `none` when one
  isn't a number, or the operator doesn't apply to them (`<<` on a `float`). -/
  numBinary : Arith.BinOp → V → V → m (Option V)
  /-- `op a` for a number, as `numBinary`. -/
  numUnary : Arith.UnaryOp → V → m (Option V)
  /-- The elements of `l`, a list or an instance of a subclass of `list`, and its resize counter,
  which moves at every change of its length and at each preallocation; `none` for any other
  value. -/
  listView : V → m (Option (Array V × Nat))
  /-- The elements of the built-in part of an instance of a subclass of `tuple`; `none` for any
  other value. -/
  tupleView : V → m (Option (Array V))
  /-- The `str` of the built-in part of an instance of a subclass of `str`. -/
  strView : V → m (Option PyStr)
  /-- The octets of the built-in part of an instance of a subclass of `bytes`. -/
  bytesView : V → m (Option (Array UInt8))
  /-- The number of the built-in part of an instance of a subclass of `int` or `float`. -/
  numView : V → m (Option Arith.Num)
  /-- The module object of the module `name`, if the module table has it. -/
  moduleGet : String → m (Option V)
  /-- The entries of the dict `d`, in order: each key, its value and its stored hash. -/
  dictEntries : V → m (Array (V × V × Hash))
  /-- Position `i` of the entry array of the dict `d`, in constant time. -/
  dictEntryAt : V → Nat → m (EntryAt V)
  /-- The size of the entry array of the dict `d`, holes included: CPython's `dk_nentries`. -/
  dictEntriesSize : V → m Nat
  /-- The number of entries of the dict `d`. -/
  dictLen : V → m Nat
  /-- Whether a key of the dict `d` was deleted since it was made or cleared, and the version of
  its keys, which changes whenever a key is added or removed. -/
  dictFlags : V → m (Bool × Nat)
  /-- A new dict with the entries of `d`, in order, and its deletion flag. -/
  dictCopy : V → m V
  /-- A new dict with the entries of `d` at the positions `i` of `dictEntries` for which `keep i`
  holds, in order, with their stored hashes: no hash or comparison runs. -/
  allocDictFrom : V → (Nat → Bool) → m V
  /-- Whether the set `s` has a member `k`: the key as in `dictFind`, without its check of a key
  stored under another hash, since a set compares the hashes first. -/
  setFind : V → V → Option Hash → (V → m Bool) → m Bool
  /-- The members of a set, a frozenset or an instance of a subclass of either; `none` for any
  other value. -/
  setView : V → m (Option (SetView V))
  /-- Whether comparing a member of the set `s` may run user code (a member of key class `user`),
  in constant time. -/
  setHasUser : V → m Bool
  /-- Whether comparing a key of the dict `d` may run user code, in constant time. -/
  dictHasUser : V → m Bool
  /-- The number of members of the set `s`. -/
  setLen : V → m Nat
  /-- A new set (a frozenset if `frozen`) with the members of `s`, as CPython's `set_merge` into
  an empty set makes it, `inexact` included. -/
  setCopy : V → (frozen : Bool) → m V
  /-- Slot `i` of the table of the set `s`, in constant time; a gap if its layout is inexact. -/
  setSlotAt : V → Nat → m (SlotAt V)

/-- What a `calls` rule may do in addition: call Python code. -/
class PyCalls (m : Type → Type 1) (V : outParam Type) extends PyReads m V where
  /-- Call a function object with an args tuple and a kwargs dict, one Python call deeper. -/
  callFunc : V → V → V → m V

/-- What a `writes` rule may do in addition: change existing state. -/
class PyWrites (m : Type → Type 1) (V : outParam Type) extends PyCalls m V where
  /-- Set the exception being handled. -/
  setHandled : V → m Unit
  /-- Write text to standard output. -/
  write : String → m Unit
  /-- `dictSetNew` on any dict. -/
  dictSet : V → V → V → Option Hash → (V → m Bool) → m Unit
  /-- `listSetNew` on any list. -/
  listSet : V → Nat → V → m Unit
  /-- `listAppendNew` on any list. -/
  listAppend : V → V → m Unit
  /-- `listSpliceNew` on any list. -/
  listSplice : V → Nat → Nat → Array V → m Unit
  /-- `listReserveNew` on any list. -/
  listReserve : V → Nat → m Unit
  /-- `dictDeleteNew` on any dict. -/
  dictDelete : V → V → Option Hash → (V → m Bool) → m (Option V)
  /-- `dictPopitemNew` on any dict. -/
  dictPopitem : V → m (Option (V × V))
  /-- Remove every entry of the dict `d`, and clear its deletion flag. -/
  dictClear : V → m Unit
  /-- `setAddNew` on any set. -/
  setAdd : V → V → Option Hash → (V → m Bool) → m Unit
  /-- `setDiscardNew` on any set. -/
  setDiscard : V → V → Option Hash → (V → m Bool) → m Bool
  /-- `setPopNew` on any set. -/
  setPop : V → m (Option V)
  /-- `setMergeNew` on any set. -/
  setMerge : V → V → (V → V → m Bool) → m Unit
  /-- `setSubtractNew` on any set. -/
  setSubtract : V → V → (V → V → m Bool) → m Unit
  /-- `setSymUpdateNew` on any set. -/
  setSymUpdate : V → V → (V → V → m Bool) → m Unit
  /-- `setReserveNew` on any set. -/
  setReserve : V → Nat → m Unit
  /-- `setTrimNew` on any set. -/
  setTrim : V → m Unit
  /-- `setClearNew` on any set. -/
  setClear : V → m Unit
  /-- `setReplaceNew` on any set. -/
  setReplace : V → V → m Unit


end

end StrataPython.Dyn.Sem
