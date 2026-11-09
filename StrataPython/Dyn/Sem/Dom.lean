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

/-- What CPython's `Py_ReprEnter` finds for a value: not in the guard; in it; or, for a tuple, a
tuple with the same items in it, which may be the same tuple or another one. -/
inductive ReprEntry where
  | fresh | hit | unknown
  deriving DecidableEq, Repr, Inhabited

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

/-- A class as generic code makes and reads it: its names, bases and MRO after the class itself,
its namespace (a dict), its solid base, and its flags (`Store.lean`'s `ClassObj`). -/
structure ClassData (V : Type) where
  name : String
  qualname : String
  module : String
  bases : Array V
  /-- Its method resolution order after the class itself. -/
  mroTail : Array V
  /-- Its namespace: a dict, which no rule hands to Python code. -/
  ns : V
  /-- Its solid base; `None` for a class with slots of its own, which is its own solid base. -/
  solidBase : V
  instanceDict : Bool := true
  slots : Array String := #[]
  immutable : Bool := false
  gapped : Array String := #[]
  writesGap : Bool := false
  instanceWritesGap : Bool := false
  tpName : Option String := none
  hasDel : Bool := false

/-- An exception's state as generic code reads it (`Store.lean`'s `ExcState`): `args` (a tuple),
`__context__`, `__cause__`, `__suppress_context__`, `__traceback__`, and the fields of its class
(`StopIteration.value`, `NameError.name`, ...) by name. -/
structure ExcData (V : Type) where
  args : V
  context : V
  cause : V
  suppressContext : Bool
  traceback : V
  fields : Array (String × V)

/-- The part of an exception's state that `excSet` writes. -/
inductive ExcPart (V : Type) where
  | args (v : V)
  | context (v : V)
  /-- `__cause__`; CPython's `PyException_SetCause` also sets `__suppress_context__`. -/
  | cause (v : V)
  | suppressContext (b : Bool)
  | traceback (v : V)
  /-- A field of the exception's class; `none` unsets it, as CPython's `NULL`, which reads as
  `None` but which `OSError.__str__` and `PyObject_GetAttr` tell apart from `None`. -/
  | field (name : String) (v : Option V)

/-- A native function as generic code makes and reads it (`Store.lean`'s `NativeFn`). -/
structure NativeData (V : Type) where
  key : String
  kind : NativeKind
  captured : Array V := #[]
  name : String
  qualname : String
  module : String
  defaults : Option V := none
  kwdefaults : Option V := none
  gapped : Array String := #[]

/-- What an object other than a container is, as generic code sees it; a list, a dict, a set, a
frozenset and the built-in part of a subclass instance have views of their own. -/
inductive ObjView (V : Type) where
  /-- An instance of a user class, or of a subclass of a built-in type. -/
  | inst
  | cls (c : ClassData V)
  /-- A translated function: its `__name__`, its `__module__`, its `__annotations__` once set, and
  whether it is a class body; never its closure. -/
  | func (name : String) (module : V) (annotations : Option V) (classBody : Bool)
  | native (f : NativeData V)
  | exc (e : ExcData V)
  | iter (it : IterStateG V)
  | module (name : String) (gapped : Array String) (writesGap : Bool)
  | property (fget fset fdel doc : V)
  /-- A `classmethod` with its callable; `none` until `__init__` sets it (CPython's `NULL`). -/
  | classmethod (f : Option V)
  /-- A `staticmethod` with its callable; `none` until `__init__` sets it. -/
  | staticmethod (f : Option V)
  | super (thisType obj : V)
  | opaque (tag : String) (state : Array V)
  /-- The descriptor of slot `index` of the class `owner`. -/
  | member (owner : V) (name : String) (index : Nat)
  /-- A read-only view of the dict `d`. -/
  | mappingProxy (d : V)

/-- A new object other than a container or an instance, with its final contents. -/
inductive NewObj (V : Type) where
  | cls (c : ClassData V)
  | iter (it : IterStateG V)
  | native (f : NativeData V)
  | module (name : String) (gapped : Array String) (writesGap : Bool)
  | property (fget fset fdel doc : V)
  /-- A `classmethod` with its callable; `none` until `__init__` sets it (CPython's `NULL`). -/
  | classmethod (f : Option V)
  /-- A `staticmethod` with its callable; `none` until `__init__` sets it. -/
  | staticmethod (f : Option V)
  | super (thisType obj : V)
  | opaque (tag : String) (state : Array V)
  | member (owner : V) (name : String) (index : Nat)
  | mappingProxy (d : V)

/-- The built-in part of a new instance: none for an instance of a plain user class; else the
state of the built-in type that its class derives from. -/
inductive BuiltinPart (V : Type) where
  | plain
  | list (elems : Array V)
  | dict
  | set
  | frozenset
  | tuple (elems : Array V)
  | str (s : PyStr)
  | int (i : Int)
  | float (bits : UInt64)
  | bytes (b : Array UInt8)
  | exc (args : Array V)

/-- What a `pure` rule may do: make and view immediates, compare identities, make objects with
their final contents, run a region, and stop with a gap. -/
class PyPure (m : Type → Type 1) (V : outParam Type) extends Monad m, MonadExcept V m where
  /-- The value of an immediate. -/
  imm : Imm V → V
  /-- `v` as an immediate, an `int` whose number depends on the hash seed (`symHash`) included;
  `none` for an object or an unassigned value.  Generic code reads `immView`, which gaps on such an
  `int`, unless it handles that case itself. -/
  immViewAll : V → m (Option (Imm V))
  /-- The name of `v` if it is unassigned. -/
  undefName? : V → m (Option String)
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
  /-- A new object of the class `cls` with the contents `o`; a new class goes first in its own
  MRO. -/
  allocObj : V → NewObj V → m V

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
  /-- Give the class `c` the MRO `mro` after itself, from a user `mro()`. -/
  classSetMroNew : V → Array V → m Unit

/-- Which members of the tables that a walk compares may meet a different key's hash while one
may run user code: a member of key class `user` with an address hash (`userAddr`), one with any
other hash (`userOther`), and any member with an exact or other symbolic hash (`nonAddr`). Two
different live objects never share an address hash. -/
structure WalkKinds where
  userAddr : Bool
  userOther : Bool
  nonAddr : Bool
  deriving Inhabited

/-- Whether a walk over tables of the kinds `ks` may run user code: a `user` member whose hash
may equal another key's. -/
def WalkKinds.mayRunUser (ks : List WalkKinds) : Bool :=
  ks.any (·.userOther) || (ks.any (·.userAddr) && ks.any (·.nonAddr))

/-- The count of nested C levels at which the model stops with a gap, 995 below CPython 3.12's
C recursion limit, where it raises `RecursionError` (lists nested 9,995 deep compare, 9,996 deep
raise).  As in CPython, each comparison counts 1 and each call into Python 2 more; the margin
covers a dict or set key's own comparison levels, which the model doesn't count (`keyDepth`). -/
def cDepthLimit : Nat := 9000

/-- `v` as an immediate; `none` for an object or an unassigned value.  An `int` whose number
depends on the hash seed stops with a gap, so that no consumer can take it for a known number. -/
@[inline] def PyPure.immView {m : Type → Type 1} {V : Type} [PyPure m V] (v : V) :
    m (Option (Imm V)) := do
  match ← PyPure.immViewAll v with
  | some (.symHash _) => PyPure.gap "a hash whose number the model does not know"
  | r => pure r

/-- Whether `v` is unassigned. -/
@[inline] def PyPure.isUndef {m : Type → Type 1} {V : Type} [PyPure m V] (v : V) : m Bool :=
  return (← PyPure.undefName? v).isSome

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
  /-- The kinds of the members of the set `s`, for `WalkKinds.mayRunUser`, in constant time. -/
  setWalkKinds : V → m WalkKinds
  /-- The kinds of the keys of the dict `d`, as `setWalkKinds`. -/
  dictWalkKinds : V → m WalkKinds
  /-- The number of members of the set `s`. -/
  setLen : V → m Nat
  /-- A new set (a frozenset if `frozen`) with the members of `s`, as CPython's `set_merge` into
  an empty set makes it, `inexact` included. -/
  setCopy : V → (frozen : Bool) → m V
  /-- Slot `i` of the table of the set `s`, in constant time; a gap if its layout is inexact. -/
  setSlotAt : V → Nat → m (SlotAt V)
  /-- A new instance of the class `cls` with the built-in part `p`, its `__dict__`'s first
  entries `dict` and its slot values `slots` (`none` for an unset slot): a model invariant (`PyM.failure`) when
  they don't fit the class's layout or `dict` repeats a name. -/
  allocInstance : V → BuiltinPart V → Array (String × V) → Array (Option V) → m V
  /-- What the object `v` is, other than a container; `none` for an immediate. -/
  objView : V → m (Option (ObjView V))
  /-- The `__dict__` of the object `v` (a dict), if it has one. -/
  objDict : V → m (Option V)
  /-- Slot `i` of the object `v`, if it is set. -/
  slotGet : V → Nat → m (Option V)
  /-- Add the module `name`, whose object is `v`, to the module table: a model invariant (`PyM.failure`) if
  the table has it.  Only a new entry, which a `reads` operation may add, as it may make a global
  cell. -/
  moduleAdd : String → V → m Unit
  /-- The count of nested C levels, CPython's C recursion count. -/
  depthC : m Nat
  /-- `body` one nested C level deeper by `n`: a gap past the model's limit, below CPython's
  `RecursionError`; the count is back as it was after `body`. -/
  withDepth : {α : Type} → Nat → m α → m α
  /-- `body` `n` Python frames deeper: a gap past the model's limit, below CPython's
  `RecursionError`; the count is back as it was after `body`.  A port of a Python function counts
  each frame that CPython spends inside it, at least as many as CPython. -/
  withPyDepth : {α : Type} → Nat → m α → m α
  /-- What `Py_ReprEnter` finds for `v` (`ReprEntry`): an object by its identity; a tuple by its
  items, `unknown` when a tuple with the same items is in the guard. -/
  reprCheck : V → m ReprEntry
  /-- `body` with `v` entered in the `repr` guard; the guard is back as it was after `body`. -/
  withRepr : {α : Type} → V → m α → m α

/-- What a `calls` rule may do in addition: call Python code. -/
class PyCalls (m : Type → Type 1) (V : outParam Type) extends PyReads m V where
  /-- Call a function object with an args tuple and a kwargs dict, one Python call deeper. -/
  callFunc : V → V → V → m V
  /-- Call a built-in callable (a built-in function, a built-in method, bound or not, or a native
  function) with an args tuple and a kwargs dict, through the assembly's bodies (`Impls`), inside
  a call bracket below `writes`. -/
  callBuiltin : V → V → V → m V

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
  /-- Set slot `i` of the object `o` to `v`. -/
  slotSet : V → Nat → V → m Unit
  /-- Unset slot `i` of the object `o`. -/
  slotDel : V → Nat → m Unit
  /-- Set the `__name__` and `__qualname__` of the class `c`. -/
  classSetName : V → String → String → m Unit
  /-- Set the `__name__` of the function `f`. -/
  funcSetName : V → String → m Unit
  /-- Set the `__annotations__` of the function `f`. -/
  funcSetAnnotations : V → V → m Unit
  /-- The `__dict__` of the object `v`, made empty first if it has none yet. -/
  objEnsureDict : V → m V
  /-- Set the state of the property, `classmethod` or `staticmethod` `v` to `s`, an object of the
  same kind. -/
  stateSet : V → NewObj V → m Unit
  /-- Write a part of the state of the exception `e`. -/
  excSet : V → ExcPart V → m Unit
  /-- Set the state of the iterator `it` to `s`. -/
  iterSet : V → IterStateG V → m Unit
  /-- Step the built-in iterator `it` of a `str` (or of a `str` subclass instance's `str`): its next
  character as a `str`, and the iterator moved on; `none` when the iterator has ended.  An abstract
  instance that doesn't know whether it has ended gives both outcomes. -/
  strIterNext : V → m (Option V)

/-- **The body of a built-in callable**, generic in the record: from its `self` (the callee itself
for a function), its args tuple and its kwargs dict, its result.  It runs at `writes`, inside the
call bracket of a caller below `writes`. -/
abbrev BuiltinImpl : Type 2 :=
  ∀ {m : Type → Type 1} {V : Type} [PyWrites m V] [PyNew m V], V → V → V → m V

/-- The bodies of the built-in callables, which `Assembly` joins from each piece's part: by
built-in function, by built-in type and method name, and by native function's key. -/
structure Impls : Type 2 where
  function : Builtin → Option BuiltinImpl := fun _ => none
  method : Builtin → String → Option BuiltinImpl := fun _ _ => none
  native : String → Option BuiltinImpl := fun _ => none

/-- What a call that can suspend gives: its result, or the frames of the built-in step machines
that it suspended, the outermost first. -/
inductive CallStep (S V : Type) where
  | done (v : V)
  | suspend (frames : List S)

/-- **A loop state `S` that holds a piece's part `P`**: `Assembly` joins the pieces' loop states, one
constructor per piece, and each piece reaches its own frames through `inj` and `proj`. A `proj` that
gives `none` is another piece's frame. -/
class HasLoopPart (S : Type) (P : Type) where
  inj : P → S
  proj : S → Option P
  proj_inj : ∀ p, proj (inj p) = some p
  inj_of_proj : ∀ s p, proj s = some p → s = inj p

/-- **The built-in step machines of every piece, at the joined loop state `S`**, which `Assembly`
instantiates: the first step of the machine of a built-in callable `f` called with `args` and
`kwargs`, `none` when `f` is not a step machine; and the resume entry, which resumes the machine
that the frame names, with the frames of its inner calls. -/
class PyMachines (m : Type → Type 1) (V : outParam Type) (S : Type) where
  startStep : V → V → V → m (Option (CallStep S V))
  resume : S → List S → m (CallStep S V)


end

end StrataPython.Dyn.Sem
