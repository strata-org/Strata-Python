/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Store
public import StrataPython.Dyn.Sem.Imm
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


end

end StrataPython.Dyn.Sem
