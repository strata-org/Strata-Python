/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.Proto.Containers
meta import StrataPython.Dyn.Sem.Proto.Containers

set_option autoImplicit false

/-!
# The record at a second value type

The generic combinators of `Proto/` elaborate and run at a value type other than
`Value`: a toy one, `Toy`, whose immediates are `Imm Toy` and whose objects are numbers, in a
toy monad.  A concrete type in a field's signature would make this file fail to compile.
-/

namespace StrataPython.Dyn.Sem.RecordTest

open StrataPython.Dyn.Sem StrataPython.Dyn.Sem.Proto

/-- A toy value: an immediate, an object by number, or an unassigned value. -/
inductive Toy where
  | imm (i : Imm Toy)
  | obj (n : Nat)
  | undef

/-- A toy monad: a result, a raised value, or a gap with its message. -/
structure TM (α : Type) : Type 1 where
  run : Except (String ⊕ Toy) α

instance : Monad TM where
  pure a := ⟨.ok a⟩
  bind x f := ⟨match x.run with | .ok a => (f a).run | .error e => .error e⟩

instance : MonadExcept Toy TM where
  throw v := ⟨.error (.inr v)⟩
  tryCatch x h := ⟨match x.run with | .error (.inr v) => (h v).run | r => r⟩

instance : PyPure TM Toy where
  imm i := .imm i
  immView v := pure (match v with | .imm i => some i | _ => none)
  isUndef v := pure (v matches .undef)
  identical _ _ := pure .unknown
  addrHash _ := pure (.exact 0)
  gap msg := ⟨.error (.inl msg)⟩
  allocExc _ _ _ _ := pure (.obj 1)
  allocDict := pure (.obj 2)
  region _ _ := ⟨.error (.inl "no region")⟩
  immHash _ := pure none
  numCompare _ _ _ := pure none
  hashValue _ := pure (.imm (.int 0))
  allocList _ := pure (.obj 3)
  allocSet _ _ := pure (.obj 4)

instance : PyNew TM Toy where
  dictSetNew _ _ _ _ _ := pure ()
  listSetNew _ _ _ := pure ()
  listAppendNew _ _ := pure ()
  listSpliceNew _ _ _ _ := pure ()
  listReserveNew _ _ := pure ()
  dictDeleteNew _ _ _ _ := pure none
  dictPopitemNew _ := pure none
  setAddNew _ _ _ _ := pure ()
  setDiscardNew _ _ _ _ := pure false
  setPopNew _ := pure none
  setMergeNew _ _ _ := pure ()
  setSubtractNew _ _ _ := pure ()
  setSymUpdateNew _ _ _ := pure ()
  setReserveNew _ _ := pure ()
  setTrimNew _ := pure ()
  setClearNew _ := pure ()
  setReplaceNew _ _ := pure ()
  setFreezeNew _ := pure ()

instance : PyReads TM Toy where
  classOf v := pure (match v with | .obj _ => .obj 99 | _ => .imm (.builtin .int))
  handled := pure (.imm .none)
  globalGet _ n := pure (if n == "g" then some (.imm (.int 3)) else none)
  builtinGet _ := pure none
  raiseNew cls _ _ := throw cls
  dictFind _ _ _ _ := pure none
  numBinary _ _ _ := pure none
  numUnary _ _ := pure none
  listView _ := pure none
  tupleView _ := pure none
  strView _ := pure none
  bytesView _ := pure none
  numView _ := pure none
  dictEntries _ := pure #[]
  dictEntryAt _ _ := pure .past
  dictEntriesSize _ := pure 0
  dictLen _ := pure 0
  dictFlags _ := pure (false, 0)
  dictCopy _ := pure (.obj 2)
  allocDictFrom _ _ := pure (.obj 2)
  setFind _ _ _ _ := pure false
  setView _ := pure none
  setHasUser _ := pure false
  dictHasUser _ := pure false
  setLen _ := pure 0
  setCopy _ _ := pure (.obj 4)
  setSlotAt _ _ := pure .past

/-- Whether a computation raised the built-in class `b`. -/
def raisedBuiltin {α : Type} (x : TM α) (b : Builtin) : Bool :=
  match x.run with
  | .error (.inr (.imm (.builtin c))) => c == b
  | _ => false

#guard (loadGlobal (m := TM) "m" "g").run matches .ok (.imm (.int 3))
#guard raisedBuiltin (loadGlobal (m := TM) "m" "nope") .NameError
#guard raisedBuiltin (requireDefined (m := TM) Toy.undef "UnboundLocalError" "x") .UnboundLocalError
#guard (mkDict (m := TM) #[Toy.imm (.int 1), Toy.imm .none]).run matches .ok (.obj 2)
#guard (isOp (m := TM) Toy.undef Toy.undef).run matches .error (.inl _)
-- An operator on an object of a user class stops with a gap until the dunder lookup exists.
/-- The gap message of a computation, if it stopped with one. -/
def gapOf {α : Type} (x : TM α) : Option String :=
  match x.run with
  | .error (.inl msg) => some msg
  | _ => none

#guard gapOf (binaryOp (m := TM) .add (Toy.obj 5) (Toy.imm (.int 1))) == some Proto.userGap
#guard gapOf (richCompare (m := TM) .lt (Toy.obj 5) (Toy.obj 6)) == some Proto.userGap
-- The container combinators run too.
#guard (getItem (m := TM) (Toy.imm (.tuple #[.imm (.int 7), .imm (.int 8)])) (.imm (.int (-1)))).run
  matches .ok (.imm (.int 8))
#guard raisedBuiltin (getItem (m := TM) (Toy.imm (.tuple #[])) (.imm (.int 0))) .IndexError
#guard gapOf (contains (m := TM) (Toy.imm (.int 1)) (Toy.obj 5)) == some Proto.userGap
-- An int whose number depends on the hash seed stops the operators with a gap.
/-- An int whose number depends on the hash seed: `hash("a")`. -/
def seeded : Toy :=
  if h : (HashSrc.buffer [97]).storeAddrFree = true then .imm (.symHash ⟨_, h⟩) else .undef

#guard gapOf (binaryOp (m := TM) .add seeded
  (.imm (.int 1))) == some "arithmetic on a hash whose number the model does not know is not modelled yet"
#guard gapOf (richCompare (m := TM) .lt seeded
  (.imm (.int 0))) == some "arithmetic on a hash whose number the model does not know is not modelled yet"
#guard gapOf (unaryOp (m := TM) .neg seeded) ==
  some "arithmetic on a hash whose number the model does not know is not modelled yet"

end StrataPython.Dyn.Sem.RecordTest
