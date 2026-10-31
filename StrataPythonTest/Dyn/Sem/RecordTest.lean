/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.Proto.Values
meta import StrataPython.Dyn.Sem.Proto.Values

set_option autoImplicit false

/-!
# The record at a second value type

The generic combinators of `Proto/Values.lean` elaborate and run at a value type other than
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

/-- A toy monad: a result, a raised value, or a gap. -/
structure TM (α : Type) : Type 1 where
  run : Except (Option Toy) α

instance : Monad TM where
  pure a := ⟨.ok a⟩
  bind x f := ⟨match x.run with | .ok a => (f a).run | .error e => .error e⟩

instance : MonadExcept Toy TM where
  throw v := ⟨.error (some v)⟩
  tryCatch x h := ⟨match x.run with | .error (some v) => (h v).run | r => r⟩

instance : PyPure TM Toy where
  imm i := .imm i
  immView v := pure (match v with | .imm i => some i | _ => none)
  isUndef v := pure (v matches .undef)
  identical _ _ := pure .unknown
  addrHash _ := pure (.exact 0)
  gap _ := ⟨.error none⟩
  allocExc _ _ _ _ := pure (.obj 1)
  allocDict := pure (.obj 2)
  region _ _ := ⟨.error none⟩

instance : PyNew TM Toy where
  dictSetNew _ _ _ _ _ := pure ()

instance : PyReads TM Toy where
  classOf _ := pure (.imm (.builtin .object))
  handled := pure (.imm .none)
  globalGet _ n := pure (if n == "g" then some (.imm (.int 3)) else none)
  builtinGet _ := pure none
  raiseNew cls _ _ := throw cls
  dictFind _ _ _ _ := pure none

/-- Whether a computation raised the built-in class `b`. -/
def raisedBuiltin {α : Type} (x : TM α) (b : Builtin) : Bool :=
  match x.run with
  | .error (some (.imm (.builtin c))) => c == b
  | _ => false

#guard (loadGlobal (m := TM) "m" "g").run matches .ok (.imm (.int 3))
#guard raisedBuiltin (loadGlobal (m := TM) "m" "nope") .NameError
#guard raisedBuiltin (requireDefined (m := TM) Toy.undef "UnboundLocalError" "x") .UnboundLocalError
#guard (mkDict (m := TM) #[Toy.imm (.int 1), Toy.imm .none]).run matches .ok (.obj 2)
#guard (isOp (m := TM) Toy.undef Toy.undef).run matches .error none

end StrataPython.Dyn.Sem.RecordTest
