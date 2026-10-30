/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Sem

set_option autoImplicit false

/-!
# World parts that take apart or build a machine request

`TableCheckTest` gives rules over these, in another module, as a table of the Python semantics
would.  Both are deliberate test inputs that the check must reject: a machine request holds
locations, so a part that takes one apart reads where a cell is, and a part that builds one asks
the machine for a cell that nobody passed.
-/

namespace Strata.Dyn.ExecTest.ReqHelpers

open Strata.Dyn.Exec

@[expose] public section

/-- A "part" of every world: the location that a read request names. -/
instance locOfReq {W : Type} {I : Ty → Type} {rs : List (List Ty × Ty)} :
    HasPart W (MReq I rs → Nat) where
  get _ := fun
    | .get _ l => l
    | _ => 0
  set w _ := w

/-- A "part" of every world: a read request of cell `n`, at the tag `t`, built without a match. -/
instance readCell {W : Type} {I : Ty → Type} {rs : List (List Ty × Ty)} :
    HasPart W (Ty → Nat → MReq I rs) where
  get _ := fun t n => .get t n
  set w _ := w

/-- `c` as a ref of `Bool`: a helper that retypes a ref, which no rule may use. -/
def retypeRef {σ : Type} [Store σ] (c : Ref σ Int) : Ref σ Bool := ⟨c.raw⟩

end

end Strata.Dyn.ExecTest.ReqHelpers
