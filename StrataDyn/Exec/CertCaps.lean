/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Cert

set_option autoImplicit false

/-!
# Capability specs: what a rule assumes of each capability, at a typing of the heap

A certificate (`Exec/CertModel.lean`) is proved operation by operation.  A language whose rules
are written once over primitives proves it primitive by primitive instead, and needs what each
capability promises at a typing (`Exec/Cert.lean`):

* `Refs σ α` says where the refs of a value of `α` are, its *account*: each ref's cell, at its
  contents' tag, and each closure's captures cell.  `RefsOK S x` says each is valid in `S`.
  `Ref`, `FnRef`, the base's literal types, `Option`, `Except`, `×`, `Array` and `List` have
  instances.
* `HeapSpec`, `CallSpec` and `PartSpec` say what a spec over typings promises of the heap, of
  calls and of a part of the world, with `RefsOK` as their pre- and postconditions.

Their lemmas are in `Exec/CertCapsProps.lean`.
-/

namespace Strata.Dyn.Exec

@[expose] public section

/-- Where the refs of a value of `α` are, at the token `σ`: each ref's cell and each closure's
captures cell. -/
class Refs (σ : Type) [Store σ] (α : Type) where
  refs : α → List Loc

section
variable {σ : Type} [Store σ]

/-- A ref's account: its cell, at its contents' tag. -/
instance instRefsRef {α : Type} [Decode σ] [t : TagOf σ α] : Refs σ (Ref σ α) :=
  ⟨fun c => [.cell c.loc t.tag]⟩

/-- A closure's account: its captures cell, if it has one.  What the cell holds is accounted
there, once: it is fixed when the closure is made. -/
instance instRefsFnRef {as : List Type} {r : Type} : Refs σ (FnRef σ as r) :=
  ⟨fun f => if f.captured = 0 then [] else [.caps f.captured]⟩

instance : Refs σ Unit := ⟨fun _ => []⟩
instance : Refs σ Empty := ⟨fun _ => []⟩
instance : Refs σ Bool := ⟨fun _ => []⟩
instance : Refs σ Int := ⟨fun _ => []⟩
instance : Refs σ Nat := ⟨fun _ => []⟩
instance : Refs σ Float := ⟨fun _ => []⟩
instance : Refs σ String := ⟨fun _ => []⟩
instance {n : Nat} : Refs σ (Fin n) := ⟨fun _ => []⟩
instance {α : Type} [Refs σ α] : Refs σ (Option α) :=
  ⟨fun | some a => Refs.refs (σ := σ) a | none => []⟩
instance {α β : Type} [Refs σ α] [Refs σ β] : Refs σ (Except α β) :=
  ⟨fun | .error a => Refs.refs (σ := σ) a | .ok b => Refs.refs (σ := σ) b⟩
instance {α β : Type} [Refs σ α] [Refs σ β] : Refs σ (α × β) :=
  ⟨fun p => Refs.refs (σ := σ) p.1 ++ Refs.refs (σ := σ) p.2⟩
instance {α : Type} [Refs σ α] : Refs σ (List α) := ⟨fun xs => xs.flatMap (Refs.refs (σ := σ))⟩
instance {α : Type} [Refs σ α] : Refs σ (Array α) :=
  ⟨fun xs => xs.toList.flatMap (Refs.refs (σ := σ))⟩

/-- Every ref of `x` is valid in `S`. -/
def RefsOK {α : Type} [Refs σ α] (S : Typing) (x : α) : Prop :=
  S.AllValid (Refs.refs (σ := σ) x)

end

/-! ## Kripke specs, and what a rule's capabilities promise -/

section
variable {ε : Eff} {E : Type}

variable {σ : Type} [Store σ] [Decode σ] (V : Spec Typing ε E)

/-- **What the machine's cells promise at the Lean type `α`, of tag `t`**: a new cell is a
valid request of a valid value, and its ref is valid; a read and a write of a valid ref are
valid requests when what is written is valid, and a read answers a valid value; an update is
valid when it keeps valid values valid. -/
structure HeapSpec (h : HasHeap σ ε) (α : Type) [t : TagOf σ α] [Refs σ α] : Prop where
  new : ∀ S (v : α), RefsOK (σ := σ) S v → V.Pre S (h.newReq t v)
  newAns : ∀ S (v : α) o, V.Post S (h.newReq t v) o → S.Valid (h.newAns t v o).loc t.tag
  get : ∀ S (c : Ref σ α), S.Valid c.loc t.tag → V.Pre S (h.getReq t c)
  getAns : ∀ S (c : Ref σ α) o, V.Post S (h.getReq t c) o → RefsOK (σ := σ) S (h.getAns t c o)
  set : ∀ S (c : Ref σ α) (v : α), S.Valid c.loc t.tag → RefsOK (σ := σ) S v →
    V.Pre S (h.setReq t c v)
  modify : ∀ S (c : Ref σ α) (f : α → α), S.Valid c.loc t.tag →
    (∀ x, RefsOK (σ := σ) S x → RefsOK (σ := σ) S (f x)) → V.Pre S (h.modifyReq t c f)

/-- **What the machine's calls promise at the signature `as → r`**: calling a valid closure on
valid arguments is a valid request, and its result is valid. -/
structure CallSpec (h : HasCall σ ε) (as : List Type) (r : Type) [s : SigOf σ as r]
    [Refs σ (Payload as)] [Refs σ r] : Prop where
  call : ∀ S (f : FnRef σ as r) a, RefsOK (σ := σ) S f → RefsOK (σ := σ) S a →
    V.Pre S (h.callReq s f a)
  callAns : ∀ S (f : FnRef σ as r) a o, V.Post S (h.callReq s f a) o →
    RefsOK (σ := σ) S (h.callAns s f a o)

end

section
variable {ε : Eff} {E : Type} {σ : Type} [Store σ] (V : Spec Typing ε E)

/-- **What a part `P` of the world promises**: a possible world's part is valid, and putting
back a valid part keeps the world possible. -/
structure PartSpec (P : Type) [HasPart ε.W P] [Refs σ P] : Prop where
  get : ∀ S w, V.World S w → RefsOK (σ := σ) S (HasPart.get (P := P) w)
  set : ∀ S w (p : P), V.World S w → RefsOK (σ := σ) S p → V.World S (HasPart.set w p)

end

end

end Strata.Dyn.Exec
