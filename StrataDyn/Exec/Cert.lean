/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Spec

set_option autoImplicit false

/-!
# Certificates: a rule respects the heap's typing

A rule's *certificate* says that it reaches only the cells and captures cells it is given: every
ref and closure it hands the machine, in a request, a result, an exit or the world, is valid in
the typing of the heap at that point, whenever everything the machine handed it was.  A typing
does not record which function a closure names or at which signature; the machine checks that
at every call.  A certificate is one choice of the ghost state and spec of `Exec/Spec.lean`: the
ghost state, a value that only proofs carry, is a typing of the heap, which grows as the heap
does.

* A **typing** `S : Typing` gives a tag to some cells and a list of tags to some captures cells.
  `S.Extends S₁` says `S₁` keeps every cell and every captures cell of `S` at its tags: a cell's
  tag never changes, and a captures cell is written once, when its closure is made.  A typing
  need not give every cell of the heap a tag: one that leaves cells out says that a rule may not
  reach them.
* A `Loc` is where a ref of a value is: a cell, at its contents' tag, or a captures cell.
  `S.LocValid p` says `p` is one of `S`'s, and `S.AllValid ps` says each of `ps` is.  Validity
  stays valid in an extension (`AllValid.mono`).

A value's *account*, the list of its refs' locations, and the certificates of a table's rules
are at the machine's tags (`Exec/CertModel.lean`).
-/

namespace Strata.Dyn.Exec

@[expose] public section

/-! ## Typings -/

/-- A typing of the heap: the tag of some cells, and the tags of what some captures cells
hold.  The captures cell of a closure whose `captured` is `k + 1` is `caps k`. -/
structure Typing where
  cell : Nat → Option Ty := fun _ => none
  caps : Nat → Option (List Ty) := fun _ => none

namespace Typing

/-- Location `l`'s cell holds values of tag `t` in `S`. -/
def Valid (S : Typing) (l : Nat) (t : Ty) : Prop := S.cell l = some t

/-- `captured` names a captures cell of `S`, or none. -/
def CapValid (S : Typing) (captured : Nat) : Prop :=
  captured = 0 ∨ ∃ ts, S.caps (captured - 1) = some ts

/-- `S₁` extends `S`: every cell of `S` is one of `S₁`, at the same tag, and every captures
cell of `S` is one of `S₁`, with the same tags. -/
def Extends (S S₁ : Typing) : Prop :=
  (∀ l t, S.cell l = some t → S₁.cell l = some t) ∧
    ∀ k ts, S.caps k = some ts → S₁.caps k = some ts

/-- Every typing extends itself. -/
theorem Extends.refl (S : Typing) : S.Extends S := ⟨fun _ _ h => h, fun _ _ h => h⟩

/-- Extension is transitive. -/
theorem Extends.trans {S₁ S₂ S₃ : Typing} (h₁ : S₁.Extends S₂) (h₂ : S₂.Extends S₃) :
    S₁.Extends S₃ :=
  ⟨fun l t h => h₂.1 l t (h₁.1 l t h), fun k ts h => h₂.2 k ts (h₁.2 k ts h)⟩

/-- A valid cell stays valid in an extension. -/
theorem Valid.mono {S S₁ : Typing} (h : S.Extends S₁) {l : Nat} {t : Ty} (hl : S.Valid l t) :
    S₁.Valid l t :=
  h.1 l t hl

/-- A valid captures cell stays valid in an extension. -/
theorem CapValid.mono {S S₁ : Typing} (h : S.Extends S₁) {k : Nat} (hk : S.CapValid k) :
    S₁.CapValid k :=
  hk.imp id fun ⟨ts, hts⟩ => ⟨ts, h.2 _ ts hts⟩

end Typing

/-! ## Where a value's refs are -/

/-- Where a ref of an account is: a cell, at the tag its contents have, or a captures cell. -/
inductive Loc where
  | cell (loc : Nat) (t : Ty)
  | caps (captured : Nat)
  deriving DecidableEq, Repr

/-- `p` is valid in `S`. -/
def Typing.LocValid (S : Typing) : Loc → Prop
  | .cell l t => S.Valid l t
  | .caps k => S.CapValid k

/-- A valid location stays valid in an extension. -/
theorem Typing.LocValid.mono {S S₁ : Typing} (h : S.Extends S₁) :
    ∀ {p : Loc}, S.LocValid p → S₁.LocValid p
  | .cell _ _, hp => Typing.Valid.mono h hp
  | .caps _, hp => Typing.CapValid.mono h hp

/-- Every location of `ps` is valid in `S`. -/
def Typing.AllValid (S : Typing) (ps : List Loc) : Prop := ∀ p ∈ ps, S.LocValid p

/-- Valid locations stay valid in an extension. -/
theorem Typing.AllValid.mono {S S₁ : Typing} (h : S.Extends S₁) {ps : List Loc}
    (hp : S.AllValid ps) : S₁.AllValid ps :=
  fun p hm => Typing.LocValid.mono h (hp p hm)

/-- A closure's account, as an `if`, is valid exactly when its captures cell is. -/
theorem Typing.capValid_of_allValid {S : Typing} {k : Nat}
    (h : S.AllValid (if k = 0 then [] else [.caps k])) : S.CapValid k := by
  by_cases hk : k = 0
  · exact .inl hk
  · rw [ite_eq_right hk] at h
    exact h _ List.mem_cons_self

/-- A closure's account, as an `if`, is valid exactly when its captures cell is, at any
decision of `k = 0`. -/
@[simp] theorem Typing.allValid_caps {S : Typing} {k : Nat} {_ : Decidable (k = 0)} :
    S.AllValid (if k = 0 then [] else [.caps k]) ↔ S.CapValid k := by
  by_cases hk : k = 0
  · rw [ite_eq_left hk]
    exact ⟨fun _ => .inl hk, fun _ => List.forall_mem_nil _⟩
  · rw [ite_eq_right hk]
    exact List.forall_mem_singleton

/-- The empty list of locations is valid. -/
@[simp] theorem Typing.allValid_nil (S : Typing) : S.AllValid [] := List.forall_mem_nil _

/-- Locations of an append are valid when both parts' are. -/
@[simp] theorem Typing.allValid_append {S : Typing} {ps qs : List Loc} :
    S.AllValid (ps ++ qs) ↔ S.AllValid ps ∧ S.AllValid qs :=
  List.forall_mem_append

/-- One location is valid when it is. -/
@[simp] theorem Typing.allValid_singleton {S : Typing} {p : Loc} :
    S.AllValid [p] ↔ S.LocValid p :=
  List.forall_mem_singleton

/-- The locations of a `flatMap` are valid when those of each element's image are. -/
@[simp] theorem Typing.allValid_flatMap {α : Type} {S : Typing} {l : List α} {f : α → List Loc} :
    S.AllValid (l.flatMap f) ↔ ∀ x ∈ l, S.AllValid (f x) :=
  List.forall_mem_flatMap.trans (forall_congr' fun _ => forall_congr' fun _ => Iff.rfl)

/-- A list of locations is valid when its head and tail are. -/
@[simp] theorem Typing.allValid_cons {S : Typing} {p : Loc} {ps : List Loc} :
    S.AllValid (p :: ps) ↔ S.LocValid p ∧ S.AllValid ps :=
  List.forall_mem_cons

end

end Strata.Dyn.Exec
