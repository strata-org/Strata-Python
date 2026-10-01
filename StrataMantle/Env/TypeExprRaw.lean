/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Name

set_option autoImplicit false

/-!
# The type expression language without well-formedness criteria.
-/

namespace Strata.Mantle

public section

inductive TypeExpr.Raw where
| var (deBruijnLevel : Nat)
| app (name : Name) (args : Array Raw)

namespace TypeExpr.Raw

/-! ### Equality -/

mutual
@[expose]
def beq : Raw → Raw → Bool
  | .var i, .var j => i == j
  | .app n ⟨as⟩, .app m ⟨bs⟩ => n == m && beqList as bs
  | _, _ => false

@[expose]
def beqList : List Raw → List Raw → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false
end

instance : BEq Raw := ⟨beq⟩

mutual
/-- `beq` implies equality. -/
private theorem eq_of_beq : ∀ {a b : Raw}, beq a b = true → a = b
  | .var _, .var _, h => by simp only [beq, beq_iff_eq] at h; simp [h]
  | .app _ ⟨_⟩, .app _ ⟨_⟩, h => by
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, eqList_of_beqList h.2]

/-- `beqList` implies equality of the lists. -/
private theorem eqList_of_beqList : ∀ {as bs : List Raw}, beqList as bs = true → as = bs
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [beqList, Bool.and_eq_true] at h
    simp [eq_of_beq h.1, eqList_of_beqList h.2]
end

mutual
/-- `beq` is reflexive. -/
private theorem beq_refl : ∀ (a : Raw), beq a a = true
  | .var _ => by simp [beq]
  | .app _ ⟨as⟩ => by
    simp only [beq, Bool.and_eq_true, beq_self_eq_true, true_and]
    exact beqList_refl as

/-- `beqList` is reflexive. -/
private theorem beqList_refl : ∀ (as : List Raw), beqList as as = true
  | [] => rfl
  | a :: as => by
    simp only [beqList, Bool.and_eq_true]
    exact ⟨beq_refl a, beqList_refl as⟩
end

instance : LawfulBEq Raw where
  eq_of_beq := eq_of_beq
  rfl := beq_refl _

instance : DecidableEq Raw := fun a b => decidable_of_iff ((a == b) = true) (by simp)

/-! ### Instantiation -/

mutual
/-- Replace each variable `i` by `args[i]`; a variable with no argument is left alone. -/
@[expose]
def instantiate (args : Array Raw) : Raw → Raw
  | .var i => args[i]?.getD (.var i)
  | .app n ⟨as⟩ => .app n ⟨instantiateList args as⟩

@[expose]
def instantiateList (args : Array Raw) : List Raw → List Raw
  | [] => []
  | e :: es => instantiate args e :: instantiateList args es
end


/-! ### Folding -/

universe u

mutual

/-- Fold over the variables and applications in a type expression. -/
@[expose]
def fold {β : Type u} (var : Nat → β) (app : Name → Array β → β) : Raw → β
  | .var i => var i
  | .app n ⟨as⟩ => app n ⟨foldList var app as⟩

@[expose]
def foldList {β : Type u} (var : Nat → β) (app : Name → Array β → β) : List Raw → List β
  | [] => []
  | e :: es => fold var app e :: foldList var app es
end

end TypeExpr.Raw

end

end Strata.Mantle
