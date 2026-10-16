/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.TypeExprRaw

set_option autoImplicit false

/-!
# Theorems for the unchecked type expressions.

Key theorems: `instantiate_app`, `instantiate_list` and `fold_app`.
-/

namespace Strata.Mantle

public section

namespace TypeExpr.Raw

/-- Instantiating a list of type expressions maps `instantiate` over it. -/
private theorem instantiateList_eq_map (args : Array Raw) :
    ∀ (as : List Raw), instantiateList args as = as.map (instantiate args)
  | [] => rfl
  | a :: as => by simp [instantiateList, instantiateList_eq_map args as]

/-- Instantiating a literal's elements instantiates each, splicing in each variable's
argument. -/
private theorem instantiateElems_eq_flatMap (args : Array Raw) :
    ∀ (es : List Raw), instantiateElems args es = es.flatMap (instantiateElem args)
  | [] => rfl
  | e :: es => by
    cases e <;> simp [instantiateElems, instantiateElem, instantiateElems_eq_flatMap args es]

mutual
/-- Instantiating with no arguments is the identity. -/
theorem instantiate_empty : ∀ (e : Raw), instantiate #[] e = e
  | .var _ => by simp [instantiate]
  | .app _ ⟨as⟩ => by simp [instantiate, instantiateList_empty as]
  | .list ⟨es⟩ => by simp [instantiate, instantiateElems_empty es]

/-- Instantiating a list of type expressions with no arguments leaves it unchanged. -/
private theorem instantiateList_empty : ∀ (as : List Raw), instantiateList #[] as = as
  | [] => rfl
  | a :: as => by simp [instantiateList, instantiate_empty a, instantiateList_empty as]

/-- Instantiating a literal's elements with no arguments leaves them unchanged. -/
private theorem instantiateElems_empty : ∀ (es : List Raw), instantiateElems #[] es = es
  | [] => rfl
  | .var _ :: es => by simp [instantiateElems, spliced, instantiateElems_empty es]
  | .app n as :: es => by
    simp [instantiateElems, instantiate_empty (.app n as), instantiateElems_empty es]
  | .list as :: es => by
    simp [instantiateElems, instantiate_empty (.list as), instantiateElems_empty es]
end

/-- Instantiating an application maps over its arguments. -/
theorem instantiate_app (args : Array Raw) (n : Name) (as : Array Raw) :
    instantiate args (.app n as) = .app n (as.map (instantiate args)) := by
  obtain ⟨as⟩ := as
  simp [instantiate, instantiateList_eq_map, Array.map]

/-- Instantiating a list literal instantiates each element, splicing in each variable's
argument. -/
theorem instantiate_list (args : Array Raw) (es : Array Raw) :
    instantiate args (.list es) = .list (es.toList.flatMap (instantiateElem args)).toArray := by
  obtain ⟨es⟩ := es
  simp [instantiate, instantiateElems_eq_flatMap]

/-- A type may be an element of a list literal. -/
theorem isElem_of_kind {scope : Array Kind} {e : Raw} (h : e.kind scope = .type) :
    e.isElem = true := by
  cases e <;> simp_all [kind, isElem]

section fold
variable {β : Type _} (var : Nat → β) (app : Name → Array β → β) (list : Array β → β)

/-- Folding a list of type expressions maps `fold` over it. -/
private theorem foldList_eq_map :
    ∀ (as : List Raw), foldList var app list as = as.map (fold var app list)
  | [] => rfl
  | a :: as => by simp [foldList, foldList_eq_map as]

/-- Folding an application folds its arguments. -/
theorem fold_app (n : Name) (as : Array Raw) :
    fold var app list (.app n as) = app n (as.map (fold var app list)) := by
  obtain ⟨as⟩ := as
  simp [fold, foldList_eq_map, Array.map]

/-- Folding a list literal folds its elements. -/
theorem fold_list (es : Array Raw) :
    fold var app list (.list es) = list (es.map (fold var app list)) := by
  obtain ⟨es⟩ := es
  simp [fold, foldList_eq_map, Array.map]

end fold

/-- There is one variable per kind. -/
@[simp] theorem length_varsFrom : ∀ (i : Nat) (ks : List Kind), (varsFrom i ks).length = ks.length
  | _, [] => rfl
  | i, .type :: ks => by simp [varsFrom, length_varsFrom (i + 1) ks]
  | i, .list :: ks => by simp [varsFrom, length_varsFrom (i + 1) ks]

/-- There is one variable per variable of the scope. -/
@[simp] theorem size_vars (scope : Array Kind) : (vars scope).size = scope.size := by
  simp [vars]

/-- The variables `i, i + 1, …` of a scope have the scope's kinds there. -/
theorem map_kind_varsFrom (scope : Array Kind) : ∀ (i : Nat) (ks : List Kind),
    (∀ (j : Nat) (h : j < ks.length), scope[i + j]? = some ks[j]) →
      (varsFrom i ks).map (kind scope) = ks
  | _, [], _ => rfl
  | i, k :: ks, h => by
    have h₀ : scope[i]? = some k := h 0 (by simp)
    have ih := map_kind_varsFrom scope (i + 1) ks fun j hj => by
      rw [show i + 1 + j = i + (j + 1) by omega]
      exact h (j + 1) (by simpa using hj)
    cases k <;> simp [varsFrom, kind, h₀, ih]

/-- The variables of a scope have the scope's kinds. -/
theorem map_kind_vars (scope : Array Kind) : (vars scope).map (kind scope) = scope := by
  rw [← Array.toList_inj, Array.toList_map, vars, map_kind_varsFrom scope 0 scope.toList]
  intro j hj
  simp

end TypeExpr.Raw

end

end Strata.Mantle
