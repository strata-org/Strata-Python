/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.TypeExprRaw

set_option autoImplicit false

/-!
# Theorems for the unchecked type expressions.

Key theorems: `instantiate_app` and `fold_app`.
-/

namespace Strata.Mantle

public section

namespace TypeExpr.Raw

/-- Instantiating a list of type expressions maps `instantiate` over it. -/
private theorem instantiateList_eq_map (args : Array Raw) :
    ∀ (as : List Raw), instantiateList args as = as.map (instantiate args)
  | [] => rfl
  | a :: as => by simp [instantiateList, instantiateList_eq_map args as]

mutual
/-- Instantiating with no arguments is the identity. -/
theorem instantiate_empty : ∀ (e : Raw), instantiate #[] e = e
  | .var _ => by simp [instantiate]
  | .app _ ⟨as⟩ => by simp [instantiate, instantiateList_empty as]

/-- Instantiating a list of type expressions with no arguments leaves it unchanged. -/
private theorem instantiateList_empty : ∀ (as : List Raw), instantiateList #[] as = as
  | [] => rfl
  | a :: as => by simp [instantiateList, instantiate_empty a, instantiateList_empty as]
end

/-- Instantiating an application maps over its arguments. -/
theorem instantiate_app (args : Array Raw) (n : Name) (as : Array Raw) :
    instantiate args (.app n as) = .app n (as.map (instantiate args)) := by
  obtain ⟨as⟩ := as
  simp [instantiate, instantiateList_eq_map, Array.map]

/-- Folding a list of type expressions maps `fold` over it. -/
private theorem foldList_eq_map {β : Type _} (var : Nat → β) (app : Name → Array β → β) :
    ∀ (as : List Raw), foldList var app as = as.map (fold var app)
  | [] => rfl
  | a :: as => by simp [foldList, foldList_eq_map var app as]

/-- Folding an application folds its arguments. -/
theorem fold_app {β : Type _} (var : Nat → β) (app : Name → Array β → β) (n : Name)
    (as : Array Raw) : fold var app (.app n as) = app n (as.map (fold var app)) := by
  obtain ⟨as⟩ := as
  simp [fold, foldList_eq_map, Array.map]

end TypeExpr.Raw

end

end Strata.Mantle
