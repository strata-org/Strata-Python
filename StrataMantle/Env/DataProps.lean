/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.Data

set_option autoImplicit false

/-!
# Theorems about common datatypes

Key theorems: `names_mapTy`, `typeOf?_mapTy` and `TypeDecl.kinds_eq_of_erase_eq`.
-/

namespace Strata.Mantle

public section

namespace DataGroup

variable {α τ τ' : Type}

/-- Changing the type representation keeps the names the group introduces. -/
@[simp] theorem names_mapTy (f : τ → τ') (g : DataGroup α τ) :
    (g.mapTy f).names = g.names := by
  apply Array.toList_inj.mp
  simp [names, mapTy, DatatypeDecl.mapTy, Ctor.mapTy, List.flatMap_map, Function.comp_def]

/-- Changing the type representation keeps the declaration of the type that heads the
group. -/
@[simp] theorem first_toTypeDecl_mapTy (f : τ → τ') (g : DataGroup α τ) :
    (g.mapTy f).first.toTypeDecl = g.first.toTypeDecl := by
  simp [first, mapTy, DatatypeDecl.mapTy, DatatypeDecl.toTypeDecl]

/-- Changing the type representation keeps the name of the type that heads the group. -/
@[simp] theorem first_name_mapTy (f : τ → τ') (g : DataGroup α τ) :
    (g.mapTy f).first.name = g.first.name := by
  simp [first, mapTy, DatatypeDecl.mapTy]

/-- Changing the type representation keeps the type the group declares under each name. -/
@[simp] theorem typeOf?_mapTy (f : τ → τ') (g : DataGroup α τ) (n : Name) :
    (g.mapTy f).typeOf? n = g.typeOf? n := by
  simp [typeOf?, mapTy, Array.find?_map, Function.comp_def, DatatypeDecl.mapTy,
    DatatypeDecl.toTypeDecl]

end DataGroup

/-- Erasing keeps the parameters. -/
@[simp] theorem TypeDecl.params_erase {α : Type} (d : TypeDecl α) : d.erase.params = d.params :=
  rfl

/-- Declarations equal up to annotations have the same parameters. -/
theorem TypeDecl.params_eq_of_erase_eq {α : Type} {d₁ d₂ : TypeDecl α}
    (h : d₁.erase = d₂.erase) : d₁.params = d₂.params :=
  congrArg (TypeDecl.params (α := Unit)) h

/-- Declarations equal up to annotations take arguments of the same kinds. -/
theorem TypeDecl.kinds_eq_of_erase_eq {α : Type} {d₁ d₂ : TypeDecl α}
    (h : d₁.erase = d₂.erase) : d₁.kinds = d₂.kinds := by
  rw [kinds, kinds, params_eq_of_erase_eq h]

/-- There is one kind per parameter. -/
@[simp] theorem TyParam.size_kinds (ps : Array (Param TyParam)) :
    (TyParam.kinds ps).size = ps.size := by
  simp [TyParam.kinds]

end

end Strata.Mantle
