/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.Data

set_option autoImplicit false

/-!
# Theorems about common datatypes

Key theorems: `names_mapTy` and `typeOf?_mapTy`.
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

end

end Strata.Mantle
