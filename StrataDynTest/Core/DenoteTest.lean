/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all StrataDyn.Core.Denote
import StrataDyn.Core.Types
import StrataDyn.TypeDenote
import all StrataDyn.Env.TypeExprElim
import StrataDyn.Env
import all StrataDyn.Base
import all StrataDynTest.Core.TypesTest

set_option autoImplicit false

/-! # Dyn types denoted directly, and the Base policy's laws

The direct Dyn meaning of base types, the laws of the test policies' concrete representations,
and `base_laws`: every generator of the Base policy preserves meaning, with one lemma per branch
of the policy. -/

namespace Strata.Dyn.CoreTypesDenoteTest

open Lambda CoreTypes CoreTypes.Denote

/-- The examples interpret Dyn names, independently of the policy tested in `CoreTypesTest`. -/
private def dyn : TypeDenote.Constructors base := fun r args =>
  if r.name == bn "Int" then Int
  else if r.name == bn "Bool" then Bool
  else if r.name == bn "Unit" then Unit
  else if r.name == bn "Except" then
    match args.values.toList.flatMap TypeDenote.splice with
    | [e, a] => Except e a
    | _ => Empty
  else if r.name == bn "Fn" then
    match args.values.toList with
    | [⟨.list, as⟩, ⟨.type, r⟩] => as.foldr (fun a r => a → r) r
    | _ => Empty
  else Empty

private def noVars : TypeDenote.Assignment #[] := fun _ _ h => absurd h (by simp)

private def source (t : TypeExpr base) : Type := TypeDenote.denote dyn noVars t

example : source Base.Int = Int := by rfl
example : source Base.Unit = Unit := by rfl

example : source (Base.Except Base.Int Base.Bool) = Except Int Bool := by
  simp only [source, TypeDenote.denote, Base.Internal.Except.ty]
  rw [TypeExpr.elim_app]
  simp [TypeExpr.Arguments.ofTypeArgs, dyn, TypeDenote.splice,
    Base.Int, Base.Internal.Int.ty, Base.Bool, Base.Internal.Bool.ty]

/-- A function type's source meaning is the curried function type over its arguments' meanings. -/
private theorem source_fn (as : List (TypeExpr base)) (r : TypeExpr base) :
    source (Base.Fn as r) = (as.map source).foldr (fun a r => a → r) (source r) := by
  simp only [source, TypeDenote.denote, Base.Internal.Fn.ty, TypeCon.ListArg.toTypeList,
    TypeExpr.elim_appK, dyn, TypeRef.name_canonical, Base.Fn.name_ref, beq_iff_eq, Name.str.injEq,
    String.reduceEq, and_false, ↓reduceIte, BEq.rfl, TypeExpr.Arguments.ofTypeArgs,
    List.map_toArray, List.map_cons, TypeArg.kind_list, TypeExpr.elim_list, List.map_map,
    Function.comp_def, TypeList.Elem.elim, TypeArg.kind_ty, List.map_nil]
  congr 1
  induction as <;> simp_all [TypeDenote.splice, source, TypeDenote.denote]

example : source (Base.Fn [Base.Int, Base.Bool] Base.Unit) = (Int → Bool → Unit) := by
  rw [source_fn]
  rfl

example : source (Base.Fn [] Base.Int) = Int := by
  rw [source_fn]
  rfl

/-- A scalar representation denotes its nullary Core constructor. -/
private theorem scalar_law {K : Signature} {V : Vars} {ks : Array Kind} (name : String)
    (hK : ∀ p ∈ (CoreTypesTest.scalar (kinds := ks) name).uses, K p.1 p.2)
    (args : TypeExpr.Arguments (Value K V) ks) (c : Constructors) (vs : TyIdentifier → Type) :
    core c vs ((CoreTypesTest.scalar name).apply hK args).val = app c name [] := by
  simp only [CoreTypesTest.scalar, Ty.app, core, List.map_nil]

/-- A list variable is spliced, not interpreted as a single type. -/
example (A B : Type) :
    TypeDenote.denote dyn
      (scope := #[.list]) (fun _ k _ => match k with | .type => Empty | .list => [A, B])
      (TypeList.lit #[.splice 0 rfl, .ty Base.Int]) = [A, B, Int] := by
  simp only [TypeDenote.denote, TypeExpr.elim_list, List.map_toArray, List.map_cons,
    TypeList.Elem.elim, List.map_nil, List.flatMap_cons, TypeDenote.splice, List.flatMap_nil,
    List.append_nil, List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
  rfl

/-- The Base policy's meanings: datatypes and nominal primitives have a supplied meaning,
Int and Bool are their Lean carriers, and a primitive taking a list and a result is the supplied
`closure`, whatever its arguments. This follows the policy's dispatch on declarations, not Core
translation. -/
private def baseMeaning (nominal : Name → List Type → Type) (closure : Type) :
    TypeDenote.Constructors base :=
  fun r args =>
    let named := nominal r.name (args.values.toList.flatMap TypeDenote.splice)
    if (base.dataOf? r.name).isSome then named
    else if r.decl.name == bn "Int" then Int
    else if r.decl.name == bn "Bool" then Bool
    else if r.kinds = #[.list, .type] then closure
    else named

section BaseLaws

variable {K : Signature} {V : Vars} (c : Constructors) (vs : TyIdentifier → Type)
  (hK : ∀ n a, signature base CoreTypesTest.basePrimitives n a → K n a) {arity : Nat}
  (r : TypeRef base arity) (args : TypeExpr.Arguments (Value K V) r.kinds)
  (nominal : Name → List Type → Type) (closure : Type)

/-- A datatype is nominal: its meaning is the supplied one. -/
private theorem datatype_branch (hn : ∀ n ts, c (typeName n) ts = nominal n ts)
    (hd : (base.dataOf? r.name).isSome = true) :
    core c vs (CoreTypes.apply CoreTypesTest.basePrimitives hK r args).val =
      nominal r.name ((args.map (value c vs)).values.toList.flatMap TypeDenote.splice) :=
  (core_apply_nominal _ c vs hK r args (by simp only [representation, hd, ↓reduceIte])).trans
    (hn _ _)

/-- `Int` is Core's `int`. -/
private theorem int_branch (hd : ¬ (base.dataOf? r.name).isSome = true)
    (hi : (r.decl.name == bn "Int") = true) :
    core c vs (CoreTypes.apply CoreTypesTest.basePrimitives hK r args).val = Int :=
  (core_apply_concrete _ c vs hK r args (CoreTypesTest.scalar "int") (by
    simp only [representation, hd, Bool.false_eq_true, ↓reduceIte, CoreTypesTest.basePrimitives,
      TypeDecl.erase, hi]
    rfl)).trans (scalar_law "int" _ args c vs)

/-- `Bool` is Core's `bool`. -/
private theorem bool_branch (hd : ¬ (base.dataOf? r.name).isSome = true)
    (hi : ¬ (r.decl.name == bn "Int") = true) (hb : (r.decl.name == bn "Bool") = true) :
    core c vs (CoreTypes.apply CoreTypesTest.basePrimitives hK r args).val = Bool :=
  (core_apply_concrete _ c vs hK r args (CoreTypesTest.scalar "bool") (by
    simp only [representation, hd, Bool.false_eq_true, ↓reduceIte, CoreTypesTest.basePrimitives,
      TypeDecl.erase, hi, hb]
    rfl)).trans (scalar_law "bool" _ args c vs)

/-- A primitive taking a list and a result is the opaque `Closure`. -/
private theorem closure_branch (hc : c "Closure" [] = closure)
    (hd : ¬ (base.dataOf? r.name).isSome = true)
    (hi : ¬ (r.decl.name == bn "Int") = true) (hb : ¬ (r.decl.name == bn "Bool") = true)
    (hk : r.kinds = #[.list, .type]) :
    core c vs (CoreTypes.apply CoreTypesTest.basePrimitives hK r args).val = closure :=
  (core_apply_concrete _ c vs hK r args (CoreTypesTest.scalar "Closure") (by
    simp only [representation, hd, Bool.false_eq_true, ↓reduceIte, CoreTypesTest.basePrimitives,
      TypeDecl.erase, hi, hb]
    exact ite_eq_left hk)).trans ((scalar_law "Closure" _ args c vs).trans hc)

/-- Every other primitive is nominal. -/
private theorem nominal_branch (hn : ∀ n ts, c (typeName n) ts = nominal n ts)
    (hd : ¬ (base.dataOf? r.name).isSome = true)
    (hi : ¬ (r.decl.name == bn "Int") = true) (hb : ¬ (r.decl.name == bn "Bool") = true)
    (hk : ¬ r.kinds = #[.list, .type]) :
    core c vs (CoreTypes.apply CoreTypesTest.basePrimitives hK r args).val =
      nominal r.name ((args.map (value c vs)).values.toList.flatMap TypeDenote.splice) :=
  (core_apply_nominal _ c vs hK r args (by
    simp only [representation, hd, Bool.false_eq_true, ↓reduceIte, CoreTypesTest.basePrimitives,
      TypeDecl.erase, hi, hb]
    exact ite_eq_right hk)).trans (hn _ _)

end BaseLaws

/-- All generators of the Base policy preserve meaning, provided corresponding nominal names
have the same interpretation and the opaque `Closure` has the supplied carrier. No semantic
premise is needed for the other concrete representations. The proof follows the branches of
`baseMeaning`, one lemma each. -/
theorem base_laws (nominal : Name → List Type → Type) (closure : Type) (c : Constructors)
    (vs : TyIdentifier → Type) (hn : ∀ n ts, c (typeName n) ts = nominal n ts)
    (hc : c "Closure" [] = closure) :
    Laws CoreTypesTest.basePrimitives (baseMeaning nominal closure) c vs := by
  intro K V hK arity r args
  simp only [baseMeaning]
  split <;> rename_i hd
  · exact datatype_branch c vs hK r args nominal hn hd
  split <;> rename_i hi
  · exact int_branch c vs hK r args hd hi
  split <;> rename_i hb
  · exact bool_branch c vs hK r args hd hi hb
  split <;> rename_i hk
  · exact closure_branch c vs hK r args closure hc hd hi hb hk
  · exact nominal_branch c vs hK r args nominal hn hd hi hb hk

end Strata.Dyn.CoreTypesDenoteTest
