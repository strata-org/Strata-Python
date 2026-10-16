/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataMantleTest.DSLTest
public import StrataMantleTest.RegionTest
public import StrataMantle.Env.Refine
import StrataMantle.Env.WF
import StrataMantle.DSL
meta import StrataMantle.Build
-- `decide +kernel` unfolds the checker, the environment and core's array operations.
import all StrataMantle.WF
import all StrataMantle.Env
import all StrataMantle.Base
import all StrataMantle.Build
import all StrataMantle.KindedTypeArgs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq

set_option autoImplicit false

/-!
# Tests of type arguments checked by kind

`ta[…]` against the kinds of DSL-generated and hand-written signatures, `infer_type_args`, and
the error each mistake gives, beside the same arguments fixed.
-/

namespace Strata.Mantle.TypeArgsTest

open Strata.Mantle.DSLTest Strata.Mantle.RegionTest

/-! ## The kinds reduce -/

-- Base's instructions, at `Base.env` and at a child.
example : KindedTypeArgsFor (Base.refGet (e := Base.env)) none := ta[Base.Int]
example : KindedTypeArgsFor (Base.Except.ok (e := Fns.env)) none := ta[Base.String, Base.Int]
example : KindedTypeArgsFor (Base.Except.case (e := Fns.env)) none :=
  ta[Base.String, Base.Except.ty Base.Int.ty Base.Bool.ty]
-- A generic refinement.
example {e : Env Unit} [Demo.env ⊑ e] : KindedTypeArgsFor (Base.refNew (e := e)) none :=
  ta[Demo.Box.ty Demo.Value.ty]
-- List parameters: a literal, an empty one, and a `TypeList` term.
example : KindedTypeArgsFor (Fns.callFn (e := Fns.env)) none :=
  ta[[Base.Int, Base.Bool], Base.Int]
example : KindedTypeArgsFor (Fns.bindFirst (e := Fns.env)) none := ta[Base.Int, [], Base.Int]
example (l : TypeList Fns.env) : KindedTypeArgsFor (Fns.callLast (e := Fns.env)) none :=
  ta[l, Base.Int]
-- `ta[…]` is the chain of constructors.
example : (ta[[Base.Int], Base.Bool] : KindedTypeArgsFor (Fns.callFn (e := Fns.env)) none) =
    .list (.ofTypes #[Base.Int.ty]) (.ty Base.Bool.ty .nil) := rfl

/-! ### A hand-written signature -/

private def natName : Name := .str .base "Nat"
private def idName : Name := .str .base "id"
private def env₀ : Env Unit := Env.empty.addType { ann := (), name := natName } (by simp)
private def natRef : TypeRef env₀ 0 :=
  TypeRef.ofAddType Env.empty { ann := (), name := natName } (by simp)
private def natTy : TypeExpr env₀ := TypeExpr.app natRef #v[]
private def polyIdSig : InsnSig env₀ :=
  { ann := (), typeParams := #[⟨"a", .type⟩]
    argTypes := #[⟨"x", TypeExpr.var 0 (by decide)⟩]
    returnType := some (TypeExpr.var 0 (by decide)) }
/-- `id` is not yet declared in `env₀`. -/
private theorem idFresh : idName ∉ env₀ := by simp [env₀, natName, idName]
private def env₁ : Env Unit := env₀.addInsn idName polyIdSig idFresh
private def idRef := InsnRef.ofAddInsn env₀ idName polyIdSig idFresh
private def natTy₁ : TypeExpr env₁ := natTy.ofSubset (Env.subset_addInsn _ _ _ _)

example : KindedTypeArgsFor idRef none := ta[natTy₁]
example : KindedTypeArgsFor idRef (some natTy₁) := by infer_type_args

/-! ## Inference -/

-- The type parameter is the result.
example :
    (by infer_type_args : KindedTypeArgsFor (Base.refGet (e := Fns.env)) (some Base.Int.ty)) =
      ta[Base.Int] := rfl
-- Under a constructor, through an abbreviation-like definition.
private def exceptT : TypeExpr Fns.env := Base.Except.ty Base.String.ty Base.Int.ty
example :
    (by infer_type_args : KindedTypeArgsFor (Base.Except.ok (e := Fns.env)) (some exceptT)) =
      ta[Base.String, Base.Int] := rfl
-- A list parameter in the result.
example :
    KindedTypeArgsFor (Reg.«try» (e := Reg.env)) (some (Reg.Completion.ty Base.Int.ty)) := by
  infer_type_args

/-! ### A list literal in the result

The result's list is a literal, `[a]`, and the caller's may be built either way: `TypeList.lit`
or `TypeList.ofTypes`, which `ta[…]` builds. -/

/-- Instructions whose results take literal lists: of a type parameter, and splicing a list
parameter after one or before one. -/
private environment Lits extends FnAbbrevs where
  open fns base
  insn lit1 [a] (x : a) : Fn [a] a
  insn cons1 [a (as : list)] (x : a) : Fn [a, *as] a
  insn snoc1 [(as : list) a] (x : a) : Fn [*as, a] a

example : KindedTypeArgsFor (Lits.lit1 (e := Lits.env))
    (some (Fns.Fn.ty (.lit #[.ty Base.Int.ty]) Base.Int.ty)) := by infer_type_args
example : KindedTypeArgsFor (Lits.lit1 (e := Lits.env))
    (some (Fns.Fn.ty (.ofTypes #[Base.Int.ty]) Base.Int.ty)) := by infer_type_args
-- Both infer `a := Int`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.lit1 (e := Lits.env))
      (some (Fns.Fn.ty (.ofTypes #[Base.Int.ty]) Base.Int.ty))) = ta[Base.Int] := rfl
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.lit1 (e := Lits.env))
      (some (Fns.Fn.ty (.lit #[.ty Base.Int.ty]) Base.Int.ty))) = ta[Base.Int] := rfl

/-! ### A splice among other elements

A literal that splices a list parameter matches the caller's elements one by one at either end,
and the parameter binds the run between them. -/

-- After a type: `a := Int`, `as := [Bool]`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.cons1 (e := Lits.env))
      (some (Fns.Fn.ty (.ofTypes #[Base.Int.ty, Base.Bool.ty]) Base.Int.ty))) =
      ta[Base.Int, [Base.Bool]] := rfl
-- The run may be empty: `as := []`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.cons1 (e := Lits.env))
      (some (Fns.Fn.ty (.ofTypes #[Base.Int.ty]) Base.Int.ty))) = ta[Base.Int, []] := rfl
-- Before a type: `as := [Int, Bool]`, `a := Int`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.snoc1 (e := Lits.env))
      (some (Fns.Fn.ty (.lit #[.ty Base.Int.ty, .ty Base.Bool.ty, .ty Base.Int.ty])
        Base.Int.ty))) = ta[[Base.Int, Base.Bool], Base.Int] := rfl

-- Through an abbreviation, whose `n.ty` appends its list argument: `withInt [Bool] Int` is
-- `Fn [Bool, Int] Int`, so `as := [Bool]`, `a := Int`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.snoc1 (e := Lits.env))
      (some (FnAbbrevs.withInt.ty (.ofTypes #[Base.Bool.ty]) Base.Int.ty))) =
      ta[[Base.Bool], Base.Int] := rfl

-- Through `++`: `[Bool] ++ [Int]` is `[Bool, Int]`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.snoc1 (e := Lits.env))
      (some (Fns.Fn.ty (TypeList.ofTypes #[Base.Bool.ty] ++ TypeList.ofTypes #[Base.Int.ty])
        Base.Int.ty))) = ta[[Base.Bool], Base.Int] := rfl

-- In the middle, as the DSL writes it: `as := [Bool, Int]`.
example :
    (by infer_type_args : KindedTypeArgsFor (FnAbbrevs.wrap (e := Lits.env))
      (some (Fns.Fn.ty (.ofTypes #[Base.Int.ty, Base.Bool.ty, Base.Int.ty, Base.Bool.ty])
        Base.Int.ty))) = ta[[Base.Bool, Base.Int]] := rfl

/-- `cons1`'s literal has one element besides the splice, so the caller's needs one. -/
private def emptyFn : TypeExpr Lits.env := Fns.Fn.ty (.ofTypes #[]) Base.Int.ty

/--
error: cannot infer the type arguments of Lits.cons1: its result type
  Fns.Fn.ty (TypeList.lit #[TypeList.Elem.ty (TypeExpr.var 0 ⋯), TypeList.Elem.splice 1 ⋯]) (TypeExpr.var 0 ⋯)
does not match
  emptyFn
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor (Lits.cons1 (e := Lits.env)) (some emptyFn) := by infer_type_args

example : KindedTypeArgsFor (Lits.cons1 (e := Lits.env))
    (some (Fns.Fn.ty (.ofTypes #[Base.Int.ty]) Base.Int.ty)) := by infer_type_args

/-! ### Splices a hand-written signature writes

The DSL writes at most one splice in a literal.  A hand-written signature may write one in
the middle, carried into an extension, which is inferred, or two, which are not. -/

private def midName : Name := .str .base "mid"
private def twoName : Name := .str .base "two"

/-- `[(as : list)] : Fn [Int, *as, Bool] Int`. -/
private def midSig : InsnSig Lits.env :=
  { ann := (), typeParams := #[⟨"as", .list⟩], argTypes := #[]
    returnType := some (Fns.Fn.ty
      (.lit #[.ty Base.Int.ty, .splice 0 (by decide), .ty Base.Bool.ty]) Base.Int.ty) }
/-- `[(as : list) (bs : list)] : Fn [*as, *bs] Int`. -/
private def twoSig : InsnSig Lits.env :=
  { ann := (), typeParams := #[⟨"as", .list⟩, ⟨"bs", .list⟩], argTypes := #[]
    returnType := some (Fns.Fn.ty
      (.lit #[.splice 0 (by decide), .splice 1 (by decide)]) Base.Int.ty) }

private theorem midFresh : midName ∉ Lits.env := by rw [Lits.mem_env]; decide
private abbrev envMid : Env Unit := Lits.env.addInsn midName midSig midFresh
private def midRef := InsnRef.ofAddInsn Lits.env midName midSig midFresh
private instance : Lits.env ⊑ envMid := ⟨Env.le_of_subset (Env.subset_addInsn _ _ _ _)⟩

private theorem twoFresh : twoName ∉ Lits.env := by rw [Lits.mem_env]; decide
private abbrev envTwo : Env Unit := Lits.env.addInsn twoName twoSig twoFresh
private def twoRef := InsnRef.ofAddInsn Lits.env twoName twoSig twoFresh
private instance : Lits.env ⊑ envTwo := ⟨Env.le_of_subset (Env.subset_addInsn _ _ _ _)⟩

-- In the middle: `as := [Bool, Int]`.
example :
    (by infer_type_args : KindedTypeArgsFor midRef (some (Fns.Fn.ty (e := envMid)
      (.ofTypes #[Base.Int.ty, Base.Bool.ty, Base.Int.ty, Base.Bool.ty]) Base.Int.ty))) =
      ta[[Base.Bool, Base.Int]] := rfl

/--
error: cannot infer the type arguments of twoRef: it is ambiguous, with more than one splice in
  TypeList.lit #[TypeList.Elem.splice 0 ⋯, TypeList.Elem.splice 1 ⋯]
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor twoRef (some (Fns.Fn.ty (e := envTwo)
    (.ofTypes #[Base.Int.ty, Base.Bool.ty]) Base.Int.ty)) := by infer_type_args

example : KindedTypeArgsFor twoRef (some (Fns.Fn.ty (e := envTwo)
    (.ofTypes #[Base.Int.ty, Base.Bool.ty]) Base.Int.ty)) := ta[[Base.Int], [Base.Bool]]

/-! ### A datatype with a list parameter

Its constructor's list parameter is inferred from the datatype applied to a list. -/

example :
    (by infer_type_args : KindedTypeArgsFor (Clos.Closure.mk (e := Clos.env))
      (some (Clos.Closure.ty (.ofTypes #[Base.Int.ty]) Base.Int.ty))) =
      ta[[Base.Int], Base.Int] := rfl

/-! ## Errors

Each rejection is followed by the same arguments fixed. -/

/-- error: type argument 1 of Clos.Closure.mk is a type, but its parameter takes a list of types -/
#guard_msgs in
example : KindedTypeArgsFor (Clos.Closure.mk (e := Clos.env)) none := ta[Base.Int, Base.Int]

example : KindedTypeArgsFor (Clos.Closure.mk (e := Clos.env)) none := ta[[Base.Int], Base.Int]

/-- error: type argument 1 of Base.refGet is a list of types, but its parameter takes a type -/
#guard_msgs in
example : KindedTypeArgsFor (Base.refGet (e := Fns.env)) none := ta[[Base.Int]]

example : KindedTypeArgsFor (Base.refGet (e := Fns.env)) none := ta[Base.Int]

/-- error: type argument 1 of Base.refGet is a list of types, but its parameter takes a type -/
#guard_msgs in
example (l : TypeList Fns.env) : KindedTypeArgsFor (Base.refGet (e := Fns.env)) none := ta[l]

example (t : TypeExpr Fns.env) : KindedTypeArgsFor (Base.refGet (e := Fns.env)) none := ta[t]

/-- error: type argument 1 of Fns.callFn is a type, but its parameter takes a list of types -/
#guard_msgs in
example : KindedTypeArgsFor (Fns.callFn (e := Fns.env)) none := ta[Base.Int, Base.Int]

example : KindedTypeArgsFor (Fns.callFn (e := Fns.env)) none := ta[[Base.Int], Base.Int]

/-- error: Base.refGet takes 1 type argument(s), [a type], but 2 are given -/
#guard_msgs in
example : KindedTypeArgsFor (Base.refGet (e := Fns.env)) none := ta[Base.Int, Base.Int]

example : KindedTypeArgsFor (Base.refGet (e := Fns.env)) none := ta[Base.Int]

/-- error: Unknown identifier `Base.Nope` -/
#guard_msgs in
example : KindedTypeArgsFor (Base.refGet (e := Fns.env)) none := ta[Base.Nope]

example : KindedTypeArgsFor (Base.refGet (e := Fns.env)) none := ta[Base.Bool]

/--
error: cannot infer type argument(s) `a` of Base.refSet: they do not occur in its result type
  Base.Unit.ty
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor (Base.refSet (e := Fns.env)) (some Base.Unit.ty) := by infer_type_args

example : KindedTypeArgsFor (Base.refSet (e := Fns.env)) (some Base.Unit.ty) := ta[Base.Int]

/--
error: cannot infer type argument(s) `as` of Fns.callFn: they do not occur in its result type
  TypeExpr.var 1 ⋯
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor (Fns.callFn (e := Fns.env)) (some Base.Int.ty) := by infer_type_args

example : KindedTypeArgsFor (Fns.callFn (e := Fns.env)) (some Base.Int.ty) :=
  ta[[Base.Bool], Base.Int]

/--
error: cannot infer the type arguments of Base.Except.case: it is terminal, with no result type to infer them from; pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor (Base.Except.case (e := Fns.env)) none := by infer_type_args

example : KindedTypeArgsFor (Base.Except.case (e := Fns.env)) none :=
  ta[Base.String, Base.Int]

/--
error: cannot infer the type arguments of Base.refNew: its result type
  Base.Ref.ty (TypeExpr.var 0 ⋯)
does not match
  Base.Int.ty
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor (Base.refNew (e := Fns.env)) (some Base.Int.ty) := by infer_type_args

example : KindedTypeArgsFor (Base.refNew (e := Fns.env)) (some (Base.Ref.ty Base.Int.ty)) := by
  infer_type_args

/--
error: cannot infer the type arguments of Base.refNew: its result type
  Base.Ref.ty (TypeExpr.var 0 ⋯)
does not match
  t
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example (t : TypeExpr Fns.env) : KindedTypeArgsFor (Base.refNew (e := Fns.env)) (some t) := by
  infer_type_args

example (t : TypeExpr Fns.env) : KindedTypeArgsFor (Base.refNew (e := Fns.env)) (some t) :=
  ta[Base.Int]

/-! ### At a builder call -/

open Build in
/--
error: could not synthesize default value for parameter 'typeArgs' using tactics
---
error: cannot infer type argument(s) `a` of Base.refSet: they do not occur in its result type
  Base.Unit.ty
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example (c v : ValId) : BuildM Fns.env Unit ValId :=
  emitApply (.str .base "u") Base.Unit.ty Base.refSet #[c, v]

open Build in
/-- error: type argument 1 of Base.refSet is a list of types, but its parameter takes a type -/
#guard_msgs in
example (c v : ValId) : BuildM Fns.env Unit ValId :=
  emitApply (.str .base "u") Base.Unit.ty Base.refSet #[c, v] (typeArgs := ta[[Base.Int]])

open Build in
example (c v : ValId) : BuildM Fns.env Unit ValId :=
  emitApply (.str .base "u") Base.Unit.ty Base.refSet #[c, v] (typeArgs := ta[Base.Int])

end Strata.Mantle.TypeArgsTest

/-! ## Scoping

Outside `Strata.Mantle`, `ta[` is not a token, so `ta[i]` indexes a variable named `ta`, and
the builder's default still infers. -/

namespace TypeArgsScopeTest

#guard (fun (ta : Array Nat) => ta[0]?) #[7] == some 7

example (c : Strata.Mantle.ValId) :
    Strata.Mantle.BuildM Strata.Mantle.DSLTest.Fns.env Unit Strata.Mantle.ValId :=
  Strata.Mantle.Build.emitApply (.str .base "v") Strata.Mantle.Base.Int.ty
    Strata.Mantle.Base.refGet #[c]

end TypeArgsScopeTest
