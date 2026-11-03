/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataDyn.Build
public import StrataDynTest.DSLTest
public import StrataDynTest.RegionTest
public import StrataDyn.Env.Handle
import StrataDyn.Env.WF
import StrataDyn.DSL
meta import StrataDyn.Build
-- `decide +kernel` unfolds the checker, the environment and core's array operations.
import all StrataDyn.WF
import all StrataDyn.Env
import all StrataDyn.Base
import all StrataDyn.Build
import all StrataDyn.KindedTypeArgs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq

set_option autoImplicit false

/-!
# Tests of type arguments checked by kind

`ta[…]` against the kinds of DSL-generated and hand-written signatures, `infer_type_args`, and
the error each mistake gives, beside the same arguments fixed.
-/

namespace Strata.Dyn.TypeArgsTest

open Strata.Dyn.DSLTest Strata.Dyn.RegionTest

/-! ## The kinds reduce -/

-- Base's instructions, at `Base.env` and at a child.
example : KindedTypeArgsFor (Base.refGet.ref (e := Base.env)) none := ta[Base.Int]
example : KindedTypeArgsFor (Base.Except.ok.ref (e := Fns.env)) none := ta[Base.String, Base.Int]
example : KindedTypeArgsFor (Base.Except.case.ref (e := Fns.env)) none :=
  ta[Base.String, Base.Except Base.Int Base.Bool]
-- A generic refinement.
example {e : Env Unit} [Demo.env ≼ e] : KindedTypeArgsFor (Base.refNew.ref (e := e)) none :=
  ta[Demo.Box Demo.Value]
-- List parameters: a literal, an empty one, and a `TypeList` term.
example : KindedTypeArgsFor (Fns.callFn.ref (e := Fns.env)) none :=
  ta[[Base.Int, Base.Bool], Base.Int]
example : KindedTypeArgsFor (Fns.bindFirst.ref (e := Fns.env)) none := ta[Base.Int, [], Base.Int]
example (l : TypeList Fns.env) : KindedTypeArgsFor (Fns.callLast.ref (e := Fns.env)) none :=
  ta[l, Base.Int]
-- `ta[…]` is the chain of constructors.
example : (ta[[Base.Int], Base.Bool] : KindedTypeArgsFor (Fns.callFn.ref (e := Fns.env)) none) =
    .list (.lit #[.ty Base.Int]) (.ty Base.Bool .nil) := rfl

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
    (by infer_type_args : KindedTypeArgsFor (Base.refGet.ref (e := Fns.env)) (some Base.Int)) =
      ta[Base.Int] := rfl
-- Under a constructor, through an abbreviation-like definition.
private def exceptT : TypeExpr Fns.env := Base.Except Base.String Base.Int
example :
    (by infer_type_args : KindedTypeArgsFor (Base.Except.ok.ref (e := Fns.env)) (some exceptT)) =
      ta[Base.String, Base.Int] := rfl
-- A list parameter in the result.
example :
    KindedTypeArgsFor (Reg.«try».ref (e := Reg.env)) (some (Reg.Completion Base.Int)) := by
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

example : KindedTypeArgsFor (Lits.lit1.ref (e := Lits.env))
    (some (Base.Fn [Base.Int] Base.Int)) := by infer_type_args
example : KindedTypeArgsFor (Lits.lit1.ref (e := Lits.env))
    (some (Base.Fn (TypeList.ofTypes #[Base.Int]) Base.Int)) := by infer_type_args
-- Both infer `a := Int`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.lit1.ref (e := Lits.env))
      (some (Base.Fn [Base.Int] Base.Int))) = ta[Base.Int] := rfl
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.lit1.ref (e := Lits.env))
      (some (Base.Fn (TypeList.ofTypes #[Base.Int]) Base.Int))) = ta[Base.Int] := rfl

/-! ### A splice among other elements

A literal that splices a list parameter matches the caller's elements one by one at either end,
and the parameter binds the run between them. -/

-- After a type: `a := Int`, `as := [Bool]`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.cons1.ref (e := Lits.env))
      (some (Base.Fn [Base.Int, Base.Bool] Base.Int))) =
      ta[Base.Int, [Base.Bool]] := rfl
-- The run may be empty: `as := []`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.cons1.ref (e := Lits.env))
      (some (Base.Fn [Base.Int] Base.Int))) = ta[Base.Int, []] := rfl
-- Before a type: `as := [Int, Bool]`, `a := Int`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.snoc1.ref (e := Lits.env))
      (some (Base.Fn [Base.Int, Base.Bool, Base.Int]
        Base.Int))) = ta[[Base.Int, Base.Bool], Base.Int] := rfl

-- Through an abbreviation, whose handle splices a list argument into one literal and appends a
-- `TypeList`: `withInt [Bool] Int` is `Fn [Bool, Int] Int`, so `as := [Bool]`, `a := Int`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.snoc1.ref (e := Lits.env))
      (some (FnAbbrevs.withInt [Base.Bool] Base.Int))) =
      ta[[Base.Bool], Base.Int] := rfl
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.snoc1.ref (e := Lits.env))
      (some (FnAbbrevs.withInt (TypeList.ofTypes #[Base.Bool]) Base.Int))) =
      ta[[Base.Bool], Base.Int] := rfl

-- Through `++`: `[Bool] ++ [Int]` is `[Bool, Int]`.
example :
    (by infer_type_args : KindedTypeArgsFor (Lits.snoc1.ref (e := Lits.env))
      (some (Base.Fn (TypeList.ofTypes #[Base.Bool] ++ TypeList.ofTypes #[Base.Int])
        Base.Int))) = ta[[Base.Bool], Base.Int] := rfl

-- In the middle, as the DSL writes it: `as := [Bool, Int]`.
example :
    (by infer_type_args : KindedTypeArgsFor (FnAbbrevs.wrap.ref (e := Lits.env))
      (some (Base.Fn [Base.Int, Base.Bool, Base.Int, Base.Bool]
        Base.Int))) = ta[[Base.Bool, Base.Int]] := rfl

/-- `cons1`'s literal has one element besides the splice, so the caller's needs one. -/
private def emptyFn : TypeExpr Lits.env := Base.Fn [] Base.Int

/--
error: cannot infer the type arguments of Lits.cons1.ref: its result type
  Base.Internal.Fn.ty (TypeList.lit #[TypeList.Elem.ty (TypeExpr.var 0 ⋯), TypeList.Elem.splice 1 ⋯]) (TypeExpr.var 0 ⋯)
does not match
  emptyFn
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor (Lits.cons1.ref (e := Lits.env)) (some emptyFn) := by infer_type_args

example : KindedTypeArgsFor (Lits.cons1.ref (e := Lits.env))
    (some (Base.Fn [Base.Int] Base.Int)) := by infer_type_args

/-! ### Splices a hand-written signature writes

The DSL writes at most one splice in a literal.  A hand-written signature may write one in
the middle, carried into an extension, which is inferred, or two, which are not. -/

private def midName : Name := .str .base "mid"
private def twoName : Name := .str .base "two"

/-- `[(as : list)] : Fn [Int, *as, Bool] Int`. -/
private def midSig : InsnSig Lits.env :=
  { ann := (), typeParams := #[⟨"as", .list⟩], argTypes := #[]
    returnType := some (Base.Fn
      (TypeList.lit #[.ty Base.Int, .splice 0 (by decide), .ty Base.Bool]) Base.Int) }
/-- `[(as : list) (bs : list)] : Fn [*as, *bs] Int`. -/
private def twoSig : InsnSig Lits.env :=
  { ann := (), typeParams := #[⟨"as", .list⟩, ⟨"bs", .list⟩], argTypes := #[]
    returnType := some (Base.Fn
      (TypeList.lit #[.splice 0 (by decide), .splice 1 (by decide)]) Base.Int) }

private theorem midFresh : midName ∉ Lits.env := by rw [Lits.mem_env]; decide
private abbrev envMid : Env Unit := Lits.env.addInsn midName midSig midFresh
private def midRef := InsnRef.ofAddInsn Lits.env midName midSig midFresh
private instance : Lits.env ≼ envMid := ⟨Env.le_of_subset (Env.subset_addInsn _ _ _ _)⟩

private theorem twoFresh : twoName ∉ Lits.env := by rw [Lits.mem_env]; decide
private abbrev envTwo : Env Unit := Lits.env.addInsn twoName twoSig twoFresh
private def twoRef := InsnRef.ofAddInsn Lits.env twoName twoSig twoFresh
private instance : Lits.env ≼ envTwo := ⟨Env.le_of_subset (Env.subset_addInsn _ _ _ _)⟩

-- In the middle: `as := [Bool, Int]`.
example :
    (by infer_type_args : KindedTypeArgsFor midRef (some (Base.Fn (e := envMid)
      [Base.Int, Base.Bool, Base.Int, Base.Bool] Base.Int))) =
      ta[[Base.Bool, Base.Int]] := rfl

/--
error: cannot infer the type arguments of twoRef: it is ambiguous, with more than one splice in
  TypeList.lit #[TypeList.Elem.splice 0 ⋯, TypeList.Elem.splice 1 ⋯]
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor twoRef (some (Base.Fn (e := envTwo)
    [Base.Int, Base.Bool] Base.Int)) := by infer_type_args

example : KindedTypeArgsFor twoRef (some (Base.Fn (e := envTwo)
    [Base.Int, Base.Bool] Base.Int)) := ta[[Base.Int], [Base.Bool]]

/-! ### A datatype with a list parameter

Its constructor's list parameter is inferred from the datatype applied to a list. -/

example :
    (by infer_type_args : KindedTypeArgsFor (Clos.Closure.mk.ref (e := Clos.env))
      (some (Clos.Closure [Base.Int] Base.Int))) =
      ta[[Base.Int], Base.Int] := rfl

/-! ## Errors

Each rejection is followed by the same arguments fixed. -/

/-- error: type argument 1 of Clos.Closure.mk.ref is a type, but its parameter takes a list of types -/
#guard_msgs in
example : KindedTypeArgsFor (Clos.Closure.mk.ref (e := Clos.env)) none := ta[Base.Int, Base.Int]

example : KindedTypeArgsFor (Clos.Closure.mk.ref (e := Clos.env)) none := ta[[Base.Int], Base.Int]

/-- error: type argument 1 of Base.refGet.ref is a list of types, but its parameter takes a type -/
#guard_msgs in
example : KindedTypeArgsFor (Base.refGet.ref (e := Fns.env)) none := ta[[Base.Int]]

example : KindedTypeArgsFor (Base.refGet.ref (e := Fns.env)) none := ta[Base.Int]

/-- error: type argument 1 of Base.refGet.ref is a list of types, but its parameter takes a type -/
#guard_msgs in
example (l : TypeList Fns.env) : KindedTypeArgsFor (Base.refGet.ref (e := Fns.env)) none := ta[l]

example (t : TypeExpr Fns.env) : KindedTypeArgsFor (Base.refGet.ref (e := Fns.env)) none := ta[t]

/-- error: type argument 1 of Fns.callFn.ref is a type, but its parameter takes a list of types -/
#guard_msgs in
example : KindedTypeArgsFor (Fns.callFn.ref (e := Fns.env)) none := ta[Base.Int, Base.Int]

example : KindedTypeArgsFor (Fns.callFn.ref (e := Fns.env)) none := ta[[Base.Int], Base.Int]

/-- error: Base.refGet.ref takes 1 type argument(s), [a type], but 2 are given -/
#guard_msgs in
example : KindedTypeArgsFor (Base.refGet.ref (e := Fns.env)) none := ta[Base.Int, Base.Int]

example : KindedTypeArgsFor (Base.refGet.ref (e := Fns.env)) none := ta[Base.Int]

/-- error: Unknown identifier `Base.Nope` -/
#guard_msgs in
example : KindedTypeArgsFor (Base.refGet.ref (e := Fns.env)) none := ta[Base.Nope]

example : KindedTypeArgsFor (Base.refGet.ref (e := Fns.env)) none := ta[Base.Bool]

/--
error: cannot infer type argument(s) `a` of Base.refSet.ref: they do not occur in its result type
  Base.Internal.Unit.ty
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor (Base.refSet.ref (e := Fns.env)) (some Base.Unit) := by infer_type_args

example : KindedTypeArgsFor (Base.refSet.ref (e := Fns.env)) (some Base.Unit) := ta[Base.Int]

/--
error: cannot infer type argument(s) `as` of Fns.callFn.ref: they do not occur in its result type
  TypeExpr.var 1 ⋯
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor (Fns.callFn.ref (e := Fns.env)) (some Base.Int) := by infer_type_args

example : KindedTypeArgsFor (Fns.callFn.ref (e := Fns.env)) (some Base.Int) :=
  ta[[Base.Bool], Base.Int]

/--
error: cannot infer the type arguments of Base.Except.case.ref: it is terminal, with no result type to infer them from; pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor (Base.Except.case.ref (e := Fns.env)) none := by infer_type_args

example : KindedTypeArgsFor (Base.Except.case.ref (e := Fns.env)) none :=
  ta[Base.String, Base.Int]

/--
error: cannot infer the type arguments of Base.refNew.ref: its result type
  Base.Internal.Ref.ty (TypeExpr.var 0 ⋯)
does not match
  Base.Int
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example : KindedTypeArgsFor (Base.refNew.ref (e := Fns.env)) (some Base.Int) := by infer_type_args

example : KindedTypeArgsFor (Base.refNew.ref (e := Fns.env)) (some (Base.Ref Base.Int)) := by
  infer_type_args

/--
error: cannot infer the type arguments of Base.refNew.ref: its result type
  Base.Internal.Ref.ty (TypeExpr.var 0 ⋯)
does not match
  t
pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example (t : TypeExpr Fns.env) : KindedTypeArgsFor (Base.refNew.ref (e := Fns.env)) (some t) := by
  infer_type_args

example (t : TypeExpr Fns.env) : KindedTypeArgsFor (Base.refNew.ref (e := Fns.env)) (some t) :=
  ta[Base.Int]

/-! ### At a builder call -/

/- At a builder call, an argument that does not occur in the result type is left to the builder,
which infers it from the operands' types when it runs (`InferTest`). -/
open Build in
example (c v : ValId) : BuildM Fns.env Unit ValId :=
  emitApply (.str .base "u") Base.Unit Base.refSet.ref #[c, v]

open Build in
example (c v : ValId) : BuildM Fns.env Unit ValId :=
  emitApply (.str .base "u") Base.Unit Base.refSet.ref #[c, v] (typeArgs := .infer)

open Build in
/-- error: type argument 1 of Base.refSet.ref is a list of types, but its parameter takes a type -/
#guard_msgs in
example (c v : ValId) : BuildM Fns.env Unit ValId :=
  emitApply (.str .base "u") Base.Unit Base.refSet.ref #[c, v] (typeArgs := ta[[Base.Int]])

open Build in
example (c v : ValId) : BuildM Fns.env Unit ValId :=
  emitApply (.str .base "u") Base.Unit Base.refSet.ref #[c, v] (typeArgs := ta[Base.Int])

end Strata.Dyn.TypeArgsTest

/-! ## Scoping

Outside `Strata.Dyn`, `ta[` is not a token, so `ta[i]` indexes a variable named `ta`, and
the builder's default still infers. -/

namespace TypeArgsScopeTest

#guard (fun (ta : Array Nat) => ta[0]?) #[7] == some 7

example (c : Strata.Dyn.ValId) :
    Strata.Dyn.BuildM Strata.Dyn.DSLTest.Fns.env Unit Strata.Dyn.ValId :=
  Strata.Dyn.Build.emitApply (.str .base "v") Strata.Dyn.Base.Int
    Strata.Dyn.Base.refGet.ref #[c]

end TypeArgsScopeTest
