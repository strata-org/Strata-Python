/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.DataProps
public import StrataMantle.Env.TypeExprRawProps
import all StrataMantle.Util.Array

set_option autoImplicit false

/-! # Kernel reduction of the array helpers and the type language

Checks that `decide` evaluates the array helpers, parameter names, and `TypeExpr.Raw`
equality, instantiation and folding. -/

namespace Strata.Mantle.DataTest

open Strata.Mantle

def py (s : String) : Name := .str (.str .base "py") s

/-! Distinctness and checks over arrays of names. -/

example : #[py "a", py "b", py "c"].Nodup := by decide
example : ¬ #[py "a", py "b", py "a"].Nodup := by decide
example : #[py "a", py "b"].allK (fun n => decide (n ∉ [py "c"])) = true := by decide
example : (#[1, 2, 3].mapK (· + 1)).Nodup := by decide

/-! `mapK` and `allK` agree with the library functions. -/

example : #[1, 2, 3].mapK (· * 2) = #[1, 2, 3].map (· * 2) := Array.mapK_eq_map
example : #[1, 2, 3].allK (· > 0) = #[1, 2, 3].all (· > 0) := Array.allK_eq_all

/-! Parameter names of declarations. -/

example : (⟨"x", 0⟩ : Param Nat) ≠ ⟨"y", 0⟩ := by decide
example : (⟨"x", .pos⟩ : Param Positivity) = ⟨"x", .pos⟩ := by decide

example : ({ ann := (), name := py "dict", params := #[⟨"k", .non⟩, ⟨"v", .pos⟩] } :
    TypeDecl Unit).paramNames.Nodup := by decide
example : ¬ ({ ann := (), name := py "pair", params := #[⟨"a", .pos⟩, ⟨"a", .pos⟩] } :
    TypeDecl Unit).paramNames.Nodup := by decide
example : ({ ann := (), name := py "opt", params := #[⟨"a", .pos⟩], ctors := #[] } :
    DatatypeDecl Unit TypeExpr.Raw).paramNames = ["a"] := by decide

/-! Equality, instantiation and folding on type expressions. -/

def list (e : TypeExpr.Raw) : TypeExpr.Raw := .app (py "list") #[e]
def int : TypeExpr.Raw := .app (py "int") #[]

example : list (.var 0) ≠ list int := by decide
example : list int = list int := by decide
example : (list (.var 0)).instantiate #[int] = list int := by decide
example : (list (.var 1)).instantiate #[int] = list (.var 1) := by decide
example : (list int).fold (fun _ => 0) (fun _ as => as.foldl (· + ·) 1) = 2 := by decide

end Strata.Mantle.DataTest
