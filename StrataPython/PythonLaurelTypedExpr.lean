/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import StrataPython.UnknownSource

/-!
# Typed Laurel Expression Builders for the Python Prelude

Type-safe wrappers around the Python Laurel prelude's runtime functions
(`from_int`, `Any..as_string!`, `DictStrAny_contains`, etc.).  These
enforce correct `HighType` at construction time so that type mismatches
are caught by the Lean type checker rather than surfacing as confusing
errors later in the Laurel or Core pipeline.

The wrapped functions correspond to declarations in
`PythonRuntimeLaurelPart.lean` and `PythonLaurelCorePrelude.lean`.
-/

public section
namespace StrataPython.Laurel

open Strata (FileRange)
open Strata.Laurel (HighType HighTypeMd StmtExpr StmtExprMd mkId Parameter QuantifierMode)

abbrev tyAny : HighType := .UserDefined "Any"

/--
A Laurel `StmtExprMd` tagged with its `HighType`.

The benefit is that composition of typed expressions is checked by the Lean type
system, catching mismatches like passing an `Int` where a `Bool` is expected.

The type parameter is not statically enforced; correctness depends on the helper
functions in this namespace producing the right type tag.  After a translation
error is reported, helpers may return a mistyped expression to allow continued
translation and further error collection.
-/
structure TypedStmtExpr (tp : HighType) where
  stmt : StmtExprMd

namespace TypedStmtExpr

def ofStmt {tp} (s : StmtExpr) (source : FileRange := unknownSource) : TypedStmtExpr tp :=
  { stmt := { val := s, source := source } }

def identifier (v : String) (tp : HighType)
    (source : FileRange := unknownSource) : TypedStmtExpr tp :=
  .ofStmt (.Var (.Local (mkId v))) source

def literalBool (v : Bool)
    (source : FileRange := unknownSource) : TypedStmtExpr .TBool :=
  .ofStmt (.LiteralBool v) source

def literalInt (v : Int)
    (source : FileRange := unknownSource) : TypedStmtExpr .TInt :=
  .ofStmt (.LiteralInt v) source

def literalString (v : String)
    (source : FileRange := unknownSource) : TypedStmtExpr .TString :=
  .ofStmt (.LiteralString v) source

def stringEq (x y : TypedStmtExpr .TString)
    (source : FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Eq [x.stmt, y.stmt]) source

def intGeq (x y : TypedStmtExpr .TInt)
    (source : FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Geq [x.stmt, y.stmt]) source

def intLeq (x y : TypedStmtExpr .TInt)
    (source : FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Leq [x.stmt, y.stmt]) source

def realGeq (x y : TypedStmtExpr .TReal)
    (source : FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Geq [x.stmt, y.stmt]) source

def realLeq (x y : TypedStmtExpr .TReal)
    (source : FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Leq [x.stmt, y.stmt]) source

def not (x : TypedStmtExpr .TBool)
    (source : FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Not [x.stmt]) source

def implies (x y : TypedStmtExpr .TBool)
    (source : FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Implies [x.stmt, y.stmt]) source

def or (x y : TypedStmtExpr .TBool)
    (source : FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .Or [x.stmt, y.stmt]) source

def and (x y : TypedStmtExpr .TBool)
    (source : FileRange := x.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.PrimitiveOp .And [x.stmt, y.stmt]) source

abbrev tyDictStrAny : HighType := .UserDefined "DictStrAny"

def anyIsfromNone (v : TypedStmtExpr tyAny)
    (source : FileRange := v.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.StaticCall (mkId "Any..isfrom_None") [v.stmt]) source

def anyToBool (v : TypedStmtExpr tyAny)
    (source : FileRange := v.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.StaticCall (mkId "Any_to_bool") [v.stmt]) source

def fromInt (v : TypedStmtExpr .TInt)
    (source : FileRange := v.stmt.source) : TypedStmtExpr tyAny :=
  .ofStmt (.StaticCall (mkId "from_int") [v.stmt]) source

def fromBool (v : TypedStmtExpr .TBool)
    (source : FileRange := v.stmt.source) : TypedStmtExpr tyAny :=
  .ofStmt (.StaticCall (mkId "from_bool") [v.stmt]) source

def fromNone (source : FileRange := unknownSource) : TypedStmtExpr tyAny :=
  .ofStmt (.StaticCall (mkId "from_None") []) source

def anyAsInt (a : TypedStmtExpr tyAny)
    (source : FileRange := a.stmt.source) : TypedStmtExpr .TInt :=
  .ofStmt (.StaticCall (mkId "Any..as_int!") [a.stmt]) source

def fromStr (v : TypedStmtExpr .TString)
    (source : FileRange := unknownSource) : TypedStmtExpr tyAny :=
  .ofStmt (.StaticCall (mkId "from_str") [v.stmt]) source

def anyAsString (a : TypedStmtExpr tyAny)
    (source : FileRange := a.stmt.source) : TypedStmtExpr .TString :=
  .ofStmt (.StaticCall (mkId "Any..as_string!") [a.stmt]) source

def anyAsFloat (a : TypedStmtExpr tyAny)
    (source : FileRange := a.stmt.source) : TypedStmtExpr .TReal :=
  .ofStmt (.StaticCall (mkId "Any..as_float!") [a.stmt]) source

def anyAsDict (a : TypedStmtExpr tyAny)
    (source : FileRange := a.stmt.source) : TypedStmtExpr tyDictStrAny :=
  .ofStmt (.StaticCall (mkId "Any..as_Dict!") [a.stmt]) source

def dictStrAnyContains (d : TypedStmtExpr tyDictStrAny) (k : TypedStmtExpr .TString)
    (source : FileRange := d.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.StaticCall (mkId "DictStrAny_contains") [d.stmt, k.stmt]) source

def anyGet (a i : TypedStmtExpr tyAny)
    (source : FileRange := unknownSource) : TypedStmtExpr tyAny :=
  .ofStmt (.StaticCall (mkId "Any_get") [a.stmt, i.stmt]) source

abbrev tyListAny : HighType := .UserDefined "ListAny"

def anyAsList (a : TypedStmtExpr tyAny)
    (source : FileRange := a.stmt.source) : TypedStmtExpr tyListAny :=
  .ofStmt (.StaticCall (mkId "Any..as_ListAny!") [a.stmt]) source

-- Membership `x ∈ l`; also serves as the trigger for list universals.
def listContains (l : TypedStmtExpr tyListAny) (x : TypedStmtExpr tyAny)
    (source : FileRange := l.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.StaticCall (mkId "List_contains") [l.stmt, x.stmt]) source

-- `d[k]` lookup on a `DictStrAny` (total under the dict quantifier's contains guard).
def dictStrAnyGet (d : TypedStmtExpr tyDictStrAny) (k : TypedStmtExpr .TString)
    (source : FileRange := d.stmt.source) : TypedStmtExpr tyAny :=
  .ofStmt (.StaticCall (mkId "DictStrAny_get") [d.stmt, k.stmt]) source

-- Total `d[k]` lookup returning `None` on a missing key. Unlike the underlying
-- Laurel prelude function `DictStrAny_get` (wrapped by `dictStrAnyGet` above),
-- this carries no `requires`, so Laurel's transparency pass keeps it a pure
-- function usable inside quantifier/contract bodies (a `requires`-bearing helper
-- gets a procedural twin and is rejected as an imperative call in pure contexts).
-- Under the dict quantifier's `contains` guard the two agree, so this is the
-- form the `.values()`/`.items()` value binder inlines.
def dictStrAnyGetOrNone (d : TypedStmtExpr tyDictStrAny) (k : TypedStmtExpr .TString)
    (source : FileRange := d.stmt.source) : TypedStmtExpr tyAny :=
  .ofStmt (.StaticCall (mkId "DictStrAny_get_or_none") [d.stmt, k.stmt]) source

-- Universal over `param` with an SMT `trigger`. Nest to bind several variables,
-- placing the trigger on the innermost so all bound variables are in scope.
def forallTrigger (param : Parameter) (trigger : StmtExprMd)
    (body : TypedStmtExpr .TBool)
    (source : FileRange := body.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.Quantifier QuantifierMode.Forall param (some trigger) body.stmt) source

-- Existential over `param` with an SMT `trigger`.
def existsTrigger (param : Parameter) (trigger : StmtExprMd)
    (body : TypedStmtExpr .TBool)
    (source : FileRange := body.stmt.source) : TypedStmtExpr .TBool :=
  .ofStmt (.Quantifier QuantifierMode.Exists param (some trigger) body.stmt) source

def strLength (a : TypedStmtExpr .TString)
    (source : FileRange := a.stmt.source) : TypedStmtExpr .TInt :=
  .ofStmt (.StaticCall (mkId "Str.Length") [a.stmt]) source

def reSearchBool (pattern s : TypedStmtExpr .TString)
    (source : FileRange := unknownSource) : TypedStmtExpr .TBool :=
  .ofStmt (.StaticCall (mkId "re_search_bool") [pattern.stmt, s.stmt]) source

end TypedStmtExpr

/--
A dependent pair that bundles a `HighType` and a `TypedStmtExpr` of that type.

This is used when the type is not statically known and must be checked at
runtime.
-/
abbrev SomeTypedStmtExpr := Σ(tp : HighType), TypedStmtExpr tp

namespace SomeTypedStmtExpr

def mkSome {tp} (e : TypedStmtExpr tp) : SomeTypedStmtExpr := ⟨tp, e⟩

instance : Inhabited SomeTypedStmtExpr where
  default :=
    let holeType : HighTypeMd := { val := tyAny, source := unknownSource }
    let stmt : StmtExprMd := { val := .Hole true (.some holeType), source := unknownSource }
    .mk tyAny { stmt := stmt }

end SomeTypedStmtExpr

end StrataPython.Laurel
end
