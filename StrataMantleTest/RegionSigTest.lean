/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.WF
public import StrataMantle.Env
-- Also imported as `meta` so the definitions below are available to the
-- interpreter: `native_decide` needs compiled code for `checkFrom` and `addInsns?`.
meta import StrataMantle.Env.WF
meta import StrataMantle.Env

set_option autoImplicit false

/-! # Region signatures

An instruction may declare the regions it takes: for each, the types of the region's
arguments and the type `ret` leaves it with.  These are checked as the instruction's own
argument types are, under its type variables.  The examples are an `if` whose branches
return the instruction's result, and a `try` whose body and handler return a completion.
-/

namespace Strata.Mantle.RegionSigTest

public section

private def boolName : Name := .str .base "Bool"
private def excName : Name := .str .base "Exc"
private def complName : Name := .str .base "Completion"
private def ifName : Name := .str .base "if"
private def tryName : Name := .str .base "try"

/-! ## Unchecked -/

namespace RawExample

open Env.Raw

private def boolDecl : Decl.Raw Unit := .type { ann := (), name := boolName }
private def excDecl : Decl.Raw Unit := .type { ann := (), name := excName }
/-- `Completion : Type → Type`. -/
private def complDecl : Decl.Raw Unit :=
  .type { ann := (), name := complName, params := #[⟨"a", .pos⟩] }

/-- `if {a} (cond : Bool) [then : () -> a] [else : () -> a] : a`. -/
private def ifDecl : Decl.Raw Unit := .insn
  { ann := (), name := ifName, typeParams := #["a"]
    argTypes := #[⟨"cond", .app boolName #[]⟩]
    returnType := some (.var 0)
    regions := #[⟨"then", { params := #[], returnType := .var 0 }⟩,
                 ⟨"else", { params := #[], returnType := .var 0 }⟩] }

/-- `try {a} [body : () -> Completion a] [handler : (exc : Exc) -> Completion a]
    : Completion a`. -/
private def tryDecl : Decl.Raw Unit := .insn
  { ann := (), name := tryName, typeParams := #["a"]
    argTypes := #[]
    returnType := some (.app complName #[.var 0])
    regions := #[⟨"body", { params := #[], returnType := .app complName #[.var 0] }⟩,
                 ⟨"handler", { params := #[⟨"exc", .app excName #[]⟩]
                               returnType := .app complName #[.var 0] }⟩] }

private def goodDecls : Array (Decl.Raw Unit) := #[boolDecl, excDecl, complDecl, ifDecl, tryDecl]
private theorem goodDistinct : DistinctDecls goodDecls := by decide

/-- Both are accepted. -/
example : (ofAscArray goodDecls goodDistinct).WF := wf_ofAscArray _ _ (by native_decide)

/-- An `if` whose `then` region takes a parameter of type `b`, which it does not bind: the
region's types are under the instruction's one type variable, so level `1` is out of scope. -/
private def illScoped (regionParam : TypeExpr.Raw) : Decl.Raw Unit := .insn
  { ann := (), name := ifName, typeParams := #["a"]
    argTypes := #[⟨"cond", .app boolName #[]⟩]
    returnType := some (.var 0)
    regions := #[⟨"then", { params := #[⟨"x", regionParam⟩], returnType := .var 0 }⟩] }

private def badDecls : Array (Decl.Raw Unit) := #[boolDecl, illScoped (.var 1)]
private theorem badDistinct : DistinctDecls badDecls := by decide

/-- An ill-scoped type variable in a region parameter is rejected. -/
example : checkFrom (ofAscArray badDecls badDistinct) 0 badDecls.toList = false := by
  native_decide

/-- And it is the region that is rejected: the same declaration with the variable in scope
is accepted. -/
private def fixedDecls : Array (Decl.Raw Unit) := #[boolDecl, illScoped (.var 0)]
private theorem fixedDistinct : DistinctDecls fixedDecls := by decide
example : checkFrom (ofAscArray fixedDecls fixedDistinct) 0 fixedDecls.toList = true := by
  native_decide

/-- A region's return type obeys declared-before-use like any other type: `try` ahead of
`Completion` is rejected. -/
private def forwardDecls : Array (Decl.Raw Unit) := #[boolDecl, excDecl, tryDecl, complDecl]
private theorem forwardDistinct : DistinctDecls forwardDecls := by decide
example : checkFrom (ofAscArray forwardDecls forwardDistinct) 0 forwardDecls.toList = false := by
  native_decide

/-- An argument and a region share one namespace: an `if` whose condition is named `then`
is rejected. -/
private def argRegionClash : Array (Decl.Raw Unit) := #[boolDecl, .insn
  { ann := (), name := ifName, typeParams := #["a"]
    argTypes := #[⟨"then", .app boolName #[]⟩]
    returnType := some (.var 0)
    regions := #[⟨"then", { params := #[], returnType := .var 0 }⟩,
                 ⟨"else", { params := #[], returnType := .var 0 }⟩] }]
private theorem argRegionClashDistinct : DistinctDecls argRegionClash := by decide
example :
    checkFrom (ofAscArray argRegionClash argRegionClashDistinct) 0
      argRegionClash.toList = false := by
  native_decide

/-- A region's parameters are named distinctly: a handler taking two `exc`s is rejected. -/
private def dupRegionParam : Array (Decl.Raw Unit) := #[boolDecl, excDecl, complDecl, .insn
  { ann := (), name := tryName, typeParams := #["a"]
    argTypes := #[]
    returnType := some (.app complName #[.var 0])
    regions := #[⟨"handler", { params := #[⟨"exc", .app excName #[]⟩, ⟨"exc", .app excName #[]⟩]
                               returnType := .app complName #[.var 0] }⟩] }]
private theorem dupRegionParamDistinct : DistinctDecls dupRegionParam := by decide
example :
    checkFrom (ofAscArray dupRegionParam dupRegionParamDistinct) 0
      dupRegionParam.toList = false := by
  native_decide

end RawExample

/-! ## Checked

The same two instructions through `InsnSig`, whose region signatures carry their own
well-formedness, so writing them down is the check. -/

namespace CheckedExample

private def boolD : TypeDecl Unit := { ann := (), name := boolName }
private def excD : TypeDecl Unit := { ann := (), name := excName }
private def complD : TypeDecl Unit := { ann := (), name := complName, params := #[⟨"a", .pos⟩] }

private def env₀ : Env Unit := Env.empty.addType boolD (by simp)
private def env₁ : Env Unit :=
  env₀.addType excD (by simp [env₀, boolD, excD, boolName, excName])
private def env₂ : Env Unit :=
  env₁.addType complD (by simp [env₁, env₀, boolD, excD, complD, boolName, excName, complName])

private def boolRef : TypeRef env₂ 0 :=
  ((TypeRef.ofAddType Env.empty boolD (by simp)).ofSubset
    (Env.subset_addType _ _ _)).ofSubset (Env.subset_addType _ _ _)
private def excRef : TypeRef env₂ 0 :=
  (TypeRef.ofAddType env₀ excD _).ofSubset (Env.subset_addType _ _ _)
private def complRef : TypeRef env₂ 1 := TypeRef.ofAddType env₁ complD _

/-- The instruction's one type variable. -/
private def a : TypeExpr env₂ 1 := .var 0 (by omega)
private def complA : TypeExpr env₂ 1 := .app complRef #v[a]

/-- A region signature is built from checked types, through `RegionSig.of`; `decide`
discharges the distinctness of its parameter names. -/
private def handlerSig : RegionSig env₂ 1 := RegionSig.of #[⟨"exc", .app excRef #v[]⟩] complA

/-- `of` hands back what it was given. -/
example : handlerSig.params.map (·.name) = #["exc"] := by simp [handlerSig]
example : handlerSig.returnType = some complA := by simp [handlerSig]

/-- The distinctness of argument and region names, `InsnSig`'s last field, is left to its
default `by decide`. -/
private def ifSig : InsnSig env₂ :=
  { ann := (), typeParams := #["a"]
    argTypes := #[⟨"cond", .app boolRef #v[]⟩]
    returnType := some a
    regions := #[⟨"then", RegionSig.of #[] a⟩, ⟨"else", RegionSig.of #[] a⟩] }

private def trySig : InsnSig env₂ :=
  { ann := (), typeParams := #["a"]
    argTypes := #[]
    returnType := some complA
    regions := #[⟨"body", RegionSig.of #[] complA⟩, ⟨"handler", handlerSig⟩] }

private def ops : Array (Name × InsnSig env₂) := #[(ifName, ifSig), (tryName, trySig)]

/-- The deciding batch accepts both. -/
private def env₃ : Env Unit := (env₂.addInsns? ops).get (by native_decide)

/-- The names of the regions the instruction `n` takes, read back through the checked
lookup: the region signatures survive erasure and re-checking. -/
private def regionNames (s : Env Unit) (n : Name) : Option (Array String) :=
  match s.get? n with
  | some (.insn (isig := i) _) => some (i.regions.map (·.name))
  | _ => none

example : regionNames env₃ ifName = some #["then", "else"] := by native_decide
example : regionNames env₃ tryName = some #["body", "handler"] := by native_decide

/-- How many parameters each region of `n` takes. -/
private def regionArity (s : Env Unit) (n : Name) : Option (Array Nat) :=
  match s.get? n with
  | some (.insn (isig := i) _) => some (i.regions.map (·.type.params.size))
  | _ => none

example : regionArity env₃ tryName = some #[0, 1] := by native_decide

/-- The total batch needs only freshness, and hands back a reference per operation whose
signature still has its regions. -/
private theorem opsFresh : env₂.FreshNames (ops.map (·.1)) := by
  simp [ops, env₂, env₁, env₀, boolD, excD, complD, ifName, tryName, boolName, excName, complName]

private def ifRef := InsnRef.ofAddInsns ops opsFresh 0

example : ifRef.name = ifName := rfl

end CheckedExample

end

end Strata.Mantle.RegionSigTest
