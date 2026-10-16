/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.WF
public import StrataMantle.Env
-- `Env.ofArray?` is private: the examples below evaluate it directly.
import all StrataMantle.Env
-- Also imported as `meta` so the definitions below are available to the
-- interpreter: `#guard` needs compiled code for `Env.ofArray?` and `addInsns?`.
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

/-- The checker accepts `ds`. -/
private def accepts (ds : Array (Decl.Raw Unit)) : Bool := (Env.ofArray? ds).isSome
/-- `ds` names each declaration once, and the checker rejects it. -/
private def rejects (ds : Array (Decl.Raw Unit)) : Bool :=
  decide (Env.Raw.DistinctDecls ds) && (Env.ofArray? ds).isNone

/-! ## Unchecked -/

namespace RawExample

private def boolDecl : Decl.Raw Unit := .type { ann := (), name := boolName }
private def excDecl : Decl.Raw Unit := .type { ann := (), name := excName }
/-- `Completion : Type → Type`. -/
private def complDecl : Decl.Raw Unit :=
  .type { ann := (), name := complName, params := #[⟨"a", .pos⟩] }

/-- `if {a} (cond : Bool) [then : () -> a] [else : () -> a] : a`. -/
private def ifDecl : Decl.Raw Unit := .insn
  { ann := (), name := ifName, typeParams := #[⟨"a", .type⟩]
    argTypes := #[⟨"cond", .app boolName #[]⟩]
    returnType := some (.var 0)
    regions := #[⟨"then", { params := #[], returnType := .var 0 }⟩,
                 ⟨"else", { params := #[], returnType := .var 0 }⟩] }

/-- `try {a} [body : () -> Completion a] [handler : (exc : Exc) -> Completion a]
    : Completion a`. -/
private def tryDecl : Decl.Raw Unit := .insn
  { ann := (), name := tryName, typeParams := #[⟨"a", .type⟩]
    argTypes := #[]
    returnType := some (.app complName #[.var 0])
    regions := #[⟨"body", { params := #[], returnType := .app complName #[.var 0] }⟩,
                 ⟨"handler", { params := #[⟨"exc", .app excName #[]⟩]
                               returnType := .app complName #[.var 0] }⟩] }

private def goodDecls : Array (Decl.Raw Unit) := #[boolDecl, excDecl, complDecl, ifDecl, tryDecl]

#guard accepts goodDecls

/-- An `if` whose `then` region takes a parameter of type `b`, which it does not bind: the
region's types are under the instruction's one type variable, so level `1` is out of scope. -/
private def illScoped (regionParam : TypeExpr.Raw) : Decl.Raw Unit := .insn
  { ann := (), name := ifName, typeParams := #[⟨"a", .type⟩]
    argTypes := #[⟨"cond", .app boolName #[]⟩]
    returnType := some (.var 0)
    regions := #[⟨"then", { params := #[⟨"x", regionParam⟩], returnType := .var 0 }⟩] }

private def badDecls : Array (Decl.Raw Unit) := #[boolDecl, illScoped (.var 1)]

/- An ill-scoped type variable in a region parameter is rejected. -/
#guard rejects badDecls

/-- And it is the region that is rejected: the same declaration with the variable in scope
is accepted. -/
private def fixedDecls : Array (Decl.Raw Unit) := #[boolDecl, illScoped (.var 0)]
#guard accepts fixedDecls

/- A list of types as a region parameter's type is rejected. -/
#guard rejects #[boolDecl, illScoped (.list #[])]

/-- `try`, returning `a`, its body region alone mentioning `Completion`. -/
private def tryRegionDecl : Decl.Raw Unit := .insn
  { ann := (), name := tryName, typeParams := #[⟨"a", .type⟩]
    argTypes := #[]
    returnType := some (.var 0)
    regions := #[⟨"body", { params := #[], returnType := .app complName #[.var 0] }⟩] }

/-- A region's return type obeys declared-before-use like any other type: a `try` whose body
region alone mentions `Completion` is rejected ahead of `Completion`, and accepted after. -/
private def forwardDecls : Array (Decl.Raw Unit) :=
  #[boolDecl, excDecl, tryRegionDecl, complDecl]
#guard rejects forwardDecls
#guard accepts #[boolDecl, excDecl, complDecl, tryRegionDecl]

/-- An argument and a region share one namespace: an `if` whose condition is named `then`
is rejected. -/
private def argRegionClash : Array (Decl.Raw Unit) := #[boolDecl, .insn
  { ann := (), name := ifName, typeParams := #[⟨"a", .type⟩]
    argTypes := #[⟨"then", .app boolName #[]⟩]
    returnType := some (.var 0)
    regions := #[⟨"then", { params := #[], returnType := .var 0 }⟩,
                 ⟨"else", { params := #[], returnType := .var 0 }⟩] }]
#guard rejects argRegionClash

/-- A region's parameters are named distinctly: a handler taking two `exc`s is rejected. -/
private def dupRegionParam : Array (Decl.Raw Unit) := #[boolDecl, excDecl, complDecl, .insn
  { ann := (), name := tryName, typeParams := #[⟨"a", .type⟩]
    argTypes := #[]
    returnType := some (.app complName #[.var 0])
    regions := #[⟨"handler", { params := #[⟨"exc", .app excName #[]⟩, ⟨"exc", .app excName #[]⟩]
                               returnType := .app complName #[.var 0] }⟩] }]
#guard rejects dupRegionParam

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
private def a : TypeExpr env₂ #[.type] := .var 0 (by decide)
private def complA : TypeExpr env₂ #[.type] :=
  .app complRef #v[a] (by simp only [TypeRef.kinds, complRef, TypeRef.decl_ofAddType]; rfl)

/-- A region signature is built from checked types, through `RegionSig.of`; `decide`
discharges the distinctness of its parameter names. -/
private def handlerSig : RegionSig env₂ #[.type] :=
  RegionSig.of #[⟨"exc", .app excRef #v[] excRef.kinds_zero⟩] complA

/-- `of` hands back what it was given. -/
example : handlerSig.params.map (·.name) = #["exc"] := by simp [handlerSig]
example : handlerSig.returnType = some complA := by simp [handlerSig]

/-- The distinctness of argument and region names, `InsnSig`'s last field, is left to its
default `by decide`. -/
private def ifSig : InsnSig env₂ :=
  { ann := (), typeParams := #[⟨"a", .type⟩]
    argTypes := #[⟨"cond", .app boolRef #v[] boolRef.kinds_zero⟩]
    returnType := some a
    regions := #[⟨"then", RegionSig.of #[] a⟩, ⟨"else", RegionSig.of #[] a⟩] }

private def trySig : InsnSig env₂ :=
  { ann := (), typeParams := #[⟨"a", .type⟩]
    argTypes := #[]
    returnType := some complA
    regions := #[⟨"body", RegionSig.of #[] complA⟩, ⟨"handler", handlerSig⟩] }

private def ops : Array (Name × InsnSig env₂) := #[(ifName, ifSig), (tryName, trySig)]

/- The deciding batch accepts both. -/
#guard (env₂.addInsns? ops).isSome
-- The guard above shows the batch is accepted, so the fallback is never taken.
private def env₃ : Env Unit := (env₂.addInsns? ops).getD env₂

/-- The names of the regions the instruction `n` takes, read back through the checked
lookup: the region signatures survive erasure and re-checking. -/
private def regionNames (s : Env Unit) (n : Name) : Option (Array String) :=
  match s.get? n with
  | some (.insn (isig := i) _) => some (i.regions.map (·.name))
  | _ => none

#guard regionNames env₃ ifName = some #["then", "else"]
#guard regionNames env₃ tryName = some #["body", "handler"]

/-- How many parameters each region of `n` takes. -/
private def regionArity (s : Env Unit) (n : Name) : Option (Array Nat) :=
  match s.get? n with
  | some (.insn (isig := i) _) => some (i.regions.map (·.type.params.size))
  | _ => none

#guard regionArity env₃ tryName = some #[0, 1]

/-- The total batch needs only freshness, and hands back a reference per operation whose
signature still has its regions. -/
private theorem opsFresh : env₂.FreshNames (ops.map (·.1)) := by
  simp [ops, env₂, env₁, env₀, boolD, excD, complD, ifName, tryName, boolName, excName, complName]

private def ifRef := InsnRef.ofAddInsns ops opsFresh 0

example : ifRef.name = ifName := rfl

end CheckedExample

end

end Strata.Mantle.RegionSigTest
