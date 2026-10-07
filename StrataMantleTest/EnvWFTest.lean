/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.WF
public import StrataMantle.Env
-- `check?` and `addData?` are private: the examples below evaluate them directly.
import all StrataMantle.Env
-- Also imported as `meta` so the definitions below are available to the
-- interpreter: `native_decide` needs compiled code for `checkFrom`.
meta import StrataMantle.Env.WF
meta import StrataMantle.Env

set_option autoImplicit false

/-! # Worked examples for `Env.Raw.WF`

`checkFrom` consults the environment's hash map, so obligations are discharged with
`native_decide`, which needs compiled code and therefore cannot run inside the
module that defines the environment. These live here instead.
-/

namespace Strata.Mantle.EnvWFTest

open Env.Raw

public section
section Example

private def natName : Name := .str .base "Nat"
private def listName : Name := .str .base "List"

/-- `Nat : Type`. -/
private def natDecl : Decl.Raw Unit := .type { ann := (), name := natName }
/-- `List : Type → Type`. -/
private def listDecl : Decl.Raw Unit :=
  .type { ann := (), name := listName, params := #[⟨"a", .pos⟩] }
private def listNat : TypeExpr.Raw := .app listName #[.app natName #[]]
/-- `cons : Nat → List Nat → List Nat`. -/
private def consDecl : Decl.Raw Unit := .insn
  { ann := (), name := .str .base "cons"
    argTypes := #[⟨"h", .app natName #[]⟩, ⟨"t", listNat⟩]
    returnType := some listNat }

private def exampleDecls : Array (Decl.Raw Unit) := #[natDecl, listDecl, consDecl]
private theorem exampleDistinct : DistinctDecls exampleDecls := by decide
private def exampleEnv : Env.Raw Unit := ofAscArray exampleDecls exampleDistinct

example : exampleEnv.WF := wf_ofAscArray _ _ (by native_decide)

/-- Forward references are rejected: moving the instruction ahead of the types it
mentions makes the checker fail. -/
private def badOrder : Array (Decl.Raw Unit) := #[consDecl, natDecl, listDecl]
private theorem badOrderDistinct : DistinctDecls badOrder := by decide
example : checkFrom (ofAscArray badOrder badOrderDistinct) 0 badOrder.toList = false := by
  native_decide

/-- Arity mismatches are rejected. -/
private def badArity : Array (Decl.Raw Unit) := #[natDecl, listDecl,
  .insn { ann := (), name := .str .base "bad", argTypes := #[],
          returnType := some (.app listName #[]) }]
private theorem badArityDistinct : DistinctDecls badArity := by decide
example : checkFrom (ofAscArray badArity badArityDistinct) 0 badArity.toList = false := by
  native_decide

/-- Out-of-scope de Bruijn variables are rejected (`typeParams` defaults to `#[]`). -/
private def openVarDecls : Array (Decl.Raw Unit) :=
  #[.insn { ann := (), name := .str .base "bad", argTypes := #[], returnType := some (.var 0) }]
private theorem openVarDistinct : DistinctDecls openVarDecls := by decide
example :
    checkFrom (ofAscArray openVarDecls openVarDistinct) 0 openVarDecls.toList = false := by
  native_decide

/-! ### Named type parameters

An instruction's type parameters and its arguments share one namespace.  The rejections
below are checked twice: by the checker, and against `WF` itself, whose distinctness
conjunct `decide` reduces in the kernel. -/

/-- An instruction with the given type parameters and argument names, every argument typed by
the first type variable. -/
private def polyInsn (typeParams : Array String) (args : Array String) : Decl.Raw Unit :=
  .insn { ann := (), name := .str .base "poly", typeParams
          argTypes := args.map (⟨·, .var 0⟩), returnType := some (.var 0) }

/-- Whether the checker accepts `d` after `Nat` and `List`. -/
private def accepts (d : Decl.Raw Unit) : Bool :=
  let ds := #[natDecl, listDecl, d]
  if h : DistinctDecls ds then checkFrom (ofAscArray ds h) 0 ds.toList else false

/-- `poly : ∀ a, a → List a → a`: one named type parameter, in scope in every argument. -/
private def polyDecl : Decl.Raw Unit := .insn
  { ann := (), name := .str .base "poly", typeParams := #["a"]
    argTypes := #[⟨"x", .var 0⟩, ⟨"xs", .app listName #[.var 0]⟩]
    returnType := some (.var 0) }

private def polyDecls : Array (Decl.Raw Unit) := #[natDecl, listDecl, polyDecl]
private theorem polyDistinct : DistinctDecls polyDecls := by decide
example : (ofAscArray polyDecls polyDistinct).WF := wf_ofAscArray _ _ (by native_decide)

example : accepts (polyInsn #["a", "b"] #["x", "y"]) = true := by native_decide

/-- A duplicate argument name is rejected. -/
example : accepts (polyInsn #["a"] #["x", "x"]) = false := by native_decide

/-- A duplicate type-parameter name is rejected. -/
example : accepts (polyInsn #["a", "a"] #["x"]) = false := by native_decide

/-- A type parameter named like an argument is rejected. -/
example : accepts (polyInsn #["x"] #["x"]) = false := by native_decide

/-- The same three, against the specification: no resolver makes them well formed. -/
example (R : Name → Nat → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "poly", typeParams := #["a"]
        argTypes := #[⟨"x", .var 0⟩, ⟨"x", .var 0⟩], returnType := some (.var 0) } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

example (R : Name → Nat → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "poly", typeParams := #["a", "a"]
        argTypes := #[⟨"x", .var 0⟩], returnType := some (.var 0) } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

example (R : Name → Nat → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "poly", typeParams := #["x"]
        argTypes := #[⟨"x", .var 0⟩], returnType := some (.var 0) } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

/-! ### The variadic's name

The variadic shares the namespace too: it may not reuse an argument's, a region's or a
successor's name. -/

/-- An instruction with one argument `x`, the variadic `v`, and the given region and
successor names. -/
private def varInsnDecl (v : String) (regions succs : Array String := #[]) :
    InsnDecl.Raw Unit :=
  { ann := (), name := .str .base "var", typeParams := #["a"]
    argTypes := #[⟨"x", .var 0⟩], variadic := some ⟨v, .var 0⟩, returnType := some (.var 0)
    regions := regions.map (⟨·, ⟨#[], .var 0⟩⟩), succs := succs.map (⟨·, #[]⟩) }

example : accepts (.insn (varInsnDecl "xs" #["r"] #["k"])) = true := by native_decide

/-- A variadic named like an argument, a region, a successor or a type parameter is
rejected. -/
example : accepts (.insn (varInsnDecl "x")) = false := by native_decide
example : accepts (.insn (varInsnDecl "r" #["r"])) = false := by native_decide
example : accepts (.insn (varInsnDecl "k" #[] #["k"])) = false := by native_decide
example : accepts (.insn (varInsnDecl "a")) = false := by native_decide

/-- …and against the specification, written as literals so that `decide` reduces. -/
example (R : Name → Nat → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "var", argTypes := #[⟨"x", .var 0⟩]
        variadic := some ⟨"x", .var 0⟩, returnType := some (.var 0) } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

example (R : Name → Nat → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "var", argTypes := #[]
        variadic := some ⟨"r", .var 0⟩, returnType := some (.var 0)
        regions := #[⟨"r", ⟨#[], .var 0⟩⟩] } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

example (R : Name → Nat → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "var", argTypes := #[]
        variadic := some ⟨"k", .var 0⟩, returnType := some (.var 0), succs := #[⟨"k", #[]⟩] } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

/-! A primitive's parameters are named distinctly too. -/

/-- `Pair a a` is rejected: two parameters share a name. -/
example : accepts (.type ⟨(), .str .base "Pair", #[⟨"a", .pos⟩, ⟨"a", .pos⟩]⟩) = false := by
  native_decide

example : accepts (.type ⟨(), .str .base "Pair", #[⟨"a", .pos⟩, ⟨"b", .pos⟩]⟩) = true := by
  native_decide

/-- …and against the specification. -/
example (R : Name → Nat → Prop) :
    ¬ Decl.Raw.WF R (.type ⟨(), .str .base "Pair", #[⟨"a", .pos⟩, ⟨"a", .pos⟩]⟩ : Decl.Raw Unit) :=
  fun h => absurd (Decl.Raw.wf_type_iff.mp h) (by decide)

end Example

/-! ## Mutual groups of datatypes

A group is declared by one `dataHead` carrying every member; the names of the other
members are aliases into it, and each constructor is an instruction whose signature the
group determines.  What the checker asks of a group is
that each payload resolve — to one of the group's own types, or to something declared
before the group — and that a member declared `.pos` in a parameter really does keep its
recursion out of positions nothing is known about. -/

section DataExample

private def nat : TypeExpr.Raw := .app natName #[]

/-- `Fn : Type → Type`, a primitive that says nothing about how it uses its argument.
Stands in for a function or a handler type. -/
private def fnName : Name := .str .base "Fn"
private def fnDecl : Decl.Raw Unit :=
  .type { ann := (), name := fnName, params := #[⟨"a", .non⟩] }

private def nilName : Name := .str .base "nil"
private def consName : Name := .str .base "cons"

/-- `data List a = nil | cons a (List a)` — one member, recursive, `a` positive. -/
private def listGroup : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := listName, params := #[⟨"a", .pos⟩],
                   ctors := #[{ ann := (), name := nilName, args := #[] },
                              { ann := (), name := consName,
                                args := #[⟨"head", .var 0⟩,
                                          ⟨"tail", .app listName #[.var 0]⟩] }] }]
    nonEmpty := by decide }

private def listDecls : Array (Decl.Raw Unit) := #[natDecl] ++ listGroup.decls

/-- `DataGroup.decls` computes the addresses and the signatures, so an environment need not
spell them out: the head, then one instruction per constructor, each marked as that
constructor, then the case instruction. -/
example : (listGroup.decls).map (·.name) =
    #[listName, nilName, consName, listName.caseName] := by native_decide
example : (listGroup.decls).map (fun d => d.asInsn.bind (·.kind.ctor?)) =
    #[none, some ⟨listName, 0, 0⟩, some ⟨listName, 0, 1⟩, none] := by native_decide

/-- `cons`'s instruction: `[a] (head : a) (tail : List a) : List a`. -/
example : listGroup.ctorInsn? 0 1 = some
    { ann := (), name := consName, typeParams := #["a"],
      argTypes := #[⟨"head", .var 0⟩, ⟨"tail", .app listName #[.var 0]⟩],
      returnType := some (.app listName #[.var 0]), kind := .ctor ⟨listName, 0, 1⟩ } := by
  native_decide

/-- `nil`'s: `[a] : List a`. -/
example : listGroup.ctorInsn? 0 0 = some
    { ann := (), name := nilName, typeParams := #["a"], argTypes := #[],
      returnType := some (.app listName #[.var 0]), kind := .ctor ⟨listName, 0, 0⟩ } := by
  native_decide
private theorem listDistinct : DistinctDecls listDecls := by native_decide
example : (ofAscArray listDecls listDistinct).WF := wf_ofAscArray _ _ (by native_decide)

/-- Mutual recursion: `Expr` mentions `Stmt` and `Stmt` mentions `Expr`, so neither can
be declared before the other and the group is the unit of declaration.  The second member
gets its name from a `dataRest` alias. -/
private def exprName : Name := .str .base "Expr"
private def stmtName : Name := .str .base "Stmt"

private def exprGroup : DataGroup Unit TypeExpr.Raw :=
  { members :=
      #[{ ann := (), name := exprName,
          ctors := #[{ ann := (), name := .str .base "lit", args := #[⟨"n", nat⟩] },
                     { ann := (), name := .str .base "block",
                       args := #[⟨"body", .app stmtName #[]⟩] }] },
        { ann := (), name := stmtName,
          ctors := #[{ ann := (), name := .str .base "expr",
                       args := #[⟨"e", .app exprName #[]⟩] }] }]
    nonEmpty := by decide }

private def exprDecls : Array (Decl.Raw Unit) := #[natDecl] ++ exprGroup.decls

example : (exprGroup.decls).map (·.name) =
    #[exprName, stmtName, .str .base "lit", .str .base "block", .str .base "expr",
      exprName.caseName, stmtName.caseName] := by
  native_decide
example : (exprGroup.decls).map (fun d => d.asInsn.bind (·.kind.ctor?)) =
    #[none, none, some ⟨exprName, 0, 0⟩, some ⟨exprName, 0, 1⟩, some ⟨exprName, 1, 0⟩,
      none, none] := by
  native_decide
/-- `expr`, the second member's constructor, returns that member. -/
example : (exprGroup.ctorInsn? 1 0).map (·.returnType) = some (some (.app stmtName #[])) := by
  native_decide
private theorem exprDistinct : DistinctDecls exprDecls := by native_decide
example : (ofAscArray exprDecls exprDistinct).WF := wf_ofAscArray _ _ (by native_decide)

/-- Recursion may not pass through a position nothing is known about: `Fn`'s argument is
declared `.non`, so the group's own types do not resolve inside it. -/
private def throughFn (params : Array (Param Positivity)) : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "T", params,
                   ctors := #[{ ann := (), name := .str .base "mk",
                                args := #[⟨"f", .app fnName #[.app (.str .base "T") #[]]⟩] }] }]
    nonEmpty := by simp }

private def badRec : Array (Decl.Raw Unit) := #[fnDecl, .dataHead (throughFn #[])]
private theorem badRecDistinct : DistinctDecls badRec := by decide
example : checkFrom (ofAscArray badRec badRecDistinct) 0 badRec.toList = false := by
  native_decide

/-- Positivity is declared, not inferred, and the declaration is checked: a member that
claims `.pos` in a parameter it then hands to `Fn` is rejected… -/
private def useParam (params : Array (Param Positivity)) : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "U", params,
                   ctors := #[{ ann := (), name := .str .base "mk",
                                args := #[⟨"f", .app fnName #[.var 0]⟩] }] }]
    nonEmpty := by simp }

private def badPos : Array (Decl.Raw Unit) := #[fnDecl, .dataHead (useParam #[⟨"a", .pos⟩])]
private theorem badPosDistinct : DistinctDecls badPos := by decide
example : checkFrom (ofAscArray badPos badPosDistinct) 0 badPos.toList = false := by
  native_decide

/-- …and the same group declaring the parameter `.non` is accepted, because then it claims
nothing. -/
private def okPos : Array (Decl.Raw Unit) :=
  #[fnDecl] ++ (useParam #[⟨"a", .non⟩]).decls
/-- `okPos` names each declaration once. -/
private theorem okPosDistinct : DistinctDecls okPos := by native_decide
example : (ofAscArray okPos okPosDistinct).WF := wf_ofAscArray _ _ (by native_decide)

/-- A payload still has to resolve: a group declared ahead of a type it mentions is
rejected, exactly as an operation would be. -/
private def groupTooEarly : Array (Decl.Raw Unit) := #[.dataHead exprGroup, natDecl]
private theorem groupTooEarlyDistinct : DistinctDecls groupTooEarly := by decide
example :
    checkFrom (ofAscArray groupTooEarly groupTooEarlyDistinct) 0 groupTooEarly.toList
      = false := by
  native_decide

/-- An alias has to address something that is there: no member 7 of `List`. -/
private def badAlias : Array (Decl.Raw Unit) :=
  #[natDecl, .dataHead listGroup, .dataRest (.str .base "other") listName 7]
private theorem badAliasDistinct : DistinctDecls badAlias := by decide
example : checkFrom (ofAscArray badAlias badAliasDistinct) 0 badAlias.toList = false := by
  native_decide

/-- A constructor's instruction has to be the one its group gives it: `cons` claiming to be
constructor 0 of `List`, which is `nil`, is rejected… -/
private def consDecl' : InsnDecl.Raw Unit := (listGroup.ctorInsn? 0 1).get (by native_decide)
private def badCtorName : Array (Decl.Raw Unit) :=
  #[natDecl, .dataHead listGroup, .insn { consDecl' with kind := .ctor ⟨listName, 0, 0⟩ }]
/-- `badCtorName` names each declaration once. -/
private theorem badCtorNameDistinct : DistinctDecls badCtorName := by native_decide
example :
    checkFrom (ofAscArray badCtorName badCtorNameDistinct) 0 badCtorName.toList = false := by
  native_decide

/-- …and so is one whose signature disagrees with its payload: `cons` taking a `Nat` tail. -/
private def badCtorSig : Array (Decl.Raw Unit) :=
  #[natDecl, .dataHead listGroup, .insn { consDecl' with
    argTypes := #[⟨"head", .var 0⟩, ⟨"tail", nat⟩] }]
/-- `badCtorSig` names each declaration once. -/
private theorem badCtorSigDistinct : DistinctDecls badCtorSig := by native_decide
example :
    checkFrom (ofAscArray badCtorSig badCtorSigDistinct) 0 badCtorSig.toList = false := by
  native_decide

/-- …and one marked as a constructor of something that is not a group. -/
private def badCtorHead : Array (Decl.Raw Unit) :=
  #[natDecl, .insn { consDecl' with kind := .ctor ⟨natName, 0, 1⟩ }]
/-- `badCtorHead` names each declaration once. -/
private theorem badCtorHeadDistinct : DistinctDecls badCtorHead := by native_decide
example :
    checkFrom (ofAscArray badCtorHead badCtorHeadDistinct) 0 badCtorHead.toList = false := by
  native_decide

/-! A datatype's parameters are named distinctly, and so is everything a constructor's
instruction binds: the parameters, then the fields. -/

/-- `Two a a`, a member whose parameters clash. -/
private def clashParams : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "Two",
                   params := #[⟨"a", .pos⟩, ⟨"a", .pos⟩],
                   ctors := #[{ ann := (), name := .str .base "two", args := #[] }] }]
    nonEmpty := by decide }
private def clashParamsDecls : Array (Decl.Raw Unit) := clashParams.decls
/-- `clashParamsDecls` names each declaration once. -/
private theorem clashParamsDistinct : DistinctDecls clashParamsDecls := by native_decide
example :
    checkFrom (ofAscArray clashParamsDecls clashParamsDistinct) 0 clashParamsDecls.toList =
      false := by
  native_decide

/-- `Box a = box (a : a)`, a field named like a parameter. -/
private def clashField : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "Box", params := #[⟨"a", .pos⟩],
                   ctors := #[{ ann := (), name := .str .base "box",
                                args := #[⟨"a", .var 0⟩] }] }]
    nonEmpty := by decide }
private def clashFieldDecls : Array (Decl.Raw Unit) := clashField.decls
/-- `clashFieldDecls` names each declaration once. -/
private theorem clashFieldDistinct : DistinctDecls clashFieldDecls := by native_decide
example :
    checkFrom (ofAscArray clashFieldDecls clashFieldDistinct) 0 clashFieldDecls.toList =
      false := by
  native_decide

/-! A group's member names are ordinary type references once the group is in an environment:
the checked lookup resolves `Stmt` through the alias to the member the head carries. -/

private def dataEnv : Env Unit :=
  (((Env.empty.addType? { ann := (), name := natName }).bind (·.addData? exprGroup))).get
    (by native_decide)

private def refOf (n : Name) : Option (Name × Nat) :=
  match dataEnv.get? n with
  | some (.type (arity := a) r) => some (r.name, a)
  | _ => none

/-- The head, named directly. -/
example : refOf exprName = some (exprName, 0) := by native_decide

/-- A member past the head, named through its alias. -/
example : refOf stmtName = some (stmtName, 0) := by native_decide

/-- A constructor name resolves too, but to an instruction, not a type… -/
example : refOf (.str .base "lit") = none := by native_decide

/-- …one marked as that constructor, with its payload as arguments. -/
private def ctorOf? (n : Name) : Option (Option CtorAddr × Nat) :=
  match dataEnv.get? n with
  | some (.insn (isig := i) r) => some (r.ctorAddr?, i.argTypes.size)
  | _ => none

example : ctorOf? (.str .base "lit") = some (some ⟨exprName, 0, 0⟩, 1) := by native_decide
example : ctorOf? (.str .base "expr") = some (some ⟨exprName, 1, 0⟩, 1) := by native_decide

example : ((.str .base "lit") : Name) ∈ dataEnv := by native_decide

/-! And the constructors read back, at whatever arguments the type supplies. -/

private def listSig : Env Unit :=
  ((Env.empty.addType? { ann := (), name := natName }).bind (·.addData? listGroup)).get (by native_decide)

private def tyOf (e : TypeExpr.Raw) : Option (TypeExpr listSig 0) := TypeExpr.check? listSig 0 e

private def natTy : TypeExpr listSig 0 := (tyOf (.app natName #[])).get (by native_decide)
private def listNatTy : TypeExpr listSig 0 :=
  (tyOf (.app listName #[.app natName #[]])).get (by native_decide)

/-- `nil` takes nothing and `cons` takes a `Nat` and a `List Nat`: the payloads of `List a`
instantiated at `a := Nat`. -/
example : listNatTy.ctorPayloads? = some #[#[], #[natTy, listNatTy]] := by native_decide

example : listNatTy.ctorArgs? consName = some #[natTy, listNatTy] := by native_decide
example : listNatTy.ctorArgs? nilName = some #[] := by native_decide

/-- A constructor of some other type is not a constructor of this one. -/
example : listNatTy.ctorArgs? natName = none := by native_decide

/-- A primitive has no constructors, which is not the same as having none declared. -/
example : natTy.ctors? = none := by native_decide

end DataExample

/-! ## Building a checked `Env`

The same declarations through `Env`, which carries its well-formedness proof.
This is the shape a prelude takes: one decision for the whole array, and each
declaration resolved from its position rather than by a lookup. -/

namespace CheckedExample

/-! A client's view: build an environment a declaration at a time, keep the
references the operations hand back, look declarations up, and carry everything
into an extension.  Nothing here names a raw type or a well-formedness
predicate. -/

private def natName : Name := .str .base "Nat"
private def idName : Name := .str .base "id"

/-- One type declaration, and the reference `addType` hands back. -/
private def env₀ : Env Unit := Env.empty.addType { ann := (), name := natName } (by simp)

private def natRef : TypeRef env₀ 0 := TypeRef.ofAddType Env.empty { ann := (), name := natName } (by simp)

example : natRef.name = natName := by simp [natRef]

/-- The arity is an index now, so `#v[…]` below needs no side proof; the
declaration itself is still readable. -/
example : natRef.decl.arity = 0 := by simp [natRef, TypeDecl.arity]

/-- A checked type expression over that reference, then an environment using it. -/
private def natTy : TypeExpr env₀ 0 := TypeExpr.app natRef #v[]

/-- Operand types at scope `0` fix `typeArgc`, so `typeParams`, `regions` and `distinct`
take their defaults. -/
private def idSig : InsnSig env₀ :=
  { ann := (), argTypes := #[⟨"x", natTy⟩], returnType := some natTy }

example : idSig.typeParams = #[] ∧ idSig.typeArgc = 0 ∧ idSig.regions.size = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- The defaults also apply where the operands are a variable; only distinctness is left to
prove. -/
private def unarySig (args : Array (Param (TypeExpr env₀ 0)))
    (distinct : (args.toList.map (·.name)).Nodup) : InsnSig env₀ :=
  { ann := (), argTypes := args, returnType := some natTy, distinct := by simpa using distinct }

private theorem idFresh : idName ∉ env₀ := by simp [env₀, natName, idName]

/-- A checked signature with a named type parameter.  Its distinctness proof is the field's
default, decided where the names are written. -/
private def polyIdSig : InsnSig env₀ :=
  { ann := (), typeParams := #["a"]
    argTypes := #[⟨"x", TypeExpr.var 0 (by decide)⟩]
    returnType := some (TypeExpr.var 0 (by decide)) }

/-- The count is the number of names, and it computes: a `Vector` of that length is a
literal. -/
example : polyIdSig.typeArgc = 1 := rfl
example : Vector (TypeExpr env₀ 0) polyIdSig.typeArgc := #v[natTy]

/-- The checked signature erases to a declaration the checker accepts as well. -/
example : (env₀.addInsns? #[(idName, polyIdSig)]).isSome := by native_decide

/-- Erasing keeps the names. -/
example : (polyIdSig.decl idName).typeParams = #["a"] := rfl

private def env₁ : Env Unit := env₀.addInsn idName idSig idFresh

/-- Adding the instruction hands back its reference, against the new signature. -/
private def idRef : InsnRef env₁ (idSig.ofSubset (Env.subset_addInsn _ _ _ _)) :=
  InsnRef.ofAddInsn env₀ idName idSig idFresh

example : idRef.name = idName := by simp [idRef]

example : env₁.size = 2 := by simp [env₁, env₀]

example : idName ∈ env₁ := by simp [env₁, Env.mem_addInsn]

/-- The type reference survives the extension. -/
private def natRef₁ : TypeRef env₁ 0 := natRef.ofSubset (Env.subset_addInsn _ _ _ _)

example : natRef₁.name = natName := by simp [natRef₁, natRef]

/-- Looking a name up gives a checked declaration, under the name asked for. -/
private theorem natIn₁ : natName ∈ env₁ := by
  simp [env₁, Env.mem_addInsn, env₀, natName, idName]

example : (env₁.get? natName).isSome := by simp [natIn₁]

example : (env₁.get natName natIn₁).name = natName :=
  Env.name_get? (Env.get?_eq_some_get natIn₁)

/-- And it can be carried into a further extension. -/
private def env₂ : Env Unit :=
  env₁.addType { ann := (), name := .str .base "Bool" } (by simp [env₁, Env.mem_addInsn, env₀, natName, idName])

example : (Env.subset_addType env₁ _ _ : env₁ ⊆ env₂) = (by simp [env₂] : env₁ ⊆ env₂) := rfl

end CheckedExample

/-! ## Annotations

An environment built in Lean uses `Unit`, but nothing in the layer requires it.  Here the
annotation is a docstring, and it survives into the checked layer: a reference carries the
declaration it resolves to, and the declaration carries its annotation. -/

namespace Annotated

private def natName : Name := .str .base "Nat"
private def idName : Name := .str .base "id"

private def natD : TypeDecl String := { ann := "the integers", name := natName }

private def env₀ : Env String := (Env.empty.addType? natD).get (by native_decide)

private def natTy : TypeExpr env₀ 0 :=
  (TypeExpr.check? env₀ 0 (.app natName #[])).get (by native_decide)

private def idSig : InsnSig env₀ :=
  { ann := "the identity", argTypes := #[⟨"x", natTy⟩], returnType := some natTy }

private def env : Env String := (env₀.addInsns? #[(idName, idSig)]).get (by native_decide)

/-- What a name's declaration is annotated with, read through the checked lookup. -/
private def annOf (n : Name) : Option String :=
  match env.get? n with
  | some (.type r) => some r.decl.ann
  | some (.insn (isig := i) _) => some i.ann
  | none => none

example : annOf natName = some "the integers" := by native_decide

example : annOf idName = some "the identity" := by native_decide

example : annOf (.str .base "nope") = none := by native_decide

end Annotated
end

end Strata.Mantle.EnvWFTest
