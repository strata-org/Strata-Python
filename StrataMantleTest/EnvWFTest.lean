/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.WF
public import StrataMantle.Env
-- `check?`, `addData?` and `Env.ofArray?` are private: the examples below evaluate them directly.
import all StrataMantle.Env
-- Also imported as `meta`: the `#guard`s run the checker and the builders as compiled code.
meta import StrataMantle.Env

set_option autoImplicit false

/-! # Worked examples for `Env.Raw.WF`

The checker consults the environment's hash map, so it and the `Option`-returning builders run
under `#guard` as compiled code.  Rejections are also checked against the specification with
`decide`, where its conjuncts reduce.
-/

namespace Strata.Mantle.EnvWFTest

open Env.Raw

public section

/-- The checker accepts `ds`. -/
private def accepts (ds : Array (Decl.Raw Unit)) : Bool := (Env.ofArray? ds).isSome
/-- `ds` names each declaration once, and the checker rejects it. -/
private def rejects (ds : Array (Decl.Raw Unit)) : Bool :=
  decide (DistinctDecls ds) && (Env.ofArray? ds).isNone

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

/- The checker accepts `exampleEnv`, which by `wf_ofAscArray` makes it well formed. -/
#guard exampleEnv.check

/-- Forward references are rejected: moving the instruction ahead of the types it
mentions makes the checker fail. -/
private def badOrder : Array (Decl.Raw Unit) := #[consDecl, natDecl, listDecl]
#guard rejects badOrder

/-- Arity mismatches are rejected. -/
private def badArity : Array (Decl.Raw Unit) := #[natDecl, listDecl,
  .insn { ann := (), name := .str .base "bad", argTypes := #[],
          returnType := some (.app listName #[]) }]
#guard rejects badArity

/-- Out-of-scope de Bruijn variables are rejected (`typeParams` defaults to `#[]`). -/
private def openVarDecls : Array (Decl.Raw Unit) :=
  #[.insn { ann := (), name := .str .base "bad", argTypes := #[], returnType := some (.var 0) }]
#guard rejects openVarDecls

/-! ### Named type parameters

An instruction's type parameters and its arguments share one namespace.  The rejections
below are checked twice: by the checker, and against `WF` itself, whose distinctness
conjunct `decide` reduces in the kernel. -/

/-- An instruction with the given type parameters and argument names, every argument typed by
the first type variable. -/
private def polyInsn (typeParams : Array String) (args : Array String) : Decl.Raw Unit :=
  .insn { ann := (), name := .str .base "poly", typeParams := typeParams.map (⟨·, .type⟩)
          argTypes := args.map (⟨·, .var 0⟩), returnType := some (.var 0) }

/-- `d` after `Nat` and `List`. -/
private def afterList (d : Decl.Raw Unit) : Array (Decl.Raw Unit) := #[natDecl, listDecl, d]

/-- `poly : ∀ a, a → List a → a`: one named type parameter, in scope in every argument. -/
private def polyDecl : Decl.Raw Unit := .insn
  { ann := (), name := .str .base "poly", typeParams := #[⟨"a", .type⟩]
    argTypes := #[⟨"x", .var 0⟩, ⟨"xs", .app listName #[.var 0]⟩]
    returnType := some (.var 0) }

private def polyDecls : Array (Decl.Raw Unit) := #[natDecl, listDecl, polyDecl]
#guard accepts polyDecls

#guard accepts (afterList (polyInsn #["a", "b"] #["x", "y"]))

/- A duplicate argument name is rejected. -/
#guard rejects (afterList (polyInsn #["a"] #["x", "x"]))

/- A duplicate type-parameter name is rejected. -/
#guard rejects (afterList (polyInsn #["a", "a"] #["x"]))

/- A type parameter named like an argument is rejected. -/
#guard rejects (afterList (polyInsn #["x"] #["x"]))

/-- The same three, against the specification: no resolver makes them well formed. -/
example (R : Name → Array Kind → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "poly", typeParams := #[⟨"a", .type⟩]
        argTypes := #[⟨"x", .var 0⟩, ⟨"x", .var 0⟩], returnType := some (.var 0) } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

example (R : Name → Array Kind → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "poly", typeParams := #[⟨"a", .type⟩, ⟨"a", .type⟩]
        argTypes := #[⟨"x", .var 0⟩], returnType := some (.var 0) } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

example (R : Name → Array Kind → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "poly", typeParams := #[⟨"x", .type⟩]
        argTypes := #[⟨"x", .var 0⟩], returnType := some (.var 0) } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

/-! ### The variadic's name

The variadic shares the namespace too: it may not reuse an argument's, a region's or a
successor's name. -/

/-- An instruction with one argument `x`, the variadic `v`, and the given region and
successor names. -/
private def varInsnDecl (v : String) (regions succs : Array String := #[]) :
    InsnDecl.Raw Unit :=
  { ann := (), name := .str .base "var", typeParams := #[⟨"a", .type⟩]
    argTypes := #[⟨"x", .var 0⟩], variadic := some ⟨v, .var 0⟩, returnType := some (.var 0)
    regions := regions.map (⟨·, ⟨#[], .var 0⟩⟩), succs := succs.map (⟨·, #[]⟩) }

#guard accepts (afterList (.insn (varInsnDecl "xs" #["r"] #["k"])))

/- A variadic named like an argument, a region, a successor or a type parameter is
rejected. -/
#guard rejects (afterList (.insn (varInsnDecl "x")))
#guard rejects (afterList (.insn (varInsnDecl "r" #["r"])))
#guard rejects (afterList (.insn (varInsnDecl "k" #[] #["k"])))
#guard rejects (afterList (.insn (varInsnDecl "a")))

/-- …and against the specification, written as literals so that `decide` reduces. -/
example (R : Name → Array Kind → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "var", argTypes := #[⟨"x", .var 0⟩]
        variadic := some ⟨"x", .var 0⟩, returnType := some (.var 0) } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

example (R : Name → Array Kind → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "var", argTypes := #[]
        variadic := some ⟨"r", .var 0⟩, returnType := some (.var 0)
        regions := #[⟨"r", ⟨#[], .var 0⟩⟩] } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

example (R : Name → Array Kind → Prop) :
    ¬ InsnDecl.Raw.WF R
      { ann := (), name := .str .base "var", argTypes := #[]
        variadic := some ⟨"k", .var 0⟩, returnType := some (.var 0), succs := #[⟨"k", #[]⟩] } :=
  fun h => absurd (InsnDecl.Raw.wf_paramNames h) (by decide)

/-! A primitive's parameters are named distinctly too. -/

/- `Pair a a` is rejected: two parameters share a name. -/
#guard rejects (afterList (.type ⟨(), .str .base "Pair", #[⟨"a", .pos⟩, ⟨"a", .pos⟩]⟩))

#guard accepts (afterList (.type ⟨(), .str .base "Pair", #[⟨"a", .pos⟩, ⟨"b", .pos⟩]⟩))

/-- …and against the specification. -/
example (R : Name → Array Kind → Prop) :
    ¬ Decl.Raw.WF R
      (.type ⟨(), .str .base "Pair", #[⟨"a", .pos⟩, ⟨"a", .pos⟩]⟩ : Decl.Raw Unit) :=
  fun h => absurd (Decl.Raw.wf_type_iff.mp h) (by decide)

/-! ### Kinds

`Fn` takes a list of types, then a type.  A wrong kind fails the lookup a wrong count does,
and a list literal holds types and splices of list variables only. -/

private def fnK : Name := .str .base "Fn"
private def natT : TypeExpr.Raw := .app natName #[]

/-- `Fn` at its kinds, and `Nat`. -/
private def kindsOf (n : Name) (ks : Array Kind) : Bool :=
  (n == fnK && ks.toList == [.list, .type]) || (n == natName && ks.toList == [])

#guard TypeExpr.Raw.check kindsOf #[.type] (.app fnK #[.list #[.var 0, natT], natT])

-- A type where a list belongs, and a list where a type belongs; each in its place is accepted.
#guard !TypeExpr.Raw.check kindsOf #[] (.app fnK #[natT, natT])
#guard !TypeExpr.Raw.check kindsOf #[] (.app fnK #[.list #[], .list #[]])
#guard TypeExpr.Raw.check kindsOf #[] (.app fnK #[.list #[], natT])

-- `[[Nat]]`, a list of lists, is rejected, and `[Nat]` accepted.
#guard !TypeExpr.Raw.check kindsOf #[] (.app fnK #[.list #[.list #[natT]], natT])
#guard TypeExpr.Raw.check kindsOf #[] (.app fnK #[.list #[natT], natT])

-- A list variable, spliced in: in scope, and not.
#guard TypeExpr.Raw.check kindsOf #[.list] (.app fnK #[.list #[.var 0, natT], natT])
#guard !TypeExpr.Raw.check kindsOf #[] (.app fnK #[.list #[.var 0], natT])

-- A variable's kind is its scope's: a list variable is a list, and a type variable a type.
-- Every list is a literal, so a list variable is passed as `[*#1]`, not bare.
#guard TypeExpr.Raw.check kindsOf #[.type, .list] (.app fnK #[.list #[.var 1], .var 0])
#guard !TypeExpr.Raw.check kindsOf #[.type, .list] (.app fnK #[.var 1, .var 0])
#guard !TypeExpr.Raw.check kindsOf #[.list, .type] (.app fnK #[.var 1, .var 0])
#guard TypeExpr.Raw.check kindsOf #[.list, .type] (.app fnK #[.list #[.var 0], .var 1])
#guard !TypeExpr.Raw.check kindsOf #[.list] (.app fnK #[.var 0, .var 0])
#guard TypeExpr.Raw.check kindsOf #[.list] (.app fnK #[.list #[.var 0], natT])

/-- `f (x : ty) : Nat`. -/
private def fArg (ty : TypeExpr.Raw) : Decl.Raw Unit :=
  .insn { ann := (), name := .str .base "f", argTypes := #[⟨"x", ty⟩], returnType := some natT }

/- A list of types where an argument's type belongs is rejected, and a type accepted. -/
#guard rejects (afterList (fArg (.list #[])))
#guard accepts (afterList (fArg natT))

/-- A datatype `D` whose one parameter is `p`, with one constructor taking nothing. -/
private def dataWith (p : TyParam) : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "D", params := #[⟨"xs", p⟩],
                   ctors := #[{ ann := (), name := .str .base "mk", args := #[] }] }]
    nonEmpty := by simp }

/- A datatype's parameter is a type or a list of types. -/
#guard accepts (#[natDecl] ++ (dataWith .non).decls)
#guard accepts (#[natDecl] ++ (dataWith ⟨.non, .list⟩).decls)

/-- A datatype `D` with one constructor taking `x : ty`. -/
private def dataField (ty : TypeExpr.Raw) : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "D",
                   ctors := #[{ ann := (), name := .str .base "mk", args := #[⟨"x", ty⟩] }] }]
    nonEmpty := by simp }

/- A payload is a type, not a list of types. -/
#guard rejects (#[natDecl] ++ (dataField (.list #[natT])).decls)
#guard accepts (#[natDecl] ++ (dataField natT).decls)

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

/- `DataGroup.decls` gives the head, then one instruction per constructor, each marked as that
constructor, then the case instruction. -/
#guard (listGroup.decls).map (·.name) =
    #[listName, nilName, consName, listName.caseName]
#guard (listGroup.decls).map (fun d => d.asInsn.bind (·.kind.ctor?)) =
    #[none, some ⟨listName, 0, 0⟩, some ⟨listName, 0, 1⟩, none]

/-- `cons`'s instruction: `[a] (head : a) (tail : List a) : List a`. -/
private def consDecl' : InsnDecl.Raw Unit :=
  { ann := (), name := consName, typeParams := #[⟨"a", .type⟩],
    argTypes := #[⟨"head", .var 0⟩, ⟨"tail", .app listName #[.var 0]⟩],
    returnType := some (.app listName #[.var 0]), kind := .ctor ⟨listName, 0, 1⟩ }

/- It is the one its group gives it. -/
#guard listGroup.ctorInsn? 0 1 = some consDecl'

/- `nil`'s: `[a] : List a`. -/
#guard listGroup.ctorInsn? 0 0 = some
    { ann := (), name := nilName, typeParams := #[⟨"a", .type⟩], argTypes := #[],
      returnType := some (.app listName #[.var 0]), kind := .ctor ⟨listName, 0, 0⟩ }

#guard accepts listDecls

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

#guard (exprGroup.decls).map (·.name) =
    #[exprName, stmtName, .str .base "lit", .str .base "block", .str .base "expr",
      exprName.caseName, stmtName.caseName]
#guard (exprGroup.decls).map (fun d => d.asInsn.bind (·.kind.ctor?)) =
    #[none, none, some ⟨exprName, 0, 0⟩, some ⟨exprName, 0, 1⟩, some ⟨exprName, 1, 0⟩,
      none, none]
/- `expr`, the second member's constructor, returns that member. -/
#guard (exprGroup.ctorInsn? 1 0).map (·.returnType) = some (some (.app stmtName #[]))

#guard accepts exprDecls

/-- Recursion may not pass through a position nothing is known about: `Fn`'s argument is
declared `.non`, so the group's own types do not resolve inside it. -/
private def throughFn (params : Array (Param TyParam)) : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "T", params,
                   ctors := #[{ ann := (), name := .str .base "mk",
                                args := #[⟨"f", .app fnName #[.app (.str .base "T") #[]]⟩] }] }]
    nonEmpty := by simp }

/-- `Fn` declaring its argument `.pos`: then `T` may recurse through it. -/
private def fnPosDecl : Decl.Raw Unit :=
  .type { ann := (), name := fnName, params := #[⟨"a", .pos⟩] }

private def badRec : Array (Decl.Raw Unit) := #[fnDecl] ++ (throughFn #[]).decls
#guard rejects badRec
#guard accepts (#[fnPosDecl] ++ (throughFn #[]).decls)

/-- Positivity is declared, not inferred, and the declaration is checked: a member that
claims `.pos` in a parameter it then hands to `Fn` is rejected… -/
private def useParam (params : Array (Param TyParam)) : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "U", params,
                   ctors := #[{ ann := (), name := .str .base "mk",
                                args := #[⟨"f", .app fnName #[.var 0]⟩] }] }]
    nonEmpty := by simp }

private def badPos : Array (Decl.Raw Unit) := #[fnDecl] ++ (useParam #[⟨"a", .pos⟩]).decls
#guard rejects badPos

/-- …and the same group declaring the parameter `.non` is accepted, because then it claims
nothing. -/
private def okPos : Array (Decl.Raw Unit) :=
  #[fnDecl] ++ (useParam #[⟨"a", .non⟩]).decls
#guard accepts okPos

/-! Positivity reaches through list literals: each element takes its position's polarity. -/

/-- `FnL : [Type] → Type → Type`, its list of arguments `.non` and its result `.pos`. -/
private def fnLName : Name := .str .base "FnL"
private def fnLDecl : Decl.Raw Unit :=
  .type { ann := (), name := fnLName, params := #[⟨"args", ⟨.non, .list⟩⟩, ⟨"r", .pos⟩] }

/-- A one-member group `T` whose one constructor takes a field of type `ty`. -/
private def withField (ty : TypeExpr.Raw) : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "T",
                   ctors := #[{ ann := (), name := .str .base "mk", args := #[⟨"f", ty⟩] }] }]
    nonEmpty := by simp }

private def tT : TypeExpr.Raw := .app (.str .base "T") #[]

/- `T` through the result is accepted, and through an element of the `.non` list rejected;
the same list holding `Nat` is accepted.  A type where the list belongs is rejected, and the
list accepted. -/
#guard accepts (#[natDecl, fnLDecl] ++ (withField (.app fnLName #[.list #[], tT])).decls)
#guard rejects (#[natDecl, fnLDecl] ++ (withField (.app fnLName #[.list #[tT], nat])).decls)
#guard accepts (#[natDecl, fnLDecl] ++ (withField (.app fnLName #[.list #[nat], nat])).decls)
#guard rejects (#[natDecl, fnLDecl] ++ (withField (.app fnLName #[nat, nat])).decls)

/-- `Tup : [Type] → Type`, its list `.pos`. -/
private def tupName : Name := .str .base "Tup"
private def tupDecl : Decl.Raw Unit :=
  .type { ann := (), name := tupName, params := #[⟨"ts", ⟨.pos, .list⟩⟩] }

/- `T` may recurse through an element of a `.pos` list. -/
#guard accepts (#[natDecl, tupDecl] ++ (withField (.app tupName #[.list #[tT]])).decls)

/-- A one-member group `U` with parameters `params`, whose one constructor takes
`f : FnL [a] Nat`. -/
private def paramInList (params : Array (Param TyParam)) : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "U", params,
                   ctors := #[{ ann := (), name := .str .base "mk",
                                args := #[⟨"f", .app fnLName #[.list #[.var 0], nat]⟩] }] }]
    nonEmpty := by simp }

/- `U` declaring `a` `.pos` and putting it in an element of the `.non` list is rejected; the
same group declaring `a` `.non` is accepted, so the rejection is for positivity. -/
#guard rejects (#[natDecl, fnLDecl] ++ (paramInList #[⟨"a", .pos⟩]).decls)
#guard accepts (#[natDecl, fnLDecl] ++ (paramInList #[⟨"a", .non⟩]).decls)

/-! A datatype's list parameter is a list variable of its payloads' scope: passed whole to a
list parameter, or spliced into a literal, but not a type. -/

/-- A one-member group `C` with parameters `params`, whose one constructor takes `f : ty`. -/
private def listData (params : Array (Param TyParam)) (ty : TypeExpr.Raw) :
    DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "C", params,
                   ctors := #[{ ann := (), name := .str .base "mk", args := #[⟨"f", ty⟩] }] }]
    nonEmpty := by simp }

private def asNon : Array (Param TyParam) := #[⟨"as", ⟨.non, .list⟩⟩]
private def asPos : Array (Param TyParam) := #[⟨"as", ⟨.pos, .list⟩⟩]

#guard accepts
  (#[natDecl, fnLDecl] ++ (listData asNon (.app fnLName #[.list #[.var 0], nat])).decls)
#guard rejects (#[natDecl, fnLDecl] ++ (listData asNon (.app fnLName #[.var 0, nat])).decls)
#guard accepts
  (#[natDecl, fnLDecl] ++ (listData asNon (.app fnLName #[.list #[nat, .var 0], nat])).decls)
#guard rejects (#[natDecl, fnLDecl] ++ (listData asNon (.var 0)).decls)
#guard rejects (#[natDecl, fnLDecl] ++ (listData asNon (.list #[.var 0])).decls)
#guard rejects (#[natDecl, fnLDecl] ++ (listData asNon (.app fnLName #[nat, nat])).decls)
#guard accepts
  (#[natDecl, fnLDecl] ++ (listData asNon (.app fnLName #[.list #[nat], nat])).decls)

/- `C`'s constructor and case instruction bind `as` as a list. -/
#guard ((listData asNon nat).ctorInsn? 0 0).map (·.typeParams) = some #[⟨"as", .list⟩]
#guard ((listData asNon nat).caseInsn? 0).map (·.typeParams) = some #[⟨"as", .list⟩]

/- Positivity: a `.pos` list parameter may not occur under a `.non` position, alone or
spliced among other elements; it may under a `.pos` one, and `C` may recurse through it. -/
#guard rejects
  (#[natDecl, fnLDecl] ++ (listData asPos (.app fnLName #[.list #[.var 0], nat])).decls)
#guard rejects
  (#[natDecl, fnLDecl] ++ (listData asPos (.app fnLName #[.list #[nat, .var 0], nat])).decls)
#guard accepts (#[natDecl, tupDecl] ++ (listData asPos (.app tupName #[.list #[.var 0]])).decls)
#guard accepts (#[natDecl, tupDecl] ++ (listData asPos
  (.app tupName #[.list #[.var 0, .app (.str .base "C") #[.list #[.var 0]]]])).decls)

/- `C` takes a list: an instruction applying it to a type is rejected. -/
#guard accepts (#[natDecl, fnLDecl] ++ (listData asNon nat).decls ++
  #[.insn { ann := (), name := .str .base "use",
            argTypes := #[⟨"c", .app (.str .base "C") #[.list #[nat]]⟩], returnType := some nat }])
#guard rejects (#[natDecl, fnLDecl] ++ (listData asNon nat).decls ++
  #[.insn { ann := (), name := .str .base "use",
            argTypes := #[⟨"c", .app (.str .base "C") #[nat]⟩], returnType := some nat }])

/-- `call [(as : list) r] (f : fTy) (*args : vTy) : ret`, an instruction with a list
parameter. -/
private def callDecl (fTy vTy : TypeExpr.Raw) (ret : TypeExpr.Raw := .var 1) : Decl.Raw Unit :=
  .insn { ann := (), name := .str .base "call", typeParams := #[⟨"as", .list⟩, ⟨"r", .type⟩],
          argTypes := #[⟨"f", fTy⟩], variadic := some ⟨"args", vTy⟩, returnType := some ret }

private def fnAsR : TypeExpr.Raw := .app fnLName #[.list #[.var 0], .var 1]

/- A list variable, as the literal `[*#0]`, passes for a list parameter and types a variadic,
but is not a type: it is rejected as the result, and a type variable is rejected for the list
parameter.  Bare, outside a literal, a list variable is rejected everywhere. -/
#guard accepts #[natDecl, fnLDecl, callDecl fnAsR (.list #[.var 0])]
#guard rejects #[natDecl, fnLDecl, callDecl fnAsR (.list #[.var 0]) (ret := .list #[.var 0])]
#guard rejects #[natDecl, fnLDecl, callDecl (.app fnLName #[.var 1, .var 1]) (.list #[.var 0])]
#guard rejects #[natDecl, fnLDecl, callDecl fnAsR (.var 0)]
#guard rejects #[natDecl, fnLDecl, callDecl (.app fnLName #[.var 0, .var 1]) (.list #[.var 0])]

/- A variadic's list may splice the list variable in; it may not hold a list. -/
#guard accepts #[natDecl, fnLDecl,
  callDecl (.app fnLName #[.list #[.var 0, nat], .var 1]) (.list #[.var 0, nat])]
#guard rejects #[natDecl, fnLDecl,
  callDecl (.app fnLName #[.list #[.var 0, nat], .var 1]) (.list #[.list #[], nat])]

/-- A payload still has to resolve: a group declared ahead of a type it mentions is
rejected, exactly as an operation would be, and the same declarations in order are accepted. -/
private def groupTooEarly : Array (Decl.Raw Unit) := exprGroup.decls ++ #[natDecl]
#guard rejects groupTooEarly
#guard accepts exprDecls

/-- `ds` with the declaration named `n` replaced by `d`. -/
private def replaceDecl (ds : Array (Decl.Raw Unit)) (n : Name) (d : Decl.Raw Unit) :
    Array (Decl.Raw Unit) :=
  ds.map fun e => if e.name == n then d else e

/-- An alias has to address something that is there: `Stmt` claiming to be member 7 of the
group headed by `Expr`, which has two, is rejected, and as member 1 accepted. -/
private def badAlias : Array (Decl.Raw Unit) :=
  replaceDecl exprDecls stmtName (.dataRest stmtName exprName 7)
#guard rejects badAlias
#guard accepts (replaceDecl exprDecls stmtName (.dataRest stmtName exprName 1))

/-- A constructor's instruction has to be the one its group gives it: `cons` claiming to be
constructor 0 of `List`, which is `nil`, is rejected, and as constructor 1 accepted… -/
private def badCtorName : Array (Decl.Raw Unit) :=
  replaceDecl listDecls consName (.insn { consDecl' with kind := .ctor ⟨listName, 0, 0⟩ })
#guard rejects badCtorName
#guard accepts (replaceDecl listDecls consName (.insn consDecl'))

/-- …and so is one whose signature disagrees with its payload: `cons` taking a `Nat` tail. -/
private def badCtorSig : Array (Decl.Raw Unit) :=
  replaceDecl listDecls consName (.insn { consDecl' with
    argTypes := #[⟨"head", .var 0⟩, ⟨"tail", nat⟩] })
#guard rejects badCtorSig

/-- …and one marked as a constructor of something that is not a group: `cons` over the
primitive `List`, marked as a constructor of `Nat`, is rejected, and as an ordinary instruction
accepted. -/
private def badCtorHead : Array (Decl.Raw Unit) :=
  #[natDecl, listDecl, .insn { consDecl' with kind := .ctor ⟨natName, 0, 1⟩ }]
#guard rejects badCtorHead
#guard accepts #[natDecl, listDecl, .insn { consDecl' with kind := .decl }]

/-! A datatype's parameters are named distinctly, and so is everything a constructor's
instruction binds: the parameters, then the fields. -/

/-- `Two a a`, a member whose parameters clash. -/
private def clashParams : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "Two",
                   params := #[⟨"a", .pos⟩, ⟨"a", .pos⟩],
                   ctors := #[{ ann := (), name := .str .base "two", args := #[] }] }]
    nonEmpty := by decide }
private def clashParamsDecls : Array (Decl.Raw Unit) := clashParams.decls
#guard rejects clashParamsDecls
#guard accepts (DataGroup.decls
  { members := #[{ ann := (), name := .str .base "Two",
                   params := #[⟨"a", .pos⟩, ⟨"b", .pos⟩],
                   ctors := #[{ ann := (), name := .str .base "two", args := #[] }] }]
    nonEmpty := by decide })

/-- `Box a = box (a : a)`, a field named like a parameter. -/
private def clashField : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "Box", params := #[⟨"a", .pos⟩],
                   ctors := #[{ ann := (), name := .str .base "box",
                                args := #[⟨"a", .var 0⟩] }] }]
    nonEmpty := by decide }
private def clashFieldDecls : Array (Decl.Raw Unit) := clashField.decls
#guard rejects clashFieldDecls
#guard accepts (DataGroup.decls
  { members := #[{ ann := (), name := .str .base "Box", params := #[⟨"a", .pos⟩],
                   ctors := #[{ ann := (), name := .str .base "box",
                                args := #[⟨"x", .var 0⟩] }] }]
    nonEmpty := by decide })

/-! A group's member names are ordinary type references once the group is in an environment:
the checked lookup resolves `Stmt` through the alias to the member the head carries. -/

private def dataEnv? : Option (Env Unit) :=
  (Env.empty.addType? { ann := (), name := natName }).bind (·.addData? exprGroup)

#guard dataEnv?.isSome

-- The guard above shows `dataEnv?` is `some`, so the fallback is never taken.
private def dataEnv : Env Unit := dataEnv?.getD Env.empty

private def refOf (n : Name) : Option (Name × Nat) :=
  match dataEnv.get? n with
  | some (.type (arity := a) r) => some (r.name, a)
  | _ => none

/- The head, named directly. -/
#guard refOf exprName = some (exprName, 0)

/- A member past the head, named through its alias. -/
#guard refOf stmtName = some (stmtName, 0)

/- A constructor name resolves too, but to an instruction, not a type… -/
#guard refOf (.str .base "lit") = none

/-- …one marked as that constructor, with its payload as arguments. -/
private def ctorOf? (n : Name) : Option (Option CtorAddr × Nat) :=
  match dataEnv.get? n with
  | some (.insn (isig := i) r) => some (r.ctorAddr?, i.argTypes.size)
  | _ => none

#guard ctorOf? (.str .base "lit") = some (some ⟨exprName, 0, 0⟩, 1)
#guard ctorOf? (.str .base "expr") = some (some ⟨exprName, 1, 0⟩, 1)

#guard ((.str .base "lit") : Name) ∈ dataEnv

/-! And the constructors read back, at whatever arguments the type supplies. -/

private def listSig? : Option (Env Unit) :=
  (Env.empty.addType? { ann := (), name := natName }).bind (·.addData? listGroup)

#guard listSig?.isSome

-- The guard above shows `listSig?` is `some`, so the fallback is never taken.
private def listSig : Env Unit := listSig?.getD Env.empty

private def tyOf (e : TypeExpr.Raw) : Option (TypeExpr listSig) := TypeExpr.check? listSig #[] e

/-- `p` of `Nat` and `List Nat`, checked against `listSig`; false if either does not check. -/
private def withTys (p : TypeExpr listSig → TypeExpr listSig → Bool) : Bool :=
  match tyOf (.app natName #[]), tyOf (.app listName #[.app natName #[]]) with
  | some natTy, some listNatTy => p natTy listNatTy
  | _, _ => false

/- `nil` takes nothing and `cons` takes a `Nat` and a `List Nat`: the payloads of `List a`
instantiated at `a := Nat`. -/
#guard withTys fun natTy listNatTy =>
  decide (listNatTy.ctorPayloads? = some #[#[], #[natTy, listNatTy]])

#guard withTys fun natTy listNatTy =>
  decide (listNatTy.ctorArgs? consName = some #[natTy, listNatTy])
#guard withTys fun _ listNatTy => decide (listNatTy.ctorArgs? nilName = some #[])

/- A constructor of some other type is not a constructor of this one. -/
#guard withTys fun _ listNatTy => decide (listNatTy.ctorArgs? natName = none)

/- A primitive has no constructors, which is not the same as having none declared. -/
#guard withTys fun natTy _ => decide (natTy.ctors? = none)

/- A datatype with a list parameter reads back at a list: `C [Nat, Nat]`'s `mk` takes a
`FnL [Nat, *[Nat, Nat]] Nat`, which is `FnL [Nat, Nat, Nat] Nat`. -/
private def closSig? : Option (Env Unit) := do
  let e ← (Env.empty : Env Unit).add? natDecl
  let e ← e.add? fnLDecl
  e.addData? (listData asNon (.app fnLName #[.list #[nat, .var 0], nat]))

#guard closSig?.isSome

#guard match closSig? with
  | some e => ((TypeExpr.check? e #[] (.app (.str .base "C") #[.list #[nat, nat]])).bind
      (·.ctorPayloads?)).map (·.map (·.map (·.toRaw))) ==
      some #[#[.app fnLName #[.list #[nat, nat, nat], nat]]]
  | none => false

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
private def natTy : TypeExpr env₀ := TypeExpr.app natRef #v[]

/-- Operand types in the empty scope fix the type parameters as none, so `regions` and
`distinct` take their defaults. -/
private def idSig : InsnSig env₀ :=
  { ann := (), argTypes := #[⟨"x", natTy⟩], returnType := some natTy }

example : idSig.typeParams = #[] ∧ idSig.typeArgc = 0 ∧ idSig.regions.size = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- The defaults also apply where the operands are a variable; only distinctness is left to
prove. -/
private def unarySig (args : Array (Param (TypeExpr env₀)))
    (distinct : (args.toList.map (·.name)).Nodup) : InsnSig env₀ :=
  { ann := (), argTypes := args, returnType := some natTy, distinct := by simpa using distinct }

private theorem idFresh : idName ∉ env₀ := by simp [env₀, natName, idName]

/-- A checked signature with a named type parameter.  Its distinctness proof is the field's
default, decided where the names are written. -/
private def polyIdSig : InsnSig env₀ :=
  { ann := (), typeParams := #[⟨"a", .type⟩]
    argTypes := #[⟨"x", TypeExpr.var 0 (by decide)⟩]
    returnType := some (TypeExpr.var 0 (by decide)) }

/-- The count is the number of names, and it computes: a `Vector` of that length is a
literal. -/
example : polyIdSig.typeArgc = 1 := rfl
example : Vector (TypeExpr env₀) polyIdSig.typeArgc := #v[natTy]

/-- Its type arguments have their parameters' kinds by `rfl`. -/
example : TypeArgs env₀ polyIdSig.scope := ⟨#[.ty natTy], rfl⟩

/- The checked signature erases to a declaration the checker accepts as well. -/
#guard (env₀.addInsns? #[(idName, polyIdSig)]).isSome

/-- Erasing keeps the names. -/
example : (polyIdSig.decl idName).typeParams = #[⟨"a", .type⟩] := rfl

private def env₁ : Env Unit := env₀.addInsn idName idSig idFresh

/-- Adding the instruction hands back its reference, against the new signature. -/
private def idRef : InsnRef env₁ (idSig.ofSubset (Env.subset_addInsn _ _ _ _)) :=
  InsnRef.ofAddInsn env₀ idName idSig idFresh

example : idRef.name = idName := by simp [idRef]

example : env₁.size = 2 := by simp only [env₁, Env.size_addInsn]; simp [env₀]

example : idName ∈ env₁ := by simp [env₁, Env.mem_addInsn]

/-- Extending `env₀` with `addInsn` only grows it, so `env₀` is a subset of `env₁`. -/
private theorem env₀_sub_env₁ : env₀ ⊆ env₁ := Env.subset_addInsn _ _ _ _

/-- The type reference survives the extension. -/
private def natRef₁ : TypeRef env₁ 0 := natRef.ofSubset env₀_sub_env₁

example : natRef₁.name = natName := by
  simp only [natRef₁, Strata.Mantle.name_TypeRef_carry]; simp [natRef]

/-- Looking a name up gives a checked declaration, under the name asked for. -/
private theorem natIn₁ : natName ∈ env₁ := by
  simp only [env₁, Env.mem_addInsn]; simp [env₀, natName, idName]

example : (env₁.get? natName).isSome := by simp [natIn₁]

example : (env₁.get natName natIn₁).name = natName :=
  Env.name_get? (Env.get?_eq_some_get natIn₁)

/-- And it can be carried into a further extension. -/
private def env₂ : Env Unit :=
  env₁.addType { ann := (), name := .str .base "Bool" } (by simp only [env₁, Env.mem_addInsn]; simp [env₀, natName, idName])

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

/-- `natD`, then `id : Nat → Nat`, or `none` if a step is rejected. -/
private def env? : Option (Env String) := do
  let env₀ ← Env.empty.addType? natD
  let natTy ← TypeExpr.check? env₀ #[] (.app natName #[])
  let idSig : InsnSig env₀ :=
    { ann := "the identity", argTypes := #[⟨"x", natTy⟩], returnType := some natTy,
      distinct := by simp }
  env₀.addInsns? #[(idName, idSig)]

#guard env?.isSome

-- The guard above shows `env?` is `some`, so the fallback is never taken.
private def env : Env String := env?.getD Env.empty

/-- What a name's declaration is annotated with, read through the checked lookup. -/
private def annOf (n : Name) : Option String :=
  match env.get? n with
  | some (.type r) => some r.decl.ann
  | some (.insn (isig := i) _) => some i.ann
  | none => none

#guard annOf natName = some "the integers"

#guard annOf idName = some "the identity"

#guard annOf (.str .base "nope") = none

end Annotated
end

end Strata.Mantle.EnvWFTest
