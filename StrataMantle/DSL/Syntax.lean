/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Parser.Command

/-!
# The `environment` command: syntax

The grammar of `environment` blocks.  The elaborator is in `Mantle/DSL/Elab.lean`.

Keywords other than `environment` are non-reserved (`&"insn"`), and the declaration category
uses `(behavior := both)`, so a non-reserved keyword can lead a declaration.

The grammar accepts binders in any order; the elaborator enforces it, reporting a binder out of
order at that binder.
-/

public meta section

namespace Strata.Mantle.DSL

/-- A type in a block: a name, or a name applied to types by juxtaposition. -/
declare_syntax_cat mantleTy
syntax:max ident : mantleTy
syntax:max "(" mantleTy ")" : mantleTy
syntax:10 ident (colGt mantleTy:max)+ : mantleTy

/-- `(x y : τ)`: entry parameters of a region. -/
syntax mantleParams := "(" ident+ " : " mantleTy ")"

/-- A binder of an `insn`: arguments `(x y : τ)`, the variadic `(*xs : τ)`, regions
`(&r (p : τ) : σ)`, or successors `(^k (x : τ))`. -/
declare_syntax_cat mantleBinder
/-- Arguments: several names share one type. -/
syntax (name := binderArgs) "(" ident+ " : " mantleTy ")" : mantleBinder
/-- The variadic tail.  It binds one name; the elaborator reports a second. -/
syntax (name := binderVariadic) "(" "*" ident+ " : " mantleTy ")" : mantleBinder
/-- Regions with one interface: their entry parameters and the type they leave with. -/
syntax (name := binderRegions) "(" ("&" ident)+ mantleParams* " : " mantleTy ")" : mantleBinder
/-- Successors with one payload: the values the instruction passes to each.  `(^k)` passes
none.  The payload's names are documentation: a signature keeps only the types. -/
syntax (name := binderSuccs) "(" ("^" ident)+ mantleParams* ")" : mantleBinder

/-- `terminal`: the instruction ends its block. -/
syntax mantleTerminal := &"terminal"

/-- A type parameter of a `type` or `data`: `(+a)` is positive, `(a)` is not. -/
syntax mantleTyParam := "(" ("+")? ident ")"

/-- `as "s"`: the environment name, when it differs from the Lean name. -/
syntax mantleAs := &"as" str

/-- A constructor of a `data` declaration. -/
syntax mantleCtor := ppLine "| " (docComment)? ident (mantleAs)? mantleBinder*

/-- A declaration of an `environment` block. -/
declare_syntax_cat mantleDecl (behavior := both)

/-- `type T (+a) (b)`: a primitive type. -/
syntax (name := declType) (docComment)? &"type" ident (mantleAs)? mantleTyParam* : mantleDecl
/-- `data T (+a) where | c (x : τ) …`: a datatype. -/
syntax (name := declData) (docComment)? &"data" ident (mantleAs)? mantleTyParam* " where"
  mantleCtor* : mantleDecl
/-- `abbrev n (a b) := τ`: a type abbreviation, expanded by the elaborator. -/
syntax (name := declAbbrev) (docComment)? "abbrev " ident (mantleAs)? ("(" ident+ ")")?
  " := " mantleTy : mantleDecl
/-- `insn n [a] (x : τ) (*xs : τ) (&r (p : τ) : σ) (^k (y : τ)) : τ`: a primitive
instruction.  A `terminal insn` has no result type.  The grammar makes it optional for both;
the elaborator demands it of exactly the non-terminal ones. -/
syntax (name := declInsn) (docComment)? (mantleTerminal)? &"insn" ident (mantleAs)?
  ("[" ident+ "]")? mantleBinder* (" : " mantleTy)? : mantleDecl
/-- `def`: a defined instruction.  Reserved: it parses, and the elaborator rejects it. -/
syntax (name := declDef) (docComment)? "def " ident (mantleAs)? ("[" ident+ "]")?
  mantleBinder* " : " mantleTy (" := " term)? : mantleDecl
/-- `namespace n`: the environment namespace of the declarations up to `end n`. -/
syntax (name := declNamespace) "namespace " ident : mantleDecl
/-- `end n`.  The name sits under `colGt`, or it would take the next declaration's
keyword. -/
syntax (name := declEnd) "end" (ppSpace colGt ident)? : mantleDecl
/-- `open n₁ n₂ …`: short names in these namespaces resolve. -/
syntax (name := declOpen) "open" (ppSpace colGt ident)+ : mantleDecl
/-- `mutual … end`: a group of mutually recursive datatypes. -/
syntax (name := declMutual) "mutual" many1Indent(ppLine notFollowedBy("end") mantleDecl)
  ppDedent(ppLine "end") : mantleDecl

/-- `[public | private] environment E [extends P] where …`: declare an environment `E.env`,
its references, and its parent rule. -/
syntax (name := environmentCmd) (docComment)? (Lean.Parser.Command.visibility)?
  "environment " ident (" extends " ident)? " where" manyIndent(ppLine mantleDecl) : command

end Strata.Mantle.DSL

end
