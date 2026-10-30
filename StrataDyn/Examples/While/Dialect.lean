/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Integration.Lean.OfAstM
import StrataDDM.Integration.Lean.Gen
import StrataDDM.Integration.Lean.HashCommands

open StrataDDM

set_option autoImplicit false

/-!
# The While language, as a DDM dialect

A small typed imperative language: integers, booleans, unit and integer lists, and mutable
cells; `while` loops, functions with recursion, and integer exceptions with `try … catch`.
`/` and `%` raise `1` on a zero divisor.  `#while … #end` (`Elab.lean`) parses a program at
elaboration time, and `Lower.lean` lowers it to Dyn over the `While` environment.

```
fun gcd(a : Int, b : Int) : Int {
  while (b != 0) { var t : Int := a % b; a := b; b := t; }
  return a;
}
```

* Types: `Int`, `Bool`, `Unit`, `IntList`; the cells `Ref`, of an `Int`, and `ListRef`, of an
  `IntList`, on the machine's heap; and `Cell`, a cell of an `Int` that rules make there.
* Expressions: integers, `true`, `false`, `unit`, `nil`, variables, `h :: t`, `f(e, …)`,
  `- e`, `! e`, `ref e`, a new cell holding `e`, `wcell(e)`, a new `Cell`, `* e`, the
  contents of cell `e`, `^`, `* / %`, `+ -`, `< <= > >= == !=`, `&&`, `||`, and
  `case e of nil => e₁ | h :: t => e₂`, loosest first from the right.  `tick()` counts how
  often it has run, and `pick(e)` is a number from `0` to `e` that the run's oracle chooses.
* Statements: `var x : T := e;`, `x := e;`, `* r := e;`, which replaces the contents of
  cell `r`, `if (c) { … } else { … }`, `while (c) { … }`, `{ … }`, `return e;`, `raise e;`,
  `try { … } catch x => { … }`, `e;`, and `print(e);`, which appends `e` to the run's output.
  A name in scope cannot be declared again.
* `region while (c) { … }` and `region if (c) { … } else { … }` lower to operations on
  regions.  A region reads the variables in scope but cannot assign them, so its effects go
  through cells; it cannot `return`; and a `region while`'s condition cannot raise.
* A program is a sequence of functions `fun f(x : T, …) : T { … }`.  A function returning
  `Unit` may fall off its end.

`#strata_gen` generates the AST: `Ty`, `Exp`, `Stmt`, `Body`, `Else`, `Param` and `Command`
(a function), each annotated with its `SourceRange`.  The keywords are the dialect's tokens,
so they reserve nothing outside `#while … #end`.
-/

namespace Strata.Dyn.While.Ast

public section

#dialect
dialect While;

category Ty;
op tyInt : Ty => "Int";
op tyBool : Ty => "Bool";
op tyUnit : Ty => "Unit";
op tyList : Ty => "IntList";
op tyRef : Ty => "Ref";
op tyListRef : Ty => "ListRef";
/* A cell of an `Int` that rules make on the machine's heap. */
op tyCell : Ty => "Cell";

category Exp;
op int (n : Num) : Exp => n;
op boolTrue : Exp => "true";
op boolFalse : Exp => "false";
op unit : Exp => "unit";
op nil : Exp => "nil";
/* The number of `tick()`s so far, this one included. */
op tick : Exp => "tick" "(" ")";
/* A number from 0 to `e`, chosen by the oracle. */
op pick (e : Exp) : Exp => "pick" "(" e ")";
/* A new `Cell` holding `e`, which a rule makes. */
op mkCell (e : Exp) : Exp => "wcell" "(" e ")";
op var (x : Ident) : Exp => x;
op paren (e : Exp) : Exp => "(" e ")";
op call (f : Ident, args : CommaSepBy Exp) : Exp => f "(" args ")";
op neg (a : Exp) : Exp => @[prec(80)] "-" a;
op not (a : Exp) : Exp => @[prec(80)] "!" a;
op mkRef (a : Exp) : Exp => @[prec(80)] "ref " a;
op deref (a : Exp) : Exp => @[prec(80)] "*" a;
/* `pow` lowers to `while.pow`, whose rule is a `semanticGap`. */
op pow (a : Exp, b : Exp) : Exp => @[prec(75), rightassoc] a " ^ " b;
op mul (a : Exp, b : Exp) : Exp => @[prec(70), leftassoc] a " * " b;
op div (a : Exp, b : Exp) : Exp => @[prec(70), leftassoc] a " / " b;
op mod (a : Exp, b : Exp) : Exp => @[prec(70), leftassoc] a " % " b;
op add (a : Exp, b : Exp) : Exp => @[prec(65), leftassoc] a " + " b;
op sub (a : Exp, b : Exp) : Exp => @[prec(65), leftassoc] a " - " b;
op cons (h : Exp, t : Exp) : Exp => @[prec(60), rightassoc] h " :: " t;
op lt (a : Exp, b : Exp) : Exp => @[prec(50)] a " < " b;
op le (a : Exp, b : Exp) : Exp => @[prec(50)] a " <= " b;
op gt (a : Exp, b : Exp) : Exp => @[prec(50)] a " > " b;
op ge (a : Exp, b : Exp) : Exp => @[prec(50)] a " >= " b;
op eq (a : Exp, b : Exp) : Exp => @[prec(50)] a " == " b;
op ne (a : Exp, b : Exp) : Exp => @[prec(50)] a " != " b;
/* `and` and `or` evaluate both operands. */
op and (a : Exp, b : Exp) : Exp => @[prec(35), leftassoc] a " && " b;
op or (a : Exp, b : Exp) : Exp => @[prec(30), leftassoc] a " || " b;
op case (e : Exp, onNil : Exp, h : Ident, t : Ident, onCons : Exp) : Exp =>
  @[prec(20)] "case " e:0 " of " "nil" " => " onNil:0 " | " h " :: " t " => " onCons:19;

category Stmt;
category Body;
op body (ss : Seq Stmt) : Body => "{" ss "}";
category Else;
op elseBody (b : Body) : Else => " else " b;

op decl (x : Ident, t : Ty, e : Exp) : Stmt => "var " x " : " t " := " e:0 ";";
op assign (x : Ident, e : Exp) : Stmt => x " := " e:0 ";";
op store (r : Exp, e : Exp) : Stmt => "*" r:80 " := " e:0 ";";
op ite (c : Exp, t : Body, e : Option Else) : Stmt => "if " "(" c:0 ")" t e;
op while (c : Exp, b : Body) : Stmt => "while " "(" c:0 ")" b;
/* `while.loop` on two regions: the condition and the body. */
op regionWhile (c : Exp, b : Body) : Stmt => "region " "while " "(" c:0 ")" b;
/* `while.if` on two regions: the branches. */
op regionIte (c : Exp, t : Body, e : Option Else) : Stmt => "region " "if " "(" c:0 ")" t e;
op block (b : Body) : Stmt => b;
op ret (e : Exp) : Stmt => "return " e:0 ";";
/* Raise the integer `e`. */
op raise (e : Exp) : Stmt => "raise " e:0 ";";
/* `x` binds the raised integer in the handler. */
op try (b : Body, x : Ident, handler : Body) : Stmt => "try " b " catch " x " => " handler;
op expr (e : Exp) : Stmt => e:0 ";";
/* Append `e` to the run's output. */
op print (e : Exp) : Stmt => "print" "(" e:0 ")" ";";

category Param;
op param (x : Ident, t : Ty) : Param => x " : " t;

op func (name : Ident, params : CommaSepBy Param, ret : Ty, b : Body) : Command =>
  "fun " name "(" params ")" " : " ret b;
#end

-- The generated AST binds its annotation type implicitly.
set_option autoImplicit true in
#strata_gen While

/-- A program: its functions. -/
abbrev Program := Array (Command SourceRange)

end

end Strata.Dyn.While.Ast
