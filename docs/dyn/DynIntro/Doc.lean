/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import VersoManual
import DynIntro.Blocks

open Verso.Genre Manual
open DynIntro

set_option pp.rawOnError true
set_option maxRecDepth 4096

/-
Introduction to Dyn. Custom blocks are in `DynIntro/Blocks.lean`; the interactive panels
are `:::widget` blocks backed by `widgets/`. `scripts/export-data.py --check` and the files of
`checks/` check some of the listings below against `data/` and the package; `README.md`,
"Layout", says which, and what is not checked.
-/

#doc (Manual) "Introduction to Dyn" =>

A guide for anyone bringing a new source language to Strata through Dyn: from your parser's AST, through the DDM, an environment and a translator, to a checked module you can print, read and run.

# Overview
%%%
number := false
tag := "what"
file := "what-dyn-is"
%%%

Dyn is a typed SSA intermediate language whose vocabulary is supplied by the language that uses it. A program is a _module_ of functions. A function is a list of labelled _blocks_. Each block takes typed parameters, runs straight-line instructions that each define one value, and ends in one _terminator_.

:::::callout "Where Dyn sits in Strata"
Strata has two other intermediate languages that front ends target. _Strata.Core_ is the verification language: programs in it are checked with an SMT-based verifier. _Laurel_ is an intermediate analysis language for imperative source languages, translated to Strata.Core; Strata's Python verification runs through it.

Dyn sits at a lower level than either. It describes a program as the control-flow graph that a language's runtime would execute, over instructions that the language declares itself. Dyn gives those instructions an executable meaning in Lean. It suits languages whose meaning a runtime defines, such as Python with its object model, where a construct's behaviour depends on run-time values more than on its syntax.

Dyn and Laurel are separate paths. Dyn functions can carry contracts, and Dyn's types and type declarations translate to Strata.Core, but Dyn's values and operations do not translate yet, so Dyn programs cannot be verified yet. This guide covers the front end only, whose job ends at a well-formed module whose instructions mean what the source means.
:::::

:::::callout "What is in the package and what is planned"
In this package:

* environments, written with the `environment` command and checked;
* the builder, with a typed emitter for every instruction and typed blocks, targets and exits, the well-formedness checker, which scopes every use by dominance, the printer and the reader;
* the function type `base.Fn` and its call `base.callCode`, with function references and closures;
* function attributes, facts that a front end states about a function and that the printer and the reader keep, though the printer leaves out an extern's;
* instruction effects, `pure`, `reads`, `calls` or `writes` ({ref "env-ops"}[Environment 3: Instructions]);
* function contracts: `requires` and `ensures` clauses, frames, extern functions, which have a contract and no body, and ghost state. The checker checks that they are well formed, not that they hold. A run ignores the clauses, the frames and the ghosts, and a module with an extern function does not run yet. Some parts are trusted, not checked: `free ensures` clauses, an extern's signature and frames, a ghost's invariant and first value, and the declarations of the environment, each instruction's effect and the rule about failures ({ref "env-ops"}[Environment 3: Instructions]). A `requires` clause is known to hold only at the calls that the verified program makes, so a callback that an extern makes may enter a function without it (`docs/Dyn.md`, §1, "The trust base");
* the translation of Dyn's types and type declarations to Strata.Core, with proofs (`StrataDyn/Core/`, `docs/Dyn.md`, §6);
* ref-to-reg, a pass that promotes cells to SSA values ({ref "tr-vars"}[Translator 3: Variables]);
* the execution engine: semantic rules over Lean types, the table that `#dyn_sem_table` generates, linking, validation, the step function whose runs are the reference semantics, and the fused engine that executes modules ({ref "env-sem"}[Environment 7], {ref "run"}[Testing], {ref "inside"}[Inside the execution DSL]);
* runs, behaviours and trace refinement, for proofs about what modules do (`docs/Dyn.md`, §5);
* certificates for rules, which While's table has, and, for a module whose rules are certified, the frame theorem, heap safety and the theorem that a target that promotes the module's cells improves on its behaviour ({ref "wip"}[Proofs about runs]);
* the While language, with its environment, rules, lowering and runs. Its lowering produces the printed modules of this guide;
* Python's environment and translator. Python and While are the only languages exercised; no other front end exists.

Not yet proved: that ref-to-reg's own output satisfies the hypothesis of its theorem; and, for any table, While's included, that no rule of a module linked against it stops with a bad cell itself, which heap safety assumes ({ref "wip"}[Proofs about runs]). Under development, and not yet in the package: abstract interpretation, which has chapters of its own, from {ref "absint"}[Abstract interpretation: the idea].

Planned: rules for Python's environment, and the translation of Dyn's values and operations to Strata.Core. Also missing: assertions and assumptions in bodies ({ref "missing"}[Missing features]).
:::::

Three rules shape everything a translator produces. Every value is defined exactly once, so a variable that changes becomes a new value at each assignment. Blocks take parameters in place of phi nodes: a transfer to a block passes the values the block needs. Control flow is explicit: every way out of a block, a raised exception included, is an edge to a named block.

Dyn has no built-in arithmetic, objects or exceptions. An _environment_ declares every type and instruction a program may use. _Semantic rules_, written in Lean beside the environment, give those instructions meaning. A _translator_ turns a source program into a module over the environment.

The path from your language has four stages:

1. a parser for your language produces its AST;
1. the Strata DDM carries that AST into Lean as typed values;
1. your translator lowers the Lean AST, with the builder, into a module over your environment;
1. the checker proves the module well formed, and the printer, the reader and the execution engine take it from there.

::::figure
:::stages
```stage "1" "Your parser" "Source text to your AST." "whilelang"
fun mean(n : Int, d : Int)
    : Int {
  var s : Int := 0;
  …
  while (i <= n) { … }
  try { return s / d; }
  catch e => { … }
}
```

```stage "2" "DDM" "AST to typed Lean values." "lean"
Command.func _ ⟨_, "mean"⟩ …
  (Body.body _ ⟨_, #[
    Stmt.decl _ ⟨_, "s"⟩ …,
    Stmt.while _ (Exp.le …) …,
    Stmt.try _ … ⟨_, "e"⟩ …])
```

```stage "3" "Environment and translator" "Lean AST to Dyn over your environment, with the builder." "lean"
Base.jump (head.goto.bindAll
  vals[n₀, d₀, k₀, k₁])
Build.Raw.startBlock
  head.label ps
let% t ← While.le i n₁
Base.branch t body.goto exit.goto
```

```stage "4" "Checked module" "Printed, read back, run." "dyn"
head.0(%n.1 : base.Int, …):
  %t.0 : base.Bool =
    while.le(%i.0, %n.1)
  branch(%t.0) ^body.0()
    ^exit.0()
main 20: ok 21
```
:::

The four stages, each with the running example's artefact at that stage. The chapters follow them: {ref "ast"}[Your AST] for stage 1, {ref "ddm"}[Into Lean] for stage 2, {ref "env"}[Environment] and {ref "tr"}[Translator] for stage 3, and {ref "run"}[Testing] for stage 4. The excerpts are abbreviated; the full texts are in {ref "app-texts"}[Appendix C: Full texts].
::::

## 1. The running example
%%%
number := false
tag := "example"
%%%

One small program runs through the whole document. It is written in While, the toy language of Dyn's worked example. While comes with the execution engine. It has loops, `try … catch`, `raise`, a division that raises on a zero divisor, calls, `print`, integer lists with `case`, cells and region forms of `while` and `if`. The program has two functions:

```whilelang "mean.while"
fun mean(n : Int, d : Int) : Int {
  var s : Int := 0;
  var i : Int := 1;
  while (i <= n) { s := s + i; i := i + 1; }
  try { return s / d; } catch e => { return 0 - e; }
}
fun main(n : Int) : Int {
  var m : Int := mean(n, n - 10);
  print(m);
  return m;
}
```

`main 20` sums 1 to 20, which is 210, divides by 10 and prints 21. `main 10` divides by zero: the handler returns `0 - 1`, and `main` prints −1.

The translator turns it into the module below, printed with constants folded into their uses. The stepper walks through the correspondence one source construct at a time. The chapter {ref "tr"}[Translator] explains each step, and {ref "app-start"}[Appendix D: Starting a new front end] lists the files a new front end needs.

:::widget "stepper"
With JavaScript enabled, Prev and Next highlight each source construct and its Dyn lines, and hovering either side highlights its counterpart. The correspondence is listed in a table in {ref "app-texts"}[Appendix C: Full texts].
:::

# Your AST
%%%
number := false
tag := "ast"
file := "source-ast"
%%%

You start with a parser and an AST for your language, such as ESTree for JavaScript or `go/ast` for Go. For the JVM, the input is the class file's instruction list and exception table, which form a control-flow graph and not a tree ({ref "tr-unstructured"}[Translator 9: Bytecode and goto]). The AST needs a _closed schema_: a finite list of node kinds, each with typed fields. A closed schema translates mechanically into a DDM dialect. Every node the parser can produce then has a typed Lean counterpart.

For the running example the schema is the While dialect. Its categories are `Exp`, `Stmt`, `Body`, `Else`, `Param`, `Ty` and `Command`, one per syntactic sort, and each node is an operation of one category. The program's tree:

```astTree "AST of mean.while"
Command.func 'mean
  params: Param.param 'n Ty.tyInt, Param.param 'd Ty.tyInt
  ret: Ty.tyInt
  b: Body.body
    Stmt.decl 's tyInt (int '0)
    Stmt.decl 'i tyInt (int '1)
    Stmt.while
      c: Exp.le (var 'i) (var 'n)
      b: Body.body
        Stmt.assign 's (add (var 's) (var 'i))
        Stmt.assign 'i (add (var 'i) (int '1))
    Stmt.try
      b: Body.body [Stmt.ret (div (var 's) (var 'd))]
      x: 'e
      handler: Body.body [Stmt.ret (sub (int '0) (var 'e))]
Command.func 'main
  params: Param.param 'n tyInt; ret: tyInt
  b: Body.body
    Stmt.decl 'm tyInt (Exp.call 'mean [var 'n, sub (var 'n) (int '10)])
    Stmt.print (var 'm)
    Stmt.ret (var 'm)
```

A front end needs a DDM dialect and a translator into programs over a Dyn environment. The [Strata DDM Manual](https://github.com/strata-org/Strata/blob/main/docs/verso/DDMDoc.lean) describes the DDM half. Generate the DDM dialect from an existing abstract syntax tree for your language. The chapter {ref "tr"}[Translator] describes the translator.

# Into Lean
%%%
number := false
tag := "ddm"
file := "ddm"
%%%

The DDM carries your AST into Lean as a typed Lean AST. A _dialect_ declares abstract syntax as categories and operations. A category is a syntactic sort. An operation is a node kind, with typed arguments. Argument types are other categories or built-ins: `Ident`, `Str`, `Num`, `Option X`, `Seq X` and `CommaSepBy X`. The `#strata_gen` command generates one Lean inductive type per category, with one constructor per operation. It also generates converters from the DDM's generic tree.

There are two ways in.

An _external parser_ serialises the AST as DDM Ion, a binary format, which Lean reads. Python does this with CPython's own parser. A JavaScript front end could do the same with a parser such as oxc.

A dialect with concrete syntax can instead be _parsed by the DDM itself_ inside a Lean file. While does this with `#while … #end`. The program is written in the Lean file and becomes a Lean value at elaboration time. This route suits a toy language and tests.

A front end whose parser is written outside Lean, a Go front end written in Go for instance, should serialise its AST as DDM Ion and do the translation in Lean. The translator then uses the builder, which checks each function as it is finished. A front end could instead emit printed Dyn text and read it with `Module.read`. Nothing then ties the text to its environment ({ref "missing"}[Missing features]: _Text interchange for front ends written outside Lean_).

The first listing shows three operations of the While dialect, verbatim. The second shows how While's lowering matches the generated constructors:

```leantext "The While dialect (excerpt)"
op div (a : Exp, b : Exp) : Exp => @[prec(70), leftassoc] a " / " b;
op while (c : Exp, b : Body) : Stmt => "while " "(" c:0 ")" b;
/* `x` binds the raised integer in the handler. */
op try (b : Body, x : Ident, handler : Body) : Stmt => "try " b " catch " x " => " handler;
```

```leantext "Matching the generated constructors (While's lowering, excerpts)"
  | .div _ a b => do binApp .div (← lowerExpr a) (← lowerExpr b)
  | .call _ ⟨_, f⟩ ⟨_, ⟨args⟩⟩ => do
  | .while _ c body => do
  | .try _ body ⟨_, x⟩ handler => do
```

The first argument of every constructor is its annotation, a source range in practice. Identifiers and sequences arrive wrapped with their own annotations, and the angle brackets take them apart.

::::deepDive "dialect mechanics and gotchas"
* Declare a dialect inline with `#dialect … #end`, or load one with `#load_dialect "path.dialect.st.ion"`. Loading also creates `<D>_map`, the dialect map `Program.fromIon` needs. Declare the file as a lake `input_file` and list it in `extraDepTargets` of every library that reads it, or edits to it will not trigger rebuilds.
* `set_option autoImplicit true in #strata_gen D` is needed: the generated AST binds its annotation type implicitly.
* Every argument is wrapped as `Ann val ann`. Match an identifier as `.var _ ⟨_, x⟩`, and a `Seq` or `CommaSepBy` as `⟨_, ⟨list⟩⟩` to recurse structurally on a `List`. `Num` is unsigned, so negative literals need a hand-written category, as Python's `IntPos`/`IntNeg` are.
* Naming hazards:

  * a category named `Expr` clashes with `Lean.Expr` (While uses `Exp`);
  * Lean keywords make poor operation names (While uses `func` and `elseBody`, not `fun` and `else`);
  * an argument named like a category shadows the type;
  * `op` and `type` are DDM reserved words.

* The generated `ofAst`/`toAst` are `partial`, so the kernel cannot run them. To use a program in `decide +kernel`, convert it at elaboration time and quote it with derived `ToExpr`, as `#while` does. `deriving ToExpr` must group mutually recursive categories together (`Stmt, Body, Else`).
* `#strata_gen` time grows with the size of mutually recursive category groups, not with the number of operations. Never put DDM AST types inside your own mutual inductive: the kernel then rechecks the whole group.
* How the Python front end calls its parser, one workable contract:

  * Lean writes its embedded copy of the dialect to a temporary file and passes it to the parser, so the parser and Lean never disagree on the schema;
  * `Program.fromIon` checks the dialect name in the program header;
  * `SourceRange` holds UTF-8 byte offsets, so a parser that counts in UTF-16 must convert.

* StrataDDM includes a Python library (`Python/strata/strata/base.py`) that reads dialects and writes programs as Ion. A parser in another language needs its own writer ({ref "missing"}[Missing features]: _DDM ergonomics for new front ends_).

:::sources
Sources: `StrataPython/PythonDialect.lean`; `StrataPython/ReadPython.lean`; `StrataPython/Dyn/Cli.lean`; StrataDDM `Integration/Lean/Gen.lean`, `Integration/Lean/HashCommands.lean`.

:::

::::

# Environment
%%%
number := false
tag := "env"
file := "environment"
%%%

## 1. What an environment is
%%%
number := false
tag := "env-what"
%%%

An environment is a checked list of declarations of three kinds: primitive types, groups of datatypes, and instructions. You write it with the `environment` command. The command generates a typed Lean reference for every declaration and proves the list well formed.

Every language extends the _base_. The base provides:

* the types `Unit`, `Bool`, `Int`, `Float64`, `String`, `Sequence`, `Ref`, `Except` and `Loc`, the type of the sets of locations that a frame names;
* the function type `Fn`, whose values are called with `callCode`;
* refs: `refNew` makes a cell and returns a ref to it, and `refGet` and `refSet` read and write the cell a ref points to;
* the eliminators `Unit.case` and `Except.case`;
* the terminators `jump`, `branch` and `unreachable`;
* for contracts, `old`, which reads the state at the call in an `ensures` clause, and `cellLoc`, the location of a cell.

Here is the whole While environment, verbatim. It is a template for a small language: two datatypes, arithmetic, a raising division, instructions that reach the world, an abbreviation for refs to integer cells, and two region-owning instructions.

```leantext "The While environment"
public environment While extends Base where
  namespace «while»
  open base
  /-- A list of integers. -/
  data IntList where
    | nil
    | cons (head : Int) (tail : IntList)
  /-- How a body region ended: it fell off its end, or raised `e`. -/
  data Flow where
    | next
    | raise (e : Int)
  insn add (lhs rhs : Int) : Int
  insn sub (lhs rhs : Int) : Int
  insn mul (lhs rhs : Int) : Int
  insn neg (x : Int) : Int
  /-- `lhs / rhs`, or `^err` with `1` if `rhs` is `0`. -/
  insn div (lhs rhs : Int) (^err (code : Int)) : Int
  /-- `lhs % rhs`, or `^err` with `1` if `rhs` is `0`. -/
  insn mod (lhs rhs : Int) (^err (code : Int)) : Int
  /-- Exponentiation, which the semantics leaves out. -/
  insn pow (lhs rhs : Int) : Int
  insn lt (lhs rhs : Int) : Bool
  insn le (lhs rhs : Int) : Bool
  insn eq (lhs rhs : Int) : Bool
  insn ne (lhs rhs : Int) : Bool
  insn not_ as "not" (x : Bool) : Bool
  insn and_ as "and" (lhs rhs : Bool) : Bool
  insn or_ as "or" (lhs rhs : Bool) : Bool
  /-- Append `x` to the run's output. -/
  insn print (x : Int) : Unit
  /-- Count, and return how often `tick` has run. -/
  insn tick : Int
  /-- A number from `0` to `n`, chosen by the oracle. -/
  insn pick (n : Int) : Int
  /-- A cell of an `Int`, which the rules make on the machine's heap. -/
  abbrev Cell := Ref Int
  insn cellNew (value : Int) : Cell
  insn cellGet (cell : Cell) : Int
  insn cellSet (cell : Cell) (value : Int) : Unit
  /-- Run `then` if `cond` holds and `else` otherwise; a raise leaves along `^err`. -/
  insn «if» (cond : Bool) (&«then» &«else» : Flow) (^err (code : Int)) : Unit
  /-- Run `body` while `cond` yields `true`; a raise leaves along `^err`. -/
  insn loop (&cond : Bool) (&body : Flow) (^err (code : Int)) : Unit
  end «while»
```

An environment can declare an instruction before anything gives it a meaning. The translator, the checker, the printer and the reader need only the declarations. A module is built, checked, printed and read back whatever its instructions do. Semantic rules give the instructions their meaning separately ({ref "env-sem"}[Environment 7: Meaning]). A front end can cover a large language before its semantics is complete. Python's environment (`StrataPython/Dyn/Env.lean`) declares instructions for Python's operations on its universal `py.Value`, among them attribute lookup, and calls and operators with their special methods. The Python translator lowers programs to these instructions, and no rules exist for them. A front end can encode each construct of its language as an instruction first, and give the instructions their semantics later, one at a time.

## 2. Types
%%%
number := false
tag := "env-types"
%%%

A source type maps to one of four things:

* a base type, as While's `Int` does;
* an abbreviation of a type, as While's `Cell` is of `Ref Int`;
* a new primitive type, as Python's single `Value` is;
* a datatype, as While's `IntList` is, and its `Flow`, which describes how a region body ended.

Two styles are in use.

In the _typed_ style, as in While, Dyn types follow source types, so the checker catches lowering mistakes. A translator that passes a `Bool` where an `Int` belongs builds a module that is not well formed.

In the _universal_ style, as in Python, one type, `py.Value`, holds every Python value, so the checker cannot tell an `int` from a `str`. The instructions' rules would check such types when a program runs, as Python does, but Python's environment has no rules yet. Base types still appear where the IR needs them: `base.Bool` for the conditions `branch` takes, `base.Ref` for cells, `base.Except` for results that may raise, `base.Fn` for function references, and `base.Loc` for frames.

Literals exist only at base types: unit, booleans, integers, floats, strings, function references, and the references to ghosts that only a contract may use (`const ghost`). A literal of a language's own type is a base constant followed by a boxing instruction, such as Python's `py.intLit`.

::::deepDive "datatypes and positivity"
* A datatype's constructors become ordinary instructions named in the enclosing namespace: `base.ok`, `while.nil`, `while.next`. Its eliminator is the terminal instruction `T.case`, named under the type (`base.Except.case`), with one successor per constructor in declaration order, each receiving that constructor's fields. Reordering constructors silently changes every case site; the builder tests pin this with a swapped-order example (`hSwapped`).
* Two datatypes in one namespace cannot share a constructor name without `as "…"`. Python prefixes its `Completion` constructors (`completionNormal`, `completionReturn`, …).
* A datatype may recurse only through `+` parameters: `Ref (+a)`, `Sequence (+a)`, `Except (+e) (+a)`. A declared `type Map (k) (+v)` lets recursion go through `v` and not `k`. In a list literal each element takes the polarity of the position the literal fills.
* Reserved Lean names in an environment block: `env`, `names`, `mem_env`, `nameSet`, `Internal`, and `to` followed by the parent's name, such as `toBase`. A type `T` declares `T.ref`, `T.name`, `T.name_ref` and `T.decl_ref`, and a datatype also `T.case` and `T.Val`, its Lean type in the executable semantics, so none of these is a constructor name.
* Environment annotations are generic (`Env α`), but the IR, the builder and the DSL all fix `α := Unit`.

:::sources
Sources: `StrataDyn/DSL.lean`, `StrataDyn/DSL/Check.lean`, `StrataDyn/Base.lean`, `StrataDyn/Env/Data.lean`, `StrataDyn/IR.lean`, `StrataPython/Dyn/Env.lean`.

:::

::::

## 3. Instructions
%%%
number := false
tag := "env-ops"
%%%

An instruction's _signature_ gives its type parameters, its operands, its result type, its successors and its regions. A _successor_ is a place to which the instruction may transfer control. The signature gives each successor a name and a _payload_: the types of the values the instruction passes on when it transfers there. For example, `Except.case` has two successors, `ok` with payload `[a]` and `error` with payload `[e]`.

A _terminal_ instruction has no result and ends a block. `jump`, `branch` and every `T.case` are terminal.

An instruction that is not terminal either falls through to the next instruction with its result, or leaves along one of its successors. So every successor of such an instruction is a _failure successor_, whatever its name: leaving along it is how the instruction reports a failure. A _raising instruction_ is one with a failure successor, by convention named `^err`. On failure it transfers to the handler block and supplies the exception as the payload. The running example's division is one:

```leantext
insn div (lhs rhs : Int) (^err (code : Int)) : Int
```

Every instruction declares an _effect_, an upper bound on what the operation itself may do. `pure` reads no mutable state, though it may allocate. `reads` may read mutable state. `calls` may run code that the module does not show, such as a user-defined method, and that code may change any state. The methods that the operation looks up on an operand, or on an object that an operand holds, count as such code, built-in methods included, such as the `__next__` of a Python built-in iterator; only the operation's own fixed computation does not. `writes` may change state itself. The effect comes first, as in `pure insn refNew` and `reads insn refGet`, and an instruction without one is `writes`. While declares none, so every instruction it declares with `insn` is `writes`.

Effects matter for contracts. The checker rejects a `writes` operation in a contract clause, so an operation can appear in a contract only if its effect is declared weaker. Nothing checks a declared effect against the rule: the checker trusts every part of it. An operation that does more than its declared effect allows makes every contract that applies it wrong. Three examples are an operation declared `pure` that reads state, one declared `pure` or `reads` that runs code the module does not show, and one not declared `writes` whose own computation changes state. The checker also trusts a rule about failures, for every instruction that is neither terminal nor declared `writes`. The instruction reports a failure only through a failure successor, never as an `error` value that it returns. And when a region that _may propagate_ returns `error`, the owner leaves along one of its failure successors: it never uses the error as a value, and never passes it to another region. A region may propagate when its owner declares a failure successor, and declares the region's result type as a `base.Except`. An operation that breaks either rule makes every contract that applies it wrong too. A clause that applies a `calls` operation is well defined only where the code it runs changes no state, and a consumer must show that before it relies on the clause. Leaving an instruction `writes` is always sound; it only keeps the instruction out of contracts (`docs/Dyn.md`, §1, "Effects", "Failures" and "The trust base").

A _region_ is a nested body that an instruction owns and runs, as in MLIR. While's loop runs its condition and its body as regions:

```leantext
insn loop (&cond : Bool) (&body : Flow) (^err (code : Int)) : Unit
```

_Type parameters_ make one instruction serve many types: `refGet [a]` reads through a ref to a cell of any type. A parameter of kind list, with a `spread` variadic, gives an instruction one operand per element of a list of types. The typed call `callCode` ({ref "env-calls"}[Environment 4: Functions and calls]) takes one operand per argument of the function it calls this way.

::::deepDive "the `insn` syntax, exactly"
* Binders come in a fixed order: arguments `(x y : τ)`; at most one variadic, `(*xs : τ)` for any number of operands of type `τ` or `(*xs : cs)` for one operand per element of the list `cs`; regions `(&r (p : τ) : ρ)`, entered with `p` and left with a `ρ`; successors `(^k (y : τ))`. `(^k)` passes nothing, and `(&a &b : ρ)` or `(^a ^b)` declares several alike. Successor payload names are documentation; only their types are kept.
* `[a (cs : list)]` declares kinded type parameters, which share one scope in the order written. A list parameter is the argument of a list parameter (`Fn cs r`), or is spliced into a list literal, at most once per literal and at any position (`Fn [*cs, Value] r`).
* An effect, `pure`, `reads`, `calls` or `writes`, may come first: `pure insn mkTuple`, `pure terminal insn jump`. A datatype's constructors and its case are `pure`. Environment refinement compares effects, so an instruction that an environment refinement turns into a constructor must be declared `pure`.
* `terminal insn` declares a terminator, with no result type. `abbrev n (a) := τ` expands where it is used and declares nothing. `namespace`/`end` and `open` scope names; `as "s"` gives an environment name different from the Lean name (`insn not_ as "not"` is `while.not` and `While.not_`). `def` is reserved and rejected.
* A name in a type resolves to a type parameter, then the namespace chain innermost-first, then the `open`ed namespaces; two matches through `open` is an error. Instructions cannot mention instructions.
* Every mistake is reported at its syntax, all in one pass, and nothing is emitted if there is one.
* A very large `environment` block is slow to elaborate. Split a large vocabulary along an `extends` chain ({ref "env-layer"}[Environment 6: Layering]).
* The emitted proofs use `decide`, `decide +kernel` and `simp`, never `native_decide`. In a public module, a `decide +kernel` that evaluates `env` (a `Func.WF` test, for instance) needs `import all` of the declaring module.

:::sources
Sources: `StrataDyn/DSL.lean`, `StrataDyn/DSL/Syntax.lean`, `StrataDyn/DSL/Check.lean`, `StrataDyn/Env.lean`, `StrataDynTest/DSLScaleTest.lean`.

:::

::::

## 4. Functions and calls
%%%
number := false
tag := "env-calls"
%%%

A function returns one value. A function that can raise returns `base.Except E T`: either `base.ok` with a result or `base.error` with an exception. The return convention is the language's choice. While returns `base.Except Int T` from every function that may raise and plain `T` from the others. A language may instead return `base.Except` from every function. Every call site is then alike. Both functions of the running example may raise, so both return `base.Except` under either convention.

The base's function type and its call use list parameters: the type `Fn` has a list parameter `as` for the argument types, and the call has a list parameter `as`, then a type parameter `r`.

```leantext "The function type and its call in the base"
  /-- `base.Fn as r`, a typed code pointer: to a function that takes arguments of the types
  `as`, in order, and returns an `r`.  A function reference has its target's `Fn` type,
  `Func.codeType`.  A datatype may recurse through `r`. -/
  type Fn (as : list) (+r)
  /-- `base.callCode`, a call of the function `f` points to: one argument per element of
  `as`, of that element's type.  The callee may change state. -/
  writes insn callCode [(as : list) r] (f : Fn as r) (*args : as) : r
```

A call is `base.callCode` on a value of the function type `base.Fn [args] ret`. When the callee may raise, the call is followed by `base.Except.case`, which branches to the success continuation or to the handler. In the running example's `main` the call takes two lines, after the argument `n - 10` is computed. The folded print shows the function reference `@mean` in place of the value `%code.0` that it defines:

```dyn
      %t.0 : base.Int = while.sub(%n.0, 10)
      %r.0 : base.Except(base.Int, base.Int) = base.callCode[[base.Int, base.Int], base.Except(base.Int, base.Int)](@mean, %n.0, %t.0)
      base.Except.case[base.Int, base.Int](%r.0) ^ok.0() ^raise.0()
```

::::deepDive "calling-convention obligations"
* A function reference's type must be the callee's `Func.codeType`, built from the function's parameter types and its return type. The typed emitter `Emit.code` ({ref "tr-build"}[Translator 2: The builder]) takes that type from the expected type of its result, and the untyped `Build.emitFunc` takes it as `ty`. Module well-formedness checks each function reference's type against its target's `Func.codeType`.
* The builder names the value of every function reference with the stem `code`, so the full print shows `%code.0 : base.Fn(…) = const @mean`.
* A value of type `base.Fn as r` is a _closure_ when a module runs: a function of the module together with the values bound to its first arguments. When a module runs, a function reference is the closure that binds nothing. Rules bind arguments with `bindFn` and `bindAll` and call closures with `callFn` ({ref "env-sem"}[Environment 7: Meaning]).
* While's may-raise analysis is a syntactic scan. A function may raise if its body contains a `raise`, a `/` or `%`, a region-owning instruction, or a call of a function that may raise. The scan counts a `/` inside a `try`, so `mean` may raise, and so does `main`, which calls it.

::::

## 5. State
%%%
number := false
tag := "env-state"
%%%

The machine owns a _heap_ of _cells_. A cell holds one value, of a fixed Lean type. A _ref_ is a value that names a cell: a value of type `base.Ref T` names a cell holding a `T`. The translator makes a cell with `base.refNew`, which returns the cell's ref. It reads and writes the cell with `base.refGet` and `base.refSet`. A rule makes, reads and writes cells with `newRef`, `readRef`, `writeRef` and `modifyRef`.

The _world_ is the rest of a language's run-time state: a Lean record that rules read and write. Output and counters belong there.

While shows both. `ref e` makes a cell with `base.refNew`. `Cell` abbreviates `Ref Int`, and the rules of `cellNew`, `cellGet` and `cellSet` make, read and write its cells on the same heap. `print` appends to the world's output.

::::deepDive "refs and the machine's checks"
* A ref may go anywhere a value goes: into a datatype, through `base.Except`, into the world, and out of a rule.
* A ref holds a proof, from the run token, that its location is a cell. The theorem `no_forge` states that no term generic in the run token is a raw ref, so no rule can turn a number into a ref at every token ({ref "inside-prims"}[Inside the execution DSL 2: The primitives]). It does not show that a rule reaches only the refs it is given: a rule can still build a ref at the machine's token classically. That property is what a rule's certificate states ({ref "wip-cert"}[Proofs about runs 1: Certificates for rules]).
* The machine checks every access through a ref: the location must be a cell of the heap, holding a value of the Lean type the access expects. A failed check ends the run with the fault `badCell`.
* A language may also keep a heap of its own in the world, with its own checks for a dangling ref.

::::

## 6. Layering
%%%
number := false
tag := "env-layer"
%%%

`environment Lang extends Parent` makes the child an _environment refinement_ of the parent: it has every declaration of the parent, with the same shape. The emitters and other generated references of an environment `E` require only `[E.env ≼ env]`, so they emit into a function over `E` or over any environment that refines `E`. A builder helper written under `[base ≼ env]` serves every language. Environment refinement is unrelated to the trace refinement of modules ({ref "run"}[Testing]).

A large vocabulary splits along a chain. A JavaScript front end might declare core JavaScript, then a host layer that extends it.

::::deepDive "environment refinement"
* `t ≤ s` (`Env.Le`) is name-based, not positional: every type, datatype and instruction of `t` resolves in `s` to the same declaration. An abstract type may become a datatype in the child, and an instruction may become a constructor or a case.
* `≼` (`RefinedBy`, scoped in `Strata.Dyn`) is the class form. Each `environment E extends P` generates an instance `[E.env ≼ e] : P.env ≼ e`, named `to` followed by the parent's name (`toBase`), so instance search climbs the whole chain.
* A child's semantic table covers its ancestors' instructions with their rules, and its world embeds its parent's parts ({ref "inside-env"}[Inside the execution DSL 1: The environment and its extensions]). `InheritTest` (`StrataDynTest/Exec/InheritTest.lean`) runs the parent's programs in the tables of two children, `ExKid` of the test environment `Ex` and `WhileKid` of While. Each run ends as it does in the parent's table, with the same result and the same number of steps.
* An environment has one parent. Multiple parents, `refine data` and `def` instructions are not implemented.
* Python's translator is written at the concrete `Py.env`, and While's at `While.env`. Neither is a worked example of one translator reused in a refinement.

:::sources
Sources: `StrataDyn/Env/Refine.lean`, `StrataDyn/DSL.lean`, `StrataDyn/DSL/Elab.lean`.

:::

::::

## 7. Meaning
%%%
number := false
tag := "env-sem"
%%%

A _semantic rule_ is a Lean function that gives one instruction its meaning. Rules are written beside the environment and name Lean types only. Each type of the environment gets a Lean type:

* `@[dyn_type T] d` makes the Lean type `d` the meaning of the primitive type `T`, as `attribute [dyn_type Base.Int] Int` does for the base;
* `#dyn_types E` generates a Lean inductive for each datatype of `E`, one constructor per Dyn constructor: `While.IntList.Val` and `While.Flow.Val`;
* the engine interprets `base.Ref` and `base.Fn` itself, and an abbreviation is its expansion.

`@[dyn_sem o] r` registers the rule `r` for the instruction `o`. The key `o` is the instruction's Lean name, `While.div`, which its typed emitter shares. A total instruction without successors or regions takes a _pure rule_, a plain function:

```leantext
@[dyn_sem While.add] def add (a b : Int) : Int := a + b
```

Any other rule returns a `Sem ε E α`, a description of what the rule does. The rule is written with `do`, and the machine runs the description ({ref "inside-prims"}[Inside the execution DSL 2: The primitives]). A rule takes its operands at their Lean types, then one `Region` per region, then one target per successor. A _target_, in a rule, is what fills a successor at Lean types. For example, `err : Target E [Int]` stands for the `^err` successor, whose payload is one `Int`, and `jump err e` leaves along it with `e`. A rule that loops also takes a _state_, `st : Option S`, of a Lean type `S` it chooses, and its instruction's `Again E S`. Its first run has `st = none`. `jump again s` runs the instruction again, on the same operands, regions and targets, with `st = some s`. Here are four of While's rules, verbatim:

```leantext "While's rules (excerpts)"
@[dyn_sem While.div] def div (a b : Int) (err : Target E [Int]) : Sem ε E Int := do
  if b = 0 then jump err divByZero
  return a / b

@[dyn_sem While.print] def print (x : Int) : Sem ε E Unit :=
  modifyThe Output fun o => { o with items := o.items.push x }

@[dyn_sem While.cellGet] def cellGet (c : Cell σ) : Sem ε E Int := readRef c

/-- One iteration: if the condition holds, run the body and the operation again.  Its state
is `Unit`: a loop's variables are cells. -/
@[dyn_sem While.loop]
def loop (cond : Region ε [] Bool) (body : Region ε [] Flow) (err : Target E [Int])
    (_st : Option Unit) (again : Again E Unit) : Sem ε E Unit := do
  if ← runRegion cond () then
    flow (← runRegion body ()) err
    jump again ()
```

A rule reaches state through _capabilities_, instance arguments that the generated table supplies. `HasPart W P` names a part `P` of the world `W`, which `getThe`, `modifyThe` and `modifyGetThe` read and write. `HasHeap σ ε` gives access to the machine's cells, and `HasCall σ ε` to calls of closures. `TagOf σ α` is the tag of the Lean type `α`, which every access to a cell holding an `α` needs. A language declares its capabilities once, as one class with the attribute `@[dyn_lang]`, and its rules take the class from a `variable` line:

```leantext "While's capabilities"
@[dyn_lang] class Lang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  out : HasPart ε.W Output
  ticks : HasPart ε.W Ticks
  heap : HasHeap σ ε
  tagInt : TagOf σ Int

variable {σ : Type} [Store σ] [Decode σ] [Lang σ ε]
```

Constructors, case instructions, `base.refNew`, `refGet`, `refSet` and `callCode` take no rules: the table derives the first two, and the machine implements the rest. The base's terminators have rules in `StrataDyn/Exec/Base.lean`, which every language inherits. So do `base.old` and `base.cellLoc`, whose rules report a gap, since a run ignores contracts. One command checks coverage, and another generates the table that modules run against:

```leantext "Coverage and the table (StrataDyn/Examples/While/Env.lean)"
#dyn_coverage While (complete)

#dyn_sem_table WhileSem for While (world := WhileRules.World)
```

::::deepDive "rule obligations"
* Order of a rule's binders: implicit and instance binders first, in any order (the token `σ`, `ε`, `E`, one `{α : Type}` per type parameter and one `{cs : List Type}` per list parameter, and the capabilities); then the operands, the variadic operands as an `Array`, or the operands of a spread over `cs` as one `Payload cs`; then one `Region` per region; then one `Target` per successor; then, for a rule that loops, `Option S` and `Again E S`. A terminal instruction's rule returns `Sem ε E Empty`.
* A `Target`'s payload is the successor's declared payload, not the target block's parameters. A mismatch is reported at the rule: `target big of err.split: expected Target [Int, Int], got Target [Int]`.
* A rule that takes or makes a ref or a closure is generic in the token `σ`, `{σ : Type} [Store σ]`. A rule that is generic in a type `A` takes `[TagOf σ A]` only if it reaches a cell or a call at `A`.
* Registration checks a rule's type against the signature, not its meaning: rules are trusted. A table's certificate proves one fact about its rules, that each reaches only the cells and captures cells it is given; the machine checks a closure's function and signature at each call ({ref "wip-cert"}[Proofs about runs 1: Certificates for rules]). The instruction's declared effect is trusted too: nothing compares it with what the rule does ({ref "env-ops"}[Environment 3: Instructions]). What a rule's body uses, such as `implemented_by`, `@[extern]` or a `partial` definition, is for review, as elsewhere in Lean.
* Each Lean type interprets the Dyn types it is given to, and Dyn types with one Lean type share a tag: a semantics that must tell two of them apart at run time gives them distinct Lean types.
* The world is a Lean type, `Unit` by default, whose `default` value is the initial world. A world that holds refs takes the token: `(σ : Type) → [Store σ] → Type`.

:::sources
Sources: `StrataDyn/Exec.lean`, `StrataDyn/Exec/Sem.lean`, `StrataDyn/Exec/Rules.lean`, `StrataDyn/Exec/Base.lean`, `StrataDyn/Examples/While/Env.lean`; `docs/Dyn.md`, "Giving a language its semantics".

:::

::::

## 8. Design checklist
%%%
number := false
tag := "env-check"
%%%

:::checklist
For each source construct, decide:

* the Dyn type it lives at;
* whether its instruction is total, raising (with a failure successor), terminal or region-owning;
* its effect: if contracts are to apply it, the weakest of `pure`, `reads` and `calls` that bounds everything it does, since the checker trusts it; otherwise `writes`;
* where its state lives: a machine cell or the world;
* its rule.

For the language as a whole, decide:

* the function return convention, and the exception payload type;
* the world record, and its default, which is the initial world;
* which constructs keep their structure as regions;
* which choices go to the oracle.

Write the environment before the translator.

:::

:::widget "env"
With JavaScript enabled, this panel lists every declaration with its kind, its signature and its rule. The environment and its rules are printed in full in {ref "app-texts"}[Appendix C: Full texts].
:::

## 9. Encoding common features
%%%
number := false
tag := "env-defaults"
%%%

An environment encodes the following features with what Dyn provides.

* _Objects, arrays and pointers_ are stored in machine cells. The environment declares a ref type, and instructions whose rules make, read and write cells with `newRef`, `readRef`, `writeRef` and `modifyRef`, as While's `cellNew`, `cellGet` and `cellSet` do. A datatype may hold refs, including refs of itself. `HeapTest` (`StrataDynTest/Exec/HeapTest.lean`) runs datatypes that hold refs, among them a chain whose links are cells that each hold a ref to the next.
* _Classes and other per-program types_ are values of one universal type, with class tables in the world or in cells. Python's values, its classes included, are values of `py.Value`. An environment can gain types and instructions while a program is translated, with `Env.addType?` and `Env.addInsns?`. But no front end does so, the typed emitters exist only for the declarations of an `environment` command, and no rule can be registered for a declaration added later. So a typed encoding of JVM classes or TypeScript interfaces is not yet supported ({ref "missing"}[Missing features]: _Checked runtime extension of environments_).
* _Multiple results_ are a datatype per arity, such as a pair or a triple, declared in the environment. Each field of a datatype holds one value, so one datatype cannot hold a field per element of a list parameter. The caller takes the result apart with the datatype's case. No language of the package returns multiple results.
* _Closures_ are values of type `base.Fn as r`. A closure is a function of the module with values bound to its first arguments, which are fixed when the closure is made. To share mutable state, a closure binds a ref. A rule makes one with `bindFn`, or `bindAll` for a list of values, and calls one with `callFn`. Python's `py.mkClosure` takes the code at its signature and the cells it binds as a typed spread: `reads insn mkClosure [(cs : list)] (code : Fn [*cs, Value, Value] failing) (*cells : cs) : Value`. `RunTest` (`StrataDynTest/Exec/RunTest.lean`) runs closures that rules make and call, among them a closure over two cells.
* _Exceptions_ carry a payload type of the language's own, such as its universal value type, and functions return `base.Except Payload T`. While's payload is `Int`. Python's is `py.Value`, and a translated Python function returns `base.Except py.Value py.Value`.

::::deepDive "where these encodings come from"
* A heap kept in the world needs its own checks for a dangling ref in the rules. The machine checks each access to its own cells.
* Python's closures and calls are described in `docs/PythonToDyn.md` ("Python's environment" and "Closures"). Python builds a class at run time by calling its body function ("Classes").

:::sources
Sources: `StrataPython/Dyn/Env.lean`; `docs/PythonToDyn.md`; `StrataDyn/Exec/Sem.lean` (`bindFn`, `bindAll`).

:::

::::

# Translator
%%%
number := false
tag := "tr"
file := "translator"
%%%

Dyn gives a translator three pieces of infrastructure. The _builder_ ({ref "tr-build"}[Translator 2: The builder]) allocates values and labels, opens and closes blocks, emits instructions through a typed emitter per instruction, and checks each function when it is finished. The _checker_ decides well-formedness. `Build.run` returns a checked function, a value of `{fn : Func env α // fn.WF}`. `Module.ofChecked` assembles checked functions, and any ghosts, into a `Module`. It checks only what concerns the module as a whole: that names are distinct, that each function reference and ghost reference fits its target, and that a ghost's initializer names only ghosts declared before it. The _printer and reader_ ({ref "tr-print"}[Translator 8: Printing and reading]) show what was produced and read it back. A translator walks the generated AST and calls the builder.

A translator must never lower a construct that it cannot express faithfully to instructions that mean something else. Analyses and runs would then trust a wrong program, and nothing in the module would mark the spot. A translator has two honest alternatives.

The first is to _reject it_, with a diagnostic at its source range. Python's translator records the diagnostic and emits `py.unsupported` in place of a rejected expression, so that the function stays well formed. It marks the whole result failed, so that no consumer analyses it.

The second is to _declare an instruction for it whose meaning is left open_. The construct then appears in the module as itself. An analysis that has no rule for the instruction still relies on its declaration, so the declaration must allow everything the construct may do:

* keep the default effect, `writes`, since a declared `pure`, `reads` or `calls` is trusted ({ref "env-ops"}[Environment 3: Instructions]);
* declare a failure successor, such as `^err`, if the construct may raise: an instruction without one cannot raise, since its rule can leave only with its result, along one of its successors, or with a fault;
* give it a result type that holds every value the construct may produce, such as the language's universal type.

An analysis must then assume that the instruction may return any value of its result type, change any state the language has, or raise along its failure successor. With the execution engine, a rule may also report a semantic gap, as While's `pow` does. A run that reaches the gap ends with the fault `gap` ({ref "run"}[Testing]).

## 1. The shape you produce
%%%
number := false
tag := "tr-shape"
%%%

A function has parameters, a return type, an optional contract and a list of blocks. The first block is the entry, and its parameters are the function's parameters. An extern function has no blocks. Every instruction defines one named value; an instruction with nothing to return produces a `base.Unit`.

Block parameters take the place of phi nodes. A successor binds a prefix of the target's parameters, and the instruction that takes the transfer supplies the rest.

`ret(v)` is the terminator that leaves the enclosing body with `v`. It is the printed form of a jump to the body's exit label, `Label.exit`. In a function it returns `v`, and in a region it ends the region with `v`. The builder emits it with `Emit.ret`, which takes the body's exit and `v`.

In `mean`, `while.div(%s.0, %d.1) ^catch.0(%n.1, %d.1, %s.0, %i.0)` binds four of the handler's five parameters, and the division supplies the fifth, `%e.0`, when it fails.

::::deepDive "`Func.WF`, every obligation"
* A function is extern exactly when it has no blocks. A defined function's entry block takes exactly the function's parameters, ids and types.
* Labels are distinct across the function, regions included, and none is `Label.exit`.
* Value names are distinct, and every defined value has a name.
* No value is defined twice, regions included.
* No transfer targets an entry block, the function's or a region's. Every loop needs a header block of its own: in `mean`, `entry.0` jumps to `head.0`.
* Each transfer supplies exactly the target's parameter types, the pre-bound arguments followed by the successor's payload, with exact type equality and no subtyping.
* Operands and results match the instruction's signature at its type arguments.
* An instruction applies an operation that has a result type, and a terminator one that has none.
* A constant has its literal's type, and a function reference has a `base.Fn` type. Which `base.Fn` type, and a ghost reference's type, the module checks against the target.
* There is one successor per declared successor and one region per declared region. Each region's entry block takes exactly the region's declared parameters. Each `ret` passes a value of its body's result type: the function's return type, or the region's declared result type.
* Every block is reachable from its body's entry, the function's or a region's.
* Every use is dominated by its definition: every path from the entry to the use passes through the definition, earlier in the use's block or in a block above it. An instruction's successor arguments are used _before_ it, so a handler never sees the failing instruction's result. A region also sees everything in scope at the instruction that owns it.
* Its contract is well formed: each clause and frame region has its type and applies no `writes` operation, at any depth, and sees only the parameters and its own values. The cells that a frame names are parameters of type `base.Ref`, each named once.
* Its `ensures` clauses are `free` exactly when it is extern, and no `requires` clause is ever `free`.
* In a clause's or a frame region's own blocks, a failure goes to a _failure block_, whose instructions are only constants. In a `requires` clause it goes to a block that gives `false`, or that ends in `unreachable`; in an `ensures` clause, to one that gives `false`, or `true` if the clause is `free`, or that ends in `unreachable`; in a frame region, to one that ends in `unreachable`. A failure in a region nested in them goes to a block that ends in `unreachable`, or, if the region may propagate, to one that passes it on with `base.error`. Every block of them ends in control flow, and none has a cycle.
* Only `ensures` clauses apply `base.old`, and an `old` region sees, from outside it, only the parameters, the clause's constants and the parameters of the regions that enclose it.
* The body names no ghost: only the contract does.

The checker stores no dominator tree. It states scoping with trees that it does not keep. A _tree_ of a body gives each block but the entry a parent, which is a point inside another block. A tree is _legal_ when every chain of parents reaches the entry and every transfer into a block leaves from its parent or below it. A function is well scoped when some legal tree of each body puts every use below its definition. With every block reachable, this condition is exactly dominance (`Func.reachable_scopable_iff`). The checker decides it by computing the immediate-dominator tree and testing each use against it. `Func.checkDom_iff` states that this check, `Func.checkDom`, succeeds exactly when every body has distinct labels, its entry reaches each of its blocks, and every use is dominated by its definition. `Func.scopeDiagnostics` explains a function that fails these checks: it names each unreachable block, and each use out of scope with a path from the entry that avoids its definition. `Build.run` does not call it ({ref "tr-ann"}[Translator 7: Annotations]).

:::sources
Sources: `StrataDyn/WF.lean` (`Func.WF`), `StrataDyn/ContractRegion.lean`.

:::

::::

## 2. The builder
%%%
number := false
tag := "tr-build"
%%%

The translator runs inside a builder. The builder allocates fresh values and labels, opens one block at a time, emits instructions into it, and closes it with a terminator. Labels are allocated before their blocks exist, so forward jumps work. Each value and label has a _stem_. The builder numbers values and labels `stem.n`, per stem, when the function is finished. Finishing a function also drops the blocks that its entry cannot reach, checks for misuses of the builder, and checks that the function is well formed. It returns either a checked function or a failure. The checked functions are then assembled into a module.

A _block_ has typed parameters. A _target_ is what a call supplies for a successor: a block, with values for a prefix of its parameters. When the instruction transfers to the target, the block receives the target's values first and then the payload, so the payload must have the types of the block's remaining parameters.

The typed builder gives each of these a Lean type.

A value is `Val env t`, where `env` is the function's environment and `t` is a `TypeExpr env`. The environment is an explicit argument, as it is for `TypeExpr`, so an annotation reads `Val W Base.Int`. The type is a phantom: at run time a value is its id.

A block is `BlockRef env ps`, where `ps` lists the types of its parameters. Opening a block gives back its parameters as typed values.

A target is `Target env ps`, where `ps` lists the types it still expects. `goto` makes the target of a block with nothing bound, and `bind` supplies the next value, removing its type from `ps`. An emitter takes a target for a successor when `ps` is the successor's payload, so a jump to a region's exit has to bind a value of the region's result type.

A body's _exit_ is a target too. `Emit.func` emits a function: it opens the entry block with the function's parameters, and gives its body their values and the function's exit, a `Target env [r]` where `r` is the function's result type. A region's body is given its region's exit in the same way. `ret exit v` leaves a body by its exit with `v`, so Lean checks `v` against the body's result type.

The constructors of `BlockRef` and `Target` are private: a block comes from `Emit.freshLabel`, and a target from `goto`, `bind`, `bindAll` or the exit that a function's or a region's body is given.

An _emitter_ is a Lean function that emits one instruction. The `environment` command generates one for each instruction, constructor and case instruction, under the instruction's own Lean name, such as `Base.refNew`, `Base.Except.case` or `While.div`. Its Lean type is the instruction's signature over type expressions.

An emitter's arguments come in one order: the operands, then the successors and regions, then an optional result name, then an optional annotation. Each type parameter is an implicit argument, which Lean infers by unifying the operands' types, the successors' payloads and the expected result with the signature. A variadic operand is an `Array` of values, and a spread is a list of values written `vals[x, y]`. A region is a Lean function of its parameters and its exit, which emits the region's body. A terminal instruction's emitter has no result and closes the block. The emitters run in any monad that emits into a function: `BuildM`, or a front end's monad over it built from `StateT`, `ReaderT` and `ExceptT`. The instruction itself, the `InsnRef` that the untyped builder takes, is `o.ref`, such as `While.div.ref`.

An environment gets emitters when its module imports `StrataDyn.Build.Typed`. `dyn_emitters Base` generates the base's emitters, from the record the `environment` command leaves. While's environment module imports the typed builder only privately, so While's emitters are private to that module, and the listings below generate them with `dyn_emitters While`.

Where `Strata.Dyn.Emit` is open, `let% x ← e` binds `x` as `let x ← e` does. It also names the value or block that `e` returns after the binder, if `e` made it and nothing else named it. A value without a name takes its instruction's name, and a block without one is `bb`:

```leantext "let% and the names it gives"
let% cell ← Base.refNew zero                       -- %cell.0
let% r ← Base.refGet (← Base.refNew zero)          -- %refNew.0, then %r.0
let% x ← Base.refGet cell (result := n "read")     -- %read.0
let% ok ← Emit.freshLabel [Base.Int]               -- ^ok.0
let% err ← Emit.freshLabel [Base.Int] "fail"       -- ^fail.0
let% x ← Emit.startBlock₁ ok                       -- %x.0, the parameter of ^ok.0
```

The next listing builds the running example's `mean` with the typed emitters. Its print is the folded print of {ref "app-texts"}[Appendix C]. In it, `W` is `While.env`, `R` is `Base.Except Base.Int Base.Int`, and `n s` is the one-component name `s`. `Emit.func` opens `entry.0`, and gives the body the parameters' values, `n₀` and `d₀`, and the function's exit, `funcExit`:

```leantext "mean, built with the typed emitters (docs/dyn/checks/TypedMean.lean)"
def mean : Built :=
  Emit.func (n "mean") [(n "n", Base.Int), (n "d", Base.Int)] R ()
      fun (.cons n₀ (.cons d₀ .nil)) funcExit => do
    let% head ← freshLabel [Base.Int, Base.Int, Base.Int, Base.Int]
    let% body ← freshLabel []
    let% exit ← freshLabel []
    let handler ← freshLabel [Base.Int, Base.Int, Base.Int, Base.Int, Base.Int] "catch"
    let k₀ ← int (n "k") 0
    let k₁ ← int (n "k") 1
    Base.jump (head.goto.bindAll vals[n₀, d₀, k₀, k₁])
    -- The loop header takes every variable in scope.
    let (nd₁, n₁) ← param (n "n") Base.Int
    let (dd₁, d₁) ← param (n "d") Base.Int
    let (sd, s) ← param (n "s") Base.Int
    let (id, i) ← param (n "i") Base.Int
    Build.Raw.startBlock head.label #[nd₁, dd₁, sd, id]
    let% t ← While.le i n₁
    Base.branch t body.goto exit.goto
    let _ ← Emit.startBlock body
    let% t ← While.add s i
    let t₁ ← While.add i (← int (n "k") 1) (result := n "t")
    Base.jump (head.goto.bindAll vals[n₁, d₁, t, t₁])
    let _ ← Emit.startBlock exit
    -- The handler in effect is `catch`: the division's `^err` binds the variables first.
    let% t ← While.div s d₁ (handler.goto.bind n₁ |>.bind d₁ |>.bind s |>.bind i)
    let% ok ← Base.Except.ok t
    ret funcExit ok
    let (nd₂, _) ← param (n "n") Base.Int
    let (dd₂, _) ← param (n "d") Base.Int
    let (sd₁, _) ← param (n "s") Base.Int
    let (id₁, _) ← param (n "i") Base.Int
    let (ed, e) ← param (n "e") Base.Int
    Build.Raw.startBlock handler.label #[nd₂, dd₂, sd₁, id₁, ed]
    let% t ← While.sub (← int (n "k") 0) e
    let% ok ← Base.Except.ok t
    ret funcExit ok
```

`Emit.startBlock` names every parameter of a block after one stem. To name each parameter, `mean` makes its block parameters with `param` and opens the block with `Build.Raw.startBlock`, from the untyped layer, which takes the block's label and the parameters' declarations. Lean does not check those parameters against the block's types; the check when the function is finished does.

`ret funcExit ok` leaves the function with `ok`. The exit expects the function's result type, so Lean infers the type of `ok`, `R`, from it, and rejects a value of another type.

:::widget "trace"
With JavaScript enabled, this panel steps through the builder calls of the `mean` listing, with the print of `mean` so far.
:::

A call goes through a value of a function type ({ref "env-calls"}[Environment 4: Functions and calls]). `code` makes a function reference at the type its result is expected to have, the callee's `Func.codeType`. `callCode`'s type arguments are inferred from the reference's type, and `vals[…]` gives one operand per argument. A call of a function that may raise is followed by `Except.case`, whose `ok` successor expects the result and whose `error` successor expects the exception:

```leantext "main, built with the typed emitters (docs/dyn/checks/TypedMean.lean)"
def main : Built :=
  Emit.func (n "main") [(n "n", Base.Int)] R () fun (.cons n₀ .nil) funcExit => do
    let% ok ← freshLabel [Base.Int]
    let% raise ← freshLabel [Base.Int]
    let% t ← While.sub n₀ (← int (n "k") 10)
    let f : Val W (Base.Fn [Base.Int, Base.Int] R) ← code (n "mean")
    let% r ← Base.callCode f vals[n₀, t]
    Base.Except.case r ok.goto raise.goto
    let% x ← startBlock₁ ok
    let _ ← While.print x (result := n "u")
    let% ok ← Base.Except.ok x
    ret funcExit ok
    let% e ← startBlock₁ raise
    let% error ← Base.Except.error e
    ret funcExit error
```

::::deepDive "builder API and gotchas"
The builder monad is `BuildM env α := StateM (Build.State env α)`, where `α` is the annotation type. The typed functions below are in `Strata.Dyn.Emit` unless noted, and run in any monad `m` with `MonadBuild env α m`. Those that emit constants or base terminators need `[base ≼ env]`. `info` is an optional annotation, defaulting to the one `withInfo` set.

:::table +header
*
  * Function and arguments
  * Returns
  * Block state
*
  * `func (name : Name) (params : List (Name × TypeExpr env)) (r : TypeExpr env) (info : α) (body : Vals env (params.map (·.2)) → Target env [r] → BuildM env α β) (entry : String := "entry")`
  * `Except (FailedFunc env α β) ({fn : Func env α // fn.WF} × β)`, `Build.run`'s result (a plain function)
  * opens the entry block for `body`, which ends with none open
*
  * `param (stem : Name) (t : TypeExpr env)`
  * `ValDecl env × Val env t`, a fresh value
  * any
*
  * `freshLabel (ps : List (TypeExpr env)) (base : Option String := none)`
  * `BlockRef env ps`
  * any
*
  * `startBlock (l : BlockRef env ps) (stem := v)`
  * `Vals env ps`, its parameters
  * none open; opens `l`
*
  * `startBlock₁ (l : BlockRef env [t]) (stem : Option Name := none)`
  * `Val env t`, its parameter
  * none open; opens `l`
*
  * `int`, `bool`, `str`, `float`, `unit`, each `(stem : Name)`, the value, `(info)`
  * `Val env Base.Int` and so on
  * open
*
  * `code (target : Name) (info)`
  * `Val env t`, at the expected type `t`
  * open
*
  * the emitter `o`: operands, successors and regions, `(result : Option Name := none) (info)`
  * `Val env r`; `Unit` for a terminal instruction
  * open; a terminal instruction closes it
*
  * `jump (k : Target env [])`, `branch (cond : Val env Base.Bool) (t f : Target env [])`, each with `(info)`; the base's emitters `Base.jump` and `Base.branch` do the same
  * `Unit`
  * open; closes it
*
  * `ret (exit : Target env [t]) (v : Val env t) (info)`
  * `Unit`
  * open; closes it
*
  * `BlockRef.goto l`, `Target.bind k v`, `Target.bindAll k vs` (plain functions)
  * `Target env ps`
  * any
*
  * `Build.withExit (r : TypeExpr env) (body : Target env [r] → m β)`
  * `β`, from `body`, which is given the exit of the innermost open body, a region's or else the function's
  * any
*
  * `Build.Raw.startFreshBlock (params : Array (ValDecl env) := #[]) (base : String := "bb")`
  * `Label`
  * none open; opens a fresh label
*
  * `Build.Raw.startBlock (label : Label) (params : Array (ValDecl env) := #[])`
  * `Unit`
  * none open; opens `label`
*
  * `Build.withInfo (info : α) (act : BuildM env α β)`
  * `β`
  * any
*
  * `Build.run (name : Name) (retType : TypeExpr env) (info : α) (act : BuildM env α β)`
  * `Except (FailedFunc env α β) ({fn : Func env α // fn.WF} × β)` (a plain function)
  * starts and ends with none open
*
  * `Build.build`, the same with `β := Unit`
  * `Except (FailedFunc env α Unit) {fn : Func env α // fn.WF}`
  * the same
*
  * `Module.ofChecked (name : Name) (fs : Array {f : Func env α // f.WF}) (info : α) (ghosts := #[])`
  * `Except (Array Name) (Module env α)`; the error names the functions and ghosts at fault, but all the functions if two functions share a name, and all the ghosts if two ghosts share a name or a ghost has a function's name
  * after building

:::

* An emitter's argument of the wrong type, two operands that disagree on a type argument, a spread too short, a successor whose payload does not match and a result annotated with the wrong type are each a Lean error at the argument, naming both types.
* `Val.ofId` and `Val.cast` give a value whatever type they are told, for a type known only when the builder runs, and `Build.withExit r` gives an exit that expects whatever `r` it is told. Lean checks nothing about them. `Build.run` does, and rejects the function if a claimed type is wrong. `Emit.func` and the region emitters give `Build.withExit` the body's own result type.
* Every exit is the label `Label.exit`, which leaves the innermost body being emitted, a region's or the function's. An instruction given an exit that does not leave the innermost open body is a misuse, and `Build.run` rejects the function: the exit of an enclosing region, of a region that has ended, or the function's exit inside a region. `Build.checkedTarget` makes this check and gives the untyped target, for the untyped layer. `Target.rawUnchecked` gives the untyped target without this check, and nothing later makes it: a function's exit used inside a region that way silently becomes the region's exit.
* A `FailedFunc` carries the builder's result, the misuses and the function it emitted. With no misuses, it says only that the function is not well formed ({ref "tr-ann"}[Translator 7: Annotations] shows how to find out why).
* Types are written as _handles_: `Base.Int`, or `Base.Except Base.Int Py.Value` for an applied type. A handle stands for a type expression, a type argument or a list of types, whichever the place expects.
* A misuse, such as emitting with no block open, opening a block while one is open, or leaving a block open at the end, is recorded as a string and not thrown.
* The builder has no `isOpen` query, but its state records the open block: `body.label` is `some l` while the block `l` is open. Python's builder reads it so in its own `isOpen` (`StrataPython/Dyn/Build.lean`).
* The first block _finished_ is the entry.
* Blocks that the entry cannot reach are dropped when the function is finished, so dead code needs no special case. A label that a kept block targets but that is never started makes the function ill formed.
* Value-name stems must read back: no empty, all-digit or dotted segments. A name spelled like a keyword of the printed dialect, such as `ret` or `unit`, prints between pipes and reads back. A stem is a structured `Name`: `x.cell` is two segments.
* A contract is emitted in the function's builder, with `Build.requires`, then `Build.ensures`, then the frames `Build.reads` and `Build.writes`; each makes its clause a region, and one out of this order is a misuse. In a clause's own blocks, a failure successor names the label that `Build.withFailureBlock` gives; in a region nested in a clause, the label that `Build.withPropagatingBlock` gives. `Build.old` emits `base.old` in an `ensures` clause, and `Build.emitGhost` emits a reference to a ghost's cell.
* `Build.buildExtern` builds an extern function, which has only a contract, `Build.ghost` builds a ghost, and `Build.stub` gives a well-formed function whose entry ends in `unreachable`. `Build.ensures` makes a checked clause unless it is given `free := true`, but an extern's `ensures` clauses must be free, so an extern built with the default is not well formed.

The _untyped builder_ is the functions `Build.emitApply` and `Build.terminate`, and the untyped layer `Build.Raw`: `Raw.freshLabel`, `Raw.startBlock`, `Raw.startBlockWith`, `Raw.startFreshBlock`, `Raw.goto`, `Raw.jump`, `Raw.branch` and `Raw.ret`. They take value ids, `o.ref`, bare labels and untyped targets, `Target.Raw`, for a front end whose types are known only when it runs. Type arguments are written as `(typeArgs := ta[…])`, or inferred from the operands' and the result's types when the builder runs, and a failure to infer them is recorded as a misuse. Nothing else is checked until `Build.run`. The typed operations are built on them. While's lowering uses the untyped builder inside a monad of its own. The monad reads the function signatures, and keeps the variables in scope, the handler in effect, and the handler labels that some edges use:

```leantext "While's lowering monad (StrataDyn/Examples/While/Lower.lean)"
/-- Lowering one function. -/
abbrev M := ReaderT LCtx (StateT LState (ExceptT String BM))
```

```leantext "While's untyped emit (StrataDyn/Examples/While/Lower.lean)"
def app {isig : InsnSig E} (stem : String) (type : TypeExpr E) (r : InsnRef E isig)
    (args : Array ValId) (succs : Array Target.Raw := #[])
    (regions : Array (BM (Dyn.Region E Unit)) := #[]) : M ValId := do
  let n := (← buildErrors).size
  let v ← build (Build.emitApply (nm stem) type r args succs regions (typeArgs := .infer))
  checkBuild n
  return v
```

`checkBuild n` fails with the first misuse the builder recorded after the first `n`, which localises a failure to the emit that caused it.

:::sources
Sources: `StrataDyn/Build.lean`; `StrataDyn/Build/Typed.lean`; `StrataDyn/Typed.lean`; `StrataDyn/DSL/Emit.lean`; `StrataDyn/WF.lean` (`Func.WF`, `Module.ofChecked`); `StrataPython/Dyn/Build.lean`.

:::

::::

## 3. Variables
%%%
number := false
tag := "tr-vars"
%%%

Front ends use one of two strategies for variables: SSA values or cells.

_SSA threading_, as in While, keeps a variable's current value as an SSA value. Joins, loop headers and handlers take every variable in scope as a parameter, and each edge passes the current values. In `mean`, `head.0` and `catch.0` take `n`, `d`, `s` and `i`, the unchanged `d` included.

_Cells_ store the variables, as in Python. Each local is a cell. The entry block makes it with `refNew`, and the code reads and writes it through its ref with `refGet` and `refSet`. Every ref is defined in the entry, which dominates every block, so every block can use every local. Block parameters are then needed only for expression joins and handler payloads.

In the cell style, `mean` makes its cells in `entry.0`, reads them in `head.0` and writes them in `body.0`. No block but the handler takes parameters.

```dyn "mean in the cell style (written by hand)"
module main {
  func @mean(%n.0 : base.Int, %d.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int, %d.0 : base.Int):
      %s.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %i.0 : base.Ref(base.Int) = base.refNew[base.Int](1)
      jump ^head.0()
    head.0():
      %t.0 : base.Int = base.refGet[base.Int](%i.0)
      %t.1 : base.Bool = while.le(%t.0, %n.0)
      branch(%t.1) ^body.0() ^exit.0()
    body.0():
      %t.2 : base.Int = base.refGet[base.Int](%s.0)
      %t.3 : base.Int = base.refGet[base.Int](%i.0)
      %t.4 : base.Int = while.add(%t.2, %t.3)
      %u.0 : base.Unit = base.refSet[base.Int](%s.0, %t.4)
      %t.5 : base.Int = base.refGet[base.Int](%i.0)
      %t.6 : base.Int = while.add(%t.5, 1)
      %u.1 : base.Unit = base.refSet[base.Int](%i.0, %t.6)
      jump ^head.0()
    exit.0():
      %t.7 : base.Int = base.refGet[base.Int](%s.0)
      %t.8 : base.Int = while.div(%t.7, %d.0) ^catch.0()
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.8)
      ret(%ok.0)
    catch.0(%e.0 : base.Int):
      %t.9 : base.Int = while.sub(0, %e.0)
      %ok.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.9)
      ret(%ok.1)
  }
}
```

Start with cells: every block can use every local. Ref-to-reg then turns them into SSA values. `refToReg m` promotes each cell that `base.refNew` makes, when its ref is used only by `base.refGet` and `base.refSet` and its content is known at each read. Each read and write is removed, and a block where contents from different edges meet takes the content as a new parameter. The `refNew` stays, unused, so that the cells made after it keep their numbers. On `mean` in the cell style, ref-to-reg gives back the SSA threading of the running example, with a handler that takes no variables:

```dyn "mean in the cell style, after ref-to-reg"
module main {
  func @mean(%n.0 : base.Int, %d.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int, %d.0 : base.Int):
      %s.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %i.0 : base.Ref(base.Int) = base.refNew[base.Int](1)
      jump ^head.0(0, 1)
    head.0(%c.4 : base.Int, %c.5 : base.Int):
      %t.1 : base.Bool = while.le(%c.5, %n.0)
      branch(%t.1) ^body.0() ^exit.0()
    body.0():
      %t.4 : base.Int = while.add(%c.4, %c.5)
      %t.6 : base.Int = while.add(%c.5, 1)
      jump ^head.0(%t.4, %t.6)
    exit.0():
      %t.8 : base.Int = while.div(%c.4, %d.0) ^catch.0()
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.8)
      ret(%ok.0)
    catch.0(%e.0 : base.Int):
      %t.9 : base.Int = while.sub(0, %e.0)
      %ok.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.9)
      ret(%ok.1)
  }
}
```

::::deepDive "what ref-to-reg needs from a front end"
* A cell is promoted only if its ref goes nowhere but to `base.refGet` and `base.refSet`, and the results of its `refSet`s are unused. A ref passed to any other instruction, stored in a value or returned stays a cell, with all its reads and writes.
* An instruction whose regions write a cell, at any depth, makes the cell's content unknown after it, on its edges and at the start of each of its regions. A read of the cell there keeps the cell as it is.
* The pass relies on two rules, which every environment and its front end must keep. A region runs only while the instruction that owns it runs, any number of times and in any order. An instruction reaches only the cells it is given, as operands or inside values it can read, so a front end passes a cell to every instruction that may read or write it. For a certified table, the certificate proves the second rule, and ref-to-reg's proof takes it from there instead of assuming it. For a table that is not certified, nothing checks it.
* The pass checks the plan it computes, applies it, and checks the module's well-formedness again. A failure returns no module, and names each function concerned with the reason.
* Python's translator goldens are run through the pass (`StrataPythonTestExtra/DynRefToRegTest.lean`).
* Dyn proves that a target that promotes a source's cells, as `PromotionOK` describes, improves on the source's behaviour, up to a bad cell, for a language whose table is certified ({ref "wip-r2r"}[Proofs about runs 2]). It is not yet proved that the pass's output satisfies `PromotionOK`. Python has no table, so the theorem does not apply to Python's modules yet.

:::sources
Sources: `StrataDyn/RefToReg.lean`, `StrataDyn/RefToRegProps.lean`, `StrataDyn/RefToRegSound/`; `docs/Dyn.md`, §3; `StrataDynTest/RefToRegTest.lean`; `docs/dyn/checks/RefToReg.lean`.

:::

::::

:::widget "cfg"
With JavaScript enabled, this panel draws each function's blocks and edges from the printed text, computes its dominator tree, and checks every use against it.
:::

## 4. Structured control flow
%%%
number := false
tag := "tr-cf"
%%%

* `if` lowers to a `branch` into two blocks and a join.
* `while` lowers to a jump to a header, a condition, a `branch` to the body or the exit, and a back edge from the body to the header.
* Short-circuit `&&` and `x if c else y` join through a block parameter that carries the value (Python).
* `break` and `continue` keep a stack of exit blocks.

```leantext "Python's `while` (StrataPython/Dyn/Translate.lean, whileStmt)"
  let head ← build (freshLabel [] "head")
  let bodyL ← build (freshLabel [] "body")
  let elseL? ← if orelse.isEmpty then pure none else some <$> build (freshLabel [] "else")
  let exit ← build (freshLabel [] "exit")
  jump head.goto
  build (startBlock head)
  transCond test bodyL.goto (elseL?.getD exit).goto
  build (startBlock bodyL)
  withExit (.loop exit head) (transStmts body)
  if ← isOpen then jump head.goto
  if let some l := elseL? then
    build (startBlock l)
    transStmts orelse
    if ← isOpen then jump exit.goto
  if ← targeted exit then build (startBlock exit)
```

In Python's translator, each block is a typed `BlockRef`, and here each takes no values. A transfer to a block is a `Target` made from it, such as `head.goto`, so Lean checks what a jump passes against what its block takes. `isOpen` says whether a block is still open: a body that ends in `break`, `return` or `raise` has closed its last block. `targeted exit` says whether a transfer names the exit block, which is opened only then.

## 5. Exceptions
%%%
number := false
tag := "tr-exc"
%%%

The translator keeps the _handler in effect_: the block to which every raising instruction's `^err` successor goes.

* At function level it is a propagate block, `raise.0` in While, that returns `base.error`.
* Inside a `try` it is the `catch` block.
* Inside a body region it is a block that yields `Flow.raise`.

`raise e` jumps to the handler with `e`. A call's error edge, from its `Except.case`, goes to the same handler. Python's `for` uses an exception edge as a loop exit: `py.next` raises `StopIteration` at the end of the iteration.

The running example shows four facts about handlers. The handler `catch.0` is entered only along the `^err` edge of `while.div`, the first line of `exit.0`. That edge leaves before the division, so `catch.0`'s dominator is `exit.0` before its first line, and the handler sees none of `exit.0`'s results. `main` has a `raise.0` block because its call's error edge uses it. `mean` has none: its label is allocated but never started, which is legal because nothing targets it. The `try`'s join label is unused in the same way, because both branches return.

::::deepDive "handler obligations"
* Values pre-bound on an `^err` edge must be defined _before_ the raising instruction.
* The handler's parameters are the pre-bound values followed by the declared payload, in that order, with exact types.
* The handler cannot use the failing instruction's result: it is not defined where the edge leaves.
* Python's builder keeps the handler in effect as a typed target, `Frame.handler : PyTarget [Py.Value]`, which takes the exception after any arguments it binds, so Lean checks that every handler a `try` installs takes the exception. The function's exit, which `return` leaves by, is the typed target `Frame.exit` (`StrataPython/Dyn/Build.lean`).
* Python lowers `try`/`finally` with a `Completion` datatype (`StrataPython/Dyn/Build.lean`, `tryFinally`), a reference for any `finally`-like construct.

:::sources
Sources: `StrataPython/Dyn/Build.lean`; `StrataPython/Dyn/Translate.lean` (`tryFinallyStmt`); `docs/PythonToDyn.md` ("`try`/`except`/`else`/`finally`").

:::

::::

## 6. Regions
%%%
number := false
tag := "tr-regions"
%%%

A region-owning instruction keeps a construct as one instruction, so an analysis sees a loop where a control-flow graph would show blocks. A region reads the values in scope at the instruction that owns it. Its transfers stay inside it, and `ret` leaves the region with its result.

Non-local exits out of a region (`break`, `return`, `raise`) need a convention. While's body regions yield a `Flow` datatype, and the owning instruction's rule jumps along `^err` on `Flow.raise`. Python's comprehension region returns an `Except`.

A region's emitter argument is a Lean function of the region's parameters and its _exit_, a target that expects the region's result. The body leaves the region by a jump to its exit. The next listing emits `mean`'s loop as `while.loop`, with its variables `s` and `i` in cells. It is from the same file as the `mean` listing:

```leantext "A region emitter (docs/dyn/checks/TypedMean.lean)"
    let _ ← While.loop
      (fun exit => do
        let% t ← While.le (← Base.refGet i) n₀
        Base.jump (exit.bind t))
      (fun exit => do
        let _ ← Base.refSet s (← While.add (← Base.refGet s) (← Base.refGet i))
        let _ ← Base.refSet i (← While.add (← Base.refGet i) (← int (n "k") 1))
        Base.jump (exit.bind (← While.Flow.next)))
      raise.goto
```

::::deepDive "region rules"
* `break`, `continue` and `return` cannot cross a region boundary: a transfer from a region's block to a block outside it is not well formed.
* Scoping is checked per body: a region's blocks must be reachable from the region's entry, and its uses dominated within the region, with everything in scope at the owning instruction visible.
* While regions read outer variables and cannot assign them, so effects inside go through cells (`setVar`'s `readOnly` check). A `region while`'s condition cannot raise, nor call a function that may raise.
* The region variant of `mean`, with cells, is below, as While's lowering prints it. The typed listing above builds a simpler function, without the `catch` handler, so its print differs. The handler `raise.0` exists because `while.loop` has an `^err` successor, whose edge leaves `entry.0` before the loop line.

```whilelang "mean, with region while"
fun mean(n : Int, d : Int) : Int {
  var s : Ref := ref 0;
  var i : Ref := ref 1;
  region while (*i <= n) { *s := *s + *i; *i := *i + 1; }
  try { return *s / d; } catch e => { return 0 - e; }
}
```

```dyn "Printed, folded"
module main {
  func @mean(%n.0 : base.Int, %d.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int, %d.0 : base.Int):
      %cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %cell.1 : base.Ref(base.Int) = base.refNew[base.Int](1)
      %u.0 : base.Unit = while.loop ^raise.0() {
        region.0():
          %t.0 : base.Int = base.refGet[base.Int](%cell.1)
          %t.1 : base.Bool = while.le(%t.0, %n.0)
          ret(%t.1)
      } {
        region.1():
          %t.2 : base.Int = base.refGet[base.Int](%cell.0)
          %t.3 : base.Int = base.refGet[base.Int](%cell.1)
          %t.4 : base.Int = while.add(%t.2, %t.3)
          %u.1 : base.Unit = base.refSet[base.Int](%cell.0, %t.4)
          %t.5 : base.Int = base.refGet[base.Int](%cell.1)
          %t.6 : base.Int = while.add(%t.5, 1)
          %u.2 : base.Unit = base.refSet[base.Int](%cell.1, %t.6)
          %next.0 : while.Flow = while.next
          ret(%next.0)
      }
      %t.7 : base.Int = base.refGet[base.Int](%cell.0)
      %t.8 : base.Int = while.div(%t.7, %d.0) ^catch.0(%n.0, %d.0, %cell.0, %cell.1)
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.8)
      ret(%ok.0)
    catch.0(%n.1 : base.Int, %d.1 : base.Int, %s.0 : base.Ref(base.Int), %i.0 : base.Ref(base.Int), %e.0 : base.Int):
      %t.9 : base.Int = while.sub(0, %e.0)
      %ok.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.9)
      ret(%ok.1)
    raise.0(%e.1 : base.Int):
      %error.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%e.1)
      ret(%error.0)
  }
}
```

:::sources
Sources: `StrataDyn/Build.lean` (`region`, `regionWith`); `StrataPython/Dyn/Build.lean`.

:::

::::

## 7. Annotations
%%%
number := false
tag := "tr-ann"
%%%

Every IR node carries an annotation. Use the source range, as Python does, so that a failure can point at source.

A front end can also state facts about a function as _attributes_: named values, such as a class's declared shape, that the printer writes below the function's signature and the reader reads back, so goldens pin them. The printer leaves out an extern's attributes, so a golden does not pin them. The IR gives them no meaning, and well-formedness does not mention them. The annotation `Info` carries a source range and attributes, and `Func.setInfo` replaces a built function's own. A key is prefixed by the front end that gives it its meaning. Python's translator states the fields and bindings of a class body:

```dyn "A class body and its attributes (a Python translator golden)"
  func @|e14_nonlocal_class_scope.C.<body>|(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    #[py.fields = []]
    #[py.bindings = [{name = "x", value = 1}, {name = "m", binding = "def"}]]
```

`Module.read` returns a module annotated with `Info`, whatever annotation the printed module had.

When `Build.run` finds no misuse but the function is not well formed, its `FailedFunc` says only that: "f is not well formed". The function it carries, `e.func` for the failure `e`, can be explained. For a failure of scoping, `Func.scopeDiagnostics e.func` names each unreachable block, and each use out of scope with a path from the entry that avoids its definition; Python's translator adds these messages to its diagnostic. Any other failure of `Func.WF` has no explanation yet ({ref "missing"}[Missing features]: _A well-formedness explainer_). To locate it, print the function in full with `Func.format .full e.func`, a module that holds only that function, and read the text back with `Module.read`, which gives located type messages.

## 8. Printing and reading
%%%
number := false
tag := "tr-print"
%%%

The printed form is the human view of a module. It is also an interchange text. Take one line of the running example:

```dyn
      %t.3 : base.Int = while.div(%s.0, %d.1) ^catch.0(%n.1, %d.1, %s.0, %i.0)
```

:::table +header
*
  * Part
  * Text
  * Meaning
*
  * value
  * `%t.3`
  * the value the line defines, by its name
*
  * type
  * `base.Int`
  * the value's type
*
  * instruction
  * `while.div`
  * the instruction, by its environment name
*
  * type arguments
  * (none)
  * in brackets when present: `base.ok[base.Int, base.Int]`
*
  * operands
  * `(%s.0, %d.1)`
  * values, or folded constants such as `0`
*
  * successors
  * `^catch.0(%n.1, %d.1, %s.0, %i.0)`
  * target label and the arguments the site binds

:::

A block header ends at its parameters. The printed form holds no dominator tree: the reader computes one when it checks a function, as the builder does.

The folded form writes constants at their uses. The full form gives each constant its own line. `Module.read env text` reads either form back into a checked module.

:::widget "fold"
Both forms are printed in full in {ref "app-texts"}[Appendix C: Full texts].
:::

::::deepDive "text front ends"
* The printed module does not name its environment, so the reader must be given it: `Module.read env text`.
* The reader checks a text as the builder checks a built function, but drops nothing. It rejects a text with a block that its entry cannot reach, so a front end that emits text must leave dead blocks out. It need not compute dominators. A use out of scope is reported with a path from the entry that avoids the definition.
* A constant written at a use reads back as a `const` instruction just before it. Values get ids in the function's definition order: an extern's parameters, then the body in printed order, then the contract's values, although the contract prints before the body.
* Lines starting with `--` are comments.

:::sources
Sources: `StrataDyn/DDM.lean`, `StrataDyn/DDMRead.lean`.

:::

::::

## 9. Bytecode and goto
%%%
number := false
tag := "tr-unstructured"
%%%

Bytecode, and source languages with `goto`, give the translator a control-flow graph and not a tree. The translator maps that graph onto Dyn blocks directly.

* Each basic block of the input gets one label, allocated before any block is built, so every jump can name its target.
* The values live across a block boundary become block parameters: the operand-stack slots and the local-variable slots, typed by the verifier's types. The JVM's `StackMapTable` gives those types at every branch target.
* The Dyn entry block is a block of its own that jumps to the first input block. No transfer may target an entry, and an input loop may start at the first instruction.
* Exception ranges become handlers in effect. Each instruction that can throw inside a protected range gets an `^err` successor to that range's handler, and one outside every range gets the function's propagate block.

Implicit exceptions are explicit in Dyn. A JVM field read can throw a `NullPointerException`, an array access an index exception, a cast a `ClassCastException` and an integer division an `ArithmeticException`. Each such operation is a raising instruction of the environment, with an `^err` successor, as While's `div` is.

Go adds labelled `break` and `continue`, `goto` and `switch` fallthrough, which all become jumps to labels allocated in advance. `defer`, `panic` and `recover` need a convention, as Python's `finally` does ({ref "tr-exc"}[Translator 5: Exceptions]). In such a convention, a panic is an exception, and the deferred calls run on both the normal and the exceptional exit. {ref "env-defaults"}[Environment 9: Encoding common features] gives an encoding of Go's multiple results. No front end implements this lowering.

::::deepDive "obligations for a graph-shaped input"
* Blocks may be finished in any order after the entry: the checker computes dominators from the finished graph.
* Blocks that the entry cannot reach are dropped when the function is finished, so dead bytecode needs no special case. A label that a kept block targets must be started.
* Pass every live slot on every edge. The simplest translator passes every slot that has a type at the target and lets a later pass trim them. Dyn types match exactly, with no subtyping, so the slots of one join must agree on their Dyn types; a universal reference type makes the verifier's merged types agree.
* A handler's parameters are the values pre-bound at the raising site, then the declared payload, in that order. For the JVM the pre-bound values are the locals at the throwing instruction, and the payload is the exception, which is the handler's whole operand stack.
* Pre-bound values must be defined before the raising instruction. A handler then sees the locals as they were before the instruction, which matches the JVM, where a throwing instruction stores nothing.
* A protected range may start or end inside an input basic block. A Dyn block may hold several raising instructions, each with its own `^err` successor and its own pre-bound values, so the block need not be split.

:::sources
Sources: `StrataDyn/Build.lean`; `StrataDyn/WF.lean` `Func.WF` ({ref "tr-shape"}[Translator 1: The shape you produce]).

:::

::::

# Testing
%%%
number := false
tag := "run"
file := "running-and-testing"
%%%

Running a function takes a module, a _model_, arguments, fuel and an oracle for nondeterministic choices. The model is what `#dyn_sem_table` generates for an environment that extends `Base`; While's is `WhileSem.model`. The engine links every name of the module to a rule of the model, validates the linked module, runs it, and returns an _outcome_. A run ignores contracts and ghosts, so a test by running checks the body and nothing in the contract. A module with an extern function does not run yet: `runModule` rejects it with `Fault.invalid` (`StrataDynTest/Exec/BaseTest.lean`). An outcome holds a result, which is a value or a fault, a _snapshot_ of the final heap and world, the number of steps and the number of choices drawn. An argument is a Lean value, `M.arg x`, and `o.read? α` reads the result at the Lean type `α`. The next listing runs the running example's `main` and reads its result:

```leantext "Running main (docs/dyn/checks/Exec.lean)"
/-- `main n`, run on the fused engine, or `none` if the lowering failed. -/
def runMain (n : Int) : Option (Outcome WhileSem.model) := (lower prog).toOption.map fun m =>
  runModule WhileSem.model m (.str .base "main") #[WhileSem.model.arg n] 100000

/-- The result, read as an `Except Int Int`, and the printed output. -/
def describe (o : Outcome WhileSem.model) : String :=
  let r := match o.read? (Except Int Int) with
    | some (.ok v) => s!"ok {v}"
    | some (.error e) => s!"error {e}"
    | none => "not an Except Int Int"
  s!"{r}, printed {o.snapshot.world.out.items}"
```

`describe` on `runMain 20` gives `ok 21, printed #[21]`, and on `runMain 10` gives `ok -1, printed #[-1]`.

What a module does is the set of its _runs_: the runs of its step relation, which performs one transition per step and may answer each choice in any way. `runModule` executes one of them, the run under its oracle, on the _fused engine_, `runFused`, which performs in one step the edges, entries and world requests that a transition decides. It is proved to follow the runs: when it ends, the run under the same oracle ends with the same result, snapshot and choices (`runFused_eq`, `beh_of_runFused`). Fuel counts fused steps, so a run takes fewer of them than steps of the relation ({ref "inside-machine"}[Inside the execution DSL 4: Linking, validation and the machine]).

The run under one oracle can also be computed a step at a time, and what its first steps show checked with `#guard`. Here `observe n k` gives what the first `k` steps of `main n` show of the printed output, and the outcome if the run has ended by then:

```leantext "Observing a run (docs/dyn/checks/Exec.lean)"
/-- What the first `k` steps of `main n` show of the output, and its result if the run has
ended by then. -/
def observe (n : Int) (k : Nat) : Option (List (Array Int) × Option String) := do
  let m ← (lower prog).toOption
  let ⟨_, hw, i⟩ ← (prepare WhileSem.model m (.str .base "main")).toOption
  let ⟨_, c, h⟩ ← (startCore hw i [WhileSem.model.arg n Run]).toOption
  let s : State WhileSem.model.at := ⟨c, .exec, 0, ()⟩
  let shown := obsTrace hw (fun _ => 0) (obsW (M := WhileSem.model.at) (·.out.items)) s h k
  let ended := match trace hw (fun _ => 0) s h k with
    | .ended f => some (describe ⟨f.result, f.snapshot, k, f.drawn⟩)
    | .running _ => none
  return (shown, ended)
```

`observe 20 184` gives `some ([#[], #[21]], some "ok 21, printed #[21]")`: the run shows the empty output, then `#[21]`, and has ended. After 183 steps it is still running. These records are the run's _behaviour_ so far. Behaviours cover runs that never end, and _trace refinement_ compares the behaviours of two modules, such as a pass's input and output: `docs/Dyn.md`, §5, "Reasoning about runs", states both.

A run that does not end with a value ends with a _fault_. The While examples are abridged outcome lines:

:::table +header
*
  * Fault
  * Meaning
  * While example
*
  * `gap`
  * a case the semantics leaves unmodelled (`semanticGap`)
  * `cube 2: fault gap: while.pow: not implemented`, where `cube` returns `x ^ 3`
*
  * `failure`
  * a case the rule's author holds impossible (`semanticFailure`), or `unreachable`
  * none
*
  * `blocked`
  * an infeasible path (`assume`), which stands for no behaviour
  * none: While's rules do not assume
*
  * `badCell`
  * an access through a ref whose location is past the heap or holds a value of another tag
  * none: While's refs come only from its rules and `refNew`
*
  * `badCall`
  * a call or a bind of a closure whose function does not take the arguments or return the result the call's tags say
  * none: While calls only through function references it typed itself
*
  * `outOfFuel`
  * the step budget ran out
  * `spin: fault out of fuel`, where `spin` loops on `while (true) { }`
*
  * `missingRules`
  * instructions without rules, all reported at link time
  * none: `#dyn_coverage While (complete)` holds
*
  * `invalid`
  * linking or validation rejected the module, or the arguments do not fit the entry function
  * an argument of the wrong type
*
  * `noFunction`
  * the entry function does not exist
  * running a name the module lacks

:::

While's tests show the testing pattern to copy:

1. every lowered program is well formed;
1. golden outcome strings, one per example;
1. the world is inspected, for printed output for instance;
1. prefixes of runs under one oracle are checked step by step, for programs that never end in particular (`StrataDynTest/Exec/TraceTest.lean`);
1. oracle tapes replay choices;
1. lowering errors are pinned by message.

Differential testing against a reference interpreter, such as CPython or node, needs a harness that you build. The harness runs each program of a corpus in both, compares the final value and the printed output, and keeps a list of expected failures.

:::widget "interp"
Expected outcomes:

* `main 20`: `ok 21`, printed `#[21]`
* `main 10`: `ok -1`, printed `#[-1]`
* `mean 4 0`: `ok -1`, printed `#[]`
:::

::::deepDive "run API and obligations"
* Call: `runModule M m f args fuel (oracle := fun _ => 0)`. `runModule` takes a checked `Module` over any environment that refines `Base`, and runs it on the fused engine for at most `fuel` fused steps.
* `prepare M m f` links and validates a module and finds its function `f`, and `startCore` starts it from a snapshot, by default an empty heap and the initial world. A module's top level can run first, and one of its functions then from `o.snapshot`, the heap and world where the top level ended, as Python runs a module and then a function it defines.
* `debugRun` runs with a hook that sees every step of the relation, and resumes each time the hook stops the run.
* `M.arg x` finds the tag of `x`'s Lean type as a rule finds one, so a caller names no tag. A start argument holds no ref and no closure.
* `o.read? α` gives `some x` if the result's tag is `α`'s, and `none` if it has another tag or the run faulted. `M.read? r α` reads a `Result` the same way.
* `chooseNat` is answered by the oracle's next number, `choose n` by that number reduced below `n + 1`, and `chooseInt` by the integer it numbers; `tapeOracle` replays a list, then answers 0.
* Blocks may come in any order: scoping depends on the graph, not on the order in which blocks are listed.
* Keep step counts out of goldens: they change with the lowering and with the engine's fusing.
* The engine has no generic value printer. Write a decoder like While's `showResult`, from `read?` at each Lean type a result may have.

:::sources
Sources: `StrataDyn/Exec/Run.lean`; `StrataDyn/Exec/Trace.lean`; `StrataDyn/Examples/While/Run.lean`; `StrataDynTest/Examples/While/RunTest.lean`; `StrataDynTest/Exec/TraceTest.lean`.

:::

::::

# Inside the execution DSL
%%%
number := false
tag := "inside"
file := "inside-the-execution-dsl"
%%%

:::::callout "Who this chapter is for"
This chapter describes how execution works: what the commands record and generate, what a rule's result is, and how the engine runs a module. A reader who writes rules and runs modules with {ref "env-sem"}[Environment 7: Meaning] and {ref "run"}[Testing] can skip it.
:::::

The _execution DSL_ is the part of Dyn that gives instructions their meaning and runs modules. It has six stages. The first three run when Lean elaborates the language's files, and the last three run when a module runs.

:::table +header
*
  * Stage
  * What it takes
  * What it produces
*
  * Environment
  * the `environment` command
  * the environment, and a record of its declarations
*
  * Rules
  * `@[dyn_type]`, `#dyn_types`, `@[dyn_sem]`, `@[dyn_lang]`
  * registrations, kept in environment extensions
*
  * Table
  * `#dyn_sem_table S for E`
  * tags, one wrapper per instruction, and the model `S.model`
*
  * Link
  * a checked module and the model
  * a linked module, `LModule`
*
  * Validate
  * the linked module
  * a proof `WF lm`
*
  * Run
  * the validated module, arguments, fuel and an oracle
  * an outcome

:::

## 1. The environment and its extensions
%%%
number := false
tag := "inside-env"
%%%

A Lean _environment extension_ is state that Lean keeps beside the declarations of a module and passes to every module that imports it. Each extension says how to add one entry, and how to combine the entries of the imported modules when a module starts.

The `environment` command leaves a _record_ of each environment it declares, an `EnvEntry`, in the extension `envEntries`. The record holds the environment's Lean namespace, its parent, its types, its abbreviations, its instructions and its names. Each instruction's record, an `OpInfo`, holds its signature: its type parameters with their kinds, its operands, its variadic, its regions, its successors and its result type. It also holds the instruction's docstring and its kind, but not its effect, which only the environment itself records:

```leantext "Instruction kinds (StrataDyn/DSL/Model.lean)"
/-- Where an instruction comes from: declared by `insn`, or derived from a datatype. -/
inductive OpKind where
  /-- An `insn`. -/
  | decl
  /-- Constructor `idx` of the datatype `data`, by environment name. -/
  | ctor (data : Name) (idx : Nat)
  /-- The case instruction of the datatype `data`. -/
  | case (data : Name)
  deriving Inhabited, Repr, BEq
```

The record is what later stages read in place of evaluating the environment. A child environment resolves its parent's declarations from it. The typed emitters are generated from it. Registration checks each rule's type against the instruction's signature in it, and the table generator lists an environment's instructions, and its ancestors', from it (`ancestry`).

Three more extensions hold the registrations:

* `typeExt` holds the type rules, one per `@[dyn_type]` and one per datatype that `#dyn_types` generates;
* `semExt` holds the semantic rules, one per `@[dyn_sem]`. A `SemRule` holds its key, the rule's declaration, whether the rule is pure, the rule's type variables, its leading binders, and whether it loops;
* `langExt` holds the classes declared with `@[dyn_lang]`.

A _key_ is the Lean name of a type or an instruction, such as `Base.Int` or `While.div`, resolved through the record. Registration rejects a key that the module, or a module it imports, registers already. Two modules that do not import each other may both register one key. A module that imports both combines their entries with `Registry.ofImports`. `Registry.ofImports` keeps the first entry for a key and records the second as a duplicate, unless both name one declaration:

```leantext "Combining imported registrations (StrataDyn/Exec/Rules.lean)"
/-- The registry of the imported entries, `ess`, one array per module, by `key`, with `decl`
naming each entry's declaration.  Two modules that register one declaration for one key give
one entry. -/
def Registry.ofImports {α : Type} (key decl : α → Lean.Name) (ess : Array (Array α)) :
    Registry α :=
  ess.foldl (init := {}) fun r es => es.foldl (init := r) fun r e =>
    match r.entries.find? (key e) with
    | some e₁ =>
      if decl e₁ == decl e then r else { r with dups := r.dups.push (key e, decl e₁, decl e) }
    | none => { r with entries := r.entries.insert (key e) e }
```

`@[dyn_sem]`, `#dyn_coverage`, `#dyn_types` and `#dyn_sem_table` report the recorded duplicates of the environment's keys, and of its ancestors' keys, in an error that names both declarations of each. In this test, two imported modules each give a rule to the type `dup.Num` and to the instruction `dup.inc`:

```plaintext "Two rules for one key (StrataDynTest/Exec/DupTest.lean)"
error: two imported modules give dup.Num a type rule: DupA.NumA (in StrataDynTest.Exec.DupA) and DupB.NumB (in StrataDynTest.Exec.DupB)
two imported modules give dup.inc a rule: DupA.incA (in StrataDynTest.Exec.DupA) and DupB.incB (in StrataDynTest.Exec.DupB)
```

A child environment refines its parent ({ref "env-layer"}[Environment 6: Layering]), and its table covers its ancestors' instructions with their rules. Three facts make a parent's rules run in a child. Rules are stored by the Lean names of the parent's declarations, which the child's record resolves to the same declarations. A rule is generic in its requests, its exits and the run token, so the child's wrappers instantiate it at the child's table. A rule reaches the world only through `HasPart`, so a child's world that embeds its parent's parts as fields serves the parent's rules. A child's `@[dyn_lang]` class extends its parent's.

## 2. The primitives
%%%
number := false
tag := "inside-prims"
%%%

### Rules as trees
%%%
number := false
tag := "inside-rules-as-trees"
%%%

A rule's result is a value of `Sem ε E α`, a _tree_. Its leaves return a value or stop. Its inner nodes are _requests_, each with a continuation that takes the answer:

```leantext "A rule's tree (StrataDyn/Exec/Sem.lean)"
/-- A rule's computation, with requests `ε` and exits `E`, returning an `α`: a finite tree
whose leaves return or stop, and whose inner nodes are requests. -/
inductive Sem (ε : Eff) (E α : Type) where
  | ret (a : α)
  | stop (s : Stop E)
  /-- Choose a number, and continue with it. -/
  | choose (k : Nat → Sem ε E α)
  /-- Run a body, or ask the machine for a cell or a closure, and continue with the answer. -/
  | vis (i : ε.I) (k : ε.O i → Sem ε E α)
  /-- Update the world: `f` takes the world and gives the new world and the continuation, so
  that one request reads and writes it. -/
  | update (f : ε.W → ε.W × Sem ε E α)
```

`ε` gives the requests a rule may make and the world it may update, and `E` is the type of its exits. A stop is a jump along an exit or a fault:

```leantext "Requests and stops (StrataDyn/Exec/Sem.lean)"
/-- What a rule may ask for: machine requests `I`, with `O i` the answer to `i`, and the world
`W` it may read and update. -/
structure Eff where
  I : Type
  O : I → Type
  W : Type

/-- Why a rule stopped without a result. -/
inductive Stop (E : Type) where
  /-- An exit along one of its targets, or to its `Again`. -/
  | jump (e : E)
  | fault (f : Fault)
```

`Sem ε E` is a monad: `Sem.bind` grafts a continuation onto every leaf that returns, and it satisfies the monad laws (`Sem.bind_assoc`, `Sem.bind_pure`, and the instance `LawfulMonad (Sem ε E)`). Each primitive a rule calls builds one node:

:::table +header
*
  * Primitive
  * Node
*
  * `return a`
  * `ret a`
*
  * `jump k p`, `jump again s`
  * `stop (.jump e)`, where `e` is the exit of `k` with `p`, or of `again` with `s`
*
  * `semanticGap msg`, `semanticFailure msg`, `assume b msg`
  * `stop (.fault …)`, with the fault `gap`, `failure` or `blocked`
*
  * `chooseNat`, `choose n`, `chooseInt`
  * `choose k`
*
  * `getThe P`, `modifyThe P f`, `modifyGetThe P f`
  * `update f`: one request reads the world and gives back the new world
*
  * `runRegion r args`
  * `vis` with a region request
*
  * `newRef`, `readRef`, `writeRef`, `modifyRef`
  * `vis` with a cell request: new, get, set or modify
*
  * `callFn f args`, `bindFn f x`
  * `vis` with a call request or a bind request

:::

`bindAll` is a sequence of `bindFn`s, one per value of a payload. A rule takes no fuel: the machine runs each of its requests as a step.

### Targets and Again
%%%
number := false
tag := "inside-targets-and-again"
%%%

A rule's _target_ is a value of `Target E ts`, a function from a payload of the Lean types `ts` to an exit. A rule's _Again_ is a value of `Again E S`, a function from a state of the Lean type `S` to an exit:

```leantext "Targets and Again (StrataDyn/Exec/Sem.lean)"
/-- The target of a successor of the operation a rule implements, whose payload has the Lean
types `ts`: the rule jumps along it with the payload.  A rule takes one per successor, after its
operands and regions, and is generic in `E`: its values of `E` come from its targets and its
`Again`. -/
structure Target (E : Type) (ts : List Type) where
  /-- The exit along this successor with a payload. -/
  exit : Payload ts → E

/-- The operation's own entry, with the rule's state, of a Lean type `S` the rule chooses.
Jumping to it runs the operation again, on the same operands, regions and targets, with the
state `some s`, as a loop's back edge.  A rule that loops takes `(st : Option S)` and then one,
after its targets: its first run has `st = none`.  It is no `Target`: it fills no successor. -/
structure Again (E : Type) (S : Type) where
  /-- The exit back into the operation, with a new state. -/
  exit : S → E
```

A rule is generic in `E`, so the only values of `E` it holds are the ones its targets and its Again make. It stops along one of its own successors, back into its own instruction, or with a fault. A jump to the Again runs the instruction again on the same operands, regions and targets, with the state `some s`. The instruction's declaration does not mention the state, so neither does the IR. The class `Jump` lets `jump` take either a target or the Again.

### The run token
%%%
number := false
tag := "inside-the-run-token"
%%%

A _run token_ is a type `σ` with an instance `Store σ`, which says which locations are cells and which functions are the module's. A _raw ref_ is a location together with the token's proof that it is a cell, and a _ref_ `Ref σ α` is a raw ref with the Lean type `α` of the cell's contents as a phantom:

```leantext "The run token and refs (StrataDyn/Exec/Sem.lean)"
/-- What the token `σ` says: which locations are cells, and which functions are the module's.
Neither names a Lean type, so a datatype may hold a ref or a closure of itself. -/
class Store (σ : Type) : Type where
  Valid : Nat → Prop
  FnValid : Nat → Prop

/-- A raw ref to a cell of the heap `σ` names: a location with `σ`'s proof that it is one.  At
run time it is its location. -/
structure Ref.Raw (σ : Type) [Store σ] : Type where
  loc : Nat
  valid : Store.Valid σ loc

/-- A ref to a cell holding an `α`: a raw ref, with the contents' Lean type as a phantom.  What
`base.Ref a` is at `σ`.  The machine checks the cell's tag against `α`'s at every access. -/
structure Ref (σ : Type) [Store σ] (α : Type) : Type where
  raw : Ref.Raw σ
```

A closure, `FnRef σ as r`, is built the same way: a raw closure `FnRef.Raw σ` holds a function's index, the location of the cell holding its bound values, and the token's proof that the function is the module's. The proofs name no Lean type, so a datatype may hold a ref or a closure of itself.

Every rule that takes or makes a ref is generic in `σ`. The theorem `no_forge` states that no term generic in the token is a raw ref:

```leantext "no_forge (StrataDyn/Exec/Sem.lean)"
/-- No term generic in the token is a raw ref: at a token whose cells are `False`, a raw ref
holds a proof of `False`.  So no such term is a `Ref` at any type. -/
theorem no_forge (f : (σ : Type) → [Store σ] → Ref.Raw σ) : False :=
  letI : Store Empty := ⟨fun _ => False, fun _ => False⟩
  (f Empty).valid
```

`no_forge_fn` states the same of raw closures. So no rule can produce a ref or a closure, at every token, out of nothing. That is all the two theorems give. Lean does not prove a rule parametric in the token: a rule can still decide classically whether a location is a cell at its token, and build a ref at the machine's token that way. That a rule reaches only the cells and captures cells it is given, and those the machine answers its requests with, is what a rule's certificate states. A closure that a rule hands the machine may still name any function; the machine checks its function and signature at each call ({ref "wip-cert"}[Proofs about runs 1: Certificates for rules]). The machine runs at its own token, `Run`, which accepts every location and every function:

```leantext "The machine's token (StrataDyn/Exec/Sem.lean)"
/-- The machine's token. -/
structure Run : Type where
  deriving DecidableEq, Repr

/-- `Run` promises nothing of a location or a function, so every access of a cell and every
call of a closure is checked. -/
instance instStoreRun : Store Run := ⟨fun _ => True, fun _ => True⟩
```

At `Run` the machine makes a ref from any location, so it checks every access.

### Tags, and checking at the access
%%%
number := false
tag := "inside-tags-and-checking-at-the-access"
%%%

A _tag_ is a value of `Ty`: a head applied to tags, or a list of tags. A tag stands for a Lean type of a table:

```leantext "Tags (StrataDyn/Exec/Sem.lean)"
/-- A tag: head `head` applied to `args`, or a list of tags, the argument of a code pointer's
parameters.  Head `0` is a ref's and head `1` a code pointer's; a table numbers its Lean type
constructors from `2`. -/
inductive Ty where
  | app (head : Nat) (args : List Ty)
  | list (elems : List Ty)
  deriving Repr, Inhabited
```

Heads `0` and `1` are the engine's: those of `base.Ref` and of `base.Fn`. A table numbers the other heads from `2`, one per Lean type constructor its type rules give. `Ty.decode σ H` gives a tag's Lean type, where `H h as` is head `h` applied to the Lean types `as`. Dyn types with one Lean type have one tag. The instance `Decode σ` holds a table's decoding, and three classes give the tags of Lean types at it:

```leantext "Tags of Lean types (StrataDyn/Exec/Sem.lean)"
/-- A tag of the Lean type `α`, at the token `σ`: what the machine checks a cell's contents
against.  The proof is erased: at run time a `TagOf` is its tag. -/
class TagOf (α : Type) where
  tag : Ty
  ok : Decode.decode σ tag = α

/-- The tags of a signature taking `as` and returning `r`: what the machine checks a closure's
function against. -/
class SigOf (as : List Type) (r : Type) where
  sig : List Ty × Ty
  ok : sig.1.map (Decode.decode σ) = as ∧ Decode.decode σ sig.2 = r

/-- Tags of the Lean types `as`, one each: what a rule over a list-kinded type variable takes
to reach cells and calls at the list's types. -/
class TagsOf (as : List Type) where
  tags : List Ty
  ok : tags.map (Decode.decode σ) = as
```

`TagCon σ F` and `TagCon₂ σ F` give the tags of `F A` and `F A B` from those of `A` and `B`. `SigOf` instances are built from `TagOf`s (`SigOf.nil`, `SigOf.cons`) and from a `TagsOf` (`SigOf.append`), so no language lists a signature.

A ref carries no tag: the tag comes from the access. A rule that makes, reads or writes a cell at `α` takes `[TagOf σ α]`, and the cell capability puts the tag into the request. The wrappers pass this cell capability, at the machine's requests:

```leantext "The cell capability at the machine (StrataDyn/Exec/Sem.lean)"
@[reducible] def HasHeap.mreq : @HasHeap σ _ ⟨I⟩ (MEff I σ W rs) :=
  @HasHeap.mk σ _ ⟨I⟩ (MEff I σ W rs)
    (fun t v => .new t.tag (cast t.ok.symm v))
    (fun t _ c => cast (congrArg (Ref σ) t.ok) c)
    (fun t c => .get t.tag c.loc)
    (fun t _ v => cast t.ok v)
    (fun t c v => .set t.tag c.loc (cast t.ok.symm v))
    (fun t c f => .modify t.tag c.loc fun v => cast t.ok.symm (f (cast t.ok v)))
```

The machine stores each cell with its tag, and compares the request's tag with the cell's at every access. The casts in this capability are the tags' proofs, and are erased when the code is compiled. A call or a bind of a closure takes `[SigOf σ as r]` in the same way, and the machine compares the signature's tags with the function's.

### A language's capabilities
%%%
number := false
tag := "inside-a-language-s-capabilities"
%%%

A _capability_ is an instance argument of a rule that gives it access to state: `HasPart W P`, `HasHeap σ ε`, `HasCall σ ε`, or a tag class. `@[dyn_lang]` declares a class whose fields are capabilities, or a parent language's class that it extends ({ref "env-sem"}[Environment 7] shows While's). The attribute checks each field and makes it an instance, so a rule that takes the class has every field as an instance. The class's first parameter, the token, is an `outParam`, so instance search finds a part of the world, which does not mention the token, through the class. The wrapper of a rule that takes the class builds the class field by field: for While's `cellGet`, `WhileRules.Lang.mk` of the world's two `HasPart` instances, `HasHeap.mreq`, and `TagOf.mk Int (Ty.app 4 []) _`.

## 3. Code generation at elaboration time
%%%
number := false
tag := "inside-gen"
%%%

### `#dyn_types`
%%%
number := false
tag := "inside-dyn-types"
%%%

`#dyn_types E` emits, for each datatype `T` of `E` that has no hand-written rule, its Lean type `T.Val`: an inductive with one constructor per Dyn constructor, of the same name, whose fields have the Dyn fields' Lean types. It also registers `T.Val` as `T`'s type rule. Mutually recursive datatypes become one `mutual` block. A datatype whose fields hold refs or closures, directly or through other types, takes the run token first. `#dyn_types While` gives `While.IntList.Val` and `While.Flow.Val`, which take no token. The base's `Unit` and `Except` have hand-written rules, Lean's `Unit` and `Except`, and registration checks their constructors against the Dyn constructors by name, count and field types.

### `#dyn_sem_table`
%%%
number := false
tag := "inside-dyn-sem-table"
%%%

`#dyn_sem_table S for E` emits, in the namespace `S`:

* `S.typeNames`, a name for each head, and `S.H σ`, each head's Lean type constructor at the token `σ`;
* `S.interp`, the decoding `Ty.decode σ (S.H σ)` at each token, and `S.W`, the world at each token;
* `S.T.n`, the tag of each type `n`, a function of its parameters' tags;
* `S.decode`, the decoding as a `Decode σ`, and at it a `TagOf`, `TagCon` or `TagCon₂` instance for each Lean type and type constructor of the table;
* `S.rule.o`, the wrapper of each instruction `o` of `E` and its ancestors that has a rule or is derived, and `S.again.o` for a rule that loops;
* `S.ops`, each wrapper as an `OpImpl` by environment name, and `S.table`;
* `S.model`, if `E` extends `Base`: the table with what the engine needs of the base, such as the tags of the literals' types.

Here are While's heads, and the tag of `base.Except`, which the table numbers `8`:

```leantext "While's heads (docs/dyn/checks/Exec.lean)"
@[reducible, expose] def Strata.Dyn.WhileSem.H : (σ : Type) → [Store σ] → Nat → List Type → Type :=
fun σ [Store σ] h as =>
  match h, as with
  | 2, [] => Unit
  | 3, [] => Bool
  | 4, [] => Int
  | 5, [] => Float
  | 6, [] => String
  | 7, [x0] => Array x0
  | 8, [x0, x1] => Except x0 x1
  | 9, [] => NoLoc
  | 10, [] => IntList.Val
  | 11, [] => Flow.Val
  | x, x_1 => Empty
```

```leantext "The tag of base.Except (docs/dyn/checks/Exec.lean)"
@[reducible, expose] def Strata.Dyn.WhileSem.T.base.Except : Ty → Ty → Ty :=
fun x0 x1 => Ty.app 8 [x0, x1]
```

A _wrapper_ is a generated function that applies one rule to its operands and to the regions, targets, Again and capabilities that it builds. Its type is fixed by the instruction's shape at its type arguments' tags: one operand per argument, at its tag's Lean type, and a tree whose exits are `Out` values over the successors' payload tags. Here are three of While's wrappers, as `#print` shows them:

```leantext "The wrapper of while.le (docs/dyn/checks/Exec.lean)"
fun σ [Store σ] a0 a1 => WhileRules.le a0 a1
```

```leantext "The wrapper of while.div (docs/dyn/checks/Exec.lean)"
fun σ [Store σ] a0 a1 => WhileRules.div a0 a1 { exit := fun p0 => Out.exit (Exit.here (Args.cons p0 Args.nil)) }
```

```leantext "The second wrapper of while.loop (docs/dyn/checks/Exec.lean)"
fun σ [Store σ] st =>
  WhileRules.loop (Region.slot ⟨0, WhileSem.rule.while.loop._proof_1⟩ fun x => Args.nil)
    (Region.slot ⟨1, WhileSem.rule.while.loop._proof_2⟩ fun x => Args.nil)
    { exit := fun p0 => Out.exit (Exit.here (Args.cons p0 Args.nil)) } (some st) { exit := Out.again }
```

`le` has a pure rule, so its wrapper applies the rule to the operands. `div`'s wrapper also passes a target, a closed term whose exit builds `Out.exit` of the first successor with the payload. The wrapper instantiates the rule's exits `E` at `Out …`, so every exit the rule's tree reaches is an `Out` value of the wrapper's type. Lean checks that type once, when the table is elaborated, and the machine reads a rule's outcome at it with no check while the module runs.

A rule that loops has two wrappers. `S.rule.o` passes the state `none`. `S.again.o` takes a state `st` after the operands and passes `some st`, and its Again is `{ exit := Out.again }`. Lean infers the state's type from the rule, and the table records it, by the instruction's position and its type arguments' tags (`Table.stateOf`). A wrapper has one of three forms:

```leantext "A wrapper's three forms (StrataDyn/Exec/Sem.lean)"
/-- The wrapper of an operation of shape `s` at the token `σ`, whose rule's state is an `S`: a
pure function of its operands, for a rule outside `Sem`, a constructor or a case instruction;
a rule's tree; or, for a rule that loops, its tree on its first run and its tree on a run
again with a state. -/
inductive Impl (σ : Type) [Store σ] (I : Ty → Type) (W : Type) (s : Shape) (S : Type) where
  | pure (f : Fn I (s.Var I (s.Pure I)) s.args)
  | sem (f : Fn I (s.Var I (s.Tree σ I W S)) s.args)
  | loop (f : Fn I (s.Var I (s.Tree σ I W S)) s.args) (again : Fn I (s.Var I (S → s.Tree σ I W S)) s.args)
```

A wrapper over a list-kinded type variable `cs` gets `List.map (interp σ) (Ty.elems cs)` for it and `⟨Ty.elems cs, rfl⟩` for its `TagsOf`. The spread's operands are curried after the others, one per element, and the wrapper passes the rule their payload.

### What registration checks
%%%
number := false
tag := "inside-what-registration-checks"
%%%

`@[dyn_sem o] r` checks:

* that the key `o` resolves through the record, to an instruction that is neither a constructor nor a case instruction nor one of the machine's (`base.refNew`, `refGet`, `refSet`, `callCode`);
* that `r`'s type has the shape of `o`'s signature: one type variable per type parameter, a `Type` for a type and a `List Type` for a list; the operands at their Lean types; one region per region, one target per successor and, for a rule that loops, its state and its Again; and the result. A mismatch is an error at the rule that names the operand, region, target, state, Again or result: `operand x of err.inc: expected Int, but incNat takes Nat`;
* that the rule is generic in its requests and its exits, and in the token if its types mention a ref or a closure;
* that a list variable occurs only as the spread and spliced into a closure operand's arguments;
* that each capability the rule takes is a part of the world, the machine's cells or calls, or a tag;
* that no imported module registers another declaration for the key.

`@[dyn_type T] d` checks that `d` takes one Lean type per parameter of `T`, after the token if it takes one. `@[dyn_lang]` checks that each field of the class is a capability or a parent language's class.

`#dyn_sem_table` checks each rule, and each datatype's type rule, again at the type rules that the table's module sees. A rule's module may have seen another type rule, through an import that the table's module does not see. A rule registered where `Num` is `Int` would otherwise pass a table where `Num` is `Nat`. The table reports:

```plaintext "A rule that does not fit the table (StrataDynTest/Exec/RecheckTest.lean)"
error: the rule RecheckRule.posI for hid.pos does not fit this table's type rules: operand x of hid.pos: expected Nat, but RecheckRule.posI takes Int
```

Registration checks a rule's shape, not what it means: rules are trusted. Nothing compares a rule with its instruction's declared effect either, so a `pure` instruction whose rule changes state is accepted ({ref "env-ops"}[Environment 3: Instructions]). What a rule's body uses is a matter for review, as elsewhere in Lean. That covers its axioms, `implemented_by`, `@[extern]` and `partial` definitions, whether it reads a ref's location (`Ref.loc`), and whether it reaches the world only through its parts.

## 4. Linking, validation and the machine
%%%
number := false
tag := "inside-machine"
%%%

### Linking
%%%
number := false
tag := "inside-linking"
%%%

_Linking_ turns a checked module into a linked module, an `LModule`, over the model at the machine's token, `M.at`. `link M m` reads only the functions' bodies, not their contracts, and resolves every name once:

* each instruction to its wrapper at its type arguments' tags, and a step then looks nothing up and compares no strings;
* `base.refNew`, `refGet` and `refSet` to the machine's heap instructions, and `base.callCode` to the machine's call;
* each type to its tag, each label to its block's index in its body or to the body's exit, and each function reference to a closure that binds nothing;
* each region to a body of the module.

It looks names up in the model's `NameMap`s, 2-3 trees that the table generator builds, and reports every instruction without a rule at once, as `Fault.missingRules`. It records each function's _slots_: one more than the largest value id the function or any of its regions defines. A frame keeps its values in an array of that many slots, indexed by id.

Linking also records each block's _scope_: the values defined in other blocks that the block reads, with their tags. A block's scope is what is in scope at its entry under the body's dominator tree and live there, where a value is live at a block's entry if some path from the entry reads it:

```leantext "A linked block (StrataDyn/Exec/Link.lean)"
/-- A block.  `scope` lists the values of other blocks it reads, with their tags. -/
structure LBlock where
  label : Label
  params : List (Nat × Ty)
  scope : List (Nat × Ty)
  insns : List (LInsn M)
  term : LTerm M
```

### Validation
%%%
number := false
tag := "inside-validation"
%%%

_Validation_ is the function `checkModule`, which checks a linked module once, before it runs. `WF lm` is the proposition `checkModule lm = .ok ()`. It checks each block in its entry context, its scope followed by its parameters:

* each instruction finds its operands in the context at the tags its wrapper takes, and adds its result to the context;
* each successor receives its payload, and each region takes the arguments and yields the result of its signature;
* each edge into a block supplies the block's parameters' tags, and has the block's scope in its own context; an edge to the body's exit supplies one value of the body's result tag;
* `refNew`, `refGet` and `refSet` take a cell and its contents at the cell type's tags, and `callCode` passes a closure the arguments its tags take;
* each function's entry block has an empty scope, and every value a body defines is an id below its slots.

Validation checks no ref and no closure, since either may be anywhere a value may be.

Nothing proves yet that validation accepts what linking makes of a well-formed module without extern functions: the theorem `link_wf` is still to be proved (`StrataDyn/Exec/Link.lean`). So nothing rules out that a run of such a module ends with `Fault.invalid` before its first step. A run validates the linked module, and rejects it if validation fails, so this cannot give a wrong result.

The machine's _invariant_ is `StateOK`, a property of a state. For a state about to run code, it says that the top frame runs code that validation accepted, in a store that _agrees_ with a context: each value the context gives the tag `t` is bound, at tag `t`. For a pending transition, it says what performing the transition needs:

```leantext "The invariant (StrataDyn/Exec/Machine.lean)"
/-- The invariant of a state: what performing its pending transition needs.  A pending
edge or entry holds the frame it leads to, which runs checked code; a rule at a request or about
to run again runs in the top frame. -/
def StateOK (B : Ty) (s : State M) : Prop :=
  match s.mode with
  | .exec => CoreOK m B s.core
  | .jump to => CoreOK m B { s.core with top := to }
  | .call callee w => CoreOK m B { s.core with top := callee, conts := w :: s.core.conts }
  | .ret v => LeftOK m B s.core v
  | .request i _ => InstOK m s.core.top i ∧ ContsOK m B s.core.top.func.ret s.core.conts
  | .again r => InstOK m s.core.top r.inst ∧ ContsOK m B s.core.top.func.ret s.core.conts
  | .done _ => True
```

`start` builds the first state of a run from `WF lm`, the arguments and a _snapshot_, a heap and a world, with its `StateOK`. The default snapshot, `Snapshot.initial`, is an empty heap and the initial world. A run ends with a snapshot, so a caller can run a module's top level, then one of its functions on the cells the top level made, as Python runs a module and then a function it defines. One value holds both, so no run starts from one run's heap and another run's world.

### The step function
%%%
number := false
tag := "inside-the-step-machine"
%%%

A machine _state_ is a `State`. It holds the running frame, the frames waiting below it, the heap, the world, a pending mode and the number of choices drawn:

```leantext "States (StrataDyn/Exec/Machine.lean)"
/-- The frames and the data: the running frame, the frames waiting below it, the heap and the
world. -/
structure Core where
  top : Frame M
  conts : List (Wait M)
  heap : Heap M
  /-- The environment's world, which the machine threads but never reads. -/
  world : M.W

/-- A state of the machine. -/
structure State where
  core : Core M
  mode : Mode M := .exec
  /-- How many choices the oracle has made: the next one is its answer at this index. -/
  drawn : Nat := 0
  /-- Reserved for a symbolic reading's path condition. -/
  path : Unit := ()
```

A _pending mode_ is the transition the next step performs:

```leantext "Pending modes (StrataDyn/Exec/Machine.lean)"
/-- The pending transition: run the top frame's next instruction or terminator, take an edge,
enter a body, leave the top frame, answer a rule's world request, or nothing, the run having
ended.  A hook sees each before the machine performs it. -/
inductive Mode where
  | exec
  /-- Continue in `to`, a block of the top frame's body. -/
  | jump (to : Frame M)
  /-- Run `callee`, a function's entry block or a region's, with `w` waiting on it. -/
  | call (callee : Frame M) (w : Wait M)
  /-- Leave the top frame with `v`. -/
  | ret (v : Dyn M.interp)
  /-- The rule of operation `i`, whose frame is the top one, is at a world request: the head
  of `t`, a choice or an update. -/
  | request (i : Inst M) (t : i.Tree)
  /-- The rule of operation `r.inst`, whose frame is the top one, jumped to its `Again`: run it
  again, on its operands, with the state `r.st`. -/
  | again (r : Reentry M)
  | done (r : Result M.interp)
```

`step` takes an oracle and a state with its `StateOK`, and performs the pending transition. An instruction that transfers control leaves a pending mode for the next step, so each edge, entry, request and run of a rule again is a step of its own and reports an `Event`. The result of a step carries the next state's `StateOK`, so every step preserves the invariant by its type:

```leantext "One step (StrataDyn/Exec/Machine.lean)"
inductive StepR where
  | next (e : Event) (s : State M) (h : StateOK m B s)
  | final (r : Result M.interp) (heap : Heap M) (world : M.W) (drawn : Nat)

/-- One step: perform the pending transition. -/
@[inline] def step : (s : State M) → StateOK m B s → StepR m B
```

With the invariant, the machine reads each operand at its tag with `getT`, which takes the proof that the value has that tag, and checks no type and no binding of the program's values.

### Runs
%%%
number := false
tag := "inside-runs"
%%%

The reference semantics is the set of runs of the _step relation_ `StepRel hwf` (`StrataDyn/Exec/Trace.lean`), which steps from a state wherever `step` does under some oracle. A run gives a _configuration_ at every time: a state that is still running, or how the run ended, its result, snapshot and choices, which every later time keeps. A run answers each choice freely. Every state steps (`stepRel_total`), since a fault is an outcome and not a stuck state. The run under one oracle, `oracleRun`, is one of the runs, and its configurations, `trace hwf oracle s h n`, compute; every run is the run under some oracle (`complete`).

`always` proves that a property holds at every configuration of every run, from a property of states that each step preserves under every oracle. A run's behaviour, `behW`, is what an observer of the world sees, and trace refinement, `Refines` and `OracleRefines`, says that every run of one module improves on a run of another. `docs/Dyn.md`, §5, "Reasoning about runs", describes both, and the ways to prove trace refinement.

### The fused engine
%%%
number := false
tag := "inside-the-fused-loop"
%%%

`runFused` executes the run under an oracle, but performs each transfer in the step that decides it. An edge, an entry into a body, a rule's choices, its world accesses and its cell requests take no step of their own, and no event is built. A run of a rule again is a fused step of its own. The theorem `runFused_eq` states that the fused engine follows the run:

```leantext "runFused_eq (StrataDyn/Exec/Fused.lean)"
theorem runFused_eq : ∀ (n : Nat) (s : State M) (h : StateOK m B s),
    ∃ t, n ≤ t ∧ trace hwf oracle s h t = (runFused hwf oracle n s h).config
```

`runFused` on `n` fuel stops or ends at the configuration that the run under its oracle has after some `t ≥ n` steps: in the same state, or with the same outcome, snapshot and number of choices. Its corollaries are these:

* `reach_runFused`: every state at which `runFused` stops can be reached by steps of the module;
* `beh_of_runFused`: when `runFused` ends, the run under its oracle ends with the same result, snapshot and choices, and behaves as `.term` with that result;
* `runFused_of_run`: a run that has ended after `n` steps, `runFused` under its oracle ends on `n` fuel;
* `diverges_iff_fused`: some run never ends if and only if, under some oracle, `runFused` runs out of fuel on every fuel;
* `runHooked_fused`: a hook that only observes, run long enough, ends as `runFused` does;
* `runHooked_resume`: a run that a hook which never modifies stopped, resumed with `runFused`, ends at a configuration of the uninterrupted run.

A rule's requests are each a step but all part of one fused step, so no fixed factor bounds `t` by `n` across models. While's `sum 100` ends after 606 fused steps and 810 steps of the relation.

### Fuel and hooks
%%%
number := false
tag := "inside-fuel-and-hooks"
%%%

Every step costs one unit of fuel, whatever its mode. A _hook_ is a function of its own state, a step's event and the state the step led to. `runHooked` runs `step` and consults a hook after each step, and the hook continues the run, stops it, or replaces the state with another that satisfies `StateOK`. When the fuel runs out or the hook stops the run, `runHooked` returns the state with its `StateOK`, from which the run can resume, so `runHooked` on one unit of fuel is a debugger's single step:

```leantext "Hooks (StrataDyn/Exec/Machine.lean)"
/-- What a hook asks for after a step. -/
inductive Action (ρ : Type) where
  | continue (st : ρ)
  /-- Continue from `s` instead: a well-formed state. -/
  | modify (st : ρ) (s : State M) (h : StateOK m B s)
  | stop (st : ρ)

/-- A hook with state `ρ`. -/
abbrev Hook (ρ : Type) : Type := ρ → Event → State M → Action m B ρ
```

`runHooked_observer` states that a hook that only observes ends at the configuration of the run under its oracle.

### The checks at run time
%%%
number := false
tag := "inside-the-checks-at-run-time"
%%%

Two checks remain while a module runs. The _cell check_ runs at every access of a cell, the machine's and a rule's. The location must be below the heap's size and hold a value of the access's tag, or the run ends with `Fault.badCell`:

```leantext "The check of a cell (StrataDyn/Exec/Machine.lean)"
/-- **The check of a cell**: location `l` of `heap` holds a value of tag `t`, and `ok` takes
the proofs, or else `bad`, which takes `()` so that a fault is built only when the check fails.
Every access of a cell, the machine's and a rule's, goes through it. -/
@[inline] def Heap.cell {R : Type} (heap : Heap M) (l : Nat) (t : Ty)
    (ok : (hl : l < heap.cells.size) → (heap.cells[l]'hl).1 = t → R) (bad : Unit → R) : R :=
  have := heap.holds l t
  if h : heap.Holds l t then ok h.lt h.code else bad ()
```

The _call check_, `LModule.callee`, runs at every call and every bind of a closure. The function must exist, take the closure's bound values' tags followed by the call's tags, and return the call's result tag, or the run ends with `Fault.badCall`. The machine checks nothing else.

For a module whose rules are certified, the machine's own cell check never fails in the runs that heap safety covers, but the call check still can ({ref "wip-safety"}[Proofs about runs 1: Heap safety]).

# Proofs about runs
%%%
number := false
tag := "wip"
file := "proofs-about-runs"
%%%

The proofs of this chapter build on runs and trace refinement ({ref "run"}[Testing]; `docs/Dyn.md`, §5). Certificates say what a language's rules may touch. With them, Dyn proves that a run leaves alone what it cannot reach, that the machine's checks of cells do not fail, and that a target that promotes its source's cells improves on the source's behaviour. Sections 1 and 2 describe these proofs, which are in the package, and what each of them assumes. Abstract interpretation builds an analyser for a language's modules from abstract domains and one lemma per instruction, with a theorem that what the analyser finds holds at every point of every run. It is under development and not yet in the package. It has chapters of its own, and section 3 points to them.

## 1. Certificates for rules
%%%
number := false
tag := "wip-cert"
%%%

Rules are trusted ({ref "env-sem"}[Environment 7: Meaning]). A rule is generic in the run token, so it cannot build a ref from a number in a term generic in the token, but Lean does not prove a rule parametric: classically, a rule can still build a ref at the machine's token. A rule's _certificate_ says that it reaches only the cells and captures cells it is given. Every ref and closure that the rule hands the machine, in a request, a result, an exit or the world, is valid in the _typing_ of the heap at that point, whenever everything the machine handed it was. A typing gives a tag to some cells and a list of tags to some captures cells. It does not record which function a closure names or at which signature: the machine checks that at every call. A table is _certified_ when every rule of it has a certificate. A proof about runs that needs this fact, such as ref-to-reg's, takes the table's certificate as a hypothesis, so a language that certifies its table can apply every such theorem to its own programs.

A language certifies its table in two steps.

1. Its _accounts_, an `Accounts M`, say where the refs are in a value of each tag: the cells its refs name, at their contents' tags, and the captures cells of its closures. They also give the accounts of the world and of each rule's state. A ref's and a closure's accounts are fixed by the engine, and the literals hold none. Accounts that leave a ref out make the certificates of the rules that reach it unprovable, so a mistake fails safe.
1. `#dyn_certs S A [h₁, …]` proves the certificate of every operation of the table `S`, each as its own theorem `cert.op`, with the tactic `dyn_cert`, which unfolds the definitions `h₁, …` of the accounts. It then proves `cert.ops`, that every operation is certified, from those theorems alone, and `Model.certified_of_ops` turns it into the table's certificate. The operations' proofs elaborate in parallel. A proof that fails names its operation and shows the goals left, each a request, result, exit or world that the tactic could not show valid. An operation whose certificate is proved by hand before the command is not proved again.

```leantext "While's accounts and certificate (StrataDyn/Examples/While/Cert.lean)"
/-- Where the refs of a value of While's tag `t` are.  Heads `0` and `1` are a ref's and a
closure's; `7` is `Array` and `8` is `Except`; the other heads hold no refs. -/
def acct : (t : Ty) → WhileSem.interp Run t → List Loc
  | .app 0 [a], x => [.cell x.loc a]
  | .app 1 [.list ts, r], f =>
    if (WhileSem.model.at.fnOf (ts := ts) (r := r) f).captured = 0 then []
    else [.caps (WhileSem.model.at.fnOf (ts := ts) (r := r) f).captured]
  | .app 7 [a], xs => xs.toList.flatMap (acct a)
  | .app 8 [e, a], x => match x with
    | .error v => acct e v
    | .ok v => acct a v
  | _, _ => []
termination_by structural t => t

/-- While's accounts. -/
def accounts : Accounts WhileSem.model.at where
  acct := acct
  world _ := []
  st _ _ := []
  ref t x := by simp only [acct, RunModel.locOf, cast_eq]
  fn ts r x := by simp only [acct]
  unit := rfl
  bool _ := rfl
  int _ := rfl
  float _ := rfl
  str _ := rfl

-- One theorem per operation, `cert.while.add` and so on, each proved by `dyn_cert`, and
-- `cert.ops`, which assembles them.
#dyn_certs WhileSem accounts [accounts, acct]

/-- **While's table is certified**: each of its rules respects every typing of the heap under
which its operands are valid. -/
theorem certified : WhileSem.model.Certified accounts :=
  Model.certified_of_ops cert.ops
```

A datatype whose values hold refs needs accounts that list them, as While's do for `Array` and `Except`. A rule that gives a ref another contents' type, as the test environment's `ex.retype` does, has no certificate. `dyn_cert` does not prove the certificate of a rule that builds a closure over a list of cells, such as the test environment's `ex.mkClo`, which has the shape of Python's `mkClosure`. Such a rule needs a certificate written by hand, and the package has none yet. `StrataDynTest/Exec/CertTest.lean` pins both cases.

`link_rulesOK` carries a table's certificate to every instruction and terminator of every module linked against the table, as `LModule.RulesOK` (`StrataDyn/Exec/CertLink.lean`). The theorems below take `LModule.RulesOK` as their hypothesis about rules. A certificate is stated with a _spec_, which says what a rule's tree may do, at a ghost state that only proofs carry. A certificate's ghost state is a typing of the heap (`StrataDyn/Exec/Spec.lean`, `StrataDyn/Exec/CertModel.lean`; {ref "app-absint-specs"}[Appendix E: Specs]).

### The frame theorem
%%%
number := false
tag := "wip-frame"
%%%

A run of a module whose rules are certified leaves alone what it cannot reach (`StrataDyn/Exec/Frame.lean`). A location is _reachable_ from a list of roots through the accounts of the cells and captures cells reached. `frame_startCore` starts a run at a function's entry, and states that the cells unreachable from the arguments and the world are unchanged at every configuration of every run, ended or not. It also needs the refs that the run starts with to name cells of their tags. `frame_startCore_ok` gives that hypothesis for arguments that hold no ref and a snapshot that a typing of its heap types: the engine's start, when the initial world holds no ref, or the snapshot where a run of a certified module ended.

`frame_call` states the same of one call (`StrataDyn/Exec/Call.lean`). Every run of a call keeps the cells that the callee's frame and the world do not reach, though the caller's frames may: along each run of the callee until it returns, and when the caller resumes. Until the callee returns, the run of a call is a run of the callee from its start, with the caller's frames below (`run_call`), so a fact proved of every run of the callee holds inside the call too. `frame_call_of_run` applies `frame_call` at a call that a run reaches from a function's start. A front end can rely on it to say, for instance, that a callee does not change a cell that only its caller holds. `StrataDynTest/Exec/LinkedCallTest.lean` does so for two While functions that go through `lower` and `link`, and `StrataDynTest/Exec/LinkedFrameTest.lean` applies `frame_startCore` to one.

### Heap safety
%%%
number := false
tag := "wip-safety"
%%%

A run of a module whose rules are certified uses only the cells it may (`StrataDyn/Exec/Safety.lean`). Every ref it holds is valid in a typing of the heap, so every access that the machine checks finds a cell of its tag (`access_ok`). A rule may still stop with `Fault.badCell` itself, since a certificate says nothing of faults. `LModule.Avoids` says that no rule of a linked module does. With it, `never_badCell_startCore` states that no run from a function's entry, on arguments that hold no ref, faults with a bad cell, from the engine's start when its world holds no ref, or from the snapshot where another run ended. `Fault.badCall` is not covered, since a typing does not record the function a closure names.

Nothing yet proves `LModule.Avoids` for a module that `link` makes from a table, While's included. `StrataDynTest/Exec/SafetyTest.lean` proves heap safety only for a module linked by hand, whose instructions are the machine's own and whose terminators are returns. Without `LModule.Avoids`, `access_ok` still says that the machine's own check of a cell never fails in such a run, so a `badCell` fault there comes from a rule that stops with it itself.

## 2. What promoting cells keeps
%%%
number := false
tag := "wip-r2r"
%%%

`StrataDyn/RefToRegSound/` proves that a target that promotes its source's cells improves on the source's behaviour, for a language whose table is certified. The theorems do not mention the pass, and it is not yet proved that the pass's own output meets their hypothesis: see the end of this section.

`refToReg_sound_cell` takes a source module linked and validated, the table's certificate, a well-formed linked target, and a hypothesis `PromotionOK lm lm₁`: the linked target promotes the linked source's cells, block by block. It also takes a hypothesis that the initial world holds no ref. It covers only a start of a function from the initial snapshot, `.initial`, an empty heap and the initial world, on arguments that hold no ref. For every such start, every observation of the world and every oracle, the target's run improves on the source's run under the same oracle, up to a bad cell: the two runs show the same, or the source faults with a bad cell after showing what the target also shows. This is trace refinement under one oracle (`Exec.OracleRefines`) whose only excused result is a bad cell. Promotion keeps every choice, so the oracle is shared. A start from the snapshot where another run ended, as a function of a Python module would start after the module's top level, is not covered.

`refToReg_sound` is a weaker corollary, which excuses every wrong result of the source: a failed rule or a bad call as well as a bad cell. When no rule of the linked source stops with a bad cell itself (`LModule.Avoids`, {ref "wip-safety"}[Heap safety]), `refToReg_sound_eq` gives equal behaviours under every oracle, and `refToReg_sound_runs` states that every run of each module behaves as some run of the other. Nothing yet proves that hypothesis for a module that `link` makes, so `refToReg_sound_cell` is the theorem that a language can apply today. The theorems observe the world, not the number of choices a run makes.

`PromotionOK` describes what ref-to-reg does to a block (`StrataDyn/RefToRegSound/Cert.lean`). A read of a promoted cell is removed, and a value that holds the cell's content stands for its result. A write of a promoted cell is removed. A `refNew` stays. A read or a write of a cell that is not promoted stays, also when the function did not allocate the cell, as for a parameter or a closure's captured cell. Every other instruction and the terminator stay, with each operand replaced by a target value that holds the source operand's value. `StrataDynTest/RefToRegSound/SoundTest.lean` proves `PromotionOK` for ref-to-reg's example in `docs/Dyn.md`, §3, and for functions that read and write a cell they did not allocate, each linked by hand, with targets written by hand.

At While's table, the theorem is one line, from While's certificate. While's world holds no ref, so `rfl` proves the hypothesis about it. `Wrong` holds only of a bad cell, the one wrong result that it excuses:

```leantext "Ref-to-reg at While's table (StrataDyn/Examples/While/RefToRegSound.lean)"
theorem refToReg_sound_while {α : Type} {m : Module While.env α} {f : Name}
    {lm : LModule WhileSem.model.at} {hw : WF lm} {i : Nat}
    (hp : prepare WhileSem.model m f = .ok ⟨lm, hw, i⟩) {lm₁ : LModule WhileSem.model.at}
    (hw₁ : WF lm₁) (hcert : PromotionOK lm lm₁)
    (args : List (Dyn WhileSem.model.at.interp)) (hargs : ∀ d ∈ args, acct d.1 d.2 = [])
    {B : Ty} {c : Core WhileSem.model.at} {h : CoreOK lm B c}
    (hs : startCore hw i args .initial = .ok ⟨B, c, h⟩) :
    ∃ B₁ c₁ h₁, startCore hw₁ i args .initial = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : WhileRules.World → O),
        Exec.OracleRefines hw hw₁ obs Wrong ⟨⟨c, .exec, 0, ()⟩, h⟩ ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩ :=
  refToReg_sound_cell WhileSem.model accounts certified hp hw₁ hcert rfl args hargs hs
```

The theorems hold for any target that `PromotionOK` relates to the source. That the pass's output, linked, satisfies `PromotionOK` is the static half of the proof, which relates the pass's plan, through linking, to the linked code. It is not yet proved, so a front end cannot yet conclude from these theorems that ref-to-reg keeps the behaviour of its modules. The rule that an instruction reaches only the cells it is given is not assumed: it is the table's certificate, which linking carries to every instruction of the linked module (`link_rulesOK`). Python has no semantic table yet ({ref "missing"}[Missing features]: _Rules for Python's environment_), so none of these theorems applies to Python's modules yet.

## 3. Abstract interpretation
%%%
number := false
tag := "wip-absint"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
Abstract interpretation of Dyn modules is under development and not yet in the package. Its chapters carry the same note.
:::::

An analysis of a language's modules is built from a _domain_. A domain gives abstract types to the Dyn types that the rules use, or, if it is relational, abstract states that relate values to each other. It also gives instructions transfer functions, each with a lemma that the instruction's rule meets it, proved at the rule's own Lean types. `#dyn_absint` builds the rest: a solver, a checker of what a solver finds, and the theorem that, on a well-formed module that links, the facts that the checker accepts hold at every point of every run, including runs that never end. The theorem rests on the checker alone, so a front end may bring a solver of its own. The analysis follows regions, and follows a call through summaries of its callee when the code shows which function the call calls. Four chapters describe it:

* {ref "absint"}[Abstract interpretation: the idea] explains abstract interpretation from the beginning, on While functions worked by hand;
* {ref "absint-dyn"}[Writing an analysis in Dyn] builds analyses of While: domains, transfer functions and their proofs, `#dyn_absint`, termination, reduced products, calls and contexts, solvers and tables, and what a front end can do to be analysable ({ref "absint-front-end"}[Using it in a front end]);
* {ref "absint-limits"}[Abstract interpretation: limits and further reading] lists what the framework does not do;
* {ref "cs13"}[Following Concrete Semantics] carries chapter 13 of Nipkow and Klein's *Concrete Semantics* over to While.

# Abstract interpretation: the idea
%%%
number := false
tag := "absint"
file := "abstract-interpretation"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
This chapter and the three after it describe abstract interpretation of Dyn modules, which is being developed and is not yet in the package. Its names, commands and theorems may change before it lands. Unlike the guide's other listings, most listings of these chapters are not compiled against the package: a title that says "under development" marks one, and names the file the code is in where it has one.
:::::

:::::callout "Who this chapter is for"
This chapter and the next three are for anyone writing a static analysis of a Dyn language who wants a theorem that the analysis's results hold on every run. This chapter explains abstract interpretation from the beginning, on small While functions worked by hand, and assumes you have not met it before. {ref "absint-dyn"}[Writing an analysis in Dyn] shows how to write an analysis, and assumes you have read {ref "env-sem"}[Environment 7: Meaning] and {ref "run"}[Testing]. Its sections on instructions with successors and with regions also read a rule as a tree, as {ref "inside-rules-as-trees"}[Inside the execution DSL: Rules as trees] explains.
:::::

## 1. An example worked by hand
%%%
number := false
tag := "absint-example"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
Dyn's constant propagation, which finds this section's result, is not yet in the package.
:::::

Here is a While function:

```whilelang "A function with a branch it never takes (under development, in StrataDynTest/Absint/ConstPropTest.lean)"
fun f(n : Int) : Int {
  var x : Int := 6;
  var y : Int := x - 4;
  if (y <= 3) { return x * y; }
  return n;
}
```

Notice that this function is unusual: it always returns `x * y` and does not actually depend on the value of `n`. This can be found directly through constant propagation, a limited form of abstract interpretation that propagates constant values through a program.

Start with a real run. A run of `f` on `5` sets `x` to `6` and `y` to `2`, finds that `y <= 3` is true, and returns `12`. A run on any other argument goes exactly the same way. Constant propagation reaches the same conclusion without picking an argument at all. For each value, it records what it knows: a constant, `⊤` if the value could be anything, or `⊥` if no value has reached it yet. It starts with `⊤` for the argument `n`, because `f` may be called with any argument. Then it evaluates each instruction on what it has recorded for the operands:

::::nowrap
:::table +header
*
  * Value
  * Instruction
  * What the analysis records
*
  * `n`
  * the argument
  * `⊤`
*
  * `x`
  * `6`
  * `6`
*
  * `y`
  * `x - 4`
  * `6 - 4 = 2`
*
  * `y <= 3`
  * `2 <= 3`
  * `true`
*
  * `x * y`
  * `6 * 2`
  * `12`
*
  * the result
  * `return x * y`
  * `12`
:::
::::

Here the analysis knows that the condition is `true`, so it never follows the branch to `return n`, and the values there stay `⊥`. The result is `12`, so every run of `f` that returns a value returns `12`.

Constant propagation is one example of _abstract interpretation_, which runs a program on descriptions of values, not on the values themselves. Constant propagation's descriptions are "this constant", "anything" and "nothing yet". Other analyses use other descriptions, such as "a positive odd integer". The sections below name each ingredient of the computation above, one at a time.

## 2. Abstract values and concretization
%%%
number := false
tag := "absint-values"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
Dyn's abstract types and domains, which this section introduces, are not yet in the package.
:::::

A _concrete value_ is a value that a run computes. While's concrete values, for example, are its integers and booleans.

An _abstract value_ describes a set of concrete values. For example, the right-hand column of the table above holds abstract values of constant propagation: `⊤` describes every concrete value, `6` describes just the integer 6, and `⊥` describes none.

The _concretization_ `γ` says which concrete values an abstract value describes. We write `γ a v` when the abstract value `a` describes the concrete value `v`:

::::nowrap
:::table +header
*
  * `a`
  * the concrete values `v` with `γ a v`
*
  * `⊥`
  * none
*
  * `6`
  * `6`
*
  * `true`
  * `true`
*
  * `⊤`
  * every value
:::
::::

The _order_ `a ⊑ b` holds when `b` describes every value that `a` describes. You can read `a ⊑ b` as "`b` is at most as precise as `a`". For example, `⊥ ⊑ 6` and `6 ⊑ ⊤` hold, but `6 ⊑ 7` does not.

An _abstract domain_ is a type of abstract values together with a concretization, an order, and the join and widening of section 4. Constant propagation's abstract domain, for example, has the abstract values `⊥`, each constant, and `⊤`. Dyn splits this notion in two. An _abstract type_ is one Lean type of abstract values with these operations, such as `CP`, the abstract values of constant propagation. A _domain_ is a named declaration that gives each type of a language its abstract type, for example intervals for integers and sets of truth values for booleans. The next chapter uses the two words in this sense.

An _abstract state_ gives an abstract value to each variable of a program point, or it is `⊥`, the abstract state that describes no state. In section 1, the abstract state at `return n` is `⊥`.

A domain whose abstract states give each variable its own abstract value is _non-relational_. A _relational_ domain describes variables together: zones, for example, record bounds such as `x - y ≤ 3` ({ref "absint-relational"}[Relational transfer functions]). A _reduced product_ runs two domains side by side, and after each instruction lets each one tighten what the other knows ({ref "absint-product"}[Reduced products]).

If you have read about abstract interpretation before, you may have met an _abstraction_ `α`, which maps a set of concrete values to the most precise abstract value that describes all of them, and a _Galois connection_ between `α` and `γ`. Dyn's framework uses `γ` only. Besides `γ`, it needs only the abstract value of a single concrete value, `abs v`: for example, `abs 6 = 6`.

## 3. Transfer functions
%%%
number := false
tag := "absint-transfer"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
Dyn's transfer functions, which this section introduces, are not yet in the package.
:::::

A _transfer function_ is the abstract version of one instruction: given the abstract values of the operands, it gives the abstract value of the result. For example, constant propagation's transfer function for `+` adds two constants:

:::table +header
*
  * operands
  * result
*
  * `2`, `3`
  * `5`
*
  * `⊤`, `3`
  * `⊤`
*
  * `⊥`, `3`
  * `⊥`
:::

A transfer function is _locally sound_ when its result describes every concrete result. For the transfer function `add♯` of `+`, local soundness says: if `γ a x` and `γ b y`, then `γ (add♯ a b) (x + y)`. In words, if `a` describes `x` and `b` describes `y`, then `add♯ a b` describes `x + y`. Local soundness is about one instruction at a time.

Some instructions decide where the run goes next. Such an instruction, a _terminator_, ends a block and names the blocks that the run may continue at, its _successors_. Its transfer function also says which successors a run may take. For example, While's `if` lowers to `base.branch`, which continues at its first successor if its condition is `true` and at its second otherwise. On the abstract value `true`, the transfer function of `base.branch` allows only the first successor. So in section 1, the analysis never reaches `return n`.

## 4. Joins, fixpoints and widening
%%%
number := false
tag := "absint-fixpoint"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
Dyn's solver, which computes the rounds of this section, is not yet in the package.
:::::

Where two paths meet, the analysis needs one abstract value that covers both. The _join_ `a ⊔ b` is an abstract value above both `a` and `b`, so it describes every value that either of them describes:

::::nowrap
:::table +header
*
  * `a`
  * `b`
  * `a ⊔ b`
*
  * `1`
  * `1`
  * `1`
*
  * `⊥`
  * `3`
  * `3`
*
  * `1`
  * `2`
  * `⊤`
:::
::::

Notice the last row: no single constant describes both `1` and `2`, so their join is `⊤`.

A loop makes a value depend on itself. For example, `sum` adds `1, …, n`:

```whilelang "A loop (StrataDynTest/Examples/While/Programs.lean)"
fun sum(n : Int) : Int {
  var s : Int := 0;
  var i : Int := 1;
  while (i <= n) { s := s + i; i := i + 1; }
  return s;
}
```

The loop's _header_ is the point where each iteration starts. The variable `i` reaches the header from two places: it is `1` on entry and `i + 1` after the body. So the analysis computes the header's abstract values in rounds:

1. On entry, `i` is `1` and `s` is `0`. The body passes back `2` and `1`, so `i` becomes `1 ⊔ 2 = ⊤` and `s` becomes `0 ⊔ 1 = ⊤`.
1. In the second round, the body computes `⊤ + ⊤ = ⊤` and `⊤ + 1 = ⊤`, so the header keeps `⊤`, and nothing changes.

A _fixpoint_ is an assignment of abstract values that a round does not change. Here the abstract values after the first round are a fixpoint, because the second round leaves them as they are.

A _post-fixpoint_ is an assignment of abstract values that every transfer function respects. It meets two conditions. First, at each instruction, the transfer function's result is `⊑` the abstract value recorded for the instruction's result. Second, for each successor that the transfer function allows, what it passes is `⊑` the abstract values of the successor's parameters. Every fixpoint is a post-fixpoint.

A domain has _finite height_ when an abstract value can grow only a bounded number of times. In constant propagation, for example, a value grows at most twice: from `⊥` to a constant, and from the constant to `⊤`. Without such a bound, the abstract values can keep growing forever. In the domain of integer intervals, for example, `i` in `sum` is `[1, 1]`, then `[1, 2]`, then `[1, 3]`, and so on. A _widening_ `a ∇ b` is an upper bound of `a` and `b` that jumps ahead so that the rounds stop. For example, `[1, 1] ∇ [1, 2] = [1, +∞]`. A domain of finite height, such as constant propagation, can use its join as its widening. Intervals cannot, and {ref "absint-dyn"}[Writing an analysis in Dyn] gives them a widening.

## 5. Soundness
%%%
number := false
tag := "absint-soundness"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
Dyn's checker and its soundness theorem, which this section describes, are not yet in the package.
:::::

An analysis is _sound_ when the abstract values it computes describe every state that a run reaches. Since this is a property of every run, we call it _global soundness_.

Global soundness follows from two properties:

* every transfer function is locally sound;
* the computed abstract values are a post-fixpoint, and they give `⊤` to the parameters of each function, since a run may start at any function, on any arguments.

Here is why. A run starts in a state that the abstract values describe, because the parameters' abstract values are `⊤`. Each step of the run executes one instruction. Local soundness says that the transfer function's result describes the instruction's concrete result. The post-fixpoint condition says that the transfer function's result is `⊑` the abstract value recorded for the instruction's result, so the recorded value describes the concrete result too. So each step from a state that the abstract values describe reaches another such state, and by induction they describe every state that a run reaches.

In Dyn's framework, an analysis has two parts. A _solver_ computes the abstract values in rounds, as in section 4, and records an abstract state at the entry of each block. A _checker_ then makes one pass over the program. It recomputes each block from its entry state by the transfer functions, and accepts the solver's abstract values only if they are a post-fixpoint that gives `⊤` to the parameters of each function. The proof of global soundness is about the checker alone, so the solver needs no proof: if its abstract values are not a post-fixpoint, the checker rejects them.

Dyn's own solver runs a bounded number of rounds. If they have not settled by then, it gives up, with `⊤` everywhere. Two more theorems are about this solver. They need the order to be reflexive and transitive, `⊤` to be above every abstract value, and the join and the widening to be above their arguments. The first says that the checker accepts what the solver finds on every module whose instructions and calls the analysis supports. The second also needs that repeated widening cannot grow a value forever, and says that a large enough bound then lets the rounds settle before the solver gives up.

Calls fit the same scheme. A _summary_ of a function is its analysis on a description of its arguments, and gives a description of what it returns. A call whose arguments the summary's description covers reads its result from the summary, and the checker checks the summary as it checks a function, from the description of its arguments. A function may have several summaries, so Dyn analyses it in several _contexts_: once as the start of a run, on any arguments, and once per summary. For example, let `main` call `inc(1)` and `inc(5)`, where `inc(x)` returns `x + 1`. With its default of a summary per input, constant propagation gives `inc` two summaries: from `1` it returns `2`, and from `5` it returns `6`. As the start of a run, on any argument, `inc` returns `⊤`. {ref "absint-calls"}[Calls and contexts] shows how Dyn does this.

# Writing an analysis in Dyn
%%%
number := false
tag := "absint-dyn"
file := "writing-an-analysis"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
The framework of this chapter is not yet in the package, and its names may change before it lands. A listing whose title names a file without saying "under development" is quoted from the package, and the guide's build checks that it is still there; every other listing is static. A box titled "Planned interface, not yet built" shows syntax that the framework does not accept yet. A paragraph that starts "Known limitation" describes behaviour that is expected to change.
:::::

:::::callout "Who this chapter is for"
This chapter is for anyone writing an analysis of a Dyn language. It builds an analysis of While over intervals and truth values, pairs intervals with parities, and then analyses calls and replaces the solver and the table. It assumes you have read {ref "env-sem"}[Environment 7: Meaning] and {ref "run"}[Testing]. It uses the ideas of {ref "absint"}[Abstract interpretation: the idea], and defines again, on intervals, each one that it uses. The parts of section 5 on instructions with successors and with regions also read a rule as a tree ({ref "inside-rules-as-trees"}[Inside the execution DSL: Rules as trees]). {ref "app-absint"}[Appendix E: Inside the analysis framework] states the framework's theorems in full, for readers who want the proofs.
:::::

:::::callout "What is expected to change"
These parts of the framework are expected to change, besides the known limitations that the sections note:

* A transfer function of an instruction with regions has no type parameters, and takes its operands and its regions' answers at one abstract type. Polymorphic transfer functions, and transfer functions over several abstract types, will take regions too ({ref "absint-regions"}[Instructions with regions]).
* `@[dyn_abs]` takes Dyn types without parameters. Type constructors, such as `Base.Sequence`, and datatypes with type parameters, such as `Base.Except`, will get abstract types ({ref "absint-domains"}[Domains], {ref "absint-sum"}[Datatypes]).
* The analysis will follow cells. Its facts say nothing about the heap ({ref "absint-limits-list"}[Limits]).
:::::

The chapter writes abstract values and their operations with the symbols below. Section 2 defines each of them on intervals. An abstract value _describes_ a set of concrete values, the values that a run computes, and the interval `[1, 3]`, for example, describes the integers `1`, `2` and `3`.

::::nowrap
:::table +header
*
  * Symbol
  * Meaning
  * In Lean
*
  * `[l, h]`
  * the interval from `l` to `h`: the integers `x` with `l ≤ x ≤ h`; `l` may be `-∞` and `h` may be `+∞`
  * a value of the type `Ivl`, with a bound `none` for `-∞` or `+∞`
*
  * `γ a x`
  * `a` describes `x`: the concrete value `x` is one of the values that the abstract value `a` describes
  * `γ a x`, a `Prop`
*
  * `⊥`
  * bottom: the abstract value that describes no value
  * `bot`
*
  * `⊤`
  * top: the abstract value that describes every value
  * `top`
*
  * `a ⊑ b`
  * `a` is below `b`: `b` describes every value that `a` describes
  * `le a b = true`
*
  * `a ⊔ b`
  * the join of `a` and `b`: an abstract value above both
  * `join a b`
*
  * `a ∇ b`
  * `a` widened by `b`: an abstract value above both that jumps ahead, so that the solver's rounds stop
  * `widen a b`
*
  * `a △ b`
  * `a` narrowed by `b`: for `b` below `a`, an abstract value between `b` and `a`
  * `narrow a b`
:::
::::

{ref "absint"}[Abstract interpretation: the idea] writes the transfer function of an operation `op` as `op♯`, such as `add♯` for `+`. This chapter writes the Lean names instead: the interval transfer function of `+` is `addIvl`.

The analysis of this chapter describes integers by intervals, of the Lean type `Ivl`, and booleans by sets of truth values, of the type `TV`. `Ivl` and `TV` are _abstract types_, and the _domain_ `IvlTV` gives `Ivl` to the Dyn type `Base.Int` and `TV` to `Base.Bool`, in the sense of {ref "absint-values"}[Abstract values and concretization]. The Lean types of `Base.Int` and `Base.Bool` are `Int` and `Bool` ({ref "env-sem"}[Environment 7: Meaning]), and the abstract types describe values of those Lean types. To write an analysis, you write five things:

* a domain, declared by name with `dyn_domain`;
* an abstract type for each Dyn type that the domain describes, with an `AbsDomain` instance, and an `Embed` instance at the Dyn type's Lean type;
* a _transfer function_, with a theorem of its _local soundness_, for each instruction whose result you want to track. Local soundness says that from operands that the abstract values describe, the instruction's rule computes a result that the transfer function's result describes. A pure instruction that you leave out gets `⊤`;
* a transfer function, with its theorem, for each instruction that your programs use and whose rule is not pure, such as an instruction with successors or with regions. `base.jump`, `base.branch` and `base.unreachable`, which every lowered `if` and `while` uses, have default transfer functions. The defaults of `base.jump` and `base.unreachable` take every successor that the rule may take. The default of `base.branch` takes the successors that the condition allows when the abstract type at `Base.Bool` says which truth values a condition may have, with a `BoolView` instance, and both successors otherwise. The checker rejects a module that uses any other instruction whose rule is not pure and that has no transfer function;
* one command, `#dyn_absint`, which builds the analysis and its theorems.

`#dyn_absint_coverage` lists what each instruction will get before you build anything. Section 1 shows all five for intervals.

Two limits decide early what you can analyse: the facts say nothing about the heap, and a call is analysed only when the function it calls is known at the call, from a code pointer that the caller stores ({ref "absint-calls"}[Calls and contexts]). {ref "absint-limits-list"}[Limits] lists the others.

Dyn gives each of the five a command or an attribute. In the table, `D` is a domain, `T` a Dyn type, `A` an abstract type, `o` an instruction, `τ` a transfer function, `h` a theorem, `S` a semantic table and `N` a namespace. Each row links to the section that defines the form.

::::nowrap
:::table +header
*
  * Form
  * What it denotes
*
  * `dyn_domain D`
  * declares a domain named `D` ({ref "absint-domains"}[Domains])
*
  * `(narrow := b)`, `(widenAfter := n)`, `(maxRounds := k)`
  * options of `dyn_domain`: the analysis narrows if `b` holds, widens after `n` rounds of joins, and runs at most `k` rounds in each phase ({ref "absint-theorem"}[What the analysis proves])
*
  * `@[dyn_abs D T] A`
  * the abstract type of the Dyn type `T` in `D` is `A` ({ref "absint-domains"}[Domains])
*
  * `@[dyn_transfer D o τ] h`
  * in `D`, `τ` is the transfer function of the instruction `o`, and `h` proves it locally sound ({ref "absint-transfer-proof"}[Writing a transfer function]); in a relational domain, `τ` acts on abstract states ({ref "absint-relational"}[Relational transfer functions])
*
  * `#dyn_transfer_obligation D o τ`
  * prints the theorem that `@[dyn_transfer D o τ]` needs ({ref "absint-pure"}[A pure instruction])
*
  * `#dyn_abs_sum D T`
  * the abstract type of the datatype `T` in `D`; from it, `#dyn_absint` generates the transfer functions of `T`'s constructors and case instruction ({ref "absint-sum"}[Datatypes])
*
  * `dyn_domain D (state := St)`
  * declares a relational domain `D`, whose abstract states have the type `St`; `StateEmbed St α` instances say which Lean types `α` its states see ({ref "absint-relational"}[Relational transfer functions])
*
  * `#dyn_absint N for S (domain := D)`
  * the analysis of `S`'s modules over `D`, its soundness theorem `N.sound`, and `N.annotate`, which prints its results, declared in the namespace `N` ({ref "absint-command"}[Running `#dyn_absint`])
*
  * `(total)`
  * option of `#dyn_absint`: also the theorem `N.total`, that the analysis returns facts on every module it covers ({ref "absint-total"}[Termination])
*
  * `(settles)`
  * option of `#dyn_absint`: also the theorem `N.settles`, that the widening rounds settle ({ref "absint-total"}[Termination])
*
  * `(contexts := c)`
  * option of `#dyn_absint`: which summaries of a callee the solver makes, `perInput k` or `perCallee` ({ref "absint-calls"}[Calls and contexts])
*
  * `(complete)`
  * option of `#dyn_absint` and `#dyn_absint_coverage`: a supported instruction whose rule is not pure and that has no transfer function and no default is an error ({ref "absint-command"}[Running `#dyn_absint`])
*
  * `#dyn_absint_coverage D for S`
  * lists what `#dyn_absint` would give each instruction of `S` in `D` ({ref "absint-command"}[Running `#dyn_absint`])
*
  * `dyn_domain P := D₁ × D₂ (reduce := f, h)`
  * declares `P`, the product of `D₁` and `D₂`, reduced by `f`, which `h` proves sound ({ref "absint-product"}[Reduced products])
*
  * `N.analyzeWith solve m`
  * the analysis of `m` with a solver of your own; `N.soundWith` is its soundness theorem ({ref "absint-solve"}[Solvers and tables])
:::
::::

An attribute may also be given after its declaration, as in `attribute [dyn_abs D T] A`, which is how the chapter's listings write most of them.

Section 1 shows the complete analysis of While over intervals and truth values, and what it finds on one program. Section 2 defines the operations on intervals, and with them each symbol of the notation table. Section 3 states what the analysis proves. Sections 4 to 8 then write the analysis part by part: the domain, the transfer functions and their proofs, the command, the results and termination. Section 9 pairs intervals with parities, and zones with intervals, and section 10 builds signs and parities into one abstract type. Section 11 analyses calls, section 12 replaces the solver and the representation of states, and section 13 lists what a front end can do to make its modules analysable.

## 1. A complete analysis
%%%
number := false
tag := "absint-complete"
%%%

The analysis of this section is not in the package yet.

Here is the whole analysis of While over intervals and truth values:

```leantext "The analysis of While over intervals and truth values (under development, in StrataDyn/Examples/While/Domains.lean)"
/-- Intervals at `Int` and sets of truth values at `Bool`. -/
dyn_domain IvlTV (narrow := true)

attribute [dyn_abs IvlTV Base.Int] Ivl
attribute [dyn_abs IvlTV Base.Bool] TV

attribute [dyn_transfer IvlTV While.add addIvl] addIvl_sound
attribute [dyn_transfer IvlTV While.sub subIvl] subIvl_sound
attribute [dyn_transfer IvlTV While.neg negIvl] negIvl_sound
attribute [dyn_transfer IvlTV While.lt ltTV] ltTV_sound
attribute [dyn_transfer IvlTV While.le leTV] leTV_sound
attribute [dyn_transfer IvlTV While.branchLt branchLtIvl] branchLtIvl_sound

#dyn_absint IvlTVWhile for WhileSem (domain := IvlTV) (total) (settles)
```

`dyn_domain` declares the domain `IvlTV`, and `(narrow := true)` makes its solver narrow after it widens (section 3). The two `dyn_abs` attributes give the Dyn type `Base.Int` the abstract type `Ivl` and `Base.Bool` the abstract type `TV`, and section 4 gives their `AbsDomain` and `Embed` instances. Each `dyn_transfer` attribute names an instruction and its transfer function, and sits on the theorem that the transfer function is locally sound. `addIvl` is the transfer function of `+`, and `ltTV` that of `<`, which takes two intervals and gives a set of truth values. Section 5 shows how to write such transfer functions and their proofs. Notice that nothing in the listing names a tag, a state or a block.

`#dyn_absint` then builds the analysis of `WhileSem`'s modules in the namespace `IvlTVWhile`, with the theorem `IvlTVWhile.sound`, that its results hold on every run. Because of `(total)`, it also proves that the analysis returns results on every module that it covers, and because of `(settles)`, that its widening rounds come to rest when the solver is given enough of them (section 8).

Nothing in the listing is registered for `base.branch` and `base.jump`. In the default lowering, every `if` and `while` of a While program becomes these two terminators, and the analysis gives them defaults. The default of `base.jump` takes its one successor. The default of `base.branch` reads the condition, because `TV` says whether a condition may be true and whether it may be false:

```leantext "Truth values read a condition (under development, in StrataDyn/Examples/While/TruthValues.lean)"
/-- A set of truth values holds each truth value it stands for. -/
instance : BoolView TV where
  mayTrue := TV.mayTrue
  mayFalse := TV.mayFalse
  γ_true h := h
  γ_false h := h
```

`mayTrue` and `mayFalse` read the set's two flags. The laws `γ_true` and `γ_false` say that a set that describes `true` may be true, and a set that describes `false` may be false; for `TV`, they hold by definition. So the analysis takes the first successor of a branch only if the condition's set may hold `true`, and the second only if it may hold `false`. A domain whose abstract type at `Base.Bool` has no `BoolView`, or that gives `Base.Bool` no abstract type, gets a default of `base.branch` that takes both successors. Section 5 shows the defaults, and how to write a transfer function of a terminator.

`#dyn_absint` gives the analysis a function `IvlTVWhile.annotate prog f`, which analyses the module `prog` and prints the facts of its function `f` block by block, each abstract value printed by its type's `ToString`. A test helper, `linesOf`, lowers a While program and returns the lines of `annotate`. Here the test runs `IvlTVWhile` on `sum` of {ref "absint-fixpoint"}[Joins, fixpoints and widening]:

```leantext "The facts of sum (under development, in StrataDynTest/Absint/DomainsTest.lean)"
/--
info: entry.0: n.0=⊤
head.0: n.1=⊤, s.0=[0, +∞], i.0=[1, +∞]
body.0:
exit.0:
ret [0, +∞]
-/
#guard_msgs in
#eval IO.println ("\n".intercalate (linesOf (IvlTVWhile.annotate · ·) sum "sum"))
```

Each line names a block of the lowered function and gives the abstract value of each of the block's parameters, named as the module names it: `n.0` and `n.1` are successive SSA values of the variable `n`. `entry.0` is the entry, `head.0` the loop's header, `body.0` its body and `exit.0` the code after it. The header takes every variable in scope as a parameter. `body.0` and `exit.0` have no parameters, because they read the header's values, which are in scope there. The last line, `ret`, gives the abstract value of the function's result. At the header, `s` is at least `0` and `i` at least `1`, and the function returns an integer of at least `0`. `IvlTVWhile.sound` says that these facts hold on every run of `sum`, whatever its argument. Section 7 explains how `annotate` prints the facts.

## 2. The interval domain
%%%
number := false
tag := "absint-ivl"
%%%

The intervals and the sets of truth values of this section are not in the package yet.

An _interval_ `[l, h]` is the set of integers from `l` to `h`. A lower bound may be `-∞` and an upper bound `+∞`, so `[1, +∞]` is the set of integers from `1` up, and `[-∞, +∞]` is the set of all integers. The interval analysis gives each integer value of a module an interval that holds every value that a run may give it.

Intervals have the Lean type `Ivl`, in `StrataDyn/Examples/While/Interval.lean`, which follows the interval analysis of Nipkow and Klein's book *Concrete Semantics*, chapter 13. An `Ivl` is `bot`, `top` or `range lo hi`. `bot` is `⊥`, `top` is `⊤`, and `range lo hi` is the interval `[lo, hi]`. Each bound is an `Option Int`, and `none` is an infinite bound: `-∞` as a lower bound, and `+∞` as an upper bound.

Booleans have sets of truth values, of the type `TV`, with these functions:

```leantext "Sets of truth values (under development, in StrataDyn/Examples/While/TruthValues.lean)"
/-- **A set of truth values**: whether it may hold `true`, and whether it may hold `false`. -/
structure TV where
  mayTrue : Bool
  mayFalse : Bool
  deriving DecidableEq, Repr

namespace TV

/-- No truth value. -/
def bot : TV := ⟨false, false⟩

/-- Both truth values. -/
def top : TV := ⟨true, true⟩

/-- Inclusion of the sets. -/
def le (a b : TV) : Bool := (!a.mayTrue || b.mayTrue) && (!a.mayFalse || b.mayFalse)

/-- Union of the sets. -/
def join (a b : TV) : TV := ⟨a.mayTrue || b.mayTrue, a.mayFalse || b.mayFalse⟩

/-- The set holds `b`. -/
def means (a : TV) (b : Bool) : Prop := (if b then a.mayTrue else a.mayFalse) = true

/-- The set of one truth value. -/
def abs (b : Bool) : TV := ⟨b, !b⟩
…

/-- A truth value is in its set. -/
theorem means_abs : ∀ b, means (abs b) b
  | true | false => rfl
…

/-- `top` holds every truth value. -/
theorem means_top : ∀ b, means top b
  | true | false => rfl

/-- A larger set holds more. -/
theorem means_le : ∀ {a b : TV}, le a b = true → ∀ {x : Bool}, means a x → means b x := by
  …

end TV
```

So `⟨true, false⟩` is the set `{true}`, `TV.bot` is the empty set, and `TV.top` is `{true, false}`. `TV.means a b` says that the set `a` holds the truth value `b`. Section 4 makes `TV` an abstract type with these functions, and `Ivl` one with the operations of this section.

The rest of this section gives `Ivl`'s operations, one per symbol of the notation table.

### Concretization
%%%
number := false
tag := "absint-ivl-gamma"
%%%

Like the rest of section 2, this describes code that is not in the package yet.

The _concretization_ `γ` says which concrete values an abstract value describes. It is a predicate: `γ a x` is the proposition that the abstract value `a` describes the concrete value `x`. For an abstract type `A` whose concrete values have the type `Val`, it has the type `γ : A → Val → Prop` (section 4). For intervals, `Val` is `Int`, and `γ` is `Ivl.means`:

* `γ [l, h] x` holds when `l ≤ x ≤ h`, and an infinite bound allows every integer;
* `γ ⊥ x` holds for no integer `x`;
* `γ ⊤ x` holds for every integer `x`.

So `γ [1, 3] 2` holds and `γ [1, 3] 5` does not, and `γ [1, +∞] x` holds for every integer `x` from `1` up.

A rule takes Lean values, such as an `Int`. The framework states `γ` at a Lean type, through an embedding of the Lean type's values into the abstract type's concrete values, and section 4 gives the definition. The embedding is separate from `γ` because one abstract type may describe several Lean types: constant propagation's `CP` describes both `Int` and `Bool` ({ref "absint-uniform"}[Uniform domains]). For intervals the embedding of `Int` is the identity, so for `x : Int`, `γ a x` is `Ivl.means a x`.

Notice that `γ` is a proposition, which only the theorems about the analysis mention. The analysis never computes the set of values that an abstract value describes.

### The order and the join
%%%
number := false
tag := "absint-ivl-order"
%%%

Like the rest of section 2, this describes code that is not in the package yet.

The _order_ `a ⊑ b` holds when `b` describes every value that `a` describes. The analysis decides it, so in Lean it is a Boolean function, `le`, and `a ⊑ b` is `le a b = true`. For intervals, the order is inclusion: `[l₁, h₁] ⊑ [l₂, h₂]` holds when `l₂ ≤ l₁` and `h₁ ≤ h₂`, where `-∞` is below every lower bound and `+∞` above every upper bound. So `[1, 3] ⊑ [0, 5]` holds, and `[1, 3] ⊑ [2, 5]` does not, since `[2, 5]` lacks `1`. `⊥` is below every abstract value, and every abstract value is below `⊤`.

Where two paths of a program meet, the analysis needs one abstract value that describes the values of both. The _join_ `a ⊔ b` is an abstract value above both `a` and `b`. For intervals, it runs from the lower of the two lower bounds to the higher of the two upper bounds, and a bound is infinite if either of the two is. The join of `⊥` and `b` is `b`. For example, `[1, 3] ⊔ [5, 6] = [1, 6]`. Notice that `[1, 6]` also describes `4`, which neither `[1, 3]` nor `[5, 6]` describes, so a join may describe more values than its two arguments together.

### Widening and narrowing
%%%
number := false
tag := "absint-ivl-widen"
%%%

Like the rest of section 2, this describes code that is not in the package yet.

Take the loop `var i : Int := 1; while (i <= n) { i := i + 1; }`. The value `i` at the loop's header is `1` on entry and `i + 1` after the body. The analysis computes its interval in _rounds_, and each round recomputes it from the entry and from the body. With joins only, `i` is `[1, 1]`, then `[1, 1] ⊔ [2, 2] = [1, 2]`, then `[1, 3]`, and the rounds never stop. A _widening_ `a ∇ b`, of the current value `a` by a new value `b`, is an abstract value above both `a` and `b` that jumps ahead, so that the rounds stop. `Ivl`'s widening keeps each bound of `a` that `b` stays within, and makes infinite each bound that `b` goes past. So `[1, 1] ∇ [1, 2] = [1, +∞]`. In the next round, `[1, +∞] ∇ [1, 3] = [1, +∞]`, nothing changes, and the rounds stop.

A widening may jump further than it needs to. A _narrowing_ `a △ b`, for `b` below `a`, is an abstract value between `b` and `a`. After the widening rounds stop, a _narrowing round_ recomputes each abstract value `a` from the current ones, which gives a value `b` below `a`, and replaces `a` by `a △ b`. `Ivl`'s narrowing takes the recomputed bound where `a`'s bound is infinite, and keeps each finite bound. For example, if a loop's condition bounds the recomputed value by `10`, so that it is `[1, 10]`, then `[1, +∞] △ [1, 10] = [1, 10]`. The widening and the narrowing are those of *Concrete Semantics*, section 13.9.

Last, `abs n` is the abstract value of the single concrete value `n`, the interval `[n, n]`.

### Abstract states
%%%
number := false
tag := "absint-ivl-state"
%%%

Like the rest of section 2, this describes code that is not in the package yet.

An _abstract state_ gives an abstract value to each value in scope at a program point, or it is `⊥`, the abstract state that describes no state. For example, at the header of a loop with the values `i` and `s` in scope, the abstract state that gives `i` the interval `[1, +∞]` and `s` the interval `[0, +∞]` describes every state in which `i ≥ 1` and `s ≥ 0`. The analysis computes an abstract state at the entry of each block. No run enters a block whose entry state is `⊥` in every context of the facts (sections 3 and 7).

## 3. What the analysis proves
%%%
number := false
tag := "absint-theorem"
%%%

The theorems of this section are not in the package yet.

An analysis is _sound_ when its results describe every point that a run reaches. For the analysis `IvlTVWhile` of section 1, `#dyn_absint` generates the theorem `IvlTVWhile.sound`. Without its binders, it reads:

```leantext "The soundness theorem, without its binders (under development)"
link WhileSem.model prog = .ok m → analyze m sch = some F →
  start hwf i args snap = .ok ⟨B, ⟨s, h⟩⟩ → ∀ (r : RunFrom hwf s h) (n : Nat), Admits F i (r.cfg n)
```

If the module `prog` links to `m`, and the analysis returns facts `F` for `m`, then for every function `i`, arguments and snapshot that a run starts from, every run `r` of the module's step relation from that start, and every number of steps `n`, the facts admit the configuration `r.cfg n`: a state that is still running, or how the run ended ({ref "inside-runs"}[Inside the execution DSL: Runs]). `hwf` is the proof that `m` is well formed. A run answers each choice freely, so the theorem covers every oracle, and no hypothesis mentions fuel, so it covers runs that never end. Since `runFused` stops only at configurations that a run reaches (`reach_runFused`), the facts also describe where an execution on fuel stops. {ref "app-absint-sound"}[The soundness theorem in full], in appendix E, gives the full statement and explains each binder.

The _facts_ `F` hold an abstract state at the entry of each block of each function and each region, a description of each function's result when a run starts it, a description of each region's result, and the summaries of the module's calls ({ref "absint-calls"}[Calls and contexts]). The facts analyse a body in one or more _contexts_: a function as the start of a run, a region as the rules run it, and a function on the arguments of one of its summaries. `Admits F i p` holds when the facts describe the point `p` of a run that started function `i`. At a configuration inside a block, a context that analyses the frame's body describes the frame's values: the block's entry state in that context, updated by the transfer functions of the instructions before the configuration's position, gives each value in scope an abstract value that describes it. At the end of the run, the description of function `i`'s result describes the value that the run returns. A run that faults is admitted too, so `sound` does not say that a run never faults. `IvlTVWhile.State` is the type of the facts' abstract states, `IvlTVWhile.Value` the type of what the facts know of one value, such as the result, and `IvlTVWhile.Facts` the type of the facts. The command defines all three from the abstract types that the domain registers, and section 7 reads the facts.

You prove one theorem per transfer function: its local soundness. The framework proves the rest once, for every analysis. `analyze` returns the solver's facts only if the checker accepts them, so the solver needs no proof, and `N.soundWith` states the theorem for a solver of your own (section 12). Facts that the checker accepts give an invariant of the machine, which holds at the start of every run and which every step preserves, so it holds at every configuration of every run. {ref "app-absint-proof"}[How the framework proves it], in appendix E, states the invariant and its proof, `claim_inductive`. You never apply either.

`analyze` takes a _schedule_, which says when the solver widens, whether it narrows, and which summaries it makes of a callee:

```leantext "Schedules (under development, in StrataDyn/Absint/Core/Domain.lean)"
structure Schedule where
  widenAfter : Nat := 3
  narrow : Bool := false
  /-- The most rounds that ascending, and then narrowing, run. -/
  maxRounds : Nat := 10000
  /-- How a module with calls is analysed: a summary per input, up to `4` per callee, by
  default. -/
  contexts : Contexts := .perInput 4
  deriving Repr
```

A round of the solver visits every body of the module, its functions, its regions and the summaries that its calls demand, callees before their callers outside call cycles, and each body's blocks in reverse postorder. The solver joins for the first `widenAfter` rounds and then widens at its _widening points_: the targets of retreating edges, the heads of loops, and the entry blocks of regions. From then on it also widens the results of regions, and of the summaries whose callee is on a call cycle. If `narrow` holds, it narrows afterwards until no state shrinks and no result changes. Each phase runs at most `maxRounds` rounds, the schedule's _cap_. If the widening rounds have not settled by then, the solver gives up with `top` at every block, and a narrowing phase that reaches the cap stops with the states it has. A round skips a block whose entry state, and the results it reads, have not changed since the block's last visit, since what the block sends would be what it sent then. `sound` holds under every schedule: a schedule changes which facts the solver finds, and how long it takes. `IvlTVWhile.analyze m`, with no schedule, runs under `IvlTVWhile.schedule`, the domain's own, which `dyn_domain`'s options `(narrow := b)`, `(widenAfter := n)` and `(maxRounds := k)` set, and `#dyn_absint`'s option `(contexts := c)`.

`(total)` and `(settles)` add two theorems. `total` says that the analysis returns facts on every module that it covers. `settles` says that, for each `widenAfter` and each choice of contexts, the widening rounds settle before the cap once the cap is large enough, so the solver does not give up with `top`. Section 8 states both. They cover modules with regions and with calls as well as modules without. `#print axioms` lists `propext`, `Classical.choice` and `Quot.sound` for all three.

## 4. Declaring a domain
%%%
number := false
tag := "absint-domain"
%%%

The commands and classes of this section are not in the package yet.

### Abstract types
%%%
number := false
tag := "absint-abs-types"
%%%

The classes of this subsection are not in the package yet.

An _abstract type_ is a Lean type of abstract values with an `AbsDomain` instance. The instance gives the order operations, the concrete values, the concretization, `bot`, `abs` and three laws. The order operations are a class of their own, `Lattice`, which every level of an analysis shares: abstract values, what a state knows of one value, and the descriptions of a relational domain:

```leantext "The order operations (under development, in StrataDyn/Absint/Domain.lean)"
class Lattice (A : Type) where
  top : A
  le : A → A → Bool
  join : A → A → A
  widen : A → A → A := join
  /-- `narrow a b`, for `b` below `a`: a value between `b` and `a`.  A narrowing round
  replaces a fact `a` whose recomputed value is `b` by `narrow a b`. -/
  narrow : A → A → A := fun a _ => a
```

```leantext "Abstract types (under development, in StrataDyn/Absint/Domain.lean)"
class AbsDomain (A : Type) extends Lattice A where
  /-- The concrete values. -/
  Val : Type
  /-- `γ a v`: the abstract value `a` stands for the concrete value `v`. -/
  γ : A → Val → Prop
  bot : A
  /-- The abstract value of the single value `v`. -/
  abs : Val → A
  γ_abs : ∀ v, γ (abs v) v
  γ_le : ∀ {a b : A}, le a b = true → ∀ {v : Val}, γ a v → γ b v
  γ_top : ∀ v, γ top v
```

An instance of `AbsDomain` gives the fields of `Lattice` among its own, as the listing for sets of truth values below does. `γ` is the concretization, `bot` is `⊥` and `top` is `⊤`, `le` is the order `⊑`, `join` the join `⊔`, `widen` the widening `∇` and `narrow` the narrowing `△`, as section 2 defines them. A domain of finite height can leave out `widen`, which is then `join`, and a domain that does not narrow can leave out `narrow`. The laws say that a concrete value is in its own abstract value (`γ_abs`), that a larger abstract value describes more values (`γ_le`), and that `top` describes every value (`γ_top`). For intervals, `γ_abs` says that `[n, n]` holds `n`, and `γ_le` says, for example, that `[0, 5]` holds every integer that `[1, 3]` holds, since `[1, 3] ⊑ [0, 5]`. No law mentions `bot`, `join`, `widen` or `narrow`, so `sound` holds whatever they compute.

A rule works on Lean types, such as `Int` and `Bool` ({ref "env-sem"}[Environment 7: Meaning]). An `Embed A α` instance makes the values of the Lean type `α` concrete values of `A`, and then `γ a x`, for `x : α`, is the concretization of the embedded value:

```leantext "The concretization at a Lean type (under development, in StrataDyn/Absint/Domain.lean)"
abbrev γ {A α : Type} [AbsDomain A] [Embed A α] (a : A) (x : α) : Prop :=
  AbsDomain.γ a (Embed.embed x)
```

The interval type `Ivl` is one abstract type. Its instance, in `Interval.lean`, collects the operations of section 2: `γ` is `Ivl.means`, the order operations are `Ivl.le`, `Ivl.join`, `Ivl.widen` and `Ivl.narrow`, and `abs` is `Ivl.abs`. The theorems `Ivl.means_abs` and `Ivl.means_le` prove the laws `γ_abs` and `γ_le`, and `γ_top` holds by definition, since `⊤` describes every integer. The concrete values of `Ivl` are integers, and its `Embed` instance at `Int` is the identity, so for `x : Int`, `γ a x` is `Ivl.means a x`, the predicate of section 2.

`TV`, the type of sets of truth values of section 2, is another abstract type, whose concrete values are booleans. Its instance has the same shape:

```leantext "Sets of truth values as an abstract type (under development, in StrataDyn/Examples/While/TruthValues.lean)"
/-- **Sets of truth values**, as an abstract type of `Bool`. -/
instance : AbsDomain TV where
  Val := Bool
  γ := TV.means
  bot := TV.bot
  top := TV.top
  le := TV.le
  join := TV.join
  abs := TV.abs
  γ_abs := TV.means_abs
  γ_le := TV.means_le
  γ_top := TV.means_top

instance : Embed TV Bool := ⟨id⟩
```

`TV` has no widening and no narrowing of its own: a set grows at most twice, so the join serves as the widening. `Ivl` describes integers only and `TV` booleans only, so each has an `Embed` instance at one Lean type.

### Domains
%%%
number := false
tag := "absint-domains"
%%%

The declarations of this subsection are not in the package yet.

A _domain_ is a named declaration that gives the Dyn types of a language their abstract types. `dyn_domain D` declares it, and `@[dyn_abs D T] A` makes `A` the abstract type of the Dyn type `T` in the domain `D`. The listing of section 1 declares `IvlTV` with `Ivl` at `Base.Int` and `TV` at `Base.Bool`. In the words of {ref "absint-values"}[Abstract values and concretization], an abstract type is an abstract domain of one type, and a domain chooses one for each type of the language.

* `dyn_domain D` takes the options `(narrow := b)`, `(widenAfter := n)` and `(maxRounds := k)`, which set the domain's schedule. An option given twice is an error. An attribute or a command that names a domain that is not declared is an error, so a misspelt name does not start a new domain.
* `@[dyn_abs D T] A` needs `AbsDomain A`, and `Embed A α` for the Lean type `α` that `@[dyn_type T] α` gives `T`. So `A` describes the values of `T`'s Lean type, and transfer functions, their theorems and `γ` are stated at Lean types.
* A Dyn type that `D` does not register has the abstract type `PUnit`, whose one value describes every value.
* `T` must have no type parameters. `@[dyn_abs D Base.Sequence] A` is an error: `Base.Sequence has parameters: abstract types of type constructors are not supported yet`. A datatype gets its abstract type from `#dyn_abs_sum` ({ref "absint-sum"}[Datatypes]).

Notice that the declaration is the abstract side of `@[dyn_type]`: it names Dyn types, as `@[dyn_type T] α` does, and never tags. The command works out the rest. Each distinct abstract type of the domain becomes one _sort_, and the analysis keeps each value's abstract value at the sort of the value's Lean type. You never write a sort.

At run time a value carries the tag of its Lean type, so two Dyn types with one Lean type cannot be told apart, and they share one abstract type in a domain. A test environment declares `Half.Meters` with the Lean type `Int`, which `Base.Int` has too:

```leantext "Dyn types that share a Lean type (under development, in StrataDynTest/Absint/RegisterTest.lean)"
attribute [dyn_type Half.Meters] Int
…
/-- Constant propagation, at `Int` and `Bool`. -/
dyn_domain HD
attribute [dyn_abs HD Base.Int] CP
attribute [dyn_abs HD Base.Bool] CP

attribute [dyn_abs HD Half.Meters] CP

/--
error: Half.Meters and Base.Int share the Lean type Int, so they have one abstract type in HD: Base.Int has CP, not Par
-/
#guard_msgs in
attribute [dyn_abs HD Half.Meters] Par
```

Registering `CP` at `Half.Meters` too is accepted, and registering `Par` is an error that names both Dyn types. A language whose analysis must tell two such types apart gives them distinct Lean types.

### Uniform domains
%%%
number := false
tag := "absint-uniform"
%%%

The domain of this subsection is not in the package yet.

A _uniform domain_ registers one abstract type at several Dyn types of different Lean types. While's domains have one, constant propagation, which tests this style of registration: every other domain of While gives `Base.Int` and `Base.Bool` abstract types of their own. Constant propagation's abstract type `CP` is a flat lattice over While's constants, which describes integers and booleans alike:

```leantext "Constant propagation's values (under development, in StrataDyn/Examples/While/ConstProp.lean)"
inductive Const where
  | int (n : Int)
  | bool (b : Bool)
  deriving DecidableEq, Repr
…
inductive CP where
  | bot
  | const (c : Const)
  | top
  deriving DecidableEq, Repr
```

```leantext "Constant propagation as a uniform domain (under development, in StrataDyn/Examples/While/Domains.lean)"
/-- Constant propagation. -/
dyn_domain CPD
attribute [dyn_abs CPD Base.Int] CP
attribute [dyn_abs CPD Base.Bool] CP
attribute [dyn_transfer CPD While.add addAbs] addAbs_sound
…
#dyn_absint CPWhile for WhileSem (domain := CPD) (total)
```

Types with one abstract type share a sort. So a value that is an `Int` on one path and a `Bool` on another joins as a `CP`, and not to `top`. In a uniform domain, every transfer function is at one type, such as `CP → CP → CP`. That is what lets `CP`'s transfer functions of `while.if` and `while.loop` read a condition and pass an integer ({ref "absint-regions"}[Instructions with regions]). The polymorphic transfer functions of section 5 are the general case.

## 5. Writing a transfer function and its proof
%%%
number := false
tag := "absint-transfer-proof"
%%%

The transfer functions of this section, and the attribute that registers them, are not in the package yet.

A transfer function takes one abstract value per operand, at the abstract type that the domain gives the operand's Lean type. For an instruction with a result and no successors, it returns the result's abstract value.

You register a transfer function by putting `@[dyn_transfer D o τ]` on a theorem. The attribute registers `τ` as the transfer function of the instruction `o` in the domain `D`, and the theorem as its proof. The theorem must state the transfer function's _obligation_, its local soundness against `o`'s rule at Lean types. `#dyn_transfer_obligation D o τ` prints the obligation.

:::::callout "Status"
A transfer function of a pure rule may take and return different abstract types: `ltTV` takes two intervals and returns a `TV`. It may also be polymorphic. A transfer function of an instruction with successors may not mix abstract types yet: its operands, its payloads and its result must all have one abstract type. `branchTV` tests a `TV` and passes nothing, so it qualifies. A terminator that tests a `Bool` and passes an `Int` has no transfer function in `IvlTV` until the abstract targets of the box "Planned interface" in {ref "absint-successors"}[An instruction with successors] are built. The same holds for an instruction with regions: its operands and the answers of its regions must have one abstract type, and it may not have type parameters.
:::::

### A pure instruction
%%%
number := false
tag := "absint-pure"
%%%

While's rules are in the package, but the transfer functions and theorems of this subsection are not yet.

`while.add` and `while.lt` have pure rules, Lean functions on integers:

```leantext "Their rules (StrataDyn/Examples/While/Env.lean)"
@[dyn_sem While.add] def add (a b : Int) : Int := a + b
…
@[dyn_sem While.lt] def lt (a b : Int) : Bool := decide (a < b)
```

The interval transfer function of `while.add`, `addIvl`, adds the bounds: the lower bound of the sum is the sum of the lower bounds, and its upper bound the sum of the upper bounds, infinite if either is. Constant propagation's, `addAbs`, adds two constants. Both are built from a helper that applies an integer operation to two abstract values. Here is constant propagation's helper, with two of the transfer functions built from it:

```leantext "The transfer functions of + and < in constant propagation (under development, in StrataDyn/Examples/While/ConstProp.lean)"
/-- An integer operation on abstract values: a constant of two constants, `bot` if either is
`bot`, and `top` otherwise. -/
def CP.lift₂ {β : Type} (f : Int → Int → β) (k : β → Const) : CP → CP → CP
  | .const (.int m), .const (.int n) => .const (k (f m n))
  | .bot, _ => .bot
  | _, .bot => .bot
  | _, _ => .top
…
/-- `a + b`. -/
def addAbs : CP → CP → CP := CP.lift₂ (· + ·) .int
…
/-- `a < b`. -/
def ltAbs : CP → CP → CP := CP.lift₂ (fun m n => decide (m < n)) .bool
```

`k` makes a constant of the operation's result: `.int` for `+`, and `.bool` for `<`. So `addAbs` gives the sum of two integer constants, `bot` if either operand is `bot`, and `top` otherwise.

The local soundness of a transfer function is its _obligation_. `@[dyn_transfer D o τ]` computes it from the rule of `o`, with the abstract type that `D` gives each operand's Lean type, and `#dyn_transfer_obligation` prints it. A test environment, `Half`, has one pure instruction, `half.half`, whose rule halves an integer, and a domain `HD` with `CP` at `Int` and `Bool`. Here are the transfer function of `half.half` in `HD` and its obligation:

```leantext "The obligation of halfAbs (under development, in StrataDynTest/Absint/RegisterTest.lean)"
@[dyn_sem Half.half] def half (x : Int) : Int := x / 2
…
/-- Half of a constant. -/
def halfAbs : CP → CP
  | .const (.int n) => .const (.int (n / 2))
  | .bot => .bot
  | _ => .top

/-- info: ∀ (xAbs : CP) (x : Int), γ xAbs x → γ (halfAbs xAbs) (HalfRules.half x) -/
#guard_msgs in
#dyn_transfer_obligation HD Half.half halfAbs
```

Read `γ xAbs x` as "the abstract value `xAbs` describes the integer `x`". The obligation then says: if `xAbs` describes `x`, then `halfAbs xAbs` describes the half of `x` that the rule `HalfRules.half` computes. `xAbs` is the abstract value of the instruction's operand `x`, and `x`, the rule's parameter, is its concrete value. Here is the theorem that states it, with its proof:

```leantext "The theorem of halfAbs (under development, in StrataDynTest/Absint/RegisterTest.lean)"
/-- `halfAbs` is sound: half of a constant is the constant's half. -/
@[dyn_transfer HD Half.half halfAbs]
theorem halfAbs_sound (xAbs : CP) (x : Int) (hx : γ xAbs x) :
    γ (halfAbs xAbs) (HalfRules.half x) :=
  match xAbs, hx with
  | .const (.int _), hx => by
    injection hx with hx
    subst hx
    rfl
  | .const (.bool _), hx => nomatch hx
  | .bot, hx => nomatch hx
  | .top, _ => trivial
```

The proof is by cases on the abstract value. An integer constant describes only itself, so `x` is that constant, and both sides compute the same half. A boolean constant and `bot` describe no integer, so these cases cannot occur. `top` describes every value. Notice the theorem's binders: the abstract values, then the values, then the hypotheses. The registration checks that the theorem states the obligation, and rejects one that does not ({ref "absint-register"}[What registration rejects]).

An instruction with two operands has two of each. `while.add`'s operands are `lhs` and `rhs`, and its rule's parameters are `a` and `b`, so the theorem of `addAbs` takes `lhsAbs`, `rhsAbs`, `a` and `b`. It applies a lemma that `ConstProp.lean` proves once, for every operation that `CP.lift₂` lifts:

```leantext "Addition, and its proof (under development, in StrataDyn/Examples/While/ConstProp.lean)"
/-- A lifted operation is sound for its operation, at every type of result that `k` embeds. -/
theorem CP.lift₂_sound {β : Type} [Embed CP β] (f : Int → Int → β) (k : β → Const)
    (hk : ∀ v, γ (CP.const (k v)) v) (x y : CP) (a b : Int) (ha : γ x a) (hb : γ y b) :
    γ (CP.lift₂ f k x y) (f a b) :=
  …

/-- `addAbs` is sound: the sum of operands in their facts is in its fact. -/
theorem addAbs_sound (lhsAbs rhsAbs : CP) (a b : Int) (ha : γ lhsAbs a) (hb : γ rhsAbs b) :
    γ (addAbs lhsAbs rhsAbs) (WhileRules.add a b) :=
  CP.lift₂_sound (· + ·) Const.int (fun _ => rfl) _ _ _ _ ha hb
```

The hypothesis `hk` says that the constant that `k` makes of a value describes that value, which holds by `rfl` for `Const.int`. Notice that the theorem mentions only Lean types and the rule, `WhileRules.add`, and no domain. `ConstProp.lean` states it without an attribute, and `Domains.lean` registers it in `CPD`, as section 1 registers `addIvl_sound` in `IvlTV`. One theorem may serve several domains: the test domain `TD` of {ref "absint-register"}[What registration rejects] registers `addIvl_sound` too.

`while.lt` takes two integers and returns a boolean, so its transfer function may go from one abstract type to another. In `IvlTV`, `ltTV` takes two intervals and returns a `TV`. Its set lacks `false` when every integer of the first interval is below every integer of the second, and lacks `true` when no integer of the first is below an integer of the second. The domain of signs and parities, `SPD`, has a transfer function of the same shape, `ltSP`, from its abstract type `SP` of integers to `TV`:

```leantext "A comparison into sets of truth values (under development, in StrataDyn/Examples/While/SignParity.lean)"
/-- `a < b`. -/
def ltSP : SP → SP → TV := SP.cmp ltT
…
/-- `ltSP` is sound: the comparison `<` of operands in their abstract values is in its abstract
value. -/
theorem ltSP_sound (lhsAbs rhsAbs : SP) (a b : Int) (ha : γ lhsAbs a) (hb : γ rhsAbs b) :
    γ (ltSP lhsAbs rhsAbs) (WhileRules.lt a b) :=
  SP.cmp_sound ltT_sound ha hb
```

The hypotheses use `SP`'s `γ`, at `Int`, and the conclusion uses `TV`'s, at `Bool`: if `lhsAbs` describes `a` and `rhsAbs` describes `b`, then the set `ltSP lhsAbs rhsAbs` holds the truth value of `a < b`. {ref "absint-sp"}[A domain of signs and parities] explains `SP` and its tables. `ltTV_sound`, the theorem of `ltTV`, has the same statement, with `Ivl` and `ltTV` in place of `SP` and `ltSP`.

### An instruction with successors
%%%
number := false
tag := "absint-successors"
%%%

The transfer functions and defaults of this subsection are not in the package yet.

An instruction with successors may leave along some of them. Its transfer function says which successors a run may take, and what each passes. It returns an `AbsOut` when the instruction has successors, or has no result. An instruction with a result and no successors returns the result's abstract value instead, even when its rule is not pure or it owns regions, as `while.pick` does:

```leantext "What a transfer function returns (under development, in StrataDyn/Absint/Domain.lean)"
/-- **What a transfer returns**: the result's abstract value, `top` if the instruction has none;
for each successor in order, `none` if the instruction never takes it, or the abstract values
of its payload; and for each of the rule's regions, by position, whether the rule may run it.
A missing successor is `none`, a missing payload value is `top`, and by default every region
may run.  A region that may not run need not start in the facts.  A transfer of an instruction
without regions leaves `runs` alone. -/
structure AbsOut (A : Type) [AbsDomain A] where
  res : A := Lattice.top
  succs : Array (Option (Array A)) := #[]
  runs : Nat → Bool := fun _ => true
```

`res` is the result's abstract value, or `top` for an instruction with no result. `succs` has one entry per successor, in order: `none` if the instruction never takes the successor, or `some fs`, where `fs` holds the abstract values of what it passes. `runs` is for instructions with regions ({ref "absint-regions"}[Instructions with regions]). Obligations and lemmas read an output through three helpers, which unfold to the fields:

```leantext "Reading an output (under development, in StrataDyn/Absint/Domain.lean)"
/-- **The instruction may take successor `j`, passing the abstract values `fs`.** -/
@[reducible] def AbsOut.Takes (o : AbsOut A) (j : Nat) (fs : Array A) : Prop :=
  o.succs[j]? = some (some fs)

/-- **The abstract value of position `i` of a payload `fs`**: `top` past its end. -/
@[reducible] def payArg (fs : Array A) (i : Nat) : A := fs.getD i Lattice.top

/-- **The rule may run its region `j`.** -/
@[reducible] def AbsOut.MayRun (o : AbsOut A) (j : Nat) : Prop := o.runs j = true
```

Here are two transfer functions of this kind, of `base.branch` and `base.jump` at `TV`. `IvlTV` of section 1 does not register them and takes the defaults, which do the same. The domains of signs and parities, `SPD`, and of parities, `ParD`, register `branchTV`, and the test domain `PD` of {ref "absint-poly"}[Polymorphic transfer functions] registers both:

```leantext "Branches and jumps (under development, in StrataDyn/Examples/While/TruthValues.lean)"
/-- `base.branch`: the successors whose truth value the condition's set holds. -/
def branchTV (c : TV) : AbsOut TV :=
  { succs := #[if c.mayTrue then some #[] else none, if c.mayFalse then some #[] else none] }

/-- `base.jump`: its one successor. -/
def jumpTV : AbsOut TV := { succs := #[some #[]] }
```

`jumpTV` allows the jump's one successor. `branchTV` allows the first successor if the condition's set may hold `true`, and the second if it may hold `false`. Neither passes a value of its own. The values in a jump such as `jump ^head.0(%n.1, %t.1, %t.2)` are arguments of the edge, and the block that the edge enters receives them first ({ref "tr-build"}[Translator 2: The builder]). The framework carries their abstract values along every edge that the transfer function allows, whatever their Lean types. A transfer function gives only what its rule passes after them, the _payload_, such as the two compared values that `while.branchLt` passes ({ref "cs13-filters"}[Filtering on conditions]).

The rule of an instruction with successors returns a tree of type `Sem ε E α` ({ref "inside-rules-as-trees"}[Rules as trees]). Its obligation is stated under a _spec_ `V`, which says which exits the rule may take and what it may ask of the machine. `V.Sat Q g t` says that the rule's tree `t` keeps to `V`, and that every value it returns satisfies `Q`. For a terminator, read `V.Exit g e` as "the analysis allows the exit `e`". You never build a spec: the obligation quantifies over every spec that allows what your transfer function allows. The argument `g` is a _ghost state_, for analyses with an abstract heap, and the analyses of this guide ignore it. {ref "app-absint-specs"}[Specs], in appendix E, defines `Spec` and `Spec.Sat`.

The obligation of a transfer function of a terminator quantifies over every spec, and so does its theorem. Here are the theorems of `branchTV` and `jumpTV`. `PD` registers both, so the registration has checked that each states its obligation:

```leantext "Their theorems (under development, in StrataDyn/Examples/While/TruthValues.lean)"
/-- `base.branch` on a condition in its set takes a successor that `branchTV` allows. -/
theorem branchTV_sound {ε : Eff} {E : Type} (condAbs : TV) {G : Type} (V : Spec G ε E) (c : Bool)
    (t f : Target E []) {g : G} (hc : γ condAbs c)
    (ht : ∀ fs, (branchTV condAbs).Takes 0 fs → ∀ g₁, V.Exit g₁ (t.exit ()))
    (hf : ∀ fs, (branchTV condAbs).Takes 1 fs → ∀ g₁, V.Exit g₁ (f.exit ())) :
    V.Sat (fun _ _ => True) g (BaseRules.branch c t f) := by
  match condAbs, c, hc with
  | ⟨true, _⟩, true, _ => exact Spec.sat_jump.mpr (ht _ rfl _)
  | ⟨_, true⟩, false, _ => exact Spec.sat_jump.mpr (hf _ rfl _)
  | ⟨false, _⟩, true, hc => exact nomatch hc
  | ⟨_, false⟩, false, hc => exact nomatch hc

/-- `base.jump` takes its one successor, which `jumpTV` allows. -/
theorem jumpTV_sound {ε : Eff} {E : Type} {G : Type} (V : Spec G ε E) (k : Target E []) {g : G}
    (hk : ∀ fs, jumpTV.Takes 0 fs → ∀ g₁, V.Exit g₁ (k.exit ())) :
    V.Sat (fun _ _ => True) g (BaseRules.jump k) :=
  Spec.sat_jump.mpr (hk _ rfl _)
```

Read `jumpTV_sound` first. For every spec `V`: if `jumpTV` takes successor `0`, then `V` allows the exit to `k` in every ghost state. The conclusion is that the rule's tree satisfies `V`. `base.jump` has no result, so the postcondition is `True`. `branchTV_sound` adds the condition. Read it hypothesis by hypothesis. For every spec `V`: the condition `c` is in its set; if `branchTV` takes successor `0`, `V` allows the exit to `t` in every ghost state; and the same holds for successor `1` and `f`. The proof is by cases on the abstract value and the condition, and `Spec.sat_jump` reduces a jump to the hypothesis about its exit.

`ht _ rfl` applies the hypothesis to the payload that `branchTV` passes: `Takes` unfolds to an equation about `succs`, which holds by `rfl` once the condition's set is known. Notice that each lemma is stated at the rule's Lean types and at every spec, so it does not depend on how the analysis continues after each exit. A proof of this kind needs five lemmas: `Spec.sat_ret`, `Spec.sat_jump` and `Spec.sat_fault` cover the leaves of a tree, `Spec.Sat.bind` composes the steps of a `do` block, and `Spec.Sat.mono` weakens a postcondition.

*Default transfer functions.* `base.jump`, `base.branch` and `base.unreachable` have defaults in every domain that registers no transfer function of them. The default of `base.jump` takes its successor, and the default of `base.unreachable`, whose rule faults, takes none. The default of `base.branch` depends on the domain. In a domain of abstract types whose abstract type at `Bool` has a `BoolView` instance, it reads the condition:

```leantext "Abstract values that read a condition (under development, in StrataDyn/Absint/Domain.lean)"
class BoolView (A : Type) [AbsDomain A] [Embed A Bool] where
  mayTrue : A → Bool
  mayFalse : A → Bool
  γ_true : ∀ {a : A}, γ a true → mayTrue a = true
  γ_false : ∀ {a : A}, γ a false → mayFalse a = true
```

```leantext "The default that reads the condition (under development, in StrataDyn/Absint/Core/Base.lean)"
/-- `base.branch`'s default transfer in a domain that reads conditions: the successors whose
truth value the condition's abstract value allows. -/
def branchBool (c : A) : AbsOut A :=
  { succs := #[if BoolView.mayTrue c then some #[] else none,
      if BoolView.mayFalse c then some #[] else none] }
```

`branchBool` is `branchTV` written once for every abstract type with a `BoolView`, and its lemma, `branchBool_sound`, is proved once from the two laws. `TV`'s instance is in section 1. In every other domain, relational ones included, the default of `base.branch` takes both of its successors. These defaults, and those of `base.jump` and `base.unreachable`, take their successors from the state before the instruction. They are stated on abstract states, as relational transfer functions are ({ref "absint-relational"}[Relational transfer functions]), so they hold in every domain, and the framework proves their lemmas once (`StrataDyn/Absint/Core/Base.lean`). The coverage report says which default a domain gets (section 6).

Two test domains show the difference. `TD` has intervals at `Int` and `TV` at `Bool`, with transfer functions of `+` and `<`. `TDs` has only `Ivlₙ`, intervals under another name, at `Int`, and no abstract type at `Bool`. Neither registers a transfer function of `base.jump` or `base.branch`:

```leantext "Two domains with the default transfer functions (under development, in StrataDynTest/Absint/DomainsTest.lean)"
/-- A test domain: intervals at `Int`, truth values at `Bool`. -/
dyn_domain TD
attribute [dyn_abs TD Base.Int] Ivl
attribute [dyn_abs TD Base.Bool] TV
…
attribute [dyn_transfer TD While.add addIvl] addIvl_sound
…
attribute [dyn_transfer TD While.lt ltTV] ltTV_sound
…
#dyn_absint TDW for WhileSem (domain := TD)
…
/-- A domain whose abstract type has no `ToString`. -/
dyn_domain TDs
attribute [dyn_abs TDs Base.Int] Ivlₙ
#dyn_absint TDsW for WhileSem (domain := TDs)
```

Here they run on `known`, whose condition `x < 2` compares the constant `3` with `2`. The test prints every value as `v`, because `Ivlₙ` has no `ToString`, so the lines show only which blocks are dead:

```leantext "What each finds (under development, in StrataDynTest/Absint/DomainsTest.lean)"
/-- A branch on a comparison of constants. -/
def known : Program := #while
  fun f(n : Int) : Int {
    var x : Int := 3;
    if (x < 2) { return n; }
    return x;
  }
#end

-- `TDs` has no abstract type at `Bool`, so its `base.branch` takes both successors, and neither
-- branch of `known` is dead; `TD`'s `TV` reads the condition, and the `then` branch is.
#guard linesOf (TDsW.annotate · · fun _ => "v") known "f" =
  ["entry.0: n.0=v", "then.0:", "else.0:", "join.0: n.1=v, x.0=v", "ret v"]
#guard linesOf (TDW.annotate · · fun _ => "v") known "f" =
  ["entry.0: n.0=v", "then.0: dead", "else.0:", "join.0: n.1=v, x.0=v", "ret v"]
```

In `TD`, `ltTV` gives `x < 2` the set that holds only `false`, so the default takes only the `else` branch, and `then.0` is dead. In `TDs`, `<` has no transfer function and its result has no abstract type, so the default takes both branches. `then.0` and `else.0` have no parameters, since they read the entry's values, which are in scope there.

:::::callout "Planned interface, not yet built"
A transfer function whose operands have different abstract types, at an instruction with successors, takes one abstract target `ATarget ts` per successor, in the rule's order, as a rule takes one `Target E ts`. It returns a writer, `AOut`, and `mayJump t payload` adds a successor that a run may take, with the refined operands. Unlike `jump`, several `mayJump`s may be taken.
:::::

### Instructions with regions
%%%
number := false
tag := "absint-regions"
%%%

While's rules with regions are in the package, but the analysis of regions is not yet.

You need this subsection only if your language has instructions that own regions. While's ordinary `if` and `while` lower to `base.branch` and `base.jump`. Only `region if` and `region while` lower to the instructions `while.if` and `while.loop`, which own regions ({ref "tr-regions"}[Translator 6: Regions]). A module with regions is solved by the same solver as a module without, with narrowing if the schedule asks for it, and `total` and `settles` hold of it.

The rule of `while.if` or `while.loop` takes one handle per region, a `Region`, and runs it with `runRegion`, which is one request to the machine. The machine runs the region's blocks, and gives the value that the region leaves with back to the rule as the request's answer. `if` makes one such request. `loop` runs its condition region, and if that answers `true`, runs its body region and then jumps to its `Again`, unless the body raised:

```leantext "While's rules with regions (StrataDyn/Examples/While/Env.lean)"
/-- Leave along `err` if a body region raised. -/
def flow (f : Flow) (err : Target E [Int]) : Sem ε E Unit := do
  if let .raise e := f then jump err e

@[dyn_sem While.if]
def «if» (c : Bool) (thenR elseR : Region ε [] Flow) (err : Target E [Int]) :
    Sem ε E Unit := do
  flow (← runRegion (if c then thenR else elseR) ()) err

/-- One iteration: if the condition holds, run the body and the operation again.  Its state
is `Unit`: a loop's variables are cells. -/
@[dyn_sem While.loop]
def loop (cond : Region ε [] Bool) (body : Region ε [] Flow) (err : Target E [Int])
    (_st : Option Unit) (again : Again E Unit) : Sem ε E Unit := do
  if ← runRegion cond () then
    flow (← runRegion body ()) err
    jump again ()
```

An analysis follows a run into the regions. Each region is a body of the linked module, named after its instruction and its position among the module's regions. For example, in a module whose only region instruction is one loop, `while.loop.0` is the loop's condition and `while.loop.1` its body. The facts give each region entry states of its own, as they give a function's, and a description of the region's result, `regionRets`. A region's entry block is a widening point, since the rule that runs the region sends it states from another body, and a region's result widens too, since the rules that read it may run inside a loop that runs the region again.

*The transfer function.* A transfer function of an instruction with regions takes one abstract value per operand and then one per region, the abstract value of the region's answer. When the instruction has successors, as While's `if` and `loop` have `^err`, it returns an `AbsOut` ({ref "absint-successors"}[An instruction with successors]), whose `runs` says which regions the rule may run. When it has a result and no successors, it returns the result's abstract value, and every region may run.

Here are constant propagation's transfer functions of `if` and `loop`. `if` has one operand, the condition, and two regions. `loop` has no operands, so both arguments of `loopAbs` are abstract values of answers, the condition region's and the body region's:

```leantext "The transfer functions of if and loop (under development, in StrataDyn/Examples/While/ConstPropRegions.lean)"
/-- `a` may stand for the truth value `b`. -/
def CP.admitsBool (a : CP) (b : Bool) : Bool := CP.le (.const (.bool b)) a
…
/-- **`while.if`'s transfer**: region `0`, `then`, runs only if the condition may be `true`, and
region `1`, `else`, only if it may be `false`; a raise leaves along `^err` with any code. -/
def ifAbs (condAbs _thenAbs _elseAbs : CP) : AbsOut CP :=
  { succs := #[some #[.top]],
    runs := fun j => if j = 0 then condAbs.admitsBool true else condAbs.admitsBool false }

/-- **`while.loop`'s transfer**: the condition region runs, and the body region only if the
condition region's answer may be `true`; a raise leaves along `^err` with any code. -/
def loopAbs (condAbs _bodyAbs : CP) : AbsOut CP :=
  { succs := #[some #[.top]], runs := fun j => if j = 0 then true else condAbs.admitsBool true }
```

They are registered as the other transfer functions are:

```leantext "Their registration (under development, in StrataDyn/Examples/While/Domains.lean)"
attribute [dyn_transfer CPD While.if ifAbs] ifAbs_sound
attribute [dyn_transfer CPD While.loop loopAbs] loopAbs_sound
#dyn_absint CPWhile for WhileSem (domain := CPD) (total)
```

Registration requires every operand and every region's answer of such a transfer function to have one abstract type, here `CP`, and requires one abstract value per operand and per region.

*The obligation.* A rule with regions makes requests of the machine, and its obligation is stated under a spec, as every obligation of a rule that is not pure is ({ref "absint-successors"}[An instruction with successors]). The lemma knows each region only through what the spec promises of the region's handle, a `RegionSpec`: running the region on arguments that `P` holds of is allowed, and its answer meets `R`. `RegionSpec.sat` turns that into `Sat` of `runRegion`:

```leantext "What a region promises (StrataDyn/Exec/Spec.lean)"
/-- **What a region promises**: running it on arguments that `P` holds of is an allowed
request, and its answer, at every grown ghost state, is a value `R` holds of. -/
structure RegionSpec {ts : List Type} {α : Type} (r : Region ε ts α) (P : G → Payload ts → Prop)
    (R : G → α → Prop) : Prop where
  req : ∀ g a, P g a → V.Pre g (r.req a)
  ans : ∀ g a o, V.Post g (r.req a) o → R g (r.ans a o)

variable {V}

/-- Running a region satisfies the spec when its arguments meet the region's precondition and
every answer the region promises meets the postcondition. -/
theorem RegionSpec.sat {ts : List Type} {α : Type} {r : Region ε ts α}
    {P : G → Payload ts → Prop} {R : G → α → Prop} (hr : RegionSpec V r P R) {a : Payload ts}
    {g : G} (ha : P g a) {Q : G → α → Prop} (hQ : ∀ g₁, V.Ext g g₁ → ∀ x, R g₁ x → Q g₁ x) :
    V.Sat Q g (runRegion r a) :=
```

`#dyn_transfer_obligation` prints the obligation of `loopAbs`. The test declares a domain `RD` with `CP` at `Int` and `Bool`, as `CPD` does:

```leantext "The obligation of loopAbs (under development, in StrataDynTest/Absint/RegionTest.lean)"
/--
info: ∀ {ε : Eff} {E : Type} (condAbs bodyAbs : CP) {G : Type} (V : Spec G ε E) (cond : Exec.Region ε [] Bool)
  (body : Exec.Region ε [] WhileRules.Flow) (err : Target E [Int]) (_st : Option Unit) (again : Again E Unit) {g : G},
  (RegionSpec V cond (fun g a => (loopAbs condAbs bodyAbs).MayRun 0) fun g x => γ condAbs x) →
    (RegionSpec V body (fun g a => (loopAbs condAbs bodyAbs).MayRun 1) fun g x => True) →
      (∀ (fs : Array CP),
          (loopAbs condAbs bodyAbs).Takes 0 fs → ∀ (q0 : Int), γ (payArg fs 0) q0 → ∀ (g : G), V.Exit g (err.exit q0)) →
        (∀ (g : G) (s : Unit), V.Exit g (again.exit s)) →
          V.Sat (fun g v => True) g (WhileRules.loop cond body err _st again)
-/
#guard_msgs in
#dyn_transfer_obligation RD While.loop loopAbs
```

Read it hypothesis by hypothesis. For every spec `V`:

* the condition region may run when `loopAbs` says that region `0` runs, and its answer is a truth value that `condAbs` describes;
* the body region may run when `loopAbs` says that region `1` runs. Its answer is a `Flow`, which has no abstract type in `CP`, so nothing is assumed of it: a Lean type that a domain does not register has the abstract type `PUnit`, which describes every value ({ref "absint-domains"}[Domains]);
* `^err` may be taken with every code that the payload's abstract value describes, as a successor may be taken in the obligation of `branchTV` ({ref "absint-successors"}[An instruction with successors]), here with a payload;
* the rule may jump to its `Again` from every state.

The conclusion is that the rule's tree satisfies `V`. Its result is `Unit`, which has no abstract type, so the postcondition is `True`.

*What you prove.* The proof is about the rule alone, at its Lean types. A lemma of the same shape as the rule does most of the work. `WhileSpecs.loop_sat` takes a region spec for each region, and lets the body's region spec assume that the condition answered `true`:

```leantext "loop under a spec (under development, in StrataDyn/Examples/While/ConstPropRegions.lean)"
/-- **One iteration of `loop` under a spec**: the condition region runs; if it answers `true`,
the body region runs, whose region spec may assume that answer, and the rule runs again. -/
theorem loop_sat {Q : G → Unit → Prop} (cond : Exec.Region ε [] Bool)
    (body : Exec.Region ε [] WhileRules.Flow) (err : Target E [Int]) (st : Option Unit)
    (again : Again E Unit) {g : G} {RC : G → Bool → Prop}
    (hc : RegionSpec V cond (fun _ _ => True) RC)
    (hb : RegionSpec V body (fun g₁ _ => RC g₁ true) (fun _ _ => True))
    (hraise : ∀ g₁ e, V.Exit g₁ (err.exit e)) (hagain : ∀ g₁, V.Exit g₁ (again.exit ()))
    (hdone : ∀ g₁, Q g₁ ()) :
    V.Sat Q g (WhileRules.loop cond body err st again) := by
  unfold WhileRules.loop
  refine Spec.Sat.bind (hc.sat (a := ()) trivial fun g₁ _ b hrc => ?_)
  cases b with
  | false => exact Spec.sat_ret.mpr (hdone g₁)
  | true =>
    exact Spec.Sat.bind (hb.sat (a := ()) hrc fun g₂ _ x _ =>
      Spec.Sat.bind (flow_sat x err (fun e _ => hraise g₂ e) fun _ =>
        Spec.sat_jump.mpr (hagain g₂)))
```

Each `runRegion` is discharged by `RegionSpec.sat`, and `Spec.Sat.bind` composes the steps, as a `do` block composes them. The transfer function's lemma is then `loop_sat` with its region specs weakened to the ones of the obligation. `RegionSpec.weaken` does that, and `CP.admitsBool_of` turns "the condition answered `true`, which `condAbs` describes" into "`loopAbs` lets the body run":

```leantext "The lemma of loopAbs (under development, in StrataDyn/Examples/While/ConstPropRegions.lean)"
/-- **`loopAbs` is sound for `while.loop`, at every spec**: the body region runs only after the
condition region answered `true`, which its answer's abstract value then admits. -/
theorem loopAbs_sound (condAbs bodyAbs : CP) {G : Type} (V : Spec G ε E)
    (cond : Exec.Region ε [] Bool) (body : Exec.Region ε [] WhileRules.Flow) (err : Target E [Int])
    (st : Option Unit) (again : Again E Unit) {g : G}
    (hc : RegionSpec V cond (fun _ _ => (loopAbs condAbs bodyAbs).MayRun 0)
      (fun _ x => γ condAbs x))
    (hb : RegionSpec V body (fun _ _ => (loopAbs condAbs bodyAbs).MayRun 1)
      (fun _ _ => True))
    (herr : ∀ fs, (loopAbs condAbs bodyAbs).Takes 0 fs →
      ∀ q0 : Int, γ (payArg fs 0) q0 → ∀ g₁, V.Exit g₁ (err.exit q0))
    (hagain : ∀ g₁ s, V.Exit g₁ (again.exit s)) :
    V.Sat (fun _ _ => True) g (WhileRules.loop cond body err st again) :=
  WhileSpecs.loop_sat cond body err st again (hc.weaken (fun _ _ _ => rfl) fun _ _ h => h)
    (hb.weaken (fun _ _ h => CP.admitsBool_of h) fun _ _ h => h)
    (fun g₁ e => herr _ rfl e trivial g₁) (fun g₁ => hagain g₁ ()) fun _ => trivial
```

`ifAbs_sound` is proved the same way from `WhileSpecs.if_sat`. Neither lemma mentions frames, stores or the facts.

*What it finds.* The tests read the facts of each body, a function or a region, by name: the abstract values that it computes, and how many of its blocks have an entry state that is not `⊥`. In a loop's body region, the region sees the function's constants: the test `regionConst` finds that `k * 2` is `10` inside the body of a `region while`. A region that no transfer function lets run keeps entry states that are all `⊥`, so the facts mark it dead as they mark a dead block:

```leantext "Dead regions (under development, in StrataDynTest/Absint/RegionTest.lean)"
/-- A loop region whose condition is `false`: its body region never runs. -/
def deadBody : Program := #while
  fun f(n : Int) : Int {
    var c : Ref := ref 0;
    region while (false) { *c := *c + 1; }
    return *c;
  }
#end

-- The condition region yields `false`, so the body region has no block that is not `bot`.
#guard (bodyFacts deadBody "while.loop.0").map (·.1.contains "false") = some true
#guard (bodyFacts deadBody "while.loop.1").map (·.2) = some 0

/-- A region `if` whose condition is constant: its `else` region never runs. -/
def constIf : Program := #while
  fun f(n : Int) : Int {
    var x : Int := 3;
    var c : Ref := ref 0;
    region if (x > 0) { *c := x * 2; } else { *c := 7; }
    return *c;
  }
#end

-- The `then` region computes `6`; the `else` region has no block that is not `bot`.
#guard (bodyFacts constIf "while.if.0").map (·.1.contains "6") = some true
#guard (bodyFacts constIf "while.if.0").map (·.2) = some 1
#guard (bodyFacts constIf "while.if.1").map (·.2) = some 0
```

Notice what `deadBody` needs. `loopAbs` reads the condition region's answer, `false`, from the facts, and so does not let the body region run. That is why `loop_sat` lets the body's region spec assume that the condition answered `true`. The same test checks regions three deep: `100` in the `if` region inside the inner loop of `rnested`.

A module with regions is covered when every body, function or region, is: the bodies have distinct names, each of their instructions has a transfer function or a default, and the code-pointer facts name the callee of each call ({ref "absint-calls"}[Calls and contexts]). Constant propagation covers `regionConst`, a `region while` whose body reads a constant of the function, so `CPWhile.total` applies to it:

```leantext "Coverage of a module with regions (under development, in StrataDynTest/Absint/RegionTest.lean)"
-- The constant analysis covers a module with regions, so `CPWhile.total` applies to it; the
-- parity analysis, which has no transfer for the loop rule, does not cover it.
#guard covers CPWhile.Internal.analysis regionConst
#guard !covers ParWhile.Internal.analysis regionConst
```

`covers` is a helper of the test, which lowers and links a program and applies the analysis's `Covers` ({ref "absint-total"}[Termination]).

An analysis whose domain has no transfer function of `if` rejects a module that uses it, as it rejects any rule that is not pure and has none. Inside a region the same holds of the region's own instructions:

```leantext "Rejection beside acceptance (under development, in StrataDynTest/Absint/RegionTest.lean)"
#guard !accepts (ParWhile.analyze ·) constIf
#guard accepts (CPWhile.analyze ·) constIf
…
#guard !accepts (CPWhile.analyze ·) modInRegion
#guard accepts (CPWhile.analyze ·) divInRegion
```

`modInRegion` has `*c := n % 2` inside a `region if`, and `divInRegion` has `*c := n / 2`.

*Products and relational domains.* A product of two domains ({ref "absint-product"}[Reduced products]) runs a region when both factors' transfer functions let it run, from the pair of the states that they run it from, and gives each factor its part of the region's answer. A factor with no transfer function of the instruction runs every region, so the product runs what the other factor runs. The product of constant propagation and parities accepts `constIf`, which parities alone reject, and leaves the body region of `deadBody` dead, as constant propagation does:

```leantext "Regions in a product (under development, in StrataDynTest/Absint/RegionTest.lean)"
/-- Constants and parities. -/
dyn_domain CPPar := CPD × ParD
#dyn_absint CPParWhile for WhileSem (domain := CPPar)

#guard accepts (CPParWhile.analyze ·) constIf
#guard accepts (CPParWhile.analyze ·) regionConst
-- `deadBody`'s condition region answers `(false, false)`, so `CPD`'s `loopAbs` does not run the
-- body region and neither does the product.
#guard (bodyFactsOf (CPParWhile.analyze ·) pairSlots deadBody
  "while.loop.0").map (·.1.contains "(false, false)") = some true
#guard (bodyFactsOf (CPParWhile.analyze ·) pairSlots deadBody
  "while.loop.1").map (·.2) = some 0
-- `ParD` has no transfer of `while.lt`, but the product keeps what `CPD` knows of `constIf`'s
-- condition: it runs the `then` region, which computes `6`, of unknown parity, and finds the
-- `else` region dead, as `CPWhile` does.
#guard (bodyFactsOf (CPParWhile.analyze ·) pairSlots constIf "while.if.0").map
  (·.1.contains "(6, ⊤)") = some true
#guard (bodyFactsOf (CPParWhile.analyze ·) pairSlots constIf "while.if.1").map (·.2) = some 0
```

`bodyFactsOf` is `bodyFacts` for any analysis, given how to render each slot's facts: `pairSlots` renders each slot's pair, one fact from each factor. The condition region's answer prints as a pair, constant propagation's `false` and parities' set of truth values, which holds only `false`.

A relational domain's transfer function of an instruction with regions is a `Transfer S` like any other ({ref "absint-relational"}[Relational transfer functions]). Its output says, per region, `none` if the rule never runs it, or the state that it runs the region from, where `some none` is the state before the instruction. The test gives zones a transfer function of `while.if` that runs both regions and forgets the result's slot, and proves it from `WhileSpecs.if_sat`, as `ifAbs_sound` is proved:

```leantext "A relational transfer function with regions (under development, in StrataDynTest/Absint/RegionTest.lean)"
/-- `while.if` on zones: both regions run from the state before, the result's slot is forgotten,
and `^err` passes any code. -/
def ifRT : Transfer ZSt := fun _ _ dst s _ =>
  { res := StateDomain.bind s [(dst, .pay Lattice.top)], succs := #[some (none, #[Lattice.top])],
    regions := fun _ => some none }
…
/-- Zones with a transfer of `while.if`. -/
dyn_domain ZR (state := ZSt)
attribute [dyn_transfer ZR While.if ifRT] ifRT_sound
#dyn_absint ZRWhile for WhileSem (domain := ZR)

-- A relational domain runs a region too: `ZRWhile` accepts `constIf`, which `ZoneWhile`, with no
-- transfer of `while.if`, rejects.
#guard accepts (ZRWhile.analyze ·) constIf
#guard !accepts (ZoneWhile.analyze ·) constIf
```

{ref "absint-limits-list"}[Limits] lists what the framework does not yet build for instructions with regions.

### Polymorphic transfer functions
%%%
number := false
tag := "absint-poly"
%%%

The polymorphic transfer functions of this subsection are not in the package yet.

A rule with type parameters takes one `{α : Type}` per parameter. Its transfer function takes one `{A : Type} [AbsDomain A]` per parameter. The analysis instantiates `A` at the abstract type that the domain gives each type argument, which the linked instruction records. A test declares a language with one polymorphic instruction, `poly.choose`, and a datatype, `Opt`:

```leantext "A language with a polymorphic instruction (under development, in StrataDynTest/Absint/PolyTest.lean)"
public environment Poly extends Base where
  namespace poly
  open base
  insn choose [a] (cond : Bool) (x y : a) : a
  insn add (lhs rhs : Int) : Int
  /-- An integer, or none. -/
  data Opt where
    | nothing
    | just (value : Int)
  end poly
```

`choose`'s rule picks one of its operands, at every Lean type `α`:

```leantext "The rule of choose (under development, in StrataDynTest/Absint/PolyTest.lean)"
/-- `x` if `c`, else `y`. -/
@[dyn_sem Poly.choose] def choose {α : Type} : Bool → α → α → α
  | true, x, _ => x
  | false, _, y => y
```

Its transfer function picks one of its abstract values, at every abstract type `A`, or gives `top` when the condition may be either:

```leantext "The transfer function of choose (under development, in StrataDynTest/Absint/PolyTest.lean)"
def chooseAbs {A : Type} [AbsDomain A] (c : TV) (x y : A) : A :=
  if c.mayFalse then (if c.mayTrue then Lattice.top else y) else x
```

The obligation quantifies over the Lean type `α` and the abstract type `A`, with an `Embed A α` instance that relates them:

```leantext "The obligation of chooseAbs (under development, in StrataDynTest/Absint/PolyTest.lean)"
/--
info: ∀ {α A : Type} [inst : AbsDomain A] [inst_1 : Embed A α] (condAbs : TV) (xAbs yAbs : A) (cond : Bool) (x y : α),
  γ condAbs cond → γ xAbs x → γ yAbs y → γ (chooseAbs condAbs xAbs yAbs) (Rules.choose cond x y)
-/
#guard_msgs in
#dyn_transfer_obligation PD Poly.choose chooseAbs
```

The theorem states it, and its proof, by cases on the condition and on the flags of `condAbs`, uses no law but `γ_top`:

```leantext "Its theorem (under development, in StrataDynTest/Absint/PolyTest.lean)"
/-- `chooseAbs` is sound for `poly.choose` at every type and abstract type. -/
@[dyn_transfer PD Poly.choose chooseAbs]
theorem chooseAbs_sound {α A : Type} [AbsDomain A] [Embed A α] (condAbs : TV) (xAbs yAbs : A)
    (c : Bool) (x y : α) (hc : γ condAbs c) (hx : γ xAbs x) (hy : γ yAbs y) :
    γ (chooseAbs condAbs xAbs yAbs) (Rules.choose c x y) := by
```

The test's domain `PD` gives `Int` intervals and `Bool` sets of truth values, as `IvlTV` does. In the function `ints`, which computes `choose[Int](true, 5, n) + 1`, the analysis runs `chooseAbs` at `Ivl`. In `bools`, which computes `choose[Bool](false, b, false)`, it runs it at `TV`:

```leantext "One transfer function at two abstract types (under development, in StrataDynTest/Absint/PolyTest.lean)"
-- At `Int`, intervals: the chosen `5`, plus one.
#guard retOf ints = some "[6, 6]"
-- At `Bool`, truth values: the chosen `false`.
#guard retOf bools = some (toString (TV.abs false))
```

`retOf f` analyzes a module with the one function `f`, and renders the abstract value of its result. Registration rejects a theorem stated at one abstract type, such as `Ivl`, in place of every one ({ref "absint-register"}[What registration rejects]). An instruction with type parameters whose rule is not pure or that has regions, or with a parameter that stands for a list of types, has no transfer function yet, and registration says so.

### Datatypes
%%%
number := false
tag := "absint-sum"
%%%

The abstract types of datatypes are not in the package yet.

`#dyn_abs_sum D T` gives the datatype `T` an abstract type in the domain `D`. It declares the abstract type `D.T`, with its embedding and its `Embed` instance, as `#dyn_types` declares a datatype's Lean type. An abstract value of `T` holds, for each constructor, `none` if no value that it describes is built by the constructor, or the abstract value of the constructor's fields:

```leantext "The abstract values of a datatype (under development, in StrataDyn/Absint/Lift/Sum.lean)"
/-- **The abstract values of a datatype** whose constructors' fields have the abstract types
`Fs`: per constructor, `none` if no value is built by it, or its fields' abstract values. -/
def SumAbs : List Type → Type
  | [] => PUnit
  | F :: Fs => Option F × SumAbs Fs
```

A constructor with no fields has the abstract type `PUnit` for them, one field has the field's abstract type, and several have the product of theirs. A field whose type is a datatype, `T` itself included, has `PUnit`, which describes every value, so the abstract type is never recursive. `SumAbs Fs` has its `AbsDomain` and `Order` instances once, from the fields'. In `PD`, `Opt` is `SumAbs [PUnit, Ivl]`: `nothing` has no fields, and `just` has one integer.

```leantext "The domain of the test (under development, in StrataDynTest/Absint/PolyTest.lean)"
dyn_domain PD

attribute [dyn_abs PD Base.Int] Ivl
attribute [dyn_abs PD Base.Bool] TV
#dyn_abs_sum PD Poly.Opt
```

`#dyn_absint` generates the transfer functions of `Opt`'s constructors and of its case instruction. A constructor's transfer function gives its own constructor the fields' abstract values and every other constructor `none`. The case instruction's transfer function takes a successor only for a constructor that the operand may be, refines the operand to that constructor along it, and passes the constructor's fields. The coverage report names them:

```leantext "The coverage of PD (under development, in StrataDynTest/Absint/PolyTest.lean)"
/--
info: type base.Unit: no abstract type: top
type base.Bool ↦ TV
type base.Int ↦ Ivl
…
type poly.Opt ↦ PD.Opt
…
op poly.choose ↦ chooseAbs, proved by chooseAbs_sound
op poly.add ↦ addIvl, proved by addIvl_sound'
op poly.nothing: derived constructor of poly.Opt: its abstract value in PD.Opt
op poly.just: derived constructor of poly.Opt: its abstract value in PD.Opt
op poly.Opt.case: derived case of poly.Opt: the constructors PD.Opt allows, with their fields
5 transfers with lemmas; 0 instructions whose rules are not pure have no transfer; 0 are not supported
-/
#guard_msgs in
#dyn_absint_coverage PD for PolySem
```

The function `opts` builds `just 7` and takes it apart with `Opt`'s case instruction. The test language has no source syntax, so `opts` is written directly as a function of the IR ({ref "tr-shape"}[Translator 1: The shape you produce]), with helpers of the test: `fn` makes a function from its blocks, `blk` a block from its label, parameters, instructions and terminator, `d n t` declares the value `%n` of type `t`, `cst` defines a constant and `app` applies an instruction:

```leantext "A value built and taken apart (under development, in StrataDynTest/Absint/PolyTest.lean)"
/-- `opts(n)`: `just 7`, taken apart again: `7`, or `n` if it is `nothing`. -/
def opts : Func E Unit := fn "opts" intT [
  blk "entry" [d 0 intT] [cst 1 intT (.int 7),
    app 2 optT Poly.Opt.just.ref ⟨#[], rfl⟩ [1]]
    (.apply () Poly.Opt.case.ref ⟨#[], rfl⟩ #[⟨2⟩] #[to "none", to "some"] #[]),
  blk "none" [] [] (.ret () ⟨0⟩),
  blk "some" [d 3 intT] [] (.ret () ⟨3⟩)]
```

```leantext "What the analysis finds (under development, in StrataDynTest/Absint/PolyTest.lean)"
-- Through a constructor and its case: the field's interval, and only the successor of `just`.
#guard retOf opts = some "[7, 7]"
```

The abstract value of `%2` is `none` at `nothing` and `[7, 7]` at `just`. So the case instruction never takes the successor `none`, whose block stays at `⊥`, and passes `[7, 7]` to `some`. Had it taken both, the result would be the join of `[7, 7]` and the interval of the argument `n`, which is `⊤`.

:::::callout "Planned interface, not yet built"
Datatypes with type parameters, such as the base's `Except e a`, have no abstract type yet, so `base.ok`, `base.error` and `base.Except.case` keep their defaults (section 6), and the coverage report lists `type base.Except: has parameters: top`. Giving them one needs sorts structured by type constructor: the analysis sees only tags with no arguments, and the tag of `Except Int Bool` has two.
:::::

### Relational transfer functions
%%%
number := false
tag := "absint-relational"
%%%

The relational domains of this subsection are not in the package yet.

You need this subsection only for a relational domain: a user who writes only value transfer functions never meets states. The domains so far are non-relational: an abstract state holds one abstract value per value, and records no relation between values. A _relational_ domain's abstract state does record relations, such as `x - y ≤ 3`. Zones, which bound each difference of two values, are one. A relational domain declares its type of states, and its transfer functions act on states:

```leantext "Zones, a relational domain (under development, in StrataDyn/Examples/While/Domains.lean)"
/-- Zones, with guards on comparisons. -/
dyn_domain Zones (state := ZSt)
attribute [dyn_transfer Zones While.add addRT] addRT_sound
…
attribute [dyn_transfer Zones Base.jump jumpRT] jumpRT_sound
#dyn_absint ZoneWhile for WhileSem (domain := Zones) (total) (settles)
```

A relational domain has no abstract types. It sees the values of each Lean type `α` that has a `StateEmbed S α` instance, as concrete values of its states, and `#dyn_absint` finds the instances. Zones see integers and booleans as While's constants:

```leantext "What the zones see (under development, in StrataDyn/Examples/While/ZoneAnalysis.lean)"
/-- The zone analysis sees `Int` values as constants. -/
instance : StateEmbed ZSt Int := ⟨Const.int⟩

/-- The zone analysis sees `Bool` values as constants. -/
instance : StateEmbed ZSt Bool := ⟨Const.bool⟩
```

A relational transfer function is a `Transfer S` over the domain's states `S`. From the tags of the instruction's type arguments, the slots of its operands and of its result in the function's frame, the state before the instruction and the descriptions of its regions' answers, it gives the state after the instruction and, for each successor, the state that it leaves from. The framework lifts every value transfer function to this form, so the checker and the solver see one form only. The zones' transfer function of `+` is one line, since `ZSt.addZ` does the work:

```leantext "The zones' transfer function of + (under development, in StrataDyn/Examples/While/ZoneAnalysis.lean)"
/-- `while.add`. -/
def addRT : Transfer ZSt := fun _ args dst s _ => { res := ZSt.addZ args dst s }
```

Its obligation is stated at the rule's Lean types, as a value transfer function's is. A test domain `ZD`, declared as `Zones` is, prints it:

```leantext "The obligation of addRT (under development, in StrataDynTest/Absint/DomainsTest.lean)"
/--
info: ∀ (targs : Array Exec.Ty) (lhsSlot rhsSlot dst : Nat) (st : ZSt) (ρ : Valuation (StateDomain.Val ZSt))
  (RF : Nat → StateDomain.Pay ZSt) (a b : Int),
  StateDomain.γ st ρ →
    ρ lhsSlot = some (Const.int a) →
      ρ rhsSlot = some (Const.int b) →
        StateDomain.γ (addRT targs [lhsSlot, rhsSlot] dst st RF).res (ρ.set dst (some (Const.int (WhileRules.add a b))))
-/
#guard_msgs in
#dyn_transfer_obligation ZD While.add addRT
```

Read it binder by binder: for the tags `targs`, a slot per operand and the result's slot `dst`, a state `st`, a valuation `ρ` of the frame's slots that `st` describes, and the regions' answers `RF`, and for the rule's values `a` and `b`: if each operand's slot holds what the states see of its value, here `Const.int a` and `Const.int b`, then the state after the instruction describes `ρ` with the rule's result bound to `dst`. A rule that is not pure has an obligation of the spec-generic form of {ref "absint-successors"}[An instruction with successors], whose successors give a state and a payload. The lemma is a line, from the zone lemma of `ZSt.addZ`:

```leantext "Its lemma (under development, in StrataDyn/Examples/While/ZoneAnalysis.lean)"
/-- `addRT` is sound for `while.add`: the sum, bound to `dst`, is in the result. -/
theorem addRT_sound (targs : Array Ty) (lhsSlot rhsSlot dst : Nat) (st : ZSt)
    (ρ : Valuation (StateDomain.Val ZSt)) (RF : Nat → StateDomain.Pay ZSt) (a b : Int)
    (hs : StateDomain.γ st ρ) (hx : ρ lhsSlot = some (Const.int a))
    (hy : ρ rhsSlot = some (Const.int b)) :
    StateDomain.γ (addRT targs [lhsSlot, rhsSlot] dst st RF).res
      (ρ.set dst (some (Const.int (WhileRules.add a b)))) :=
  ZSt.addZ_sound hs hx hy
```

Registration checks the lemma against the obligation, as for a value transfer function. A lemma with another statement is an error that prints both, and so is a transfer function of another type:

```leantext "Relational registrations rejected beside their twins (under development, in StrataDynTest/Absint/DomainsTest.lean)"
/--
error: subRT_sound does not state that addRT is sound for while.add.  The obligation is
…
but subRT_sound states
…
-/
#guard_msgs in
attribute [dyn_transfer ZD While.add addRT] subRT_sound
attribute [dyn_transfer ZD While.add addRT] addRT_sound

/--
error: the transfer addIvl of while.sub in ZD must have type Transfer ZSt, but addIvl : Ivl → Ivl → Ivl
-/
#guard_msgs in
attribute [dyn_transfer ZD While.sub addIvl] addIvl_sound
attribute [dyn_transfer ZD While.sub subRT] subRT_sound
```

The first error prints the obligation, and then `subRT_sound`'s statement, which is about `subRT` and `WhileRules.sub`. A transfer function on states in a domain of abstract types is an error too: `operand lhs of while.add in TD: expected Ivl, the abstract type of Int, but addRT takes Array Exec.Ty`.

The defaults of `base.jump` and `base.unreachable`, and the default of `base.branch` that takes both successors ({ref "absint-successors"}[An instruction with successors]), are transfer functions on states, which read nothing of the state they are given. A relational domain that registers no `base.branch` gets that one:

```leantext "The default transfer functions (under development, in StrataDyn/Absint/Core/Base.lean)"
/-- `base.jump`'s default transfer: its one successor, from the state before. -/
def jumpTransfer : Transfer S := fun _ _ _ s _ => { res := s, succs := #[some (none, #[])] }

/-- `base.branch`'s default transfer: both successors, from the state before. -/
def branchTransfer : Transfer S := fun _ _ _ s _ =>
  { res := s, succs := #[some (none, #[]), some (none, #[])] }

/-- `base.unreachable`'s default transfer: no successor. -/
def unreachableTransfer : Transfer S := fun _ _ _ s _ => { res := s }
```

`none` in place of a state stands for the state before the instruction. The zones register their own `branchRT`, which takes each successor from the state that the guard of its condition refines, and `jumpRT`, which is `jumpTransfer` at `ZSt`. With `(total)` and `(settles)`, a relational domain needs `StateOrder` and `StateAscendingWF` of its states, and `Order` and `AscendingWF` of their descriptions ({ref "absint-total"}[Termination]). The zones' instances are in `StrataDyn/Examples/While/ZoneOrder.lean`.

### What registration rejects
%%%
number := false
tag := "absint-register"
%%%

The checks of this subsection are not in the package yet.

`@[dyn_abs]` and `@[dyn_transfer]` check the domain, the instruction, the transfer function and the theorem, and name what does not match, as `@[dyn_sem]` does. `StrataDynTest/Absint/DomainsTest.lean` shows errors beside registrations that pass:

```leantext "Rejections beside their twins (under development, in StrataDynTest/Absint/DomainsTest.lean)"
-- A misspelt domain is an error; the same transfer in the declared domain is accepted.
/-- error: unknown domain `TDx`: declare it with `dyn_domain TDx` -/
#guard_msgs in
attribute [dyn_transfer TDx While.add addIvl] addIvl_sound
attribute [dyn_transfer TD While.add addIvl] addIvl_sound

-- A transfer at the wrong abstract type is an error; the one at the right type is accepted.
/-- error: the result of while.lt in TD: expected TV, the abstract type of Bool, but addIvl returns Ivl -/
#guard_msgs in
attribute [dyn_transfer TD While.lt addIvl] addIvl_sound
attribute [dyn_transfer TD While.lt ltTV] ltTV_sound
```

The other errors:

:::table +header
*
  * Registration
  * Error
*
  * a second abstract type of one Dyn type
  * `Base.Int already has the abstract type Ivl in TD`
*
  * a different abstract type of a Dyn type that shares its Lean type with another
  * `Half.Meters and Base.Int share the Lean type Int, so they have one abstract type in HD: Base.Int has CP, not Par`
*
  * an abstract type of a Dyn type with type parameters
  * `Base.Sequence has parameters: abstract types of type constructors are not supported yet`
*
  * an abstract type of an instruction
  * `` `Half.half` is an instruction, not a Dyn type ``
*
  * an abstract type with no `Embed` at the Dyn type's Lean type
  * `Ivlₑ does not describe Base.Bool, of Lean type Bool, in TDs: no instance Embed Ivlₑ Bool`
*
  * an operand at the wrong abstract type
  * `operand x of half.half in HD: expected CP, the abstract type of Int, but natAbs takes Nat`
*
  * a second transfer function of one instruction in one domain
  * `while.lt already has the transfer ltTV in TD, proved by ltTV_sound`
*
  * a theorem that is not the obligation
  * `halfTop does not state that halfAbs is sound for half.half.  The obligation is …`
*
  * a polymorphic transfer function's theorem stated at one abstract type
  * `chooseIvl_sound does not state that chooseAbs is sound for poly.choose.  The obligation is …`
*
  * two imported modules that register one instruction in one domain
  * an error naming both, reported by `#dyn_absint` and the coverage command, not by the attribute
*
  * a constructor
  * `base.ok is a constructor of base.Except, derived, and the analysis gives it its default`
*
  * `#dyn_abs_sum` of an instruction
  * `` `Poly.add` is an instruction, not a datatype ``
*
  * `#dyn_abs_sum` of a datatype that has an abstract type
  * `Poly.Opt already has the abstract type PD₂.Opt in PD₂, at its Lean type Poly.Opt.Val`
*
  * a transfer function of an instruction that the analysis does not support
  * `while.print has a rule that takes the run token or capabilities: transfers of such instructions are not supported yet`
:::

Registration also rejects a key that names no instruction. It says that an instruction is not supported before it checks the transfer function's type, at the instruction's name, for a rule that takes the run token or capabilities, a rule without regions that loops, a variadic instruction, an instruction generic over a list of types, and an instruction with type parameters whose rule is not pure or has regions. For an instruction with regions, it rejects a transfer function that takes too few abstract values:

:::table +header
*
  * Registration
  * Error
*
  * a transfer function of `while.loop` without the abstract value of the body region's answer
  * `the transfer loopShort of while.loop in RD must take one abstract value per operand and per region (0 + 2), but loopShort : CP → AbsOut CP`
:::

## 6. Running `#dyn_absint`
%%%
number := false
tag := "absint-command"
%%%

`#dyn_absint` and `#dyn_absint_coverage` are not in the package yet.

`#dyn_absint N for S (domain := D)` reads the table `S` and its environment, the abstract types that `D` registers, and the transfer functions registered in `D` for the environment's instructions and its ancestors'. It generates, in the namespace `N`:

:::table +header
*
  * Declaration
  * What it is
*
  * `State`, `Value`, `Facts`
  * the types of the facts' abstract states, of what the facts know of one value, and of the facts
*
  * `schedule`
  * the domain's schedule, which `dyn_domain`'s options set, with the contexts of calls that `(contexts := c)` names (section 11)
*
  * `analyze`
  * the abstract interpreter: the facts of a linked module under a schedule, by default `schedule`, or `none` if the checker rejects them
*
  * `Admits`
  * `N.Admits F i`, the facts' concretization at a point of a run that starts function `i`
*
  * `sound`
  * the theorem of section 3
*
  * `Solver`, `defaultSolver`, `analyzeWith`, `soundWith`
  * the type of solvers, the solver that `analyze` uses, the analysis with a given solver, and its soundness theorem, which holds of every solver (section 12)
*
  * `transfers`, `transfers_sound`, `instAbsTable`
  * the table of the domain's transfer functions, its soundness, and the instance that the analysis is built from (section 12)
*
  * `render`
  * what the facts know of one value, as text, by the abstract types' `ToString`; only if every abstract type has `ToString` (section 7)
*
  * `annotate`
  * the facts of one function of a module, as text: block by block, then its result and its summaries, each value printed by `render` unless another printer is given (section 7)
*
  * `Covers`
  * whether the analysis covers a linked module (section 8)
*
  * `total`
  * with `(total)` only: the theorem that the analysis returns facts on every module it covers, or an error that names the missing instance (section 8)
*
  * `ascended`, `Settled`, `settles`
  * with `(settles)` only: the facts that the solver's ascent reaches, or `none` if it reaches the cap on rounds; whether facts are settled; and the theorem that beyond some cap the ascent settles without reaching it, or an error that names the missing instance (section 8)
:::

The declarations under `N.Internal` are the framework's, and no generated statement names them. They hold the domain as the command assembles it, `N.Internal.Dom`, the analysis, `N.Internal.analysis`, and for each instruction with a transfer function its table entry and the proof that the instruction's wrapper meets it, as `N.Internal.While.add.entry` and `N.Internal.While.add.entry_sound`, named after the instruction's key. A relational domain's are `transfer` and `sound`.

A generated declaration that fails to elaborate is a bug in `#dyn_absint`, not in your domain, and its error is reported at the command. `set_option dyn.absint.debug true` before the command elaborates the generated proofs one after another, which is slower, and prefixes each such error with the instruction, and with the transfer function and its theorem, that the declaration was generated for.

`#dyn_absint_coverage D for S` reports, before any analysis is built, what `#dyn_absint` would give each type and each instruction of `S`. The analysis gives each instruction its registered transfer function, or a default:

:::table +header
*
  * Instruction
  * What the analysis gives it
*
  * an instruction with a registered transfer function
  * that transfer function
*
  * a pure rule with no transfer function
  * `top`
*
  * `base.jump` and `base.unreachable` with no transfer function
  * the default transfer function, which takes every successor that the rule may take, from the state before ({ref "absint-successors"}[An instruction with successors])
*
  * `base.branch` with no transfer function
  * the default transfer function, from the state before: the successors that the condition's abstract value allows, if the domain's abstract type at `Bool` has a `BoolView`, and both successors otherwise ({ref "absint-successors"}[An instruction with successors])
*
  * a constructor or a case instruction of a datatype that the domain registers with `#dyn_abs_sum`
  * a generated transfer function ({ref "absint-sum"}[Datatypes])
*
  * any other constructor or case instruction, `base.refNew`, `base.refGet`
  * `top`, and every successor of a case instruction
*
  * any other rule that is not pure and has no transfer function
  * none: the checker rejects a module that uses it
*
  * a rule that the analysis does not support
  * none: the checker rejects a module that uses it
*
  * `base.callCode`
  * a summary of the callee, when a code-pointer fact names it; otherwise none, and the checker rejects the module ({ref "absint-calls"}[Calls and contexts])
:::

The analysis does not support a rule that takes the run token or capabilities, such as While's `print`, `tick` and the cell rules, a rule without regions that loops, a variadic instruction, an instruction generic over a list of types, and an instruction with type parameters whose rule is not pure or has regions ({ref "absint-register"}[What registration rejects]).

The report has one line per type and one per instruction. `type T ↦ A` says that the Dyn type `T` has the abstract type `A`, and any other `type` line says why it has none and gets `top`. `op o ↦ τ, proved by h` says that `o` has the transfer function `τ`, registered with the theorem `h`. Any other `op` line gives the instruction's default and the reason for it: `no transfer` for an instruction that has no transfer function, followed by `the default, which …` for one of the base's three, `derived` for a constructor or a case instruction, `the machine's` for an instruction that the machine runs itself, without a rule, and `unsupported, it …` with the reason, for a rule that the analysis does not support. The last line counts the transfer functions, the instructions whose rules are not pure and that have no transfer function and no default, and the instructions that are not supported. For `IvlTV`:

```leantext "What IvlTV gives each type and instruction (under development; illustrative, not pinned by a test)"
/--
info: type base.Unit: no abstract type: top
type base.Bool ↦ TV
type base.Int ↦ Ivl
…
type base.Sequence: has parameters: top
type base.Ref: the engine's: top
…
op base.jump: no transfer: the default, which takes its successor
op base.branch: no transfer: the default, which takes the successors that the condition's TV allows
op base.unreachable: no transfer: the default, which takes no successor
op base.callCode: the machine's call: through a summary of the callee that the code-pointer facts name
…
op while.add ↦ addIvl, proved by addIvl_sound
op while.sub ↦ subIvl, proved by subIvl_sound
op while.mul: no transfer: top
op while.neg ↦ negIvl, proved by negIvl_sound
op while.div: no transfer: a module that uses it is rejected
…
op while.lt ↦ ltTV, proved by ltTV_sound
…
op while.print: unsupported, it has a rule that takes the run token or capabilities: a module that uses it is rejected
…
6 transfers with lemmas; 6 instructions whose rules are not pure have no transfer; 5 are not supported
-/
#guard_msgs in
#dyn_absint_coverage IvlTV for WhileSem
```

`base.jump` and `base.branch` take their defaults, and the line of `base.branch` says that its default reads the condition through `TV`. `while.mul` has a pure rule and no transfer function, so the analysis gives its result `top`. `while.div` has successors and no transfer function, so the checker rejects a module that uses it. `while.print` takes capabilities, so no transfer function of it can be registered.

`(complete)` makes the second count an error. On `#dyn_absint_coverage`, the command then reports nothing if the count is zero, and otherwise is an error that names those instructions. Unsupported instructions and the base's three do not count:

```leantext "The coverage of IvlTV, complete (under development; illustrative, not pinned by a test)"
/--
error: IvlTV does not cover WhileSem: while.div (no transfer), while.mod (no transfer), while.pow (no transfer), while.pick (no transfer), while.if (no transfer), while.loop (no transfer)
-/
#guard_msgs in
#dyn_absint_coverage IvlTV for WhileSem (complete)
```

`IvlTV` has no transfer function of `while.div`, so the command of section 1 leaves `(complete)` out. On `#dyn_absint`, `(complete)` is the same error. `(complete)` is within reach for While: constant propagation, which has transfer functions of `/`, `if` and `loop`, lacks three:

```leantext "The coverage of constant propagation, complete (under development; illustrative, not pinned by a test)"
/--
error: CPD does not cover WhileSem: while.mod (no transfer), while.pow (no transfer), while.pick (no transfer)
-/
#guard_msgs in
#dyn_absint_coverage CPD for WhileSem (complete)
```

The options of `#dyn_absint` are `(domain := D)`, which it needs, `(contexts := c)` (section 11), and the flags `(complete)`, `(total)` and `(settles)`. An option given twice is an error.

### The abstract side beside the concrete side
%%%
number := false
tag := "absint-mirror"
%%%

The abstract side of this comparison is not in the package yet. The last column says how much of each form the work under development has built.

The abstract side reads like the concrete side of {ref "env-sem"}[Environment 7: Meaning]. Each construct that gives While its meaning has an abstract counterpart, written the same way. The table writes them with the letters of the table of forms at the start of the chapter, and with `E` an environment, `P` its parent, `d` a Lean type and `f` a rule:

::::nowrap
:::table +header
*
  * Concrete side
  * Abstract side
  * Status of the work under development
*
  * `environment E extends P`
  * `dyn_domain D` declares a domain, as `environment` declares an environment
  * built
*
  * `@[dyn_type T] d`
  * `@[dyn_abs D T] A` gives the Dyn type `T` its abstract type `A`, as `@[dyn_type T] d` gives it its Lean type `d`
  * built for Dyn types without type parameters
*
  * `@[dyn_sem o] f`
  * `@[dyn_transfer D o τ] h` gives the instruction `o` its transfer function `τ` and its proof `h`, as `@[dyn_sem o]` gives it its rule `f`
  * built
*
  * `{α : Type}`
  * `{A : Type} [AbsDomain A]`: a transfer function takes these per type parameter, as a rule takes `{α : Type}`
  * built for pure rules
*
  * `Region`, `runRegion`
  * a transfer function takes one abstract value per region's answer, where a rule takes one `Region` per region and runs it with `runRegion`; the transfer function says which regions may run, and its lemma takes one `RegionSpec` per region
  * built for instructions without type parameters, at one abstract type, in domains of abstract types, products and relational domains
*
  * `data T where …`
  * `#dyn_abs_sum D T` gives the datatype `T` an abstract type, as `#dyn_types` gives it a Lean type, and `#dyn_absint` then generates the transfer functions of its constructors and case instruction
  * built for datatypes with no type parameters
*
  * `#dyn_coverage E`
  * `#dyn_absint_coverage D for S` lists what each type and each instruction gets, as `#dyn_coverage` reports what has no rule, and `(complete)` on `#dyn_absint` makes a missing transfer function an error
  * built
*
  * `#dyn_sem_table S for E`
  * `#dyn_absint N for S (domain := D)` builds the analysis and its theorems, as `#dyn_sem_table` builds the table `S`
  * built
:::
::::

Notice the direction of each pair. A rule is trusted, since a rule defines what its instruction means. A transfer function is not trusted, so it comes with a theorem, and the attribute sits on the theorem and names the function. Notice also that both sides key on Dyn names, of types and of instructions, and that what each side's theorems are about, a rule's values or a transfer function's concretization, is stated at Lean types. So a domain does not depend on one table, and a child environment's analysis uses its ancestors' transfer functions, as its table uses their rules.

Three differences are deliberate. A transfer function may allow several successors where a rule takes one, and several regions where a rule runs one. Transfer functions make no requests, so there is no counterpart of `@[dyn_lang]`. And two Dyn types with one Lean type share an abstract type, as they share a tag.

## 7. Reading the result
%%%
number := false
tag := "absint-result"
%%%

Nothing that this section shows is in the package yet: the printers that `#dyn_absint` generates, the library functions that they use, and the tests.

The facts hold an abstract state at the entry of each block, in each context where the block's body is analysed, and a description of each result (section 11). `N.annotate prog f` prints them for the function `f` of the module `prog`. It links `prog` and analyses it under the domain's schedule, or under the schedule given as `(sch := …)`, and prints one line per block of `f`, with the block's label and the abstract value of each of the block's parameters, named as `prog` names it, or `dead` if the block's entry state is `⊥` in the root context, where a run starts the function; `annotate` does not read the summaries. The next line, `ret`, gives the abstract value of `f`'s result as the entry of a run. Then, for each summary of `f`, it prints a line `summary` with the summary's key, the facts of `f`'s parameters, and its result's (section 11). If the checker rejects the facts, it prints `rejected`. The library reads the facts through `Analysis.blockFacts`, which gives each block's label and, unless the block is dead, its parameters' values, and `Analysis.annotate` (`StrataDyn/Absint/Core/Show.lean`).

Each value is printed by `render`, the default of `annotate`'s third argument. `render` takes a value of `N.Value`, what the facts know of one value: `⊥`, `⊤`, or an abstract value of one of the domain's abstract types, which it prints by the type's `ToString`. A product's values print as pairs, such as `([10, 10], even)`, and a datatype's as the constructors that it may be, with their fields, such as `nothing | just([7, 7])`. `#dyn_absint` generates `N.render` when every abstract type of the domain has `ToString`, and for a relational domain when the type of its descriptions has one. Otherwise `annotate` takes a printer as its third argument. The test domain `TDs` has an abstract type without `ToString`:

```leantext "A domain whose values do not print (under development, in StrataDynTest/Absint/DomainsTest.lean)"
-- `TDsW` has no `render`, so its `annotate` takes a renderer; `TDW` has `render`, by default.
/-- error: Unknown identifier `TDsW.render` -/
#guard_msgs in
#check TDsW.render
#guard linesOf (TDsW.annotate · · fun _ => "v") sum "sum" =
  linesOf (TDW.annotate · · fun _ => "v") sum "sum"
```

`linesOf`, a helper of that test, lowers a program without comparison branches and returns the lines of `annotate`.

The test pins the lines of `sum` of {ref "absint-fixpoint"}[Joins, fixpoints and widening], lowered without comparison branches:

```leantext "The facts of sum without comparison branches (under development, in StrataDynTest/Absint/DomainsTest.lean)"
/--
info: entry.0: n.0=⊤
head.0: n.1=⊤, s.0=[0, +∞], i.0=[1, +∞]
body.0:
exit.0:
ret [0, +∞]
-/
#guard_msgs in
#eval IO.println ("\n".intercalate (linesOf (IvlTVWhile.annotate · ·) sum "sum"))
```

In SSA form, a variable is a different value in each block. A loop's header, and the join after an `if`, take every variable in scope as a parameter, and a block with one predecessor reads the values of the blocks that dominate it. So, without comparison branches, `body.0` and `exit.0` have no parameters, and their lines are empty. At the header, `s` is at least `0` and `i` at least `1`, and the result is at least `0`.

The same test shows a dead block, on `known`, a function whose condition compares constants:

```whilelang "A branch on a comparison of constants (under development, in StrataDynTest/Absint/DomainsTest.lean)"
fun f(n : Int) : Int {
  var x : Int := 3;
  if (x < 2) { return n; }
  return x;
}
```

```leantext "A dead branch, and the same branch without truth values (under development, in StrataDynTest/Absint/DomainsTest.lean)"
-- `TDs` has no abstract type at `Bool`, so its `base.branch` takes both successors, and neither
-- branch of `known` is dead; `TD`'s `TV` reads the condition, and the `then` branch is.
#guard linesOf (TDsW.annotate · · fun _ => "v") known "f" =
  ["entry.0: n.0=v", "then.0:", "else.0:", "join.0: n.1=v, x.0=v", "ret v"]
#guard linesOf (TDW.annotate · · fun _ => "v") known "f" =
  ["entry.0: n.0=v", "then.0: dead", "else.0:", "join.0: n.1=v, x.0=v", "ret v"]
```

Both analyses print every value as `v`. `TD`, the domain of `TDW`, has intervals at `Int`, `TV` at `Bool`, and the transfer function `ltTV` of `<`. So `x < 2` is a set that lacks `true`, the default of `base.branch` takes only the `else` successor, and the `then` block is `dead`. `TDs` has no abstract type at `Bool`, so its default of `base.branch` takes both successors.

On `pruned`, the function of {ref "absint-example"}[An example worked by hand], constant propagation finds the result `12`, as the hand computation does, and gives two of the function's four blocks the state `⊥` (`StrataDynTest/Absint/ConstPropTest.lean`). On a function with `%`, which neither `IvlTV` nor constant propagation has a transfer function of, the checker rejects the module, and `annotate` prints `rejected`.

Notice what the entry states say about blocks. A transfer function that rules a successor out, such as `IvlTV`'s default of `base.branch` on a set that lacks `true`, leaves the successor's block at `⊥` unless another edge reaches it. No configuration of a run runs in or enters a block whose entry state is `⊥` in every context that analyses its body. The framework's `Analysis.exec_not_bot` and `Analysis.entry_not_bot` give this from `sound`, and a test states it for `IvlTVWhile` as `bot_unreached` ({ref "app-absint-results"}[Dead blocks and settling], in appendix E). The theorem shows a block that `annotate` prints `dead` to be unreached only when the block is also `⊥` in each summary of its function. So the facts mark dead blocks with no separate liveness, even a block with no instructions. The test checks one: in a function whose untaken branch is an empty block, that block's entry state is `⊥`, and the empty block where the branches join is not.

The facts are Lean values that `analyze` computes, and `sound` says what they mean. With `sound`, a property of the facts becomes a property of every run.

## 8. Termination
%%%
number := false
tag := "absint-total"
%%%

Nothing that this section shows is in the package yet: the termination theorems that `#dyn_absint` generates, the classes, definitions and theorems of the framework that they rest on, and the tests.

With `(total)`, `#dyn_absint` also generates the theorem `total`:

```leantext "The theorem total (under development, in StrataDynTest/Absint/DomainsTest.lean)"
/--
info: @IvlTVWhile.total : ∀ {m : LModule WhileSem.model.at},
  IvlTVWhile.Covers m = true → ∀ (sch : Schedule), ∃ F, IvlTVWhile.analyze m sch = some F
-/
#guard_msgs in
#check @IvlTVWhile.total
```

`total` says that the analysis returns facts on every module that it _covers_, under every schedule. `IvlTVWhile.Covers` is the framework's `Covers` at the analysis:

```leantext "Covered modules (under development, in StrataDyn/Absint/Core/Solve.lean)"
/-- **The analysis covers the module**: its bodies, functions and regions, have distinct names;
every block has distinct parameters, a transfer for every rule with successors, and no exit with
more than one value; and every call of a block that a site reaches has a callee that the
module's code-pointer facts (`codesOf`) name, with as many parameters as the call has arguments:
its slot holds a code pointer that was stored on every path from its body's entry.  On a covered
module the checker accepts what the solver finds. -/
def Covers (m : LModule M.at) : Bool :=
  decide ((bodiesOf m).toList.map (·.name)).Nodup && (bodiesOf m).all T.bodyCovered &&
    (bodiesOf m).all fun b => (List.range b.blocks.size).all fun i =>
      match b.blocks[i]?, codesBy (codesOf m) b i with
      | some blk, some cs => callsCovered m cs blk.insns
      | _, _ => true
```

The module's bodies are its functions and its regions, so `total` covers modules with regions and with calls. In each body, the blocks have distinct parameters, no exit passes more than one value, every instruction whose rule is not pure has a transfer function, its own or a default, and every call in a block that the entry reaches has a callee that a code-pointer fact names ({ref "absint-calls"}[Calls and contexts]). Together, `sound` and `total` say that on a covered module the analysis returns facts, and that every run respects them.

`total` needs one more instance for each abstract type of the domain, the order's laws. They say that `⊑` is a preorder with `⊤` above every abstract value, and that `a ⊔ b` and `a ∇ b` are above both `a` and `b`. The class is stated once, for every `Lattice`:

```leantext "The order's laws (under development, in StrataDyn/Absint/Order.lean)"
/-- **The order laws that the solver's termination needs**, with no mention of `γ`: `le` is a
preorder with `top` above every value, and `join` and `widen` are upper bounds of their
arguments.  Soundness needs none of them. -/
class Order (A : Type) [Lattice A] : Prop where
  le_refl : ∀ a : A, Lattice.le a a = true
  le_trans : ∀ {a b c : A}, Lattice.le a b = true → Lattice.le b c = true →
    Lattice.le a c = true
  le_top : ∀ a : A, Lattice.le a Lattice.top = true
  le_join_left : ∀ a b : A, Lattice.le a (Lattice.join a b) = true
  le_join_right : ∀ a b : A, Lattice.le b (Lattice.join a b) = true
  le_widen_left : ∀ a b : A, Lattice.le a (Lattice.widen a b) = true
  le_widen_right : ∀ a b : A, Lattice.le b (Lattice.widen a b) = true
```

Notice that `Order` mentions no concrete value and no `γ`. Sets of truth values have it. Their widening is their join, so the laws of the widening are those of the join:

```leantext "The order's laws of truth values (under development, in StrataDyn/Examples/While/TruthValues.lean)"
/-- The order laws of truth-value sets. -/
instance : Order TV where
  le_refl := TV.le_refl
  le_trans := TV.le_trans
  le_top := TV.le_top
  le_join_left := TV.le_join_left
  le_join_right := TV.le_join_right
  le_widen_left := TV.le_join_left
  le_widen_right := TV.le_join_right
```

Intervals have `Order` too, in `StrataDyn/Examples/While/Interval.lean`. With `(total)`, `#dyn_absint` generates `total` if it finds `Order` for every abstract type of the domain, and otherwise reports the missing instances, in an error such as `D has no total: no instance Order A` (illustrative, not pinned by a test). A relational domain needs `StateOrder` of its states and `Order` of their descriptions instead ({ref "absint-relational"}[Relational transfer functions]).

With the order's laws, the checker accepts the solver's result on a covered module whether the rounds settle or reach the cap, so the analysis returns facts. Facts at the cap are `top` at every block, which says nothing. A domain avoids them when its widening _stabilises_, that is, when a chain of widening steps cannot go on forever. Then a large enough cap is never reached. A _widening step_ takes `a` to `a ∇ b` for a value `b` that is not below `a`, so that the solver's value grows. `AscendingWF A` says that the widening steps of `A` stabilise: the relation is well founded, so no infinite chain of them exists:

```leantext "Widening steps and their stabilisation (under development, in StrataDyn/Absint/Order.lean)"
/-- **A widening step**: `a₁` is `a` widened by a value that `a` does not admit. -/
def WidenStep (a₁ a : A) : Prop :=
  ∃ b, Lattice.le b a = false ∧ a₁ = Lattice.widen a b

/-- **Repeated widening stabilises**: there is no infinite chain `a₀, a₁, …` in which each
`aᵢ₊₁` is `aᵢ` widened by a value that `aᵢ` does not admit. -/
class AscendingWF (A : Type) [Lattice A] : Prop where
  wf : WellFounded (WidenStep (A := A))
```

For example, `[1, 1]`, `[1, 1] ∇ [1, 2] = [1, +∞]`, `[1, +∞] ∇ [0, 5] = [-∞, +∞]` is a chain of two widening steps. `AscendingWF.ofRank` gives stabilisation from a measure that each widening step lowers:

```leantext "Stabilisation from a measure (under development, in StrataDyn/Absint/Order.lean)"
/-- **Widening stabilises when it lowers a rank**: widening `a` by a value it does not admit
gives a value of lower rank. -/
theorem AscendingWF.ofRank (rank : A → Nat)
    (h : ∀ {a b : A}, Lattice.le b a = false → rank (Lattice.widen a b) < rank a) :
    AscendingWF A :=
  ⟨wf_of_rank rank fun ⟨_, hb, e⟩ => e ▸ h hb⟩
```

The measure of intervals counts their finite bounds: a widening step makes at least one finite bound infinite, or moves up from `⊥` or to `⊤`, so it lowers the measure. `StrataDyn/Examples/While/Interval.lean` proves it. `DescendingWF` is the same class for narrowing steps, and intervals have it too. `TV`, the domain's other abstract type, has `Order` and both classes. Its measure is the number of truth values that a set lacks:

```leantext "Truth values stabilise (under development, in StrataDyn/Examples/While/TruthValues.lean)"
/-- The number of truth values the set lacks. -/
def rank (a : TV) : Nat := (if a.mayTrue then 0 else 1) + (if a.mayFalse then 0 else 1)
…
/-- A union with a set that `a` does not include lacks fewer truth values than `a`. -/
theorem rank_join : ∀ {a b : TV}, le b a = false → rank (join a b) < rank a := by
  …
/-- Widening of truth-value sets stabilises: it lowers the truth values a set lacks. -/
instance : AscendingWF TV := AscendingWF.ofRank TV.rank TV.rank_join
```

The framework's theorem `ascended_settles` says that, for an analysis whose states have these instances, the solver's ascent settles before a large enough cap: on every module, with or without regions and calls, and under every context allocator. With `(settles)`, `#dyn_absint` states it for the domain that it assembles, as `settles`, if it finds `Order` and `AscendingWF` for every abstract type of the domain, or, for a relational domain, `StateOrder` and `StateAscendingWF` of its states and `Order` and `AscendingWF` of their descriptions. Neither `(total)` nor `(settles)` needs `DescendingWF`, since narrowing stops at the cap. The command of section 1 has `(settles)`:

```leantext "The theorem settles (under development, in StrataDynTest/Absint/DomainsTest.lean)"
/--
info: IvlTVWhile.settles : ∀ (m : LModule WhileSem.model.at) (wa : Nat) (c : Contexts),
  ∃ F n,
    ∀ (sch : Schedule),
      sch.widenAfter = wa →
        sch.contexts = c → n ≤ sch.maxRounds → IvlTVWhile.ascended m sch = some F ∧ IvlTVWhile.Settled m F
-/
#guard_msgs in
#check @IvlTVWhile.settles
```

`IvlTVWhile.ascended m sch` is the facts that the solver's ascent reaches on `m` under `sch`, before any narrowing, or `none` if the ascent reaches the cap, where the solver gives up with `top`. `IvlTVWhile.Settled m F` says that `F` are the facts of settled states: they fit a layout of `m`'s bodies and summaries, they already admit what each block sends and what each body starts from, and every call has a summary that serves it. Then one more round changes nothing. So `settles` says: for every module `m`, every number `wa` of joining rounds and every context allocator `c`, there are facts `F` and a number of rounds `n` such that, under every schedule that joins for `wa` rounds, allocates by `c` and has a cap of at least `n`, the ascent reaches `F` without reaching the cap, and `F` is settled. So the solver does not fall back to `top`, and the facts do not depend on the cap once it is large enough. The theorem is about `ascended`, not `analyze`, since `analyze` may return narrowed facts. A domain with an abstract type that lacks one of the instances has no `settles`, and the command names the instance:

```leantext "A domain whose widening is not known to stabilise (under development, in StrataDynTest/Absint/PolyTest.lean)"
/-- error: PD has no settles: no instance AscendingWF PD.Opt -/
#guard_msgs in
#dyn_absint PolyAnS for PolySem (domain := PD) (settles)
```

Notice that these classes mention no concrete value, and `sound` uses none of them. So an analysis has its soundness theorem without a termination proof, and a termination proof needs no semantics.

:::::callout "Planned interface, not yet built"
The abstract types of datatypes, `SumAbs Fs` ({ref "absint-sum"}[Datatypes]), get an `AscendingWF` instance from their fields', as they get `Order`. Until then, a domain with a `#dyn_abs_sum` type has no `(settles)`, as `PD` shows.
:::::

## 9. Reduced products
%%%
number := false
tag := "absint-product"
%%%

Reduced products are not in the package yet.

A loop that counts by two:

```whilelang "A loop that counts by two (under development, in StrataDynTest/Absint/ReducedTest.lean)"
fun f() : Int {
  var i : Int := 0;
  while (i < 9) { i := i + 2; }
  return i;
}
```

The _parity domain_ `ParD` describes an integer by whether it is even or odd. Its abstract type `Par` has four values, `⊥`, `even`, `odd` and `⊤`, and `StrataDyn/Examples/While/Parity.lean` defines it, with its transfer functions and their proofs. `ParD` gives `Par` to `Base.Int` and `TV` to `Base.Bool`, as `IvlTV` gives `Ivl` and `TV`.

`Par`'s order puts `⊥` below `even` and `odd`, and both below `⊤`, so `even ⊔ odd = ⊤`. Intervals find that `i` is in `[9, 10]` at the exit: the loop exits when `i < 9` fails, and the widening and narrowing bound `i` by `10`. Parities find that `i` is even, since it starts even and grows by two. Neither alone finds that `i` is `10`. Together, they do: the only even integer in `[9, 10]` is `10`.

The _product_ of two domains pairs their abstract values: a value is in `(a, p)` when it is in `a` and in `p`. A _reduction_ maps an abstract value of the product to one that describes at least the values that it describes, in which each part drops what the other rules out. A product with a reduction is a _reduced product_. Here, the reduction moves an interval's bounds in to the nearest integers of its parity:

```leantext "The reduction (under development, in StrataDyn/Examples/While/Reduced.lean)"
/-- **An interval tightened by a parity**: its bounds moved in to the nearest integers of the
parity, `bot` for the parity `bot`. -/
def tighten : Ivl → Par → Ivl
  | .range lo hi, .even => Ivl.mk (lo.map upEven) (hi.map downEven)
  | .range lo hi, .odd => Ivl.mk (lo.map upOdd) (hi.map downOdd)
  | _, .bot => .bot
  | a, _ => a
```

`upEven n` is the least even integer at or above `n`, and the other three move a bound in the same way:

```leantext "Moving a bound to a parity (under development, in StrataDyn/Examples/While/Reduced.lean)"
/-- The least even integer at or above `n`. -/
def upEven (n : Int) : Int := n + n % 2

/-- The greatest even integer at or below `n`. -/
def downEven (n : Int) : Int := n - n % 2

/-- The least odd integer at or above `n`. -/
def upOdd (n : Int) : Int := n + (1 - n % 2)

/-- The greatest odd integer at or below `n`. -/
def downOdd (n : Int) : Int := n - (1 - n % 2)
```

For example, `tighten [9, 10] even` is `[10, 10]`. Its soundness lemma, `tighten_sound`, says that the tightened interval keeps every integer of the parity that the interval held.

The product's reduction maps a pair to a pair: it tightens the interval by the parity, and keeps the parity. Its lemma states that every integer that a pair describes, the reduced pair describes too. A product is declared from two domains, with its reduction:

```leantext "The reduced product, declared (under development, in StrataDyn/Examples/While/Reduced.lean)"
/-- **The reduction of an interval by a parity**: the interval tightened, the parity kept. -/
def ivlParReduce (d : Ivl × Par) : Ivl × Par := (tighten d.1 d.2, d.2)

/-- `ivlParReduce` keeps every integer that the pair stands for. -/
theorem ivlParReduce_sound (d : Ivl × Par) (x : Int) (h : γ d x) : γ (ivlParReduce d) x :=
  ⟨tighten_sound h.1 h.2, h.2⟩

/-- Intervals and truth values, and parities, reduced. -/
dyn_domain IP := IvlTV × ParD (reduce := ivlParReduce, ivlParReduce_sound) (narrow := true)

#dyn_absint IPWhile for WhileSem (domain := IP) (total) (settles)
```

* `dyn_domain P := D₁ × D₂` declares the product of two domains declared with `@[dyn_abs]`. A slot of the product has an abstract value of each factor: in `IP`, an interval and a parity at `Base.Int`, and two sets of truth values at `Base.Bool`. A pair describes a value when both of its parts do, so `γ d x` is `γ d.1 x ∧ γ d.2 x`, and the proof of `ivlParReduce_sound` is a pair of proofs.
* Its transfer functions are derived. The transfer function of an instruction runs both factors' transfer functions, each on its own part. A factor that has no transfer function of the instruction knows nothing of its result, and allows every successor and every region. The product allows a successor if both factors allow it, and runs a region if both factors run it ({ref "absint-regions"}[Instructions with regions]). It applies the reduction to its result and to every value that it passes.
* `(reduce := f, h)` applies `f` only at the Lean type that `h` is stated at, here `Int`, and the pairs at `Bool` are not reduced. `#dyn_absint` checks that `h` states the reduction's obligation.
* A factor must be a domain of abstract types: a factor that is a relational domain or a product is an error. A product takes the schedule options of `dyn_domain`, but no `(state := S)`: its states are its factors'.

The coverage report gives each instruction both factors' lines:

```leantext "The coverage of a product (under development, in StrataDynTest/Absint/ReducedTest.lean)"
/--
info: type base.Unit: no abstract type: top
type base.Bool ↦ TV
type base.Int: in IvlTV ↦ Ivl; in ParD ↦ Par
…
op base.jump: in IvlTV: no transfer: the default, which takes its successor; in ParD ↦ jumpPar, proved by jumpPar_sound
op base.branch: in IvlTV: no transfer: the default, which takes the successors that the condition's TV allows; in ParD ↦ branchTV, proved by branchTV_sound
op base.unreachable: no transfer: the default, which takes no successor
…
op while.add: in IvlTV ↦ addIvl, proved by addIvl_sound; in ParD ↦ addPar, proved by addPar_sound
…
op while.lt: in IvlTV ↦ ltTV, proved by ltTV_sound; in ParD: no transfer: top
…
12 transfers with lemmas; 6 instructions whose rules are not pure have no transfer; 5 are not supported
-/
#guard_msgs in
#dyn_absint_coverage IP for WhileSem
```

So the product's transfer function of `<` pairs `ltTV`'s set of truth values with `top`, and that of `base.branch` pairs `IvlTV`'s default, which reads the condition's `TV`, with `ParD`'s `branchTV`. Where both factors have the same line, as for `base.Bool`, whose abstract type is `TV` in both, or `base.unreachable`, the report gives it once. The test shows two rejections beside declarations that pass:

```leantext "Products rejected beside their twins (under development, in StrataDynTest/Absint/ReducedTest.lean)"
-- A factor that is a relational domain is an error; a domain of abstract types is a factor.
/--
error: Zones is not a domain of abstract types: a product's factors are domains declared with `@[dyn_abs]`
-/
#guard_msgs in
dyn_domain IPZ := IvlTV × Zones
dyn_domain IPP := IvlTV × ParD (narrow := true)

…
-- A reduction whose lemma states another obligation is an error; `IP`'s lemma is the one.
dyn_domain IPB := IvlTV × ParD (reduce := ivlParReduce, ivlParReduce_fst)
/--
error: ivlParReduce_fst does not state that ivlParReduce is a reduction of IPB at Int.  The obligation is
  ∀ (d : Ivl × Par) (x : Int), γ d x → γ (ivlParReduce d) x
but ivlParReduce_fst states
  ∀ (d : Ivl × Par) (x : Int), γ d x → γ (ivlParReduce d).fst x
-/
#guard_msgs in
#dyn_absint IPBWhile for WhileSem (domain := IPB)
```

`IPP` is the product without a reduction. `ivlParReduce_fst` states only that the tightened interval keeps `x`, which is less than the obligation.

:::::callout "Planned interface, not yet built"
* A conversion `@[dyn_abs_conv] def c : A → B`, with a lemma `γ a x → γ (c a) x`, lets a factor's transfer function at `B` take operands at `A`.
* A transfer function registered for the product by hand replaces the derived one.
:::::

`#dyn_absint` builds the analysis `IPWhile`, with its theorems `IPWhile.sound`, `IPWhile.total` and `IPWhile.settles`. Its test pins the results of the three domains, and of the product without its reduction:

```leantext "What each finds (under development, in StrataDynTest/Absint/ReducedTest.lean)"
#guard ipRet byTwo = some (some ("[10, 10]", "even"))
-- Intervals alone give `[9, 10]`.
#guard typedRet (IvlTVWhile.analyze ·) byTwo = some "[9, 10]"
-- Parities alone give `even`.
#guard typedRet (ParWhile.analyze ·) byTwo = some "even"
```

```leantext "The product without its reduction (under development, in StrataDynTest/Absint/ReducedTest.lean)"
-- Without the reduction, the product finds what intervals find.
#guard ipRet byTwo (fun lm => IPPWhile.analyze lm) = some (some ("[9, 10]", "even"))
```

::::nowrap
:::table +header
*
  * Domain
  * The result
*
  * intervals
  * `[9, 10]`
*
  * parities
  * `even`
*
  * intervals and parities, not reduced
  * `[9, 10]` and `even`
*
  * intervals and parities, reduced
  * `[10, 10]` and `even`
:::
::::

The analysis applies the reduction after each transfer function, to the value that the instruction defines and to every value that it passes along a successor, and never after a widening or a narrowing. A reduction after a widening can undo it, and then the rounds may never stop. With the reduction kept out of widening, the product's widening steps are steps of its factors, and the product stabilises when its factors do. So `IPWhile.total` and `IPWhile.settles` need nothing of the reduction.

### Products of state domains
%%%
number := false
tag := "absint-product-states"
%%%

The library's reduced products are not in the package yet.

`dyn_domain P := D₁ × D₂` is one way to build a reduced product. The library builds one from any two state domains, relational ones included. `RP R` keeps a state of each factor for the same frame, and each factor sees the machine's values as its own table does. After each transfer, the _reducer_ `R` exchanges what the two states know of the slot that the instruction writes, at the tag of its result, and of each value that it passes, at that value's tag. A reducer's only law is that an exchange keeps what the pair stands for. It need not be idempotent or optimal. Inclusion, join, widening and narrowing go factor by factor, and a pair with a factor that is `⊥` is `⊥`. `RP.table R t₁ t₂` builds the product's table from the factors' tables, and `RP.table_sound` proves it sound, once for every product. The order laws and the stabilisation of `RP R` follow from the factors', so `total` and `settles` need nothing of the reducer. `dyn_domain P := D₁ × D₂ (reduce := f, h)` is the case of two domains of abstract types, with the reducer of `f` at the tag of the Lean type that `h` is stated at.

The zones of {ref "absint-relational"}[Relational transfer functions] bound differences of integers, but have no transfer function of negation. Intervals have one. Their product, written with the library, gives the zone the interval of each integer slot that an instruction writes:

```leantext "A reduced product of zones and intervals (under development, in StrataDyn/Examples/While/ZoneInterval.lean)"
/-- The reducer of zones by intervals: `ziSlot` at each written slot, and nothing at payload
values. -/
def zoneIvl : Reducer ziViews where
  slot := ziSlot
  pay _ q := q
  slot_sound := ziSlot_sound
  pay_sound h := h
…
/-- Zones and intervals, reduced. -/
dyn_domain ZI

/-- **The table of `ZI`**: the product of the tables of `Zones` and `IvlTV`, with their
defaults. -/
instance : AbsTable WhileSem.model ZI (RP zoneIvl) :=
  ⟨RP.table zoneIvl (AbsTable.table Zones) (AbsTable.table IvlTV),
    RP.table_sound AbsTable.sound AbsTable.sound rfl rfl⟩
```

`ziViews` are the two tables' views of While's values. `ziSlot` bounds the zone's slot by the slot's interval, and `ziSlot_sound` proves that this keeps the pair's valuations. The declared domain `ZI` names the analysis, and the instance gives it its table (section 12). Here is a program that needs both:

```whilelang "The smaller of a and ten (under development, in StrataDynTest/Absint/ZoneIntervalTest.lean)"
fun f(a : Int) : Int {
  var m : Int := 0 - 10;
  var n : Int := -m;
  var r : Int := a;
  if (n < a) { r := n; }
  return r;
}
```

```leantext "What each finds (under development, in StrataDynTest/Absint/ZoneIntervalTest.lean)"
-- Zones alone, and intervals alone, know nothing of the result.
#guard retOf (ZoneWhile.analyze ·) ZoneWhile.render minTen = some "⊤"
#guard retOf (IvlTVWhile.analyze ·) IvlTVWhile.render minTen = some "⊤"
-- The product proves `r ≤ 10` in its zone.
#guard retOf (ZIWhile.analysis.analyze ·) pairText minTen = some "([-∞, 10], ⊤)"
…
-- Without the reduction, the product proves nothing more than its factors.
#guard retOf ((defaultAnalysis WhileSem.model ZN (RP (Reducer.none ziViews))).analyze ·)
  pairText minTen = some "(⊤, ⊤)"
```

Intervals know that `n` is `10`, but do not relate `r` to `a` at the comparison. Zones relate `r` to `n` along both branches, but do not know `n`. With the reduction, the zone learns `n`'s interval when `-m` is computed, and so bounds `r` by `10`. `ZN` is the same product with `Reducer.none`, which changes nothing, and finds what the factors find.

*Known limitation.* The reducer runs only after a transfer function. A call's result, a jump's arguments, and a region's entry state are not reduced, so in zones × intervals the zone does not learn the interval of a call's result.

## 10. A domain of signs and parities
%%%
number := false
tag := "absint-sp"
%%%

The domain of this section is not in the package yet.

A reduced product can also live inside one abstract type. The abstract type `SP` describes an integer by its possible signs and parities, and it reduces itself. The domain `SPD` gives `SP` to `Base.Int` and `TV` to `Base.Bool`, as `IvlTV` gives `Ivl` and `TV`. Its proofs are in `StrataDyn/Examples/While/SignParity.lean`.

### Signs and parities in one type
%%%
number := false
tag := "absint-sp-product"
%%%

`SP` is not in the package yet.

`SP` pairs a set of signs, a subset of `{-, 0, +}`, with a set of parities, a subset of `{even, odd}`: an integer is in `(S, P)` when its sign is in `S` and its parity is in `P`. `SP` holds one flag per sign and parity:

```leantext "Signs and parities (under development, in StrataDyn/Examples/While/SignParity.lean)"
/-- **Signs and parities**: which of each an integer may have. -/
structure SP where
  neg : Bool
  zero : Bool
  pos : Bool
  even : Bool
  odd : Bool
  deriving DecidableEq, Repr

/-- What an abstract value stands for: an integer whose sign and parity it allows. -/
def means (a : SP) (n : Int) : Prop := (a.hasSg (sg n) && a.hasPa (pa n)) = true
```

`sg n` and `pa n` are `n`'s sign and parity, and `hasSg` and `hasPa` read a flag. The order compares flag by flag, and the join keeps the flags of either. `⊥` has no flag, and `⊤` has every flag. The tests print an abstract value as its flags. For example, `-+o` describes the odd integers, and `0+eo` the nonnegative integers.

### The reduction
%%%
number := false
tag := "absint-sp-reduce"
%%%

`SP.reduce` is not in the package yet.

In `SP`, the signs may allow what the parities rule out. For example, the flags `{0, +}` with `{odd}` allow the sign `0`. No integer is both zero and odd, so they describe only the positive odd integers. `SP.reduce`, a reduction in the sense of section 9, drops each sign that no allowed parity has, and each parity that no allowed sign has:

```leantext "The reduction (under development, in StrataDyn/Examples/While/SignParity.lean)"
def reduce (a : SP) : SP :=
  { a with
    neg := a.neg && (a.even || a.odd)
    zero := a.zero && a.even
    pos := a.pos && (a.even || a.odd)
    even := a.even && (a.neg || a.zero || a.pos)
    odd := a.odd && (a.neg || a.pos) }

theorem reduce_means (a : SP) (n : Int) : means a.reduce n ↔ means a n :=
```

`reduce_means` states that the reduction keeps the concretization. Its proof is by cases on the sign and the parity and by `decide` on the flags, and `#print axioms` reports that it depends on no axiom.

### Transfer functions from sign and parity tables
%%%
number := false
tag := "absint-sp-tables"
%%%

The transfer functions of `SP` are not in the package yet.

The sign of a sum depends only on the operands' signs, and its parity only on their parities. A _table_ gives the possible signs of a result from the signs of the operands:

```leantext "The signs of a sum (under development, in StrataDyn/Examples/While/SignParity.lean)"
def addSg : Sg → Sg → Sg → Bool
  | .neg, .neg, r | .neg, .zero, r | .zero, .neg, r => r == .neg
  | .zero, .zero, r => r == .zero
  | .zero, .pos, r | .pos, .zero, r | .pos, .pos, r => r == .pos
  | .neg, .pos, _ | .pos, .neg, _ => true

theorem addSg_sound (x y : Int) : addSg (sg x) (sg y) (sg (x + y)) = true := by
  unfold sg
  repeat' split
  all_goals first | rfl | omega
```

`SP.arith` lifts a sign table and a parity table to a transfer function, and reduces its result. `SP.arith_sound` proves, once for every operation, that the lifted transfer function meets the operation's obligation if the tables allow the sign and the parity of every result. So the proof of each arithmetic transfer function is one application:

```leantext "Addition (under development, in StrataDyn/Examples/While/SignParity.lean)"
def addSP : SP → SP → SP := SP.arith addSg addPa
```

```leantext "Its proof (under development, in StrataDyn/Examples/While/SignParity.lean)"
/-- `addSP` is sound: the sum of operands in their abstract values is in its abstract value. -/
theorem addSP_sound (lhsAbs rhsAbs : SP) (a b : Int) (ha : γ lhsAbs a) (hb : γ rhsAbs b) :
    γ (addSP lhsAbs rhsAbs) (WhileRules.add a b) :=
  SP.arith_sound addSg_sound addPa_sound ha hb
```

Subtraction and multiplication work the same way. Negation, `negSP`, swaps the flags `-` and `+`. The comparisons `<`, `<=` and `==` use a table from both operands' signs and parities to the possible truth values, and `SP.cmp` lifts the table to a set of truth values. For example, `x == y` is false when `x` and `y` differ in sign or in parity:

```leantext "Comparisons and division (under development, in StrataDyn/Examples/While/SignParity.lean)"
/-- A comparison on abstract values, from its table, as a set of truth values. -/
def cmp (t : Sg → Pa → Sg → Pa → Bool → Bool) (a b : SP) : TV := TV.ofFn (liftCmp t a b)

/-- `a < b`. -/
def ltSP : SP → SP → TV := SP.cmp ltT

/-- `a / b`: any integer, and `^err` with `divByZero` only if the divisor may be zero. -/
def divSP (_ b : SP) : AbsOut SP :=
  { res := SP.top, succs := #[if b.zero then some #[SP.abs WhileRules.divByZero] else none] }
```

`TV.ofFn f` is the set of the truth values that `f` holds of, and `liftCmp t a b r` says that the table `t` allows the result `r` for some sign and parity that `a` and `b` allow. `divSP` takes `^err` only if the divisor's abstract value has the flag `0`, and its quotient is `SP.top`. The domain `SPD` of `StrataDyn/Examples/While/Domains.lean` registers `SP` at `Base.Int`, `TV` at `Base.Bool`, these transfer functions with their proofs, and `branchTV` for `base.branch`, and `#dyn_absint SPWhile for WhileSem (domain := SPD) (total)` builds the analysis. The results below are `SPWhile`'s.

### What it finds
%%%
number := false
tag := "absint-sp-results"
%%%

`SPWhile` is not in the package yet, and the tests that pin these results are not either.

In this function, only the reduced product proves the divisor nonzero:

```whilelang "A divisor that only the reduced product proves nonzero (under development, in StrataDynTest/Absint/SignParityTest.lean)"
fun f(n : Int) : Int {
  var y : Int := 0 - 1;
  var i : Int := 0;
  while (i < n) { y := y + 2; i := i + 1; }
  var z : Int := y * 4;
  return 100 / z;
}
```

At the loop's header, `y` is `-1` on entry and `y + 2` after the body. Its sign is unknown, but it stays odd, so the reduction drops `0`, and `y` is `-+o`. `z := y * 4` is even, so its parity alone allows zero. Its sign is the product of a nonzero sign and a positive one, `-+`, so `z` is `-+e`. So `divSP` never takes `^err`, and no run enters `^err`'s handler. The analysis gives four of `f`'s five blocks a state that is not `⊥`.

Two more results, from `StrataDynTest/Absint/SignParityTest.lean`:

::::nowrap 2 3
:::table +header
*
  * Program
  * `SP`
  * `CP` (the test pins only the first program's count of blocks)
*
  * `if (2 * n == 1) { return 1 / 0; } return n;`
  * `2 * n` is `-0+e` and `1` is `+o`, so `2 * n == 1` is `false`, and the block that divides by zero is `⊥` (3 blocks are not `⊥`)
  * `2 * n` is `⊤`, and 5 blocks are not `⊥`
*
  * `sum`
  * at the header, `i` is `+eo` and `s` is `0+eo`, and the result is `0+eo`
  * `i`, `s` and the result are `⊤`
:::
::::

## 11. Calls and contexts
%%%
number := false
tag := "absint-calls"
%%%

The analysis of calls is not in the package yet.

The analysis follows a `base.callCode` call through a _summary_ of its callee: the analysis of the callee's body on a _key_, facts of its arguments above those of the call. A summary serves every call whose arguments its key is above, and a value that the callee returns reaches only the callers that read that summary. There is one solver for modules with calls and without: it analyses each summary as one more body, created when a call first demands it, and a module without calls has none.

The facts are indexed by a _context_, the place where a body is analysed:

* `root i`, the run's own context of function `i`, in which `i` is analysed as the entry of a run, on arguments it knows nothing of, with a description of its own result;
* `region k`, in which region `k` is analysed as the rules run it;
* `sum i j`, entry `j` of function `i`'s summaries.

The root contexts and the regions' share their states. `N.annotate prog f` prints the facts of `f` in its root context, with its result there, then one line per summary of `f`: its key's facts and its result's.

*The callee.* The function that a call runs is the one that a _code-pointer fact_ at the call names. The call's operand must hold a code pointer with no captures, stored in the call's block or along every path to it, and not written since. The facts are found once per module and checked like the states, along every edge from a block that the entry reaches, so they need no proof either. A block that the entry does not reach, such as dead code after a `return`, has every fact, so it costs no call its callee. A call through any other code pointer, such as a function's parameter or a closure with captures, is rejected, and so is a partial application. A front end that calls through a function reference, as `Emit.code` and `Base.callCode` emit it ({ref "tr-build"}[Translator 2: The builder]), is analysed.

*Which summaries exist.* A _context allocator_ chooses, and the schedule's `contexts` names it:

* `perInput k`, the default with `k = 4`, keeps a summary per input up to `k` per callee, and then widens the last key by each further input;
* `perCallee` keeps one summary per callee, whose key widens by every input that it is not above.

`#dyn_absint N for S (domain := D) (contexts := perCallee)` chooses the second. A call reads a summary whose key is above its arguments, the most precise such key that exists, so the allocator decides which keys exist, not which one a call reads. The checker accepts any summaries that serve every call, so the choice changes what the analysis finds, not its soundness.

Here is constant propagation on a helper called on two inputs, from a test of calls:

```whilelang "A helper called on two inputs (under development, in StrataDynTest/Absint/CallsTest.lean)"
fun inc(x : Int) : Int { return x + 1; }
fun main() : Int { var a : Int := inc(1); var b : Int := inc(5); return a + b; }
fun run() : Int { return main(); }
```

```leantext "Its summaries, per input and per callee (under development, in StrataDynTest/Absint/CallsTest.lean)"
-- A summary per input: `inc` on `1` returns `2`, on `5` returns `6`, and `main` returns `8`.
#guard cp twice "inc" = ["entry.0: x.0=⊤", "ret ⊤", "summary x.0=1: ret 2", "summary x.0=5: ret 6"]
#guard cp twice "main" = ["entry.0:", "ret 8", "summary : ret 8"]
-- One summary per callee: the inputs join, and so do the results.
#guard cpCallee twice "inc" = ["entry.0: x.0=⊤", "ret ⊤", "summary x.0=⊤: ret ⊤"]
#guard cpCallee twice "main" = ["entry.0:", "ret ⊤", "summary : ret ⊤"]
```

`cp` and `cpCallee` print the lines of `annotate` under `CPWhile` and under `CPCallee`, which is `CPWhile` with `(contexts := perCallee)`. `main` returns `8` as the entry of a run, and in its own summary, which `run` reads. `inc`, as the entry of a run, is analysed on any argument, so it returns any integer.

Until a summary serves a call, the solver takes the call as one that does not return, as tabulating solvers do. The call's result is `⊥`, and the rest of its block sends nothing, so no `⊤` from a call that is not served yet stays in the states. On `main() { var a : Int := id(5); var r : Int := 0; if (a < 3) { r := 1; } return a; }`, `a` keeps `5` past the branch, whose `then` block is `dead`, and `main` returns `5`.

A recursive function terminates too. On `down`, which counts down from `5`, the solver makes summaries keyed `5`, `4` and `3`, besides one keyed `⊤` for the call in `down`'s root context, which also serves `2` and below; every one returns `0`. A round visits callees before their callers, by the call graph that the code-pointer facts give. It joins the result of a summary whose callee is on no cycle of calls, and, once the solver widens, widens the result of one whose callee is on a cycle. So `count`, which adds one per call, returns `⊤` at every key. Narrowing goes on while a result changes, so a caller's result follows its callee's narrowed result.

Calls and cells meet at ref-to-reg. An analysis's states describe frames, not the heap, so a value read from a cell is `⊤`. Once ref-to-reg has promoted a local's cell to a value, its fact survives a call, since the callee's frame is not the caller's. A cell that the caller passes to the callee is not promoted, and its contents after the call are `⊤`.

A product analyses calls as any domain does: a summary's key and result are pairs of the factors' descriptions, which widen factor by factor, and the reducer runs in the callee's transfer functions as in the caller's. Under intervals and parities, a callee that counts by two up to nine returns `([10, 10], even)` from `0` and `([9, 9], odd)` from `1`, where intervals alone give `[9, 10]` from each. Its caller, which adds the two results, returns `([19, 19], odd)`.

*Soundness per context.* For facts that the checker accepts, each context has a theorem of its own, `Analysis.ctx_sound`: from a frame at a point of a body that a context analyses, in a store that the state there admits, every point of every run of that frame is admitted, and a value that the body returns is described by the context's result. A machine state is admitted by the state at its point in a context that analyses its frame's body: a root context for a function, the region's own for a region, and, for a callee, a context that analyses the callee's body: one of its summaries or its root context. `N.sound` is the case of a run from a start of function `i`, in `root i`, so the run's result is described by `i`'s own result. `Analysis.summary_sound` is the case of the run of a callee on arguments that a summary's key admits. {ref "app-absint-sound"}[The soundness theorem in full] states them.

*Known limitations.* These change what the analysis finds, not its soundness, and are expected to change:

* Regions do not depend on the context. A region that a summary's callee runs is analysed in the region's own context, and every run of the region, from any context, shares that context's states and result. So a region's answer is not confined to one summary, as a callee's result is.
* A reducer does not run at a call's result ({ref "absint-product-states"}[Products of state domains]).

## 12. Solvers and tables
%%%
number := false
tag := "absint-solve"
%%%

Solvers and tables are not in the package yet.

*Solvers.* The solver proposes facts and the checker decides. A solver, `N.Solver`, takes a linked module and returns a list of facts, in the order to try them. `N.analyzeWith solve m` returns the first that the checker accepts, or `none`. `N.soundWith` is `N.sound` for `analyzeWith solve`, for every `solve`, so a solver of your own needs no proof. `N.analyze m sch` is `analyzeWith` of the default solver, `N.defaultSolver sch`, which proposes the narrowed facts, if the schedule narrows, and then the ascended ones, with the summaries of the calls in both. A test gives constant propagation two solvers of its own:

```leantext "Solvers of one's own (under development, in StrataDynTest/Absint/ConstPropTest.lean)"
/-- Facts with no state at any block. -/
def noStates : CPWhile.Solver := fun _ => [{}]

/-- The facts with no state at any block, then the default solver's. -/
def thenDefault : CPWhile.Solver := fun m =>
  noStates m ++ CPWhile.defaultSolver CPWhile.schedule m
```

`noStates` proposes facts with no state at any block. The checker rejects them, since a function's entry block must have a state above the run's start, so `CPWhile.analyzeWith noStates` returns `none`. `thenDefault` proposes the same facts and then the default solver's, so `CPWhile.analyzeWith thenDefault` finds what `CPWhile.analyze` finds.

*Tables.* `#dyn_absint` builds the analysis from a _table_, which gives each instruction its transfer function with the proof that the instruction's wrapper meets it, and which does not depend on how the analysis finds its facts. It declares:

* `N.transfers` and `N.transfers_sound`, the table of the domain's transfer functions and its soundness. For a domain of abstract types it is a _value table_ (`VTable`), whose transfer functions act on abstract values and whose obligations mention no state. For a relational domain or a product it is a table on `N.State` (`STable`).
* `N.instAbsTable`, an instance of `AbsTable S.model D N.State`: the table on `N.State`, with the defaults of the instructions that have no transfer function, and its soundness.

The analysis is `defaultAnalysis S.model D N.State`, which is defined for every `AbsTable` instance and runs by `D`'s schedule. The instance is found by the domain as well as the states, so two domains with the same states keep their own tables.

A value table lifts to the states of any state domain that describes single values as the domain's typed states do, as a `PayView` instance says. `VTable.lift` lifts the table and `VTable.lift_sound` its soundness. `STable.extend` adds entries, such as the defaults, and `STable.extend_sound` keeps the soundness. A `PayView` reads and writes a slot's value through `proj` and `bind` by default, and a state domain may give faster `read` and `write`. So a language can change how its states are represented and keep its transfer lemmas. A test lifts the interval table to a state type of its own, `WSt`:

```leantext "A value table lifted to other states (under development, in StrataDynTest/Absint/TableTest.lean)"
def WSt : Type := IvlTVWhile.State

/-- `WSt`'s states are typed states. -/
instance : StateDomain WSt := inferInstanceAs (StateDomain IvlTVWhile.State)

/-- `WSt` describes values by the typed domain's slot values. -/
instance : PayView WSt IvlTVWhile.Internal.Dom (WhileSem.model.interp Run) :=
  inferInstanceAs (PayView IvlTVWhile.State IvlTVWhile.Internal.Dom _)

/-- `IvlTVWhile`'s value table lifted to `WSt`, with its defaults. -/
def wTable : STable WhileSem.model WSt :=
  (IvlTVWhile.transfers.lift WSt).extend IvlTVWhile.Internal.defaults

/-- The lifted table is sound, from the value table's soundness and the defaults'. -/
theorem wTable_sound : wTable.Sound :=
  STable.extend_sound (VTable.lift_sound IvlTVWhile.transfers_sound)
    IvlTVWhile.Internal.defaults_sound

/-- The table of `IvlTV` on `WSt`. -/
instance : AbsTable WhileSem.model IvlTV WSt := ⟨wTable, wTable_sound⟩
```

No transfer lemma is proved again. `(defaultAnalysis WhileSem.model IvlTV WSt).analyze m` finds the facts that `IvlTVWhile.analyze m` finds, and rejects the modules that it rejects. `WSt` has the representation of the typed states. The same test also lifts the table to sparse states, which list the slots they know and leave every other slot `top`, with a `StateDomain` and a `PayView` of their own, and that analysis gives every block the entry state that `IvlTVWhile` gives it.

## 13. Using it in a front end
%%%
number := false
tag := "absint-front-end"
%%%

The framework is not in the package yet.

:::checklist
To make a language's modules analysable once this work lands:

* give the values an analysis should see Dyn types with Lean types that a domain can describe;
* write the instructions an analysis should see through as pure rules, or as rules with successors, not as rules that take capabilities;
* keep structured constructs as regions where an analysis benefits, and give their instructions transfer functions;
* run ref-to-reg before analysing, so that locals are values;
* call functions through function references that the caller stores on every path to the call, not through parameters or closures with captures;
* certify the table ({ref "wip-cert"}[Proofs about runs 1: Certificates for rules]), so that ref-to-reg's theorem and the frame theorem apply to the language's modules.

:::

# Abstract interpretation: limits and further reading
%%%
number := false
tag := "absint-limits"
file := "abstract-interpretation-limits"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
This chapter describes the limits of a framework that is not yet in the package. Some of them are expected to go before it lands. Section 2 also describes Pylate v3, which is not in the package either.
:::::

## 1. Limits
%%%
number := false
tag := "absint-limits-list"
%%%

The framework is under development and not yet in the package, and these are its limits today. It rejects the following, or says nothing about them. The box "What is expected to change" at the start of {ref "absint-dyn"}[Writing an analysis in Dyn] lists the parts that are expected to change, and the sections of that chapter note known limitations where they arise.

* A datatype with type parameters, such as `Base.Except`, has no abstract type: `#dyn_abs_sum` rejects it. Its constructors give `⊤`, and its case instruction takes every successor, with `⊤` for the payloads.
* A `base.callCode` call is analysed only when a code-pointer fact names its callee: the call's operand holds a code pointer with no captures, stored in the call's block or along every path to it, and not written since. A call through a parameter or a closure with captures, a partial application, and a rule's own call request are rejected. A summary depends only on its key, the facts of the callee's arguments, so calls from different sites on the same facts share one summary ({ref "absint-calls"}[Calls and contexts]).
* In a domain of abstract types, a transfer function of a rule that is not pure, such as one with successors or regions, takes its operands, its payloads, its result and its regions' answers at one abstract type, and its instruction has no type parameters ({ref "absint-successors"}[An instruction with successors], {ref "absint-regions"}[Instructions with regions]). So, in the default lowering, `if (i < 10)` tells such a domain nothing about `i` in either branch: `base.branch` tests a `Bool` and passes no `Int`. With `lower (cmpBranches := true)`, a comparison lowers to the terminator `while.branchLt`, which passes the compared values along each successor, so its transfer function can filter them ({ref "cs13-filters"}[Filtering on conditions]). Only a variable that is a whole operand is filtered, and `==` and `!=` are not. While's `if` and `while` statements lower to branches and jumps, so only `region if` and `region while` need transfer functions with regions.
* The analysis does not support a rule that takes the run token or capabilities, a rule without regions that loops through its `Again`, a variadic instruction, an instruction generic over a list of types, or an instruction with type parameters whose rule is not pure or has regions. Registration says so, coverage lists such an instruction as unsupported, and a module that uses one is rejected. A rule with regions may loop, but its `Again` may run from any state, so its transfer function must be sound from every state, as `loopAbs_sound` shows for constant propagation's `while.loop`.
* The analysis's spec allows a rule no cell request, so the lemma of a rule that makes one cannot hold. The machine's `refNew` and `refGet` give `⊤`, and the facts say nothing about the heap.
* `@[dyn_abs]` takes a Dyn type without parameters, whose Lean type does not take the run token. Two Dyn types with one Lean type share one abstract type in a domain.
* The value domains of this guide are non-relational: an abstract state holds one abstract value per value in scope, and records no relation between values, such as `x < y`. Relational domains, such as While's zones, write their transfer functions on states ({ref "absint-relational"}[Relational transfer functions]). A zone keeps a matrix over every slot of its function, not only over the values in scope at a block's entry, so its cost grows with the function.
* A reduced product reduces only what a transfer function returns: the slot that the instruction writes and the values that it passes. The state after a join or a widening is not reduced again ({ref "absint-product"}[Reduced products]).
* The default of `base.branch` reads the condition only in a domain of abstract types whose abstract type at `Bool` has a `BoolView`, and in a product, in each factor that is such a domain. Otherwise it takes both successors. A domain that can tell which successor a condition rules out registers its own transfer function, as the zones register `branchRT`, which assumes the guard that a comparison left on the condition.
* There is no disjunctive completion: an abstract state cannot be a set of states, one per path. Trace partitioning, or a set of states with its own widening, is future work.
* No pass rewrites a module under its facts.

## 2. Toward domains for Python values
%%%
number := false
tag := "absint-python"
%%%

The framework that this section discusses is not yet in the package, and neither is Pylate v3, which the section describes.

Python's environment declares its instructions but has no rules for them yet ({ref "env-what"}[What an environment is]), so Python has no table for `#dyn_absint` to build an analysis from. A domain for Python values would need those rules first. It would also need the framework to lift four limits of section 1. It would need facts about cells, named by their allocation sites; calls through the functions and closures that a value may denote; rules that loop; and abstract types for values whose Lean types take the run token.

The package holds Pylate v1, an abstract interpreter for a subset of Python, under `Pylate/`. It reads Python's syntax tree, not Dyn modules, and it does not use this framework. Its abstract value, `AbsVal` in `Pylate/Domains/Value.lean`, is a reduced product in one type, as `SP` is. Its parts are a set of runtime type tags, the literals that a value may equal with a completeness marker per tag, the heap objects that it may point to, and the functions and classes that it may denote. `reduce_gamma` (`Pylate/Domains/Gamma.lean`) states that its reduction keeps the concretization, as `reduce_means` does for `SP`.

### Pylate v3
%%%
number := false
tag := "absint-pylate-v3"
%%%

Pylate v3 is under development and not yet in the package. It replaces Pylate v1, and its `Pylate/README.md` maps its code. It analyses Python 3.12 programs of a subset in which every class keeps the shape and the method resolution order of its declaration. It rejects every other program, and a program that uses an operation it does not support gets no result. Like Pylate v1, it reads CPython's syntax tree, serialized through Strata's Python dialect. For each variable and heap location of an admitted program, it computes an abstract value that says:

* whether the value is bound, or unbound on some paths;
* which runtime types it may have, which literals it may equal, and, for an integer, an interval;
* which heap cells it may point to: a cell is named by its allocation site and its context, and the most recent objects of a cell are kept apart from the rest, so that a write to one of them replaces what it held;
* the elements of lists and tuples, and the keys of dicts;
* which functions and classes it may denote.

It also bounds the exceptions that each statement may raise.

Its domains form a library, POMAD, the Python Object Model Abstract Domain, which `Pylate/doc/pomad/design/10-pomad-domains.md` designs. Each domain is an instance of one interface whose fields are its laws against a concretization, and the laws are proved in Lean. For example, the integer domain is a reduced product of a set of literals, an interval and a sign. Two engines compose the domains' transfer functions: the default one runs on the syntax tree, and the other on a control-flow-graph IR of Pylate's own. Gates check the engines against CPython: they run each test case under both, and require the engine's result to contain each exception that CPython raises and each binding that CPython leaves. A theorem, `analyze_sound`, states that the syntax-tree engine's result describes every outcome of a concrete interpreter written in Lean, for programs of a scalar fragment only. A design for the next version, on the control-flow-graph IR, plans that theorem for the whole IR.

Pylate v3 does not use Dyn or the framework of these chapters. Its newest concrete semantics, a step machine, follows Dyn's execution DSL: a rule is a tree of requests that the machine answers ({ref "inside-rules-as-trees"}[Inside the execution DSL: Rules as trees]). It is Pylate's own code, and imports nothing from Dyn. The two analysers differ as follows:

* _Soundness._ In this framework, one theorem states that the facts that the checker accepts hold at every point of every run, under the language's rules. Pylate v3 proves its domains' laws, and checks against CPython the engines that compose them.
* _The heap._ Pylate v3 tracks cells and what they hold. This framework's facts say nothing about the heap.
* _Calls._ Pylate v3 analyses a callee's body again at each call, under the whole string of calls and to a bounded depth, and refuses recursive calls. This framework analyses a callee once per summary, and analyses recursive calls.
* _Languages._ Pylate v3 is for Python. This framework analyses any Dyn language whose rules a domain covers.

## 3. Further reading
%%%
number := false
tag := "absint-reading"
%%%

These works are background for the framework of these chapters, which is not yet in the package. From gentlest to deepest:

1. Møller and Schwartzbach, _Static Program Analysis_ (Aarhus lecture notes), chapters 4 to 6 and 12: lattices, dataflow analysis and widening on a small language, then soundness through abstraction and concretization.
1. Nipkow and Klein, _Concrete Semantics_, chapter 13: an abstract interpreter for a small imperative language in Isabelle, with concretization only, and its soundness theorem `AI c = Some C ⟹ CS c ≤ γ⇩c C`. It is the published model closest to this framework, and {ref "cs13"}[the next chapter] follows it on While.
1. Leroy, "Mechanizing abstract interpretation" (talk, 2024): the case for analysers in proof assistants that use concretization only, run on fuel and check their result.
1. Miné, "Tutorial on Static Inference of Numeric Invariants by Abstract Interpretation" (Foundations and Trends in Programming Languages, 2017): the theory stated with concretization first, numeric domains, and reduced products.
1. Rival and Yi, _Introduction to Static Analysis_ (MIT Press, 2020): a textbook on the design of analysers, from the abstract interpretation side.
1. Jourdan, Laporte, Blazy, Leroy and Pichardie, "A Formally-Verified C Static Analyzer" (POPL 2015): the Verasco analyser in Coq, whose domains follow the same pattern at scale.
1. Monat, Ouadjaout and Miné, "Static Type Analysis by Abstract Interpretation of Python Programs" (ECOOP 2020): abstract domains for Python's objects, attributes and method resolution order.
1. Cousot and Cousot, "Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints" (POPL 1977), and Nielson, Nielson and Hankin, _Principles of Program Analysis_, chapter 4: the theory with abstraction and Galois connections. Darais and Van Horn, "Constructive Galois Connections" (ICFP 2016), mechanizes that layer.

# Following *Concrete Semantics*: abstract interpretation of While
%%%
number := false
tag := "cs13"
file := "concrete-semantics"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
The analyses of this chapter, the comparison branches of While's lowering and the terminator `while.branchLt` are under development and not yet in the package. The chapter's listings are static.
:::::

:::::callout "Who this chapter is for"
This chapter is for a reader of Nipkow and Klein's *Concrete Semantics* who wants to see its chapter 13, "Abstract Interpretation", carried over to Dyn. Its sections match the book's sections one by one, and it is best read beside the book and the files it names. It assumes {ref "absint"}[Abstract interpretation: the idea] and {ref "absint-dyn"}[Writing an analysis in Dyn].
:::::

:::::callout "Where the code is"
None of this code is in the package yet. The parity domain is in `StrataDyn/Examples/While/Parity.lean`, the interval domain in `StrataDyn/Examples/While/Interval.lean`, and the sets of truth values that both use for booleans in `StrataDyn/Examples/While/TruthValues.lean`. `StrataDyn/Examples/While/Domains.lean` declares them, with constant propagation, as the domains `ParD`, `IvlTV` and `CPD`, and builds the analyses `ParWhile`, `IvlTVWhile` and `CPWhile`. The tests are in `StrataDynTest/Absint/CS13Test.lean`, which runs the book's examples, and a few new ones, in While, and pins what each analysis finds for them.
:::::

:::::callout "About the sources"
This chapter is written independently of the book, and quotes none of its prose. It follows the order of the book's developments, and cites the section at each point. The book's Isabelle theories are HOL-IMP, in the Isabelle distribution. `Parity.lean`, `Interval.lean` and `CS13Test.lean` follow them. Most programs of `CS13Test.lean` re-express in While the book's examples and those of the theories `Abs_Int_Tests` and `Abs_Int1_parity`, and the others are new. This chapter describes these three files in prose, and shows none of their code, since they keep the BSD license notice of HOL-IMP, which they follow.
:::::

## 1. From IMP to While
%%%
number := false
tag := "cs13-imp"
%%%

While is in the package, but the analyses that this chapter runs on it are under development and not yet in the package.

*Concrete Semantics* works on IMP, the language of its chapter 7. The programs of its chapter 13 are IMP commands. Here is each IMP construct in While:

::::nowrap
:::table +header
*
  * IMP
  * While
*
  * `N n`
  * the integer literal `n`
*
  * `V x`
  * the variable `x`
*
  * `Plus a₁ a₂`
  * `a₁ + a₂`
*
  * `Bc True`, `Bc False`
  * `true`, `false`
*
  * `Not b`
  * `!b`
*
  * `And b₁ b₂`
  * `b₁ && b₂`
*
  * `Less a₁ a₂`
  * `a₁ < a₂`
*
  * `SKIP`
  * `{ }`
*
  * `x ::= a`
  * `x := a;`, or `var x : Int := a;` where `x` is first assigned
*
  * `c₁;; c₂`
  * `c₁ c₂`
*
  * `IF b THEN c₁ ELSE c₂`
  * `if (b) { c₁ } else { c₂ }`
*
  * `WHILE b DO c`
  * `while (b) { c }`
:::
::::

IMP has no declarations, and its runs may start in any state. A While function declares its variables, so an IMP variable that a program reads before assigning it becomes a parameter of the function. A run may start a function on any arguments, which plays the part of IMP's arbitrary start state.

While has every IMP construct, and more: `-`, `*`, `/`, `<=`, `==`, `||`, cells, calls and exceptions. The analyses of this chapter give some of these no transfer function, and section 11 shows what happens then. They follow calls through summaries of the callees ({ref "absint-calls"}[Calls and contexts]), which IMP, with no procedures, does not need.

`StrataDynTest/Absint/CS13Test.lean` holds the book's examples as While functions, and this chapter describes them in words.

## 2. The running example
%%%
number := false
tag := "cs13-example"
%%%

The analyses of this section are under development and not yet in the package.

Following *Concrete Semantics* §13.1. The book's first example is a loop that adds `2` to `x`, from `0`, while `x` is below `3`. In `CS13Test.lean`, it is a While function with no parameters that returns `x`.

The interval analysis of sections 9 and 10 finds the book's annotations for it: `[0, 4]` at the loop's head, `[0, 2]` before its body, and `[3, 4]` after it, which is also the function's result. `IvlTVWhile.annotate` prints such facts block by block ({ref "absint-result"}[Reading the result]). Section 3 shows which blocks stand for the book's program points, section 4 says what the facts mean, and section 9 gives the interval domain.

The book computes its annotations in steps, and shows each step in a table. Dyn's solver computes its facts in rounds (section 6), and does not print the rounds. In the book, each step computes every annotation from the previous step's. Dyn's solver goes through the blocks in reverse postorder, and each transfer function reads the facts as the round has updated them so far.

## 3. Annotated commands and blocks
%%%
number := false
tag := "cs13-blocks"
%%%

The comparison branches of this section are under development and not yet in the package.

Following *Concrete Semantics* §13.2. An _annotated command_ is an IMP command with an annotation at each program point. The book's analyses compute the annotations.

Dyn has no annotated commands. The tests lower each program with the option `cmpBranches` of `lower`. With it, each branch of an `if`, and the body and the exit of a `while`, take the variables in scope as block parameters. The facts give each of these parameters an abstract value, so a block's parameters stand where the book has an annotation. The book's three annotations of a loop sit at its head, before its body and after it. In the lowered running example, they are the parameters of the blocks `head`, `body` and `exit`. An `if` has an annotation before each branch and one after the `if`, which are the parameters of the blocks `then`, `else` and `join`. An assignment's annotation is the abstract value of the value that the assignment defines, in the state after the instruction: the block's entry state, updated by the transfer functions of the instructions up to it.

The block `head` ends with `while.branchLt`, a terminator that compares two integers, and section 8 explains it. Each of its two edges goes through a block of its own, `yes` or `no`, which takes the two compared values and passes them on for the variables that they were read from. In the running example, the facts give `x` the interval `[0, 2]` where `x < 3` holds, and `[3, 4]` where it fails.

*Differences from the original.* An annotation of the book is a whole state: an abstract value for every variable. A Dyn fact is a whole state too, at a block's entry: an abstract value for each value in scope there. In SSA form, a variable is a different value in each block, so the state of the variables at a program point is spread over the values in scope there, which the parameters of a block collect. The book's analyses and the analyses of this chapter are _non-relational_: an abstract value describes one variable on its own, and records no relation between variables.

## 4. The collecting semantics and the points of runs
%%%
number := false
tag := "cs13-collecting"
%%%

The analysis's theorem in this section is under development and not yet in the package.

Following *Concrete Semantics* §13.3. The _collecting semantics_ annotates each program point with the set of states that a run can have there. The book defines it as the least fixpoint of a step function on annotated commands. The analyses approximate it.

Dyn's counterpart is the set of points of the module's runs. A point of a run is a state of the machine that is still running, or how the run ended, with its result. A run starts at the state that `start` builds, from a function `i`, arguments and a snapshot, and a run `r` of the module's step relation gives its point `r.cfg n` after each number of steps `n` ({ref "inside-runs"}[Inside the execution DSL: Runs]). `IvlTVWhile.Admits F i p` holds when the facts `F` describe the point `p` of a run that starts function `i`. The analysis's theorem, `IvlTVWhile.sound` ({ref "absint-theorem"}[What the analysis proves]), takes a module that links and is well formed, and facts `F` that `IvlTVWhile.analyze` returns for it under a schedule `sch` (section 6). It says that `F` describes every point of every run, from every start, after any number of steps. A point inside a call is described in a context that analyses the callee's body, one of its summaries or its root context ({ref "absint-calls"}[Calls and contexts]). A run that faults is admitted too: the facts promise nothing about faults. The book's theorem has the same shape: if the interpreter returns an annotated command, the collecting semantics is below the annotations' concretization.

*Differences from the original.* The book's least fixpoint needs a complete lattice of annotated commands and the Knaster-Tarski theorem. Dyn's theorem is about the runs of the machine's step relation, so it needs no lattice of sets of states and no fuel, and it relates the facts to the machine directly. A point of a Dyn run also has parts that the book's states do not have: the heap, the world and the result.

## 5. Abstract values
%%%
number := false
tag := "cs13-values"
%%%

The domains of this section are under development and not yet in the package.

Following *Concrete Semantics* §13.4. A domain of the book is a type of abstract values with an order, a join, a top element, and a monotone concretization `γ`. The book uses concretization only, with no abstraction function.

Dyn's `AbsDomain`, in `StrataDyn/Absint/Domain.lean`, is the same idea ({ref "absint-domain"}[Declaring a domain]). It extends `Lattice`, the order operations `top`, `le`, `join`, `widen` and `narrow`. `widen` and `narrow` serve section 10: `widen` is the join, and `narrow` keeps its first argument, unless a domain gives its own. When the solver widens, and whether it narrows, is not part of the domain: the schedule of section 6 says so.

*Differences from the original.* The book's order must be reflexive, transitive and antisymmetric, and its join an upper bound. `AbsDomain` has three laws only: a value is in its own abstract value (`γ_abs`), `top` describes every value (`γ_top`), and `le a b` implies that `b` describes every value that `a` describes (`γ_le`). Soundness rests on these three alone. The order's laws, that `le` is a preorder with `top` above every value and that `join` and `widen` are upper bounds, form a separate class, `Order`, which only the termination theorems need ({ref "absint-total"}[Termination]). Antisymmetry is not one of them. The book's abstract values describe integers only, as `Ivl`'s and `Par`'s do. A Dyn domain also describes While's booleans, with an abstract type of their own: the parity and interval domains of this chapter give `Bool` the sets of truth values `TV`.

## 6. The generic abstract interpreter
%%%
number := false
tag := "cs13-interpreter"
%%%

The generic interpreter of this section is under development and not yet in the package.

Following *Concrete Semantics* §13.5. The book defines one interpreter for every domain, in a locale. Its abstract step function moves every annotation of a command one step forward on abstract values. The interpreter iterates the step from the least annotations until it reaches a _pre-fixpoint_, annotations that a step does not increase. The book proves the interpreter correct once (§13.5.5). It then proves that the interpreter terminates for a monotone step function and a domain of finite height (§13.5.6 to §13.5.8).

Dyn's generic interpreter is `#dyn_absint`. Its parts line up with the book's:

:::table +header
*
  * *Concrete Semantics* §13.5
  * Dyn
*
  * the locale's parameters: `γ`, `num'`, `plus'`
  * an `AbsDomain` instance, and one transfer function per instruction, each registered with `@[dyn_transfer]` on its local soundness theorem
*
  * the abstract step function `step'`
  * a round of the solver, which visits every function, region and summary of a call, callees before their callers, and in each the blocks in reverse postorder, skipping a block whose entry state, and the results it reads, have not changed since its last visit
*
  * the interpreter `AI`, which iterates `step'` to a pre-fixpoint
  * `analyze`: the solver, then the checker
*
  * the pre-fixpoint test of the iteration
  * the checker, `check`: one pass over the module
*
  * the correctness theorem, from the pre-fixpoint
  * `sound`, from the checker alone
*
  * termination, from monotonicity and finite height
  * a cap on the solver's rounds, with `top` everywhere at the cap, so that the solver always returns; `total`, that `analyze` returns facts on every module that the analysis covers; and `settles`, from the stabilisation of widening, that beyond some cap the solver settles without reaching it
:::

The generic interpreter is instantiated with a domain declaration and one command ({ref "absint-command"}[Running `#dyn_absint`]). The interval domain is `IvlTV`, whose declaration {ref "absint-complete"}[A complete analysis] shows in full. The parity domain is declared the same way, with parities at `Int`:

```leantext "Parity as a declared domain (under development, in StrataDyn/Examples/While/Domains.lean)"
/-- Parities at `Int`, sets of truth values at `Bool`. -/
dyn_domain ParD
attribute [dyn_abs ParD Base.Int] Par
attribute [dyn_abs ParD Base.Bool] TV
attribute [dyn_transfer ParD While.add addPar] addPar_sound
attribute [dyn_transfer ParD While.sub subPar] subPar_sound
attribute [dyn_transfer ParD While.neg negPar] negPar_sound
attribute [dyn_transfer ParD Base.branch branchTV] branchTV_sound
attribute [dyn_transfer ParD Base.jump jumpPar] jumpPar_sound
attribute [dyn_transfer ParD While.branchLt branchLtPar] branchLtPar_sound
#dyn_absint ParWhile for WhileSem (domain := ParD) (total)
```

`analyze` returns the first of the solver's facts that the checker accepts, and `none` if it accepts none ({ref "absint-solve"}[Solvers and tables]). The checker accepts facts that are a post-fixpoint, in the sense of {ref "absint-fixpoint"}[Joins, fixpoints and widening], in which each function's entry block is above the state that a run starts it in, with `⊤` for its parameters, and each summary's entry block is above its key. The book calls the same condition a pre-fixpoint.

A _schedule_, an argument of `analyze`, says how the solver runs ({ref "absint-theorem"}[What the analysis proves]): it joins for the first `widenAfter` rounds and widens at its widening points after them, then narrows if `narrow` holds, and each phase runs at most `maxRounds` rounds. Its field `contexts` says how many summaries a callee may get ({ref "absint-calls"}[Calls and contexts]). `IvlTVWhile.analyze m` runs under the domain's own schedule, which `dyn_domain IvlTV (narrow := true)` sets, and `IvlTVWhile.analyze m sch` under `sch`. The theorem of section 4 quantifies over `sch`, so it covers the facts found under every schedule. A schedule changes which facts the solver finds, and how many rounds it takes.

*Differences from the original.* The book proves its iteration correct. Dyn proves the checker correct, so the solver needs no proof: the theorem covers whichever facts the checker accepts. Notice what this means for termination. The book needs monotonicity and a finite height to show that its interpreter returns. Dyn's solver stops at the schedule's cap, `maxRounds`, and if its widening rounds have not settled by then, it gives `top` at every block. `analyze` is a total Lean function, so it always returns. Dyn's theorems do not use monotonicity.

## 7. Parity and constant propagation
%%%
number := false
tag := "cs13-parity-const"
%%%

The analyses of this section are under development and not yet in the package.

Following *Concrete Semantics* §13.6. The book makes its abstract states executable, as finite maps from variables to abstract values, and instantiates the interpreter with parity (§13.6.1) and with constant propagation (§13.6.2). Dyn's facts are executable already: they are Lean values that `analyze` computes, an array of entry states per body, function or region ({ref "absint-result"}[Reading the result]).

### Parity
%%%
number := false
tag := "cs13-parity"
%%%

The parity domain is under development and not yet in the package.

Following *Concrete Semantics* §13.6.1. The parity domain is `Par`, in `Parity.lean`, with its concretization `Par.means`: `even` describes the integers whose remainder by `2` is `0`, `odd` those whose remainder is `1`, `top` every integer, and `bot` none. An integer is `even`, `odd`, or either, `top`. Dyn's domain adds `bot` for a value that no run has reached. The book has no such value, and marks unreached points at the level of states.

The transfer function of `+`, `addPar`, is the book's table of the parity of a sum. `subPar` is the same table, since `a - b` has the parity of `a + b`. `addPar_of` proves the obligation once for every operation whose result has the parity of the sum, by `omega`. The transfer function of `while.branchLt`, `branchLtPar`, takes both successors and passes the compared parities on unchanged.

`CS13Test.lean` runs the book's two parity examples, two loops that add to an odd `x` while `x` is below `100`. When the loop adds `2`, `ParWhile` finds `x` `odd` at the head, in the body and at the exit. When it adds `3`, `x` is odd, then even, then odd again, so its abstract value at the head is `⊤`, and so are those in the body and at the exit. For domains of the same kind, see the book's Exercises 13.14 and 13.15, and the sign and parity product `SP` of {ref "absint-sp"}[A domain of signs and parities]. {ref "absint-product"}[Reduced products] pairs `Par` with intervals: on a loop that counts by two, the reduced product finds a result that neither domain finds alone.

### Constant propagation
%%%
number := false
tag := "cs13-const"
%%%

The constant propagation of this section is under development and not yet in the package.

Following *Concrete Semantics* §13.6.2. An abstract value of constant propagation is a constant, or `⊤` for any value. Dyn's `CP`, in `StrataDyn/Examples/While/ConstProp.lean`, is this domain, with `bot` ({ref "absint-domain"}[Declaring a domain]). `CPD` registers it at both `Int` and `Bool`, with a transfer function of `while.branchLt` among its others (section 8). `CS13Test.lean` runs the book's examples of constant propagation, and pins what `CPWhile` finds for them.

*Differences from the original.* The interpreter of the book's §13.5 does not look at conditions: both branches of an `IF` get the state before it, and a loop's exit gets the loop's invariant. Dyn's `CP` decides a comparison of two constants and a constant condition. With these decisions, `CP` rules out a branch whose condition compares two constants, and the exit of a loop whose condition is `true`: their entry states are `⊥`. In the book, the backward analysis of §13.7 is the first to rule out branches, and §13.8 instantiates it with intervals. Dyn's parity analysis does not filter on comparisons, as in the book.

## 8. Filtering on conditions
%%%
number := false
tag := "cs13-filters"
%%%

The terminator `while.branchLt`, the comparison branches of While's lowering and the filters of this section are under development and not yet in the package.

Following *Concrete Semantics* §13.7. A condition that holds bounds the variables that it reads: where `x < 3` holds, `x` is below `3`. A _filter_ takes abstract values and an outcome of a condition, and gives smaller abstract values that still describe every state in which the condition has that outcome. In the book, the filter of `Less a₁ a₂` asks the domain for smaller abstract values of both sides, and passes them back through an arithmetic expression to its variables (§13.7.1). The filter of `Not` swaps the outcome. The filter of `And` applies both filters for the outcome true, and joins them for the outcome false (§13.7.2).

In SSA form, a value does not change, so a filtered abstract value needs a new value to belong to. While has a terminator that compares two integers and passes both of them along each successor:

```leantext "A compare-and-branch terminator (under development, in StrataDyn/Examples/While/Env.lean)"
  /-- Continue at `^yes` if `lhs < rhs` and at `^no` otherwise, passing both operands. -/
  terminal insn branchLt (lhs rhs : Int) (^yes ^no (lhs rhs : Int))
```

```leantext "Its rule (under development, in StrataDyn/Examples/While/Env.lean)"
@[dyn_sem While.branchLt]
def branchLt (a b : Int) (yes no : Target E [Int, Int]) : Sem ε E Empty :=
  if a < b then jump yes (a, b) else jump no (a, b)
```

The block that a successor enters binds the passed values as new parameters. With `cmpBranches`, `lower` lowers a condition to these terminators. It evaluates the operands of the condition's comparisons first, in source order, and then branches:

* `a < b` is `branchLt a b`, `a > b` is `branchLt b a`, `a <= b` is `!(b < a)`, and `a >= b` is `!(a < b)`;
* `!c` swaps the successors of `c`;
* `c₁ && c₂` branches on `c₁`, and, where `c₁` holds, on `c₂` from an intermediate block; `c₁ || c₂` is the same with the outcomes swapped;
* along each edge of a comparison, a variable that an operand reads is _rebound_ to the passed value, so the blocks after the edge read the passed value as that variable.

The work under development adds checks of this lowering to `StrataDynTest/Examples/While/RunTest.lean`. They run every example of `StrataDynTest/Examples/While/Programs.lean` with and without `cmpBranches`, and each example ends alike, with the same world and the same choices. Two more functions end alike, with the same world, on several arguments: one whose conditions use `!`, `&&`, `||` and every comparison, and one whose condition's operands tick and may raise.

A transfer function of `branchLt` returns, for each successor, the abstract values of the passed values. So it filters by giving them smaller abstract values. Constant propagation's transfer function does not filter, but it shows the form:

```leantext "Constant propagation's transfer function of branchLt (under development, in StrataDyn/Examples/While/ConstProp.lean)"
/-- `while.branchLt a b ^yes ^no`: only the successor that two constants pick, and either
otherwise, passing the operands' abstract values. -/
def branchLtAbs (a b : CP) : AbsOut CP :=
  match a, b with
  | .bot, _ | _, .bot => { succs := #[] }
  | .const (.int m), .const (.int n) =>
    if m < n then { succs := #[some #[a, b], none] } else { succs := #[none, some #[a, b]] }
  | _, _ => { succs := #[some #[a, b], some #[a, b]] }
```

The entries of `succs` are the successors, `^yes` and then `^no`. `none` rules a successor out, and `some` gives the abstract values of the two values that it passes. `branchLtAbs` passes its operands' abstract values unchanged, and rules out the successor that two constants exclude.

The interval domain's transfer function of `branchLt` is `branchLtIvl`, in `Interval.lean`. It follows the book's filter of `Less` on two variables. Where `a < b` holds, its filter `ltFilter` bounds `a` above by `b`'s upper bound minus one, and `b` below by `a`'s lower bound plus one. Where `a < b` fails, `geFilter` bounds `a` below by `b`'s lower bound, and `b` above by `a`'s upper bound. If either filtered abstract value is `⊥`, the transfer function rules the successor out. `#dyn_transfer_obligation IvlTV While.branchLt branchLtIvl` prints the obligation, and `branchLtIvl_sound` proves it from `ltFilter_sound` and `geFilter_sound`.

`CS13Test.lean` runs the book's examples of filtering under the interval analysis of section 9, and a conjunction and a disjunction. Where `x` is compared with a variable that holds `7`, `x` is `[-∞, 6]` in the first branch and `[7, +∞]` in the second. Like constant propagation, the filters rule out a branch that two constants exclude. Where a conjunction holds, both comparisons filter `x`, one after the other, as the book's filter of `And` does. Where it fails, the second branch has two predecessors, one per failing comparison, and its parameter's abstract value is the join of what each passes. So a conjunction that bounds `x` between `1` and `9` gives `[1, 9]` in the first branch, but the second branch joins `[-∞, 0]` and `[10, +∞]`, which gives `[-∞, +∞]`. A disjunction is the same with the outcomes swapped, so its second branch gets the bounds: where `x` is neither below `0` nor above `10`, it is `[0, 10]`.

*Differences from the original.* The book filters the whole state by the whole condition, inside the analysis. Dyn filters on the edges of the control flow, so the lowering does part of the work: `!`, `&&` and `||` become branches, and joins happen where edges meet. Two parts of the book's filter are left out. First, a comparison filters a variable only when the variable is a whole operand: in `x + 1 < y`, `y` is filtered and `x` is not, because the book's backward step through `Plus` (§13.7.1) has no counterpart here. Second, `==` and `!=` stay boolean values that `base.branch` tests.

## 9. Interval analysis
%%%
number := false
tag := "cs13-intervals"
%%%

The interval analysis is under development and not yet in the package.

Following *Concrete Semantics* §13.8. The interval domain is `Ivl`, in `Interval.lean`, the domain on which {ref "absint-dyn"}[Writing an analysis in Dyn] builds its analysis. An abstract value of the book's domain is an interval of integers, whose bounds may be infinite. An `Ivl` interval has optional bounds, and a missing bound is infinite. Dyn's `Ivl` adds `bot`, and the domain `IvlTV` describes booleans by sets of truth values, `TV`. The order is inclusion, and the join of two intervals runs from the lower of their lower bounds to the higher of their upper bounds. The transfer functions of `+`, `-` and unary `-` add and negate bounds, those of `<` and `<=` compare intervals into sets of truth values, and that of `branchLt` filters as in section 8. `*` and `/` have no transfer function, and section 11 shows what that means.

The book first runs this analysis with no widening, and shows that it may not terminate. In Dyn, that is a schedule whose `widenAfter` equals its `maxRounds`, so the solver joins until its cap. `CS13Test.lean` runs the book's examples under such schedules:

* On a loop that adds `1` to `x` while `x` is below `100`, from an unknown `x`, joins settle within `100` rounds. In the body, `x` is `[-∞, 99]`, and at the exit `[100, +∞]`.
* On the same loop from `0`, `x`'s interval at the head grows by one each round, so the rounds settle in round `102`. With a cap of `101` rounds, the solver reaches the cap and gives every value `⊤`. With a cap of `102`, it finds `[0, 100]` at the head, `[0, 99]` in the body, and `[100, 100]` at the exit. `IvlTVWhile.ascended` tells the two cases apart: it is `none` when the solver reaches the cap.
* Two more loops do not settle within `300` rounds: one with a second counter that the condition does not bound, and one that never exits. Every abstract value is `⊤`.

*Differences from the original.* In the book, an iteration that does not stop gives no result, and running the interpreter does not return. In Dyn, the solver stops at its cap and falls back to `⊤`, and the theorem covers that result too. So in Dyn, a missing widening costs precision and rounds, and `analyze` still returns.

## 10. Widening and narrowing
%%%
number := false
tag := "cs13-widening"
%%%

The solver's widening and narrowing are under development and not yet in the package.

Following *Concrete Semantics* §13.9. A _widening_ `a ∇ b` is an upper bound of `a` and `b` that jumps ahead, to make an increasing iteration stop ({ref "absint-fixpoint"}[Joins, fixpoints and widening]). A _narrowing_ `a △ b`, for `b` below `a`, gives a value between them. After a widening iteration stops, iterating a narrowing recovers some of the precision that widening gave up.

`Ivl.widen` sends a bound that grows to infinity, and `Ivl.narrow` replaces an infinite bound by the bound of the recomputed value ({ref "absint-ivl-widen"}[Widening and narrowing]). `CS13Test.lean` checks the book's three examples of widening: `[0, 1] ∇ [0, 2]` is `[0, +∞]`, `[0, 2] ∇ [0, 1]` is `[0, 2]`, and `[1, 2] ∇ [0, 5]` is `[-∞, +∞]`.

From round `widenAfter` on, the solver widens at its _widening points_, and joins everywhere else. The widening points are the targets of retreating edges, which in a lowered While function are the heads of loops, and the entry blocks of regions. Once its rounds settle, if the schedule's `narrow` holds, it runs _narrowing rounds_. A narrowing round recomputes the blocks' entry states, and the results, from the current states, and narrows each state by its recomputed one when that shrinks it:

```leantext "The narrowing of one state (under development, in StrataDyn/Absint/Core/Solve.lean)"
/-- A state narrowed by its recomputed one, if that is below it and narrowing shrinks it; and
whether it shrank. -/
def narrowOne (old new : T.S) : T.S × Bool :=
  if StateDomain.le new old && !StateDomain.le old (StateDomain.narrow old new) then
    (StateDomain.narrow old new, true)
  else (old, false)
```

The rounds stop when no state shrinks and no result changes, or at the cap. `analyze` then checks the narrowed facts, and if the checker rejects them, it checks the facts from before narrowing ({ref "absint-solve"}[Solvers and tables]). The book widens from its first step, which in Dyn is a schedule with `widenAfter := 0`. `CS13Test.lean` runs three loops under it, with and without narrowing:

* On the loop that counts `x` from `0` to `100`, widening alone gives `[0, +∞]` at the head, `[0, 99]` in the body, and `[100, +∞]` at the exit. Narrowing then gives `[0, 100]`, `[0, 99]` and `[100, 100]`.
* On the running example, widening alone gives `[0, +∞]` at the head, `[0, 2]` in the body, and `[3, +∞]` at the exit. Narrowing then gives the book's `[0, 4]`, `[0, 2]` and `[3, 4]`.
* On a loop that adds `1` to `x` from `0` while `x` is above `-1`, widening gives `[0, +∞]` at the head and in the body. The exit's entry state is `⊥`, and so is the result, with or without narrowing.

Notice the first example. Widening alone gives the book's result after widening at the head and at the exit, and narrowing gives the book's result after narrowing. In the body, widening alone gives `[0, 99]`, where the book has `[0, +∞]`. The book widens every annotation, and the annotation before the body is one of them. Dyn's solver widens only at the head, and the body's entry state is the head's state filtered by `x < 100`, so it keeps the bound `99`. The running example's body keeps the bound `2` in the same way. In the third example, the exit's filter needs `x` to be at most `-1`, and `x` is at least `0`, so the exit's entry state is `⊥`. By `IvlTVWhile.sound` and `Analysis.entry_not_bot`, no run enters it.

`IvlTV`'s own schedule, from `dyn_domain IvlTV (narrow := true)`, widens from round `3` and narrows. With it, the book's loop in which `y` trails `x` by one ends with `x` at `[100, 100]` and `y` at `[0, 99]`. After every iteration, `y` is `x - 1`, but the facts bound `x` and `y` separately: intervals record no relation between variables.

### Termination
%%%
number := false
tag := "cs13-termination"
%%%

The termination results of this section are under development and not yet in the package.

Following *Concrete Semantics* §13.9.4 and §13.9.5. The book proves that its widening and narrowing iterations terminate by a measure on abstract values. For intervals, the measure counts the finite bounds. `Ivl.rank`, in `Interval.lean`, is such a measure for `Ivl`: one more than the number of finite bounds of an interval, `0` for `top`, and `4` for `bot`. Three theorems there describe it:

* `Ivl.rank_le`: the rank is at most `4`;
* `Ivl.rank_widen`: widening `a` by a value `b` that is not below `a` lowers the rank;
* `Ivl.rank_narrow`: narrowing `a` by a value below it raises the rank, unless `a` is below the result.

From them, `Interval.lean` builds the instances `AscendingWF Ivl`, that repeated widening stabilises, and `DescendingWF Ivl`, that repeated narrowing stabilises ({ref "absint-total"}[Termination]).

*Differences from the original.* The book combines these measures over all annotations, and proves that its widening and narrowing iterations terminate for every program. Dyn's solver returns on every module because its rounds stop at the schedule's cap. The measure says more for widening: from `AscendingWF Ivl` and the order's laws, the framework's theorem `solve_settles` proves that the widening rounds settle on every module before a large enough cap, as the book's theorem does for every program. `#dyn_absint IvlTVWhile … (settles)` states this for the interval domain, as `IvlTVWhile.settles`, so with a large enough cap the `⊤` fallback is not taken. No theorem of the solver uses `DescendingWF` yet: the narrowing rounds stop when no state shrinks, or at the cap.

The book widens every annotation once per step, against the whole step's result. Dyn's solver widens only at its widening points: the targets of the edges that go back in a reverse postorder of the blocks, the loop heads that the dominator tree finds, and the entry blocks of regions. There it widens a state by each state that flows into it, one at a time, so a head with two predecessors may widen twice in one round. The book also widens from its first step, and `IvlTV`'s own schedule widens from round `3`. Last, the book's narrowing iteration keeps a pre-fixpoint because its step function is monotone. Dyn's narrowing relies on the checker instead: if the checker rejects the narrowed facts, `analyze` returns the facts from before narrowing.

## 11. Rejection
%%%
number := false
tag := "cs13-rejection"
%%%

The analyses and the checker of this section are under development and not yet in the package.

This section has no counterpart in the book, where every IMP construct has an abstract meaning in every domain. A Dyn module may use an instruction that has no transfer function in the domain. A pure rule with no transfer function gets `⊤`. `base.jump`, `base.unreachable` and `base.branch` have default transfer functions ({ref "absint-successors"}[An instruction with successors]). Any other rule that is not pure and has no transfer function makes the checker reject the module, and `analyze` returns `none`. `CS13Test.lean` shows each case beside an accepted twin:

* A function that divides `x` by `2` where `x` is positive is rejected by `IvlTVWhile`: the rule of `/` is not pure, and `IvlTV` gives it no transfer function. The same function with `*` is accepted: in that branch `x` is `[1, +∞]`, and the product is `⊤`.
* The first parity example, lowered with `cmpBranches`, is rejected by `SPWhile`: `SPD` has no transfer function of `while.branchLt`. Lowered without `cmpBranches`, it is accepted, and `x` is positive and odd at the loop's head.

## 12. Each section's status
%%%
number := false
tag := "cs13-status"
%%%

Every Dyn counterpart in this table is under development and not yet in the package.

::::nowrap
:::table +header
*
  * *Concrete Semantics*
  * Dyn
  * Status
*
  * §13.1, §13.2: annotated commands
  * blocks with the variables in scope as parameters, lowered with `cmpBranches`; an abstract value per value
  * adapted
*
  * §13.3: the collecting semantics
  * the runs of the step relation, `always` and `Admits`
  * adapted: the points of the machine's runs
*
  * §13.4: abstract values
  * `AbsDomain` and `Lattice`, with `widen` and `narrow`; whether to narrow is the schedule's
  * ported
*
  * §13.5: the generic interpreter and its correctness
  * `#dyn_absint`, the solver and the checker, and `sound`
  * adapted: correctness from the checker
*
  * §13.5.6 to §13.5.8: monotonicity and termination
  * a cap on the rounds, with `top` everywhere at it; `total`, and `settles` from the stabilisation of widening
  * replaced: the cap stops the solver, and `settles` proves that widening settles
*
  * §13.6.1: parity
  * `Par`
  * ported
*
  * §13.6.2: constant propagation
  * `CP`, with a transfer function of `branchLt`
  * reused; prunes on constant comparisons
*
  * §13.6.3, §13.6.4: representations of abstract states
  * `Facts`, an array of entry states per body
  * left out
*
  * §13.7: the analysis of boolean expressions
  * `while.branchLt`, comparison branches, and `Ivl`'s filters
  * adapted: on edges; no backward step through `+`
*
  * §13.8: intervals
  * `Ivl`
  * ported
*
  * §13.9.1 to §13.9.3: widening and narrowing
  * `Ivl.widen`, `Ivl.narrow`, and the solver's narrowing rounds
  * ported; widening at widening points only, by each incoming state
*
  * §13.9.4, §13.9.5: their termination
  * `Ivl.rank` and its theorems, and `AscendingWF Ivl` and `DescendingWF Ivl` from them
  * ported; `settles` uses widening's measure, and no theorem uses narrowing's yet
:::
::::

### Exercises
%%%
number := false
tag := "cs13-exercises"
%%%

These exercises build on work that is under development and not yet in the package.

The book's Exercises 13.14 to 13.21 go with its §13.6 to §13.9. Five more, for Dyn:

1. Give `Ivl` a transfer function of `while.mul`, and prove it. The product's bounds are the least and the greatest of the four products of bounds, with care for the infinite ones.
1. Give `SP` a transfer function of `while.branchLt` that filters signs: where `x < 0` holds, `x` is negative.
1. Extend the lowering to filter `x` in a comparison `x + c < y`, for a constant `c`, and give `Ivl` the transfer function that the extension needs.
1. State and prove a bound on the solver's rounds for `Ivl` from `rank_widen`, as a function of the number of values of a module.
1. Find a program for which `IvlTVWhile`, widening from the first round, gives an abstract value `[0, +∞]` that narrowing does not improve, and explain why.

## References
%%%
number := false
tag := "cs13-references"
%%%

The Dyn work that this chapter maps the book onto is under development and not yet in the package.

* Tobias Nipkow and Gerwin Klein. *Concrete Semantics with Isabelle/HOL*. Springer, 2014. DOI 10.1007/978-3-319-10542-0. Free PDF at http://www.concrete-semantics.org/concrete-semantics.pdf. Chapter 13, "Abstract Interpretation".
* Tobias Nipkow. The Isabelle theories `ACom`, `Collecting`, `Abs_Int0`, `Abs_Int1`, `Abs_Int1_parity`, `Abs_Int1_const`, `Abs_State`, `Abs_Int2`, `Abs_Int2_ivl`, `Abs_Int3` and `Abs_Int_Tests`, in the session HOL-IMP of the Isabelle distribution, `src/HOL/IMP/`. BSD 3-Clause license. https://isabelle.in.tum.de/repos/isabelle/file/tip/src/HOL/IMP

# Missing features
%%%
number := false
tag := "missing"
file := "missing-features"
%%%

Dyn lacks the features below, ranked by what each blocks. The first three block a second source language. Without them, a typed object-oriented language such as Java or TypeScript, or a front end written outside Lean, has no faithful encoding or no way in. The next three block verification. The rest would make any front end simpler to write. Each entry gives a motivation, evidence and a sketch. The sketch of a feature that has a design opens with "Planned". Other sections refer to them by name.

::::missingFeatures
1. *Checked runtime extension of environments.*

   : Motivation

     JVM classes and TypeScript interfaces are per-program types.

   : Evidence

     `StrataDyn/Env.lean`: `addType`, `addTypes`, `addData`, `addInsn` and `addInsns` are public, and take proofs of their obligations. Of the forms that decide the obligations, `addType?` and `addInsns?` are public, but `add?`, `ofArray?` and `addData?` are internal. A rule is registered for a declaration of an `environment` command (`StrataDyn/Exec/Rules.lean`), so a declaration added while a program is translated has none.

   : Sketch

     Planned: a program's types are declared in a child environment of its language's environment, made for the program when it is translated. Like a child declared with `extends` ({ref "env-layer"}[Environment 6: Layering]), it has every declaration of its parent, with the same shape. It needs a public `Env.addData?` (and `ofArray?`), with lemmas that recover `InsnRef`s from the result.

1. *Text interchange for front ends written outside Lean.*

   : Motivation

     Nothing ties a printed module to its environment, so a JavaScript or Go front end that emits printed Dyn cannot say which environment its text is over.

   : Evidence

     `StrataDyn/DDMRead.lean`: the reader takes the environment as an argument.

   : Sketch

     An environment header (its name and a hash of its declarations) in printed modules; optionally a printed form of environment signatures.

1. *DDM ergonomics for new front ends.*

   : Motivation

     Parts of the DDM half are not mechanical: a front end writes them by hand or finds them by trial.

   : Evidence

     No specification of the Ion program format, and only a Python writer (StrataDDM's `Python/strata/strata/base.py`); `partial` `ofAst` (StrataDDM `Integration/Lean/Gen.lean`); `autoImplicit` around `#strata_gen`; the boilerplate of an embedding command such as `#while`; name clashes found by trial.

   : Sketch

     A written Ion encoding specification with reference writers; `#strata_embed D "#tag" "#end"`; a total `ofAst`; an explicit annotation binder; a dialect lint for keyword and category clashes.

1. *Rules for Python's environment.*

   : Motivation

     A translated Python program does not run, and no proof can say what it does, until its instructions have a meaning.

   : Evidence

     `StrataPython/Dyn/Env.lean` declares Python's instructions, but no `@[dyn_sem]` rule exists for any of them, and Python has no semantic table.

   : Sketch

     Planned: a rule for every instruction of Python's environment, written with the execution DSL, so that a translated program behaves as CPython 3.12 runs it, or stops with a gap that names the case left out; and runs that compare translated programs with CPython.

1. *Assertions and assumptions in bodies.*

   : Motivation

     Verification needs assertions and assumptions inside a function's body, beside the function contracts that Dyn already has.

   : Evidence

     Functions carry contracts: `requires` and `ensures` clauses, frames, extern functions and ghost state (`StrataDyn/IR.lean`, `docs/Dyn.md`, §1). But no instruction asserts or assumes a condition in a body. Rules have `assume`, which ends an infeasible path with `Fault.blocked`, the engine has no fault for a failed assertion, and a run ignores contracts.

   : Sketch

     Assertions, assumptions and nondeterministic values as instructions with rules, and one new fault for a failed assertion.

1. *Translation of values and operations to Strata.Core.*

   : Motivation

     Strata's verifier works on Strata.Core, and nothing carries a Dyn module's code there.

   : Evidence

     `StrataDyn/Core/Types.lean` translates Dyn's types and type declarations to Strata.Core, with proofs (`docs/Dyn.md`, §6), but no values or operations.

   : Sketch

     Planned: a translation of modules over a fixed environment into Strata.Core, with each instruction mapped to its Strata.Core counterpart and anything else rejected, never approximated. It needs to know which environment a module is over, as _Text interchange_ does.

1. *A well-formedness explainer.*

   : Motivation

     A type or arity mistake gives only "f is not well formed". Only scoping failures are explained.

   : Evidence

     `StrataDyn/Build.lean`: a `FailedFunc` with no misuses carries no explanation. Python's translator adds the scoping explanations, `Func.scopeDiagnostics`, when they apply, and otherwise reports only the function's name (`builtFunc`, `StrataPython/Dyn/Translate.lean`). The reader already has located messages (`StrataDyn/DDMRead.lean`).

   : Sketch

     Diagnostics for every obligation, in the style of the scoping explanations, naming the block, the instruction, and the expected and actual type or count, with the instruction's annotation.

1. *A generic runner, value printer and differential harness.*

   : Motivation

     Every front end rewrites result decoding, and there is no command-line way to run a file.

   : Evidence

     `Model.arg` and `Outcome.read?` give arguments and results at Lean types, but each of the execution engine's test suites writes its own value printer, as While's `showResult` is; there is no run executable in the lakefile.

   : Sketch

     `#dyn_sem_table` derives a printer and an equality for results; a `dyn run FILE.dyn --env E --entry f --args …` executable prints the result and a designated part of the world; a template harness compares against an external reference with expected-failure lists, and its goldens exclude step counts by default.

1. *A shared lowering library.*

   : Motivation

     Handler stacks, call-plus-`Except.case`, SSA variable threading, and `isOpen` and `targeted` tracking are reimplemented in every front end.

   : Evidence

     While's lowering; Python's `StrataPython/Dyn/Build.lean` and `StrataPython/Dyn/Translate.lean`.

   : Sketch

     `Build.isOpen`, `Build.currentLabel?` and `Build.isTargeted`; a language-neutral `HandlerFrame`; `emitCallRaising` (`callCode` plus `Except.case` to the handler); `openWithVars`/`jumpWith` helpers; a `Build.regionWith` that closes its region when its body throws, as a body in `ExceptT` does on an error. Today such a body leaves the region open.

1. *Per-emission checking in the builder.*

   : Motivation

     The typed emitters, blocks and exits check operands, payloads, results and returns where a call is written, but the escapes and the untyped builder are checked only when the function is finished.

   : Evidence

     `StrataDyn/Typed.lean` and `StrataDyn/Build/Typed.lean`: `Val.ofId`, `Val.cast` and `Build.withExit` are unchecked, and the untyped layer, `Build.Raw`, takes bare labels and value ids; `Build.emitApply` checks that a block is open and, when its type arguments are left out, infers them from the operands' and the result's types, recording a misuse if none fit; deciding `Func.WF` in `Build.run` is the first check of everything else. `Emit.startBlock` names all of a block's parameters after one stem, so the `mean` listing opens its blocks whose parameters have names of their own with `Build.Raw.startBlock`.

   : Sketch

     `startBlock` takes a stem per parameter, and `BuildM` becomes opaque.

1. *Source locations in faults and events.*

   : Motivation

     A failing run cannot be traced to a source line.

   : Evidence

     The execution engine's events carry a position, a body, a block and an index, but no annotation; faults carry neither, and linked blocks drop the annotation. While's lowering annotates with `Unit`.

   : Sketch

     Keep each instruction's annotation in linked code and report it in `Event` and `Fault`; give While's lowering source-range annotations and positioned diagnostics.

1. *Rule-writing affordances.*

   : Motivation

     A rule over a list-kinded type variable may use it only as the spread and spliced into a closure operand's arguments. No rule can then cover an instruction whose list parameter occurs in its result, a region, a payload or inside a datatype operand.

   : Evidence

     `StrataDyn/Exec/Rules.lean` rejects such a rule, and `StrataDynTest/Exec/RuleErrorTest.lean` pins each rejection.

   : Sketch

     Rules over argument packs in those positions; coverage that reports "no rule possible".

1. *Constructor names scoped under their datatype.*

   : Motivation

     Common constructor names collide within a namespace.

   : Evidence

     `StrataDyn/DSL/Check.lean`; Python's `completion…` prefixes.

   : Sketch

     An option to name constructors `T.c` in the environment, as `T.case` already is.
::::

# Appendices
%%%
number := false
tag := "appendix"
file := "appendices"
%%%

## A. File map
%%%
number := false
tag := "app-files"
%%%

Paths are relative to the package root.

:::table +header
*
  * Role
  * Paths
*
  * Environments: data and checking
  * `StrataDyn/Env.lean`, `StrataDyn/Env/Data.lean`, `StrataDyn/Env/Refine.lean`, `StrataDyn/Env/WF.lean`
*
  * Environment DSL
  * `StrataDyn/DSL.lean`, `StrataDyn/DSL/Syntax.lean`, `StrataDyn/DSL/Check.lean`, `StrataDyn/DSL/Elab.lean`
*
  * Base environment
  * `StrataDyn/Base.lean`
*
  * IR
  * `StrataDyn/IR.lean`
*
  * Builder and type arguments
  * `StrataDyn/Build.lean`, `StrataDyn/KindedTypeArgs.lean`
*
  * Typed values and emitters
  * `StrataDyn/Typed.lean`, `StrataDyn/Build/Typed.lean`, `StrataDyn/DSL/Emit.lean`
*
  * Well-formedness, contracts included
  * `StrataDyn/WF.lean`, `StrataDyn/WFProps.lean`, `StrataDyn/ContractRegion.lean`, `StrataDyn/ContractRegionProps.lean`
*
  * Dyn's types in Strata.Core
  * `StrataDyn/Core/Types.lean`, `StrataDyn/Core/Denote.lean`, `StrataDyn/TypeDenote.lean`
*
  * Printer and reader
  * `StrataDyn/DDM.lean`, `StrataDyn/DDMRead.lean`
*
  * Execution: rules, types and the table
  * `StrataDyn/Exec.lean`, `StrataDyn/Exec/Sem.lean`, `StrataDyn/Exec/Rules.lean`, `StrataDyn/Exec/Types.lean`, `StrataDyn/Exec/Table.lean`, `StrataDyn/Exec/Base.lean`
*
  * Execution: linking, validation, the machine and the fused engine
  * `StrataDyn/Exec/Link.lean`, `StrataDyn/Exec/Check.lean`, `StrataDyn/Exec/Machine.lean`, `StrataDyn/Exec/Fused.lean`, `StrataDyn/Exec/Run.lean`
*
  * Runs, behaviours and trace refinement
  * `StrataDyn/Exec/Trace.lean`; for any step relation, `StrataDyn/Util/Trace.lean` and `StrataDyn/Util/Trace/Backward.lean`
*
  * Certificates, the frame theorem and heap safety
  * `StrataDyn/Exec/Spec.lean`, `StrataDyn/Exec/Cert.lean`, `StrataDyn/Exec/CertModel.lean`, `StrataDyn/Exec/CertTactic.lean`, `StrataDyn/Exec/CertLink.lean`, `StrataDyn/Exec/LinkInv.lean`, `StrataDyn/Exec/Frame.lean`, `StrataDyn/Exec/Call.lean`, `StrataDyn/Exec/Safety.lean`
*
  * Ref-to-reg
  * `StrataDyn/RefToReg.lean`, `StrataDyn/RefToRegProps.lean`, `StrataDyn/Rewrite.lean`; the proof about targets that promote a source's cells, `StrataDyn/RefToRegSound/`
*
  * Function attributes
  * `StrataDyn/Attr.lean`
*
  * The While example
  * `StrataDyn/Examples/While/`: `Dialect.lean`, `Elab.lean`, `Env.lean`, `Lower.lean`, `Run.lean`, `Cert.lean`, `RefToRegSound.lean`
*
  * Tests
  * `StrataDynTest/`, with the engine's in `StrataDynTest/Exec/` and While's in `StrataDynTest/Examples/While/`
*
  * Python environment and translator
  * `StrataPython/Dyn/Env.lean`, `StrataPython/Dyn/Build.lean`, `StrataPython/Dyn/Translate.lean`, `StrataPython/Dyn/Cli.lean`; reading Python: `StrataPython/PythonDialect.lean`, `StrataPython/ReadPython.lean`, `Python/strata-python/strata_python/`
*
  * Design documents
  * `docs/Dyn.md`, `docs/PythonToDyn.md`
*
  * This guide
  * `docs/dyn/`, with its Lean checks in `docs/dyn/checks/`

:::

## B. Glossary
%%%
number := false
tag := "app-gloss"
%%%

: environment

  A checked list of type, datatype and instruction declarations: the whole vocabulary a module may use.

: environment refinement

  An environment that has every declaration of another with the same shape: `t ≼ s`, "s refines t". `extends` makes one. Unrelated to trace refinement.

: successor

  A place to which an instruction may transfer control. The instruction's signature gives each successor a name and a payload, the types of the values the instruction passes on.

: target

  What fills a successor: a block, with values for a prefix of its parameters. In the builder a target is `Target env ps`, and in a rule `Target E ts`.

: region

  A nested body owned by an instruction, which the instruction's rule runs; its transfers stay inside it. A function's contract clauses and frames, and a ghost's initializer and invariant, are regions too, owned by the function or the ghost.

: effect

  What an operation itself may do, declared with its instruction: `pure`, `reads`, `calls` or `writes`, the default. A contract applies no `writes` operation. The checker trusts the declared effect.

: contract

  A function's `requires` and `ensures` clauses, regions that return a `base.Bool`, and its frames, the locations it may read or change. A run ignores it.

: extern function

  A function with a signature and a contract and no body.

: terminator

  A block's last line: an application of a terminal instruction, which defines no value.

: block parameter

  A typed value a block takes on entry; Dyn's form of a phi node.

: handler

  The block a raising instruction's `^err` successor goes to.

: emitter

  The Lean function, named after an instruction, that emits it; its Lean type is the instruction's signature.

: cell

  A piece of the machine's heap, holding one value of a fixed Lean type. `base.refNew` and a rule's `newRef` make one.

: ref

  A value that names a cell, of type `base.Ref T` for a cell holding a `T`. `base.refGet` and `base.refSet` read and write the cell through it.

: function reference

  The IR constant `@f`, which names the function `f` of the module at its `Func.codeType`, a `base.Fn` type. When a module runs, it is the closure that binds nothing.

: closure

  A value of type `base.Fn as r` when a module runs: a function of the module with values bound to its first arguments.

: world

  A language's mutable state outside the machine's heap: a Lean record that rules read and write.

: rule

  The Lean function that gives one instruction its meaning.

: tag

  A value of `Ty` that stands for a Lean type of a semantic table. The machine checks a cell's tag at every access.

: run token

  The type `σ` that every rule touching refs is generic in; the machine runs at the token `Run`.

: wrapper

  The function `#dyn_sem_table` generates for an instruction, which applies its rule to the operands and to the regions, targets, Again and capabilities that it builds.

: run

  A sequence of configurations of a module's step relation, one at every time: a state that is still running, or how the run ended. What a module does is the set of its runs.

: behaviour

  What an observer of the world sees of a run: the records it shows, and how it ends, with a result, without end silently, or without end showing records forever.

: trace refinement

  A relation between two modules, such as a pass's input and output: every run of the target improves on some run of the source.

: fault

  How a run ends when it does not end with a value: a gap, a failure, a blocked path, a bad cell, a bad call, out of fuel, missing rules, an invalid module, or a missing function.

: account

  Where the refs of a value are: the cells its refs name, at their contents' tags, and the captures cells of its closures. A table's `Accounts` give the account of a value of each tag, of the world and of each rule's state.

: typing

  A tag for some cells of the heap and a list of tags for some captures cells. A value is valid in a typing when the typing has each location of the value's account: each cell, at the tag that the account gives it, and each captures cell.

: certificate

  The proof that a rule reaches only the cells and captures cells it is given: every ref and closure it hands the machine is valid in the typing of the heap at that point, whenever everything the machine handed it was. A table is certified when all its rules are. `#dyn_certs` proves it.

: spec

  What a rule's tree may ask of the machine, which answers it may get, which worlds the machine may hold and which exits it may take, at a ghost state, a value that only proofs carry: a `Spec G ε E`. A certificate uses a spec whose ghost state is a typing of the heap.

### Abstract interpretation (under development)
%%%
number := false
tag := "app-gloss-absint"
%%%

These terms belong to abstract interpretation, which is under development and not yet in the package ({ref "absint"}[Abstract interpretation: the idea]).

: abstract value

  A description of a set of concrete values, the values a run computes. In constant propagation, `⊥`, a constant or `⊤`.

: concretization

  The relation `γ a v` between an abstract value `a` and each concrete value `v` that it describes.

: order

  The relation `a ⊑ b` between abstract values, which holds when `b` describes every value that `a` describes. In Lean, `le a b = true`.

: join

  An abstract value `a ⊔ b` above both `a` and `b`, which the analysis uses where two paths meet.

: widening

  An upper bound `a ∇ b` of two abstract values that jumps ahead, to make the solver's rounds stop.

: narrowing

  A value `a △ b` between `b` and `a`, for `b` below `a`, which a narrowing round uses to recover precision that widening gave up.

: interval

  The abstract value `[l, h]` that describes the integers from `l` to `h`, where `l` may be `-∞` and `h` may be `+∞`.

: abstract type

  A Lean type of abstract values with an `AbsDomain` instance, which a domain gives to a Dyn type, as the constants' domain `CPD` gives `CP` to `Base.Int`. Its abstract values describe values of the Dyn type's Lean type.

: domain

  A named declaration, `dyn_domain D`, that gives Dyn types their abstract types and instructions their transfer functions.

: relational domain

  A domain whose abstract states record relations between values, such as zones, declared with `dyn_domain D (state := S)`. Its transfer functions act on states, and `StateEmbed S α` instances say which Lean types its states see.

: sort

  One of the distinct abstract types of a domain. The analysis keeps each value's abstract value at the sort of the value's Lean type, and types with one abstract type share a sort.

: abstract state

  An abstract value for each value in scope at a program point, or `⊥`, which describes no state. By an analysis's soundness theorem, no run enters a block whose entry state is `⊥` in every context that analyses the block's body.

: transfer function

  The abstract version of one instruction: from the operands' abstract values, the result's abstract value and the successors a run may take.

: local soundness

  The property of a transfer function that its result describes every result of the instruction's rule on operands that the operands' abstract values describe. For a transfer function `τ` of addition: if `γ a x` and `γ b y`, then `γ (τ a b) (x + y)`.

: obligation

  The statement of a transfer function's local soundness that `@[dyn_transfer]` computes from the instruction's rule, and checks the theorem it sits on against. `#dyn_transfer_obligation` prints it.

: polymorphic transfer function

  A transfer function that takes `{A : Type} [AbsDomain A]` per type parameter of its instruction, and that the analysis instantiates at the abstract type of each type argument.

: abstract value of a datatype

  For each constructor of the datatype, `none` or the abstract value of the constructor's fields: a value of `SumAbs Fs`. `#dyn_abs_sum D T` makes it the abstract type of `T` in `D`.

: default transfer function

  The transfer function that `base.jump`, `base.branch` or `base.unreachable` gets in a domain that registers none of its own, from the state before the instruction. It takes every successor that the rule may take, except that the default of `base.branch` takes only the successors that the condition allows when the domain's abstract type at `Bool` has a `BoolView`.

: `BoolView`

  An instance on an abstract type of `Bool` that says whether an abstract value of a condition may be true (`mayTrue`) and whether it may be false (`mayFalse`). It gives `base.branch` a default that reads the condition.

: spec, in an analysis

  A spec, as defined above, that allows what a transfer function allows. The obligation of every rule that is not pure holds at every such spec.

: coverage report

  What `#dyn_absint_coverage D for S` prints: for each Dyn type of `S`, its abstract type in `D` or why it has none, and for each instruction, its transfer function in `D` and its proof, the default it gets, why it has none, or why the analysis does not support it.

: facts

  The result of an analysis: an abstract state at the entry of each block of each function and each region, a description of each function's result as a run's entry and of each region's result, the summaries of the module's calls, and the code-pointer facts.

: soundness

  The property of an analysis that its facts describe every point of every run of the module's step relation, after any number of steps. `#dyn_absint` proves it as the theorem `sound`.

: solver

  The part of an analysis that proposes facts, computed in rounds, joining and then widening, and then narrowing if the schedule asks for it, which it does not by default. It needs no proof, and `N.analyzeWith` takes one of your own.

: checker

  The part of an analysis that makes one pass over the module and accepts the solver's facts only if they are a post-fixpoint.

: post-fixpoint

  Facts that every transfer function respects: what it passes along each successor that it allows is `⊑` the successor's entry state, and each value that leaves a body is `⊑` the description of the body's result. The checker recomputes the state after each instruction from its block's entry state.

: schedule

  When the solver widens, whether it narrows, its cap on the rounds, and which summaries of a callee it makes: a value of `Schedule`, and an argument of `analyze`.

: table

  The transfer functions of a domain with the proof that each instruction's wrapper meets its own, apart from how the analysis finds its facts. A domain of abstract types has a value table, which lifts to any state domain whose states describe single values as its typed states do.

: summary

  The analysis of a callee's body on a key, facts of its arguments, with a description of its result. It serves every call whose arguments its key is above.

: context

  Where a body is analysed: a function as a run's entry (`root i`), a region as the rules run it, or a function on a summary's key (`sum i j`). `Analysis.ctx_sound` is the soundness theorem of each context.

: context allocator

  The solver's choice of which summaries exist: `perInput k`, a summary per input up to `k` per callee, or `perCallee`, one per callee.

: code-pointer fact

  A fact that a slot holds a code pointer with no captures to a known function, along every path to a call. A call's callee is the function that the fact at the call names.

: reduced product

  Two state domains side by side, with a reducer that exchanges what each knows of the values that an instruction defines and passes, and keeps what the pair stands for. `dyn_domain P := D₁ × D₂ (reduce := f, h)` declares one from two domains of abstract types, and `RP R` builds one from any two state domains.

: live block

  A block whose entry state is not `⊥`: one that the facts say a run may enter.

## C. Full texts
%%%
number := false
tag := "app-texts"
%%%

The While environment and the base environment, verbatim; then the running example's printed module in both forms.

```leantext "The While environment"
public environment While extends Base where
  namespace «while»
  open base
  /-- A list of integers. -/
  data IntList where
    | nil
    | cons (head : Int) (tail : IntList)
  /-- How a body region ended: it fell off its end, or raised `e`. -/
  data Flow where
    | next
    | raise (e : Int)
  insn add (lhs rhs : Int) : Int
  insn sub (lhs rhs : Int) : Int
  insn mul (lhs rhs : Int) : Int
  insn neg (x : Int) : Int
  /-- `lhs / rhs`, or `^err` with `1` if `rhs` is `0`. -/
  insn div (lhs rhs : Int) (^err (code : Int)) : Int
  /-- `lhs % rhs`, or `^err` with `1` if `rhs` is `0`. -/
  insn mod (lhs rhs : Int) (^err (code : Int)) : Int
  /-- Exponentiation, which the semantics leaves out. -/
  insn pow (lhs rhs : Int) : Int
  insn lt (lhs rhs : Int) : Bool
  insn le (lhs rhs : Int) : Bool
  insn eq (lhs rhs : Int) : Bool
  insn ne (lhs rhs : Int) : Bool
  insn not_ as "not" (x : Bool) : Bool
  insn and_ as "and" (lhs rhs : Bool) : Bool
  insn or_ as "or" (lhs rhs : Bool) : Bool
  /-- Append `x` to the run's output. -/
  insn print (x : Int) : Unit
  /-- Count, and return how often `tick` has run. -/
  insn tick : Int
  /-- A number from `0` to `n`, chosen by the oracle. -/
  insn pick (n : Int) : Int
  /-- A cell of an `Int`, which the rules make on the machine's heap. -/
  abbrev Cell := Ref Int
  insn cellNew (value : Int) : Cell
  insn cellGet (cell : Cell) : Int
  insn cellSet (cell : Cell) (value : Int) : Unit
  /-- Run `then` if `cond` holds and `else` otherwise; a raise leaves along `^err`. -/
  insn «if» (cond : Bool) (&«then» &«else» : Flow) (^err (code : Int)) : Unit
  /-- Run `body` while `cond` yields `true`; a raise leaves along `^err`. -/
  insn loop (&cond : Bool) (&body : Flow) (^err (code : Int)) : Unit
  end «while»
```

The base environment, verbatim. {ref "env-calls"}[Environment 4: Functions and calls] explains its function type `Fn` and its call `callCode`.

```leantext "The base environment (StrataDyn/Base.lean)"
public environment Base where
  namespace base
  /-- `base.Unit`, the type of `()`. -/
  data Unit where
    | /-- `base.unit`, the unit value. -/ unit
  /-- `base.Bool`. -/
  type Bool
  /-- `base.Int`, the unbounded integers. -/
  type Int
  /-- `base.Float64`. -/
  type Float64
  /-- `base.String`. -/
  type String
  /-- `base.Sequence a`, a sequence of `a`. -/
  type Sequence (+a)
  /-- `base.Ref a`, a mutable cell holding an `a`.  A datatype may recurse through one. -/
  type Ref (+a)

  /-- `base.Except e a`: a value, or the error that replaced it.  `base.Except.case`'s
  successors are in this order, `ok` first; a datatype may recurse through either
  parameter. -/
  data Except (+e) (+a) where
    | /-- `base.ok`, a success. -/ ok (value : a)
    | /-- `base.error`, a failure. -/ error (err : e)

  /-- `base.refNew`, a new cell holding `value`. -/
  pure insn refNew [a] (value : a) : Ref a
  /-- `base.refGet`, the contents of `cell`. -/
  reads insn refGet [a] (cell : Ref a) : a
  /-- `base.refSet`, which replaces the contents of `cell` with `value`. -/
  writes insn refSet [a] (cell : Ref a) (value : a) : Unit
  /-- `base.old`, which runs `body` in the state at the call of the function whose `ensures`
  clause applies it: the value of an `ok`, or a transfer to `err` with the error of an
  `error`.  Only an `ensures` clause may apply it. -/
  reads insn old [e a] (&body : Except e a) (^err (exc : e)) : a

  /-- `base.Loc`, a set of mutable locations of the program state, which a frame names.  A
  language adds operations that give its own locations. -/
  type Loc
  /-- `base.cellLoc`, the contents of `cell`: a set of one location.  It denotes the location by
  the cell's identity, and reads no state. -/
  pure insn cellLoc [a] (cell : Ref a) : Loc

  /-- `base.jump`: A jump to a block `k`.  A jump to a body's exit returns from it. -/
  pure terminal insn jump (^k)
  /-- `base.branch`: continue at `t` if `cond` holds. -/
  pure terminal insn branch (cond : Bool) (^t ^f)
  /-- `base.unreachable`: control never gets here. In a contract region, such as a clause, a
  frame region, an initializer or an invariant, reaching it means that the region is not well
  defined, so a consumer must not read it as `assume(false)`. -/
  pure terminal insn unreachable

  /-- `base.Fn as r`, a typed code pointer: to a function that takes arguments of the types
  `as`, in order, and returns an `r`.  A function reference has its target's `Fn` type,
  `Func.codeType`.  A datatype may recurse through `r`. -/
  type Fn (as : list) (+r)
  /-- `base.callCode`, a call of the function `f` points to: one argument per element of
  `as`, of that element's type.  The callee may change state. -/
  writes insn callCode [(as : list) r] (f : Fn as r) (*args : as) : r
  end base
```

```dyn "Folded (Module.format)"
module main {
  func @mean(%n.0 : base.Int, %d.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int, %d.0 : base.Int):
      jump ^head.0(%n.0, %d.0, 0, 1)
    head.0(%n.1 : base.Int, %d.1 : base.Int, %s.0 : base.Int, %i.0 : base.Int):
      %t.0 : base.Bool = while.le(%i.0, %n.1)
      branch(%t.0) ^body.0() ^exit.0()
    body.0():
      %t.1 : base.Int = while.add(%s.0, %i.0)
      %t.2 : base.Int = while.add(%i.0, 1)
      jump ^head.0(%n.1, %d.1, %t.1, %t.2)
    exit.0():
      %t.3 : base.Int = while.div(%s.0, %d.1) ^catch.0(%n.1, %d.1, %s.0, %i.0)
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.3)
      ret(%ok.0)
    catch.0(%n.2 : base.Int, %d.2 : base.Int, %s.1 : base.Int, %i.1 : base.Int, %e.0 : base.Int):
      %t.4 : base.Int = while.sub(0, %e.0)
      %ok.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.4)
      ret(%ok.1)
  }
  func @main(%n.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int):
      %t.0 : base.Int = while.sub(%n.0, 10)
      %r.0 : base.Except(base.Int, base.Int) = base.callCode[[base.Int, base.Int], base.Except(base.Int, base.Int)](@mean, %n.0, %t.0)
      base.Except.case[base.Int, base.Int](%r.0) ^ok.0() ^raise.0()
    ok.0(%x.0 : base.Int):
      %u.0 : base.Unit = while.print(%x.0)
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
      ret(%ok.0)
    raise.0(%e.0 : base.Int):
      %error.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%e.0)
      ret(%error.0)
  }
}
```

```dyn "Full (Module.Raw.format .full)"
module main {
  func @mean(%n.0 : base.Int, %d.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int, %d.0 : base.Int):
      %k.0 : base.Int = const 0
      %k.1 : base.Int = const 1
      jump ^head.0(%n.0, %d.0, %k.0, %k.1)
    head.0(%n.1 : base.Int, %d.1 : base.Int, %s.0 : base.Int, %i.0 : base.Int):
      %t.0 : base.Bool = while.le(%i.0, %n.1)
      branch(%t.0) ^body.0() ^exit.0()
    body.0():
      %t.1 : base.Int = while.add(%s.0, %i.0)
      %k.2 : base.Int = const 1
      %t.2 : base.Int = while.add(%i.0, %k.2)
      jump ^head.0(%n.1, %d.1, %t.1, %t.2)
    exit.0():
      %t.3 : base.Int = while.div(%s.0, %d.1) ^catch.0(%n.1, %d.1, %s.0, %i.0)
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.3)
      ret(%ok.0)
    catch.0(%n.2 : base.Int, %d.2 : base.Int, %s.1 : base.Int, %i.1 : base.Int, %e.0 : base.Int):
      %k.3 : base.Int = const 0
      %t.4 : base.Int = while.sub(%k.3, %e.0)
      %ok.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.4)
      ret(%ok.1)
  }
  func @main(%n.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int):
      %k.0 : base.Int = const 10
      %t.0 : base.Int = while.sub(%n.0, %k.0)
      %code.0 : base.Fn([base.Int, base.Int], base.Except(base.Int, base.Int)) = const @mean
      %r.0 : base.Except(base.Int, base.Int) = base.callCode[[base.Int, base.Int], base.Except(base.Int, base.Int)](%code.0, %n.0, %t.0)
      base.Except.case[base.Int, base.Int](%r.0) ^ok.0() ^raise.0()
    ok.0(%x.0 : base.Int):
      %u.0 : base.Unit = while.print(%x.0)
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
      ret(%ok.0)
    raise.0(%e.0 : base.Int):
      %error.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%e.0)
      ret(%error.0)
  }
}
```

### The correspondence table
%%%
number := false
tag := "app-texts-table"
%%%

:::table +header
*
  * Source span
  * Dyn lines (folded)
  * Caption
*
  * `var s : Int := 0; var i : Int := 1;`
  * `entry.0(%n.0 : base.Int, %d.0 : base.Int):`

    `jump ^head.0(%n.0, %d.0, 0, 1)`
  * The declarations make the constants 0 and 1, which the entry block passes to the loop header as the first values of s and i.
*
  * `while (i <= n)`
  * `jump ^head.0(%n.0, %d.0, 0, 1)`

    `head.0(%n.1 : base.Int, %d.1 : base.Int, %s.0 : base.Int, %i.0 : base.Int):`

    `%t.0 : base.Bool = while.le(%i.0, %n.1)`

    `branch(%t.0) ^body.0() ^exit.0()`
  * The loop header takes every variable in scope as a parameter, tests the condition, and branches to the body or the exit.
*
  * `s := s + i`
  * `%t.1 : base.Int = while.add(%s.0, %i.0)`
  * An assignment defines a new value: from here on, s is %t.1.
*
  * `i := i + 1`
  * `%t.2 : base.Int = while.add(%i.0, 1)`

    `jump ^head.0(%n.1, %d.1, %t.1, %t.2)`
  * The back edge passes the current value of every variable to the header, the unchanged d included.
*
  * `try {`
  * `%t.3 : base.Int = while.div(%s.0, %d.1) ^catch.0(%n.1, %d.1, %s.0, %i.0)`
  * Inside the try, the handler in effect is catch.0, so the raising division gets the successor ^catch.0 with the four variables.
*
  * `s / d`
  * `%t.3 : base.Int = while.div(%s.0, %d.1) ^catch.0(%n.1, %d.1, %s.0, %i.0)`
  * Division is a raising instruction: on success it defines %t.3, and on a zero divisor it transfers along its ^err successor.
*
  * `return s / d;`
  * `%ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.3)`

    `ret(%ok.0)`
  * Because mean may raise (a division), its returns are wrapped in base.ok.
*
  * `catch e => { return 0 - e; }`
  * `catch.0(%n.2 : base.Int, %d.2 : base.Int, %s.1 : base.Int, %i.1 : base.Int, %e.0…`

    `%t.4 : base.Int = while.sub(0, %e.0)`

    `%ok.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.4)`

    `ret(%ok.1)`
  * The handler takes the four values the edge binds, then the payload %e.0, which while.div supplies.
*
  * `mean(n, n - 10)`
  * `%t.0 : base.Int = while.sub(%n.0, 10)`

    `%r.0 : base.Except(base.Int, base.Int) = base.callCode[[base.Int, base.Int], bas…`

    `base.Except.case[base.Int, base.Int](%r.0) ^ok.0() ^raise.0()`

    `ok.0(%x.0 : base.Int):`
  * A call is base.callCode on the function reference @mean, then base.Except.case, which continues at ok.0 with the result, or goes to the handler.
*
  * `print(m)`
  * `%u.0 : base.Unit = while.print(%x.0)`
  * print has nothing to return, so it defines a base.Unit value; m is the block parameter %x.0.
*
  * `return m;`
  * `%ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)`

    `ret(%ok.0)`
  * main returns m wrapped in base.ok.
*
  * implicit propagate (the call's error edge)
  * `raise.0(%e.0 : base.Int):`

    `%error.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%e.0…`

    `ret(%error.0)`
  * The call's error edge goes to raise.0, the function's propagate block, which returns the error as base.error.

:::

## D. Starting a new front end
%%%
number := false
tag := "app-start"
%%%

A front end for a language `Lang` is a library of its own, as Python's is in `StrataPython/Dyn/`: a few Lean modules and their tests. Every file is a `module` file.

1. *The dialect*, `Lang/Dialect.lean`: the AST as a DDM dialect and its generated Lean types.

   ```leantext
   module
   public import StrataDDM.Integration.Lean.OfAstM
   import StrataDDM.Integration.Lean.Gen
   import StrataDDM.Integration.Lean.HashCommands
   open StrataDDM

   namespace Strata.Dyn.Lang.Ast
   public section
   #dialect
   dialect Lang;
   category Exp;
   op var (x : Ident) : Exp => x;
   /* … one op per node kind */
   #end
   -- The generated AST binds its annotation type implicitly.
   set_option autoImplicit true in
   #strata_gen Lang
   end
   ```

   With an external parser, replace `#dialect … #end` by `#load_dialect "path/Lang.dialect.st.ion"`, and declare the file in the lakefile (step 6).

1. *The environment*, `Lang/Env.lean`.

   ```leantext
   module
   public import StrataDyn.Base
   -- The typed builder, so that the environment gets emitters.
   public import StrataDyn.Build.Typed
   import StrataDyn.Env.WF
   import StrataDyn.DSL
   -- The rule interface and the base's rules.
   public import StrataDyn.Exec
   public import StrataDyn.Exec.Base

   namespace Strata.Dyn
   public environment Lang extends Base where
     namespace lang
     open base
     insn add (lhs rhs : Int) : Int
     -- … types, datatypes and instructions (see the Environment chapter)
     end lang
   ```

   The rules go beside the environment, in this order ({ref "env-sem"}[Environment 7: Meaning]):

   * `@[dyn_type]` for the primitive types;
   * `#dyn_types Lang` for the datatypes;
   * a `World` record that derives `Inhabited`, with a `HasPart` instance per part;
   * a `@[dyn_lang]` class of the language's capabilities;
   * one `@[dyn_sem Lang.op]` rule per instruction;
   * `#dyn_coverage Lang (complete)`;
   * `#dyn_sem_table LangSem for Lang (world := LangRules.World)`.

   The rules, the world and the class go in a namespace of their own, `LangRules`, inside an `@[expose] public section`, and the table inside a `public section`. Made outside a public scope, the table's definitions are private, so no other module can run a program against it; and a public table cannot use private rules. The rest of the file, after the environment:

   ```leantext
   #dyn_types Lang

   namespace LangRules
   open Strata.Dyn.Exec

   @[expose] public section

   structure World where
     -- … one field per part of the world, each with a default
     deriving Inhabited

   -- … a `HasPart World P` instance per part, and the `@[dyn_lang]` class
   @[dyn_sem Lang.add] def add (a b : Int) : Int := a + b
   -- … one rule per instruction

   end
   end LangRules

   #dyn_coverage Lang (complete)

   public section
   #dyn_sem_table LangSem for Lang (world := LangRules.World)
   end

   end Strata.Dyn
   ```

1. *The translator*, `Lang/Lower.lean`: a monad over `BuildM` ({ref "tr-build"}[Translator 2: The builder]), `lowerExpr` and `lowerStmt` over the generated AST, emitting through the typed emitters, one `Emit.func` per function, which checks it with `Build.run`, and `Module.ofChecked` for the module. It imports `Lang.Dialect`, `Lang.Env` and `StrataDyn.Build.Typed`, and also `StrataDyn.Env.WF`, which building instructions needs at code-generation time. It opens `Strata.Dyn` for `vals[…]` and `Strata.Dyn.Emit` for `let%`.
1. *The runner*: lower a program, call `runModule LangSem.model` with arguments `LangSem.model.arg x`, and decode the result with `read?` into a string, as While's `showResult` and `showOutcome` do. It imports `StrataDyn.Exec.Run`.
1. *Tests*, as `module` files that may use `import all`. A test that runs code with `#guard` or `#eval`, such as the lowering or a run, also needs a `meta import` of each module whose code it runs, beside its ordinary import, as While's `RunTest` has (`StrataDynTest/Examples/While/RunTest.lean`). The tests are:

   * a programs file, holding the example programs, written with an embedding command like `#while` or read from Ion;
   * that every program lowers: `#guard (lower p).toBool`, as `RunTest` checks it. A `Module` carries the proof that it is well formed, so a program that lowers gives a well-formed module;
   * golden printed modules and lowering errors, as `#guard` equalities or `#guard_msgs` blocks, and golden outcomes with no step counts;
   * for a program that never ends, or a property of every step, prefixes of its run under one oracle, with `trace` and `obsTrace`.

1. *The lakefile.* A library for the new modules, with a glob, and one for its tests. A loaded dialect file needs an input file, listed in every library that reads it:

   ```plaintext
   [[input_file]]
   name = "LangDialectIon"
   path = "path/Lang.dialect.st.ion"

   [[lean_lib]]
   name = "Lang"
   globs = ["Lang.+"]
   extraDepTargets = ["LangDialectIon"]

   [[lean_lib]]
   name = "LangTest"
   globs = ["LangTest.+"]
   extraDepTargets = ["LangDialectIon"]
   ```

   Lake builds only the targets that something asks for, so a library that nothing depends on is not built, and its tests never run. Add `Lang` to the package's `defaultTargets`, and `LangTest` to `defaultTargets` or to the `needs` of the test driver, the executable that `testDriver` names. `lakefile.toml` does so for its own libraries: `StrataDyn` is in `defaultTargets`, and `StrataDynTest` in the test driver's `needs`.

1. *Build and test* with `lake build Lang LangTest`, then `lake test`. The tests run at elaboration time, so a failing `#guard` is a build error.

:::sources
Sources: `lakefile.toml`; `StrataPython/Dyn/`; `StrataDyn/Base.lean`; `StrataDyn/Examples/While/`.

:::

## E. Inside the analysis framework
%%%
number := false
tag := "app-absint"
%%%

:::::callout "Under development: abstract interpretation (not yet in the package)" (kind := "warning")
This appendix describes the framework of {ref "absint-dyn"}[Writing an analysis in Dyn], which is not yet in the package. Its listings are static, except those whose title ends with the path of a file in the package: the guide's build checks that their code is still there.
:::::

This appendix gives the statements that {ref "absint-dyn"}[Writing an analysis in Dyn] abbreviates, and how the framework proves them. A user of the framework applies none of them. Their statements are about the runs of a module's step relation ({ref "inside-runs"}[Inside the execution DSL: Runs]).

### The soundness theorem in full
%%%
number := false
tag := "app-absint-sound"
%%%

The theorems of this section belong to the framework, which is not yet in the package.

A run of a Dyn module passes through _configurations_ ({ref "run"}[Testing]): a machine state that is still running, or how the run ended, with its result, a value or a fault. A run of the function `i` on the arguments `args`, from the snapshot `snap`, a heap with a world, starts at the state `s` that `start hwf i args snap` builds. `RunFrom hwf s h` is the type of the runs of the step relation from `s`, and `r.cfg n` is the configuration of the run `r` after `n` steps. A run answers each choice freely, so the runs cover every oracle.

The result of `analyze` is the analysis's facts:

```leantext "What an analysis finds (under development, in StrataDyn/Absint/Core/Check.lean)"
structure Facts (S P : Type) where
  bodies : Std.HashMap Name (Array S) := {}
  funcRets : Array P := #[]
  regionRets : Array P := #[]
  sums : Memo S P := {}
  codes : Std.HashMap Name (Array (Option Internal.Codes)) := {}
```

For each body, a function or a region, by name, `bodies` holds an abstract state at the entry of each block. `funcRets` describes the result of each function as a run's entry, and `regionRets` the result of each region. Both go by position in the module, since a run starts a function by its position, and a rule names the regions it runs by position. `sums` holds the summaries of the module's calls, each a key and the states and result of its callee's analysis on that key. `codes` holds the code-pointer facts at the entry of each block of each body that stores a code pointer, `none` at a block that no path from the body's entry reaches ({ref "absint-calls"}[Calls and contexts]). A block with no entry has the state `bot`, and a function or a region with no entry the description `top`. `P` is the type of what the facts know of one value, which `#dyn_absint` names `N.Value`, and `N.Facts` is `Facts N.State N.Value`.

The facts are read in a _context_:

```leantext "Contexts (under development, in StrataDyn/Absint/Core/Check.lean)"
/-- **A context of the facts**, where a body is analysed: `root i`, function `i` as a run's
entry; `region k`, region `k` as the rules run it; `sum i j`, function `i` on the key of entry
`j` of its summaries. -/
inductive Context where
  | root (i : Nat)
  | region (k : Nat)
  | sum (i j : Nat)
  deriving DecidableEq, Repr
```

The root contexts and the regions' share the states of `bodies`, and a summary's context has the states of its memo entry. Each root context has its own result, function `i`'s entry of `funcRets`. `BodyOf F m ctx b` says which body a context analyses: `root i` analyses function `i`, `region k` analyses region `k`, and `sum i j` analyses function `i` when the memo has that entry.

An abstract state describes the values of a frame when it is not `⊥` and, for each value `x` in scope, `γ a x` holds of the abstract value `a` that the state gives `x`. `AdmitsAt F base p` holds when the facts `F` describe the point `p` of a run whose bottom frame runs in the context `base`: at a machine state that runs a frame, the frame's store is described by the state at the frame's point in a context that analyses the frame's body, the block's entry state updated by the transfer functions of the instructions before that point; at a state that enters a block, by the block's entry state in such a context; and a value that the bottom frame returns, and the result the run ends with, are described by `base`'s result. Every fault is admitted. `Admits F i p` is `AdmitsAt F (.root i) p`, for a run that starts function `i`, and `N.Admits` is `Admits` at the analysis that the command builds.

For the analysis `IvlTVWhile`, the command generates this theorem:

```plaintext "The soundness theorem (under development, pinned in StrataDynTest/Absint/DomainsTest.lean)"
@IvlTVWhile.sound : ∀ {env : Env Unit} [inst : base ≼ env] {α : Type} {prog : Module env α}
  {m : LModule WhileSem.model.at},
  link WhileSem.model prog = Except.ok m →
    ∀ (hwf : WF m) {sch : Schedule} {F : IvlTVWhile.Facts},
      IvlTVWhile.analyze m sch = some F →
        ∀ {i : Nat} {args : List (Dyn WhileSem.model.at.interp)} {snap : Snapshot WhileSem.model.at} {B : Exec.Ty}
          {s : State WhileSem.model.at} {h : StateOK m B s},
          start hwf i args snap = Except.ok ⟨B, ⟨s, h⟩⟩ →
            ∀ (r : RunFrom hwf s h) (n : Nat), IvlTVWhile.Admits F i (r.cfg n)
```

`sound` has four hypotheses:

* `link WhileSem.model prog = Except.ok m` says that `m` is the linked module of `prog`, a module over any environment that refines `base` ({ref "inside-linking"}[Linking]);
* `hwf : WF m` says that validation accepts `m` ({ref "inside-validation"}[Validation]);
* `IvlTVWhile.analyze m sch = some F` says that the analysis, run under the schedule `sch`, returns the facts `F`;
* `start hwf i args snap = Except.ok ⟨B, ⟨s, h⟩⟩` says that `s` is the first state of a run of the function `i` on `args` from the snapshot `snap` ({ref "inside-validation"}[Validation]), with `B` its result's tag and `h` its invariant.

Its conclusion holds for every run `r` from `s` and every number of steps `n`: if the run is still running after `n` steps, the facts admit its state, and if it has ended with a value, function `i`'s result describes the value. It is `Analysis.analyze_sound` at the analysis that the command builds, and `N.soundWith` is `Analysis.analyzeWith_sound`, the same for every solver. Its companion `Analysis.analyze_reach` states it for every configuration that steps of the module reach from `s`:

```leantext "Facts at the configurations reached (under development, in StrataDyn/Absint/Core/Solve.lean)"
theorem analyze_reach {env : Env Unit} [base ≼ env] {α : Type} {prog : Module env α}
    {m : LModule M.at} (hl : link M prog = .ok m) (hwf : WF m) {sch : Schedule}
    {F : Facts T.S (StateDomain.Pay T.S)} (ha : T.analyze m sch = some F) {i : Nat}
    {args : List (Dyn M.at.interp)} {snap : Snapshot M.at} {B : Ty} {s : State M.at}
    {h : StateOK m B s} (hs : start hwf i args snap = .ok ⟨B, s, h⟩) {p : Config m B}
    (hp : Reach hwf s h p) :
    T.Admits F i p :=
```

By `reach_runFused`, `runFused` stops only at configurations that are reached, so the facts also describe every configuration at which an execution on fuel stops.

The theorem of each context is `Analysis.ctx_sound`. From a frame `g` at a point of a body that the context `ctx` analyses, in a store that the state there admits, every point of every run of `g` alone, on any heap and world, is admitted with `ctx` as the bottom context. `Analysis.summary_sound` is its case at a summary: from the callee's entry frame, on arguments that the summary's key describes, every value that the callee returns is described by the summary's result. `sound` is its case at a start, in the root context `root i` of the function that the run starts. Both theorems assume that the linked module is well formed (`WF m`), that each of its instructions runs the wrapper that its table entry gives (`Honest M m`, which `link_honest` gives for every linked module), that the checker accepted the facts (`T.check F m = true`), and that the frame runs in `m` (`Runs m g`). `summary_sound` also assumes that the arguments have the callee's parameter types. Since `AdmitsAt` asks for a context that analyses the frame's body, a summary's states are read only for frames of its callee.

### How the framework proves it
%%%
number := false
tag := "app-absint-proof"
%%%

This proof belongs to the framework, which is not yet in the package.

The framework proves the theorems once, for every analysis. The first three steps give `sound`, and the fourth `total`:

1. `analyze` runs the solver and then the checker, and returns only facts that the checker accepts, so `sound` rests on the checker, and the solver needs no proof.
1. Facts that the checker accepts give a _claim_, a property of machine states and of results, that every start satisfies and that every step of the machine preserves, under every oracle. By invariance, `always` ({ref "inside-runs"}[Runs]), the claim then holds at every configuration of every run.
1. Each instruction of a linked module runs the rule that its table entry names. The linker's own proof gives this of every module that `link` produces (`link_honest`, below).
1. For `total`, the solver's rounds stop at `maxRounds` at the latest, and, for a domain with the order laws, on a covered module the checker accepts what they stop at, even the fallback of `top` at every block ({ref "absint-total"}[Termination]).

The invariant step, the second, is one theorem about the checker's claim. `StateIn base` is the claim at a machine state, in a run whose bottom frame runs in the context `base`, and `ResultIn base` at a result. `ModOK` says that the checker's obligations hold at every point of every block of every body, in every context of the facts. The theorem is the hypothesis of `always`, a step from a state that the claim holds of:

```leantext "Every step keeps the claim (under development, in StrataDyn/Absint/Core/Frag.lean)"
/-- **The fragment analysis is sound**: if the obligations hold at every point of every block of
every body of every context and of every region, every step from a machine state in
`StateIn base`, under every oracle, leads to one in `StateIn base` or ends with a result in
`ResultIn base`, as `Exec.always` takes it. -/
theorem claim_inductive (hm : ModOK m D C hwf) (oracle : Nat → Nat) (s : State M)
    (h : StateOK m B s) (hs : StateIn m D C base s) :
    (step hwf oracle s h).config.Sat (fun c => StateIn m D C base c.1)
      (fun f => ResultIn D C base f.result) := by
  …
```

The claim describes every frame of the machine: the running one, in a function, a region or a callee, and each frame below it, a caller waiting for a call to return or a rule waiting at a region request. A waiting caller's frame is described in the context it runs in, and a value returned to it by the result of the summary it called. Entering a region or a callee, leaving it and running a rule's `Again` are steps of the machine like the others, and the proof that the claim is inductive covers them.

The third step is a fact about linking, not about the analysis, and it lives beside the linker, in `Strata.Dyn.Exec`. A module is _honest_ when every instruction and terminator of every function and region runs the wrapper of the table entry that its key names, and a rule's tree for its `Again` is the entry's:

```leantext "Linking is honest (under development, in StrataDyn/Exec/LinkHonest.lean)"
/-- **Every function and every region of `m` is honest**: it runs its table entries' wrappers,
as linking `m` against `M` installs them. -/
def Honest (m : LModule M.at) : Prop := ∀ b, InM m b → BodyHonest M b
…
theorem link_honest (M : Model) {env : Env Unit} [base ≼ env] {α : Type} (m : Module env α)
    {lm : LModule M.at} (h : link M m = .ok lm) : Honest M lm := by
  obtain ⟨hf, hr⟩ := link_inv (LinkInv.honest M) h
```

`link_honest` is one application of a program logic for the linker, which is in the package. A _link invariant_ is a property of wrappers that every wrapper of the table has, with properties of linked instructions and terminators that what linking makes of such a wrapper has, and that the instructions linking makes with no wrapper, such as constants, have too. `link_inv` proves that every instruction and terminator of a linked module then has them:

```leantext "A program logic for linking (StrataDyn/Exec/LinkInv.lean)"
/-- **Linking keeps a link invariant**: every instruction and terminator of every function and
every region of a module that links against `M` satisfies the invariant. -/
theorem link_inv (P : LinkInv M) {env : Env Unit} [base ≼ env] {α : Type} {m : Module env α}
    {lm : LModule M.at} (h : link M m = .ok lm) : lm.All P.insn P.term := by
```

For honesty, the wrappers are the table's own. The same theorem gives `link_rulesOK`, which is in the package: a module linked against a model whose rules are certified to reach only the cells they are given has certified rules, with the certified wrappers as the invariant (`StrataDyn/Exec/CertLink.lean`, {ref "wip-cert"}[Proofs about runs 1: Certificates for rules]).

### The solver
%%%
number := false
tag := "app-absint-solver"
%%%

The solver belongs to the framework, which is not yet in the package.

One solver runs over every module, with or without regions and calls. It first builds the module's _layout_. Its _units_ are bodies analysed in a context: first the module's functions and regions, in the run's own facts, then the summaries, each its callee's body on a key, which the solver adds as calls demand them. For each unit the layout keeps the body's _plan_ and the _support_ of each block, the slots that the block's states track. A plan orders a body's blocks in reverse postorder from the entry, and marks its widening points, the targets of retreating edges and the loop heads. A region's plan also marks its entry block, since the rule that runs the region sends that block states from another body:

```leantext "The layout (under development, in StrataDyn/Absint/Core/Solve.lean)"
structure Layout (M : RunModel) (P : Type) where
  mod : LModule M
  bodies : Array (LBody M)
  plans : Array Plan
  sups : Array (Array Support)
  readers : Array (List (Nat × Nat))
  /-- The code-pointer facts of the module's bodies, by name (`codesOf`). -/
  codes : Std.HashMap Name (Array (Option Codes))
  /-- The blocks, of every unit, that make a call. -/
  callers : List (Nat × Nat) := []
  /-- The blocks, of every unit, whose calls name each function, by its position: the readers of
  the results of its summaries. -/
  calls : Array (List (Nat × Nat)) := #[]
  /-- The callee of each summary unit. -/
  callees : Array Nat := #[]
  /-- The key of each summary unit. -/
  keys : Array (Array P) := #[]
  /-- Each callee's summary units, in the order they were made. -/
  unitsOf : Std.HashMap Nat (Array Nat) := {}
  /-- The height of each of the module's bodies in its call graph, by the code-pointer facts
  (`heightsOf`): a body is higher than the functions its calls name, unless they call it back.
  Rounds visit lower units first (`Layout.order`). -/
  heights : Array Nat := #[]
```

A region's _readers_ are the blocks whose rules read the region's result, each by its unit's and its own position. A function's readers, in `calls`, are the blocks whose calls name it by the code-pointer facts, and they read the results of its summaries. `heights` places each body in the call graph that the code-pointer facts give: a body is higher than the functions its calls name, unless they call it back.

What a block sends is a list of items, each an entry state for a block of some unit, or a description of a value that leaves the unit. A rule that runs a region sends the region's entry block a state, as an edge sends one to a block of its own body. A call reads the result of the callee's summary whose key is the most precise above its arguments. Until a summary serves a call, the call and the rest of its block send nothing, so the call's result is `⊥` rather than `⊤`, as in tabulation.

A round visits the units lower in the call graph first, so a summary comes before its callers, unless they are on a call cycle with it. It grows each item's target: it joins until the schedule's `widenAfter`, and then widens at widening points, at the results of regions, and at the results of summaries whose callee is on a call cycle. The other summaries' results, and each function's result as a run's entry, which nothing reads, only join. After each round, the calls demand the summaries they need, and the context allocator answers with new units or widened keys. Ascending stops at a round that, with its demands, changes nothing. If it reaches the cap first, it returns `none`, and the solver gives up with `top` at every block of every unit, `top` for every result and a summary keyed `top` per function. If the schedule narrows, which it does not by default (`Schedule.narrow`, set by `(narrow := true)`), narrowing then recomputes every state and result from the current states, and narrows each state by its recomputed one, until no state shrinks and no result changes, or the cap is reached. Both are well-founded recursions on the rounds left before the cap, so `solve` is a total function.

The solver avoids work in three ways. `Total.lean` proves, for a domain with the order laws, that the first changes no result. The other two are part of narrowing:

* It remembers, for each block, what the block sent at its last visit, for as long as the block's entry state and the results it reads are unchanged. A block with no memo is to visit, and a round visits only those. When a result grows, only its readers lose their memos: a region's readers, or the blocks whose calls name a summary's callee. A demand that adds a summary, or widens its key, makes the blocks whose calls name the callee visit again.
* Narrowing takes a remembered block's items from its memo instead of evaluating its transfer functions again. It evaluates only the blocks that ascending left to visit, the blocks whose state shrank in the last narrowing round, and the readers of the results that changed in it.
* After the first narrowing round, a block whose state did not shrink, and to which no block to visit sends, keeps its recomputed state: it is neither joined into nor narrowed again.

Nothing about narrowing is proved: the default solver proposes the narrowed facts and then the ascended ones, and the checker decides which are kept. _Completeness_, the theorem that, for a domain with the order laws, on a covered module the checker accepts what ascending returns, settled states or the fallback, covers regions and calls: a settled state passes the checker's test of every region that a rule runs, of every region's exits, and of every call's summary. The measure of termination is lexicographic: the summaries that may still be made, the keys, which grow only by widening, and the states of the widening points and the widened results, which take a pointwise widening step in each round in which one of them grows. A round in which none of them grows settles the states: a joined result changes only while its own unit is visited, and every unit that reads it comes later in the round.

### Specs
%%%
number := false
tag := "app-absint-specs"
%%%

Specs are in the package, where the certificates of rules use them ({ref "wip-cert"}[Proofs about runs 1: Certificates for rules]). Their use in an analysis, like the rest of this appendix, is not yet in the package.

The obligation of a rule that is not pure is stated under a _spec_ ({ref "absint-successors"}[An instruction with successors]): what the rule may ask of the machine, what answers it may get, and which exits it may take. A spec also carries a _ghost state_ `g : G`, which a points-to analysis would use for its abstract heap. The analyses of this guide need none, and their lemmas are generic in `G`. Specs are not particular to the analysis. `StrataDyn/Exec/Spec.lean` states them once for every proof about a rule's tree, and the certificates that a rule reaches only the cells it is given take `G` to be a typing of the heap:

```leantext "Specs (StrataDyn/Exec/Spec.lean)"
/-- What a proof about a rule may assume of the machine, and what it requires of the rule, at a
ghost state of type `G`: how the ghost state grows, which requests are allowed and which answers
they may get, which worlds are possible, and which exits are allowed. -/
structure Spec (G : Type) (ε : Eff) (E : Type) where
  /-- The ghost state may grow from the first to the second while a request is served. -/
  Ext : G → G → Prop
  /-- The rule may make this request in this ghost state. -/
  Pre : G → ε.I → Prop
  /-- The machine may answer the request with this value, in this ghost state. -/
  Post : G → (i : ε.I) → ε.O i → Prop
  /-- The machine may hold this world in this ghost state. -/
  World : G → ε.W → Prop
  /-- The rule may take this exit in this ghost state. -/
  Exit : G → E → Prop
```

`V.Sat Q g t` says that the tree `t` meets the spec `V` from the ghost state `g`, with the postcondition `Q` on the values it returns. Its cases follow the constructors of `Sem` ({ref "inside-rules-as-trees"}[Rules as trees]):

```leantext "A tree under a spec (StrataDyn/Exec/Spec.lean)"
/-- **The tree `t` satisfies the spec `V`, with postcondition `Q`, from ghost state `g`**: every
request is allowed, every leaf reached under allowed answers returns a value `Q` holds of or
takes an allowed exit, and every world update keeps the world possible.  A fault is allowed:
a spec says nothing of faults.  A choice may be any number, so every one is covered. -/
def Spec.Sat (Q : G → α → Prop) : G → Sem ε E α → Prop
  | g, .ret a => Q g a
  | g, .stop (.jump e) => V.Exit g e
  | _, .stop (.fault _) => True
  | g, .choose k => ∀ c, Spec.Sat Q g (k c)
  | g, .vis i k => V.Pre g i ∧ ∀ g₁, V.Ext g g₁ → ∀ o, V.Post g₁ i o → Spec.Sat Q g₁ (k o)
  | g, .update f => ∀ w, V.World g w → Spec.SatAfter Q g (f w)
```

### Regions
%%%
number := false
tag := "app-absint-regions"
%%%

The region handles below are in the package. Their analysis, which the rest of this section describes, is not yet in the package.

A rule runs a region through a handle:

```leantext "Handles (StrataDyn/Exec/Sem.lean)"
/-- A region of the operation, with parameters of the Lean types `ts`, yielding an `α`: the
request that runs it on its arguments, and how its answer is the value. -/
structure Region (ε : Eff) (ts : List Type) (α : Type) where
  req : Payload ts → ε.I
  ans : (a : Payload ts) → ε.O (req a) → α

/-- Run region `r` on `args`. -/
@[inline] def runRegion {ε : Eff} {E : Type} {ts : List Type} {α : Type} (r : Region ε ts α)
    (args : Payload ts) : Sem ε E α :=
  .vis (r.req args) fun o => .ret (r.ans args o)
```

`runRegion r args` is one request to the machine, a `vis` node of the rule's tree ({ref "inside-rules-as-trees"}[Rules as trees]). The machine serves it in the middle of the rule. It keeps the rule, with the rest of its tree, as a waiting frame, and runs the region's entry block in a copy of the owner's store, with the region's parameters bound. When the region's body leaves with a value, the machine gives that value to the rule's tree as the answer.

A transfer function's lemma takes a `RegionSpec` for each region ({ref "absint-regions"}[Instructions with regions]): running the region's handle is allowed when the transfer function may run it, and its answer is in the region's abstract value. `#dyn_absint` turns the lemma into the analysis's obligation. For each transfer function with regions, it generates the proof that the table's wrapper meets the transfer function at every spec that allows what the transfer function allows. That proof applies the lemma, and builds each region's `RegionSpec` from what the spec allows of that region's requests and answers.

The checker then supplies one spec, the analysis's own. Under it, a rule that runs in a frame `fr` may request region `j` when the region starts in the facts, and the answer is a value that the region's result admits. No other request is allowed:

```leantext "The analysis's spec for region requests (under development, in StrataDyn/Absint/Core/Frag.lean)"
/-- The requests a rule running in `fr`, with the module's regions `regs`, may make: a region
request whose region starts in the certificate.  Calls and cell requests are not allowed. -/
def ReqPre (fr : Frame M) (regs : List Nat) {rs : List (List Ty × Ty)} :
    MReq M.interp rs → Prop
  | .region j args => ∀ k, regs[j.1]? = some k → RegionEntry m D C fr k args
  | _ => False

/-- The answers the machine may give a rule with the module's regions `regs`: to a region
request, a value that the region's result admits. -/
def ReqPost (regs : List Nat) {rs : List (List Ty × Ty)} :
    (q : MReq M.interp rs) → q.Out Run → Prop
  | .region j _, o => ∀ k, regs[j.1]? = some k → C.Ret (C.region k) ⟨_, o⟩
  | _, _ => True
```

`RegionEntry` says that the region's entry frame, the owner's store with the parameters bound, is in the state at the start of the region's entry block. The checker makes it true. For each region that a transfer function lets run, it checks that the state the rule runs it from, with the region's parameters forgotten, is below the entry state of the region's entry block:

```leantext "The check at a region's entry (under development, in StrataDyn/Absint/Core/Check.lean)"
/-- **Region `k` of `m`, run from the state `s` of its owner, starts in the facts**: `s` is
`isBot`, or the entry state of the region's entry block is above `s` with the block's parameters
forgotten, restricted to the block's support, read from the module's supports `L`. -/
def regionOK (m : LModule M.at) (L : Array (Array Support)) (s : T.S) (k : Nat) : Bool :=
  StateDomain.isBot s || match m.regions[k]? with
    | some rb => match rb.blocks[0]? with
      | some blk => StateDomain.le (StateDomain.restrict (T.enterState s blk)
          ((L.getD (m.funcs.size + k) #[]).getD 0 {})) (T.entryOf F rb 0)
      | none => true
    | none => true
```

The supports `L` are the ones that the checker computes once per module, as the solver does. It checks each region as it checks a function, against the region's own entry states, and checks that the values the region's body leaves with are below the region's result description. So the analysis's spec allows what the transfer function lets run, and answers within the abstract values that the transfer function was given (`allows_frameSpec`). A transfer function's output, lifted to states, gives for each region `none` if the rule does not run it, or the state it runs it from, where `some none` stands for the state before the instruction.

### Dead blocks and settling
%%%
number := false
tag := "app-absint-results"
%%%

The theorems of this section belong to the framework, which is not yet in the package.

From `Analysis.analyze_reach`, `Analysis.exec_not_bot` and `Analysis.entry_not_bot`, no configuration of a run runs in or enters a block whose entry state is `⊥` in every context that analyses the block's body ({ref "absint-result"}[Reading the result]). A test states it for `IvlTVWhile`:

```leantext "A block whose entry state is ⊥ is never reached (under development, in StrataDynTest/Absint/TypedTest.lean)"
public theorem bot_unreached {env : Env Unit} [base ≼ env] {α : Type} {prog : Module env α}
    {m : LModule WhileSem.model.at} (hl : link WhileSem.model prog = .ok m) (hwf : WF m)
    {F : IvlTVWhile.Facts} (ha : IvlTVWhile.analyze m = some F)
    {b : LBody WhileSem.model.at} {i : Nat}
    (hb : ∀ ctx, IvlTVWhile.Internal.analysis.BodyOf F m ctx b →
      StateDomain.isBot (IvlTVWhile.Internal.analysis.entryIn F ctx b i) = true)
    {i₀ : Nat} {args : List (Dyn WhileSem.model.at.interp)}
    {snap : Snapshot WhileSem.model.at} {B : Ty} {s₀ : State WhileSem.model.at}
    {h₀ : StateOK m B s₀} (hs₀ : start hwf i₀ args snap = .ok ⟨B, s₀, h₀⟩)
    {s : State WhileSem.model.at} {hs : StateOK m B s}
    (hp : Reach hwf s₀ h₀ (.running ⟨s, hs⟩)) :
    (s.mode = .exec → s.core.top.func = b → s.core.top.block ≠ i) ∧
      ∀ to : Frame WhileSem.model.at, s.mode = .jump to → to.func = b → to.block ≠ i := by
```

`bot_unreached` names `IvlTVWhile.Internal.analysis`, the analysis that the command builds, to read a block's entry state in each context; the statements that the command generates name none of the framework's internals.

`IvlTVWhile.ascended` and `IvlTVWhile.Settled` ({ref "absint-total"}[Termination]) are the framework's `Analysis.ascended` and `Analysis.SettledFacts` at that analysis. `ascended` is the facts of the solver's ascent, before any narrowing, and `none` if the ascent reaches the cap on rounds:

```leantext "Settled facts (under development, in StrataDyn/Absint/Core/Total.lean)"
/-- **`F` is the facts of what ascending returns on `m`**: of a layout that fits `m` and of
states that fit the layout, are settled (every item that a block of a unit sends from them, and
every unit's start state, is admitted by them) and serve every call's demand.  The `top`
fallback's facts are such facts too; `ascended_settles` says when the solver reaches others. -/
def SettledFacts (m : LModule M.at) (F : Facts T.S (StateDomain.Pay T.S)) : Prop :=
  ∃ Lr A, T.toFacts Lr A = F ∧ T.Ascended m Lr A
```

`Ascended` asks for a layout that fits `m`, and for states that fit the layout, are settled and serve every call. `settles` is `Analysis.ascended_settles`, which follows from `solve_settles`, the theorem about the solver's states, and asks for the instances that `(settles)` checks for. Both take the context allocator. The `top` fallback's facts satisfy `SettledFacts` too, so what rules the fallback out is `ascended m sch = some F` in `settles`: beyond some cap on the rounds, the ascent stops before it reaches the cap.
