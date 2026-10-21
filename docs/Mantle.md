# Mantle

Mantle is a typed intermediate representation for programs, defined in Lean. A front end
translates a source language into Mantle, and analyses and interpreters work on Mantle
rather than on the source language. This document is a self-contained reference for Mantle
itself. [Python to Mantle](./PythonToMantle.md) describes how Python is translated into it.

## 1. Overview

Mantle separates the vocabulary a language provides from the programs written in it:

* An **environment** declares the vocabulary: types and instructions. A type is either
  primitive, such as `Int`, or a datatype with constructors, such as `Except`. An
  instruction declaration gives an operation's name and signature, such as an `add` that
  takes two values and returns a value. Apart from constants, every instruction a program
  uses is declared in its environment. Primitive types, datatypes and instructions may have
  type parameters, each ranging over types or over lists of types, such as the argument types
  of a function type `Fn [Int, Bool] Int`. A list may splice in list parameters' elements:
  `[*as, Int]`. The DSL that writes environments accepts at most one splice in a literal, at any
  position, as in `[Int, *as, Bool]`, so that inference from a result type has one answer. An
  instruction's variadic operands are any
  number of one type, or one per element of a list, and a successor's payload may likewise
  pass one value per element of a list; a constructor's fields, a region's parameters and a
  block's parameters are one value each. An application passes an argument
  of its parameter's kind for each type parameter.
* A **program** is a module of functions written against one environment. A function is a
  set of blocks. A block takes parameters, runs a sequence of instructions, and ends with a
  terminal instruction, such as a jump to another block or a return. Each value is defined
  once and has a type from the environment.

Environments are built in layers. The **base environment** declares what every language
needs, and a language's environment refines the base by adding its own types and
instructions. For example, Python's environment adds a value type and the Python
operations. We have a general notion of refinement for environments that captures extending
environments with new operations as well as replacing abstract types with more precise
definitions (such as inductive types).

We write `t ≤ s`, or `t ⊑ s` for the class that instance search uses, when `s` refines `t`:

* **Types:** every type of `t` is a type of `s`, with the same parameters. An abstract type of
  `t` may be a datatype in `s`.
* **Datatypes:** every datatype of `t` is the same datatype in `s`.
* **Instructions:** every instruction of `t` is an instruction of `s` with the same signature.
  An ordinary instruction of `t` may be a constructor or a case instruction in `s`.
* **Annotations:** `≤` requires each annotation of `t` to equal that of its refinement in `s`.
  `Env.LeBy R` relates them by `R` instead.

`s` may declare more than `t`. Refinement ignores positions: the same declarations in another
order refine each other.

Environments and programs come with a well-formedness check. A well-formed environment is one
whose type references all resolve to earlier declarations. A well-formed program uses only
instructions its environment declares, at their declared types, and passes each block the
arguments it expects. Lean's types guarantee that every reference to a type or instruction
resolves; a checker decides the rest. A function is checked on its own, and a module is
checked from its functions: their names are distinct, and every reference to a function names
one of them, at its code type. A function's code type is `base.Fn as r`, with `as` its
parameters' types and `r` its return type, and `base.callCode` calls through a value of that
type. A reference may instead have the untyped `base.Code`, which cannot be called. A `Module.Raw` is a module as built, which may not be well formed; it still
prints, in full, for diagnostics. A `Module` is one with its proof of well-formedness, and is
the same data at run time.

**Scoping.** In an SSA function, block A *dominates* block B when every path from the entry
to B passes through A. The *immediate dominator* of B is the closest block that dominates
it, and the immediate dominators form the *dominator tree*. A value may be used only where
its definition dominates the use. Mantle refines dominance to points within a block: a
block's parameters are in scope from its start, and an instruction's result is in scope
after that instruction. A transfer to one of an instruction's successors, such as an
exception edge, leaves from just before the instruction, so a handler cannot see the result
of the instruction that raised.

The IR stores no dominance information. A well-formed function has every block reachable from
its body's entry, and for each body *some* legal tree puts every use in scope. A tree gives
each block other than the entry a parent, a point of the body: another block after some of its
instructions. It is legal when every chain of parents reaches the entry and every transfer into
a block leaves from the block's parent or a point below it in the tree. The rule names no
algorithm. The checker computes the immediate-dominator tree and checks the uses against it.
That tree is proved legal and, when every block is reachable, exact: a point's ancestors in it
are exactly its dominators. So the check accepts exactly the functions that some legal tree
scopes, and these are exactly the dominance-correct ones. The builder drops the blocks the
entry cannot reach, so a producer leaves dominance to the checker. When a function it reads is
not well formed for these reasons, the reader names each unreachable block, and each use out of
scope with a path from the entry that reaches it without passing its definition.

**Regions.** An instruction may own nested bodies, called regions, as in MLIR. A region is a
list of blocks, the first its entry, whose parameters are the region's arguments. A transfer
inside a region names a block of the same region or the region's exit, so control leaves a
region only through its exit, back to the instruction that owns it. A region's blocks have
trees of their own, rooted at its entry. Values in scope at the owning instruction
are visible inside the region, and values defined inside are local to it. Regions keep
structured constructs structured, so analyses can treat them directly. The first user is the
comprehension, as a `py.forEach` whose body is a region over the item, with one cell per
iteration variable per evaluation, as in CPython. An `if` whose branches are regions:

```
%r.0 : base.Int = demo.if[base.Int](%c.0) {
  then.0():
    ret(%x.0)
} {
  else.0():
    ret(%y.0)
}
```

**Annotations.** Every part of a program carries an annotation of a type the front end chooses,
such as a source position, so that results can be reported against the original source.
Mantle does not depend on annotations for its semantics.

Mantle is implemented in the directory `StrataMantle`. Declarations are defined in
the namespace `Strata.Mantle`.

## 2. Printed form

A module prints as text, through a Strata DDM dialect (`StrataMantle/DDM.lean`), and the
text reads back (`StrataMantle/DDMRead.lean`):

```
module m {
  func @m.f(%x.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%x.0 : py.Value):
      %int.0 : py.Value = py.intLit(1)
      %add.0 : py.Value = py.add(%x.0, %int.0) ^propagate.0()
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%add.0)
      ret(%ret.0)
    propagate.0(%exc.0 : py.Value):
      %exc.1 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.0)
      ret(%exc.1)
  }
}
```

* **Values** print by name, `%x.0`, with their type where they are defined.
* **Blocks** print as their label and parameters; the entry block's parameters are also the
  function's.
* **Applications** print as the operation, its type arguments in brackets, its operands in
  parentheses, then its successors, each `^label(args)`, then its regions, each in braces.
  Empty brackets and parentheses are left out: `py.noneLit`, `unreachable`. A list of types
  prints as a literal, as a type argument or inside a type:
  `fns.callFn[[base.Int, base.Bool], base.Int](%g.0, %x.0, %y.0)`.
* **Terminators** print as applications without a result. The base's control flow drops
  `base.`: `jump ^done.0(%v.0)`, `branch(%c.0) ^some.0() ^none.0()`, `unreachable`. A jump
  to the exit is `ret(%ret.0)`.
* **Names** print dotted, as one identifier, escaped whole when needed: `@|m.<module>|`. A
  function name is marked `@`.
* **Literals** are untagged, and a literal's form fixes its type, with no widening. An
  integer `5` or `-1` is a `base.Int`. A float always has a decimal point or an exponent
  (`1.0`, `0.0025`, `1e22`), and is the shortest decimal that reads back as it, or `inf`,
  `-inf` or `nan`; it is a `base.Float64`, so `1` is never one. A boolean is `true` or
  `false`, a string `"…"`, the unit `unit`, and a function pointer `@m.f`.
* **Constants** are written at their uses by default, as in `py.intLit(1)`.
  `PrintOptions.full` prints each on its own line instead: `%c.0 : base.Int = const 1`, then
  `py.intLit(%c.0)`.

`Module.format` prints a `Module`, folded by default. `Module.read env text` reads either form
against an environment and returns a `Module`, or the diagnostics. Reading and printing in
the same form gives the text back. Lines that start with `--` are comments. `pymantle read
FILE` reads a printed module against the Python environment and prints it again.
