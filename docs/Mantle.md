# Mantle

Mantle is a typed intermediate representation for programs, defined in Lean. A front end
translates a source language into Mantle, and analyses and interpreters work on Mantle
rather than on the source language. This document is a self-contained reference for Mantle
itself. How Python is translated into it is described separately.

## 1. Overview

This section introduces the two parts of Mantle and the guarantee that connects them. The
later sections define each part in detail.

Mantle separates the vocabulary a language provides from the programs written in it:

* An **environment** declares the vocabulary: types and instructions. A type is either
  primitive, such as `Int`, or a datatype with constructors, such as `Except`. An
  instruction declaration gives an operation's name and signature, such as an `add` that
  takes two values and returns a value. Apart from constants, every instruction a program
  uses is declared in its environment.
* A **program** is a module of functions written against one environment. A function is a
  set of blocks. A block takes parameters, runs a sequence of instructions, and ends with a
  terminal instruction, such as a jump to another block or a return. Each value is defined
  once and has a type from the environment.

Environments are built in layers. The **base environment** declares what every language
needs while a language's environment refines the base by adding its own types and instructions.
For example, Python's environment adds a value type and the Python operations. We have a general
notion of refinement for environments that captures extending environments with new operations
as well as replacing abstract types with more precise definitions (such as inductive types).
We write `t ⊑ s` to indicate that `s` refines `t`.

Environments and programs come with a well-formedness check. A well-formed environment is one
whose type references all resolve to earlier declarations. A well-formed program uses only
instructions its environment declares, at their declared types, and passes each block the
arguments it expects. Lean's types guarantee that every reference to a type or instruction
resolves; a checker decides the rest.

**Regions.** An instruction may own nested bodies, called regions, as in MLIR. A region is a
list of blocks, the first its entry, whose parameters are the region's arguments. A transfer
inside a region names a block of the same region or the region's exit, so control leaves a
region only through its exit, back to the instruction that owns it. Values defined outside a
region are visible inside it, and values defined inside are local to it; the checker does not
yet enforce this. Regions keep structured constructs structured, so analyses can treat them
directly. The planned first user is the comprehension, as a `forEach` whose body is a region
over the item, with one cell per iteration variable per evaluation, as in CPython.
Instructions such as `if` or `try` can take regions too:

```
%4 : base.Int = demo.if[base.Int](%1) {
  then.0():
    ret(%2)
} {
  else.0():
    ret(%3)
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
  func @m.f(%0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%0 : py.Value):
      %2 : py.Value = py.intLit(1)
      %3 : py.Value = py.add(%0, %2) ^propagate.0()
      %4 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%3)
      ret(%4)
    propagate.0(%5 : py.Value):
      %6 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%5)
      ret(%6)
  }
}
```

* **Values** print as `%n`, with their type where they are defined. A block prints as its
  label and parameters; the entry block's parameters are also the function's.
* **Applications** print as the operation, its type arguments in brackets, its operands in
  parentheses, then its successors, each `^label(args)`, then its regions, each in braces.
  Empty brackets and parentheses are left out: `py.noneLit`, `jump ^done.0()`.
* **Terminators** print as applications without a result. The base's control flow drops
  `base.`: `jump`, `branch(%0) ^t.0() ^f.0()`, `unreachable`. A jump to the exit is
  `ret(%4)`.
* **Names** print dotted, as one identifier, escaped whole when needed: `@|m.<module>|`. A
  function name is marked `@`.
* **Literals** are untagged, and a literal's form fixes its type, with no widening. An
  integer `5` or `-1` is a `base.Int`. A float always has a decimal point or an exponent
  (`1.0`, `0.0025`, `1e22`), and is the shortest decimal that reads back as it, or `inf`,
  `-inf` or `nan`; it is a `base.Float64`, so `1` is never one. A boolean is `true` or
  `false`, a string `"…"`, the unit `unit`, and a function pointer `@m.f`. A bitvector, if
  added, needs a literal syntax that carries its width.

By default each constant a function uses is written at its uses and its line is dropped:
`py.intLit(1)`. The other values keep their ids. `PrintOptions.full` prints every constant on
its own line instead.

`Module.read env text` reads either form against an environment and checks the result
against `Module.WF`. A folded constant comes back as a `const` just before its use, with a
fresh id. Reading and printing in the same form gives the text back. Lines that start with
`--` are comments.
`pymantle read FILE` reads a printed module against the Python environment and prints it
again.
