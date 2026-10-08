# Translating Python to Mantle

This document specifies how each Python construct lowers into Mantle, the project's typed SSA
intermediate representation. It is written for whoever implements the translator from the
Python AST (`StrataPython.stmt` / `StrataPython.expr`) to a Mantle `Module` over Python's
environment. Section 1 introduces as much Mantle as the examples need. Mantle itself is
specified in [`Mantle.md`](./Mantle.md).

The scope is the Python subset the front end analyses: functions, classes, closures,
control flow, exceptions, `with`, and comprehensions. Generators, `async` and `match` are
rejected (§6.9). The gaps this spec found in the environment and builder are listed in §8.

**The translator** is `PyTranslate.translate` in `StrataPython/Mantle/Translate.lean`. §11
marks what it implements, and the module docstring has a recipe for adding a construct.
`pymantle mantle FILE` prints the diagnostics and the module for a `.py` or Python Ion file.
The tests are the programs `NAME.py` in `StrataPythonTest/Mantle/mantle_tests/`.
`StrataPythonTestExtra/MantleTranslateTest.lean` runs every one, as listed in
`StrataPythonTest/Mantle/mantle_tests.txt`, and compares each one marked supported with its
golden, `NAME.expected.mantle` beside `NAME.py`.

**Design decisions.** Every local is a cell declared in the entry block. The translator does
no SSA construction: promoting cells to SSA values is a later ref-to-reg pass. Control flow is
plain blocks plus completions (§4, §7). The one region-based construct is the comprehension
(§6.8). Loops and `try` as regions are a future refinement (§9, Q1). Name resolution and
comprehension scoping follow CPython 3.12.

## 1. Mantle in brief

**Environments and programs.** An *environment* declares types and instructions. A
*program* is a module of functions written against one environment. The *base*
environment declares the datatype `base.Unit` with the one constructor `base.unit`,
`base.Bool`, `base.Int`, `base.Float64`, `base.String`, `base.Sequence a`, `base.Ref a` (a
mutable cell), `base.Code` (an opaque code pointer) and the datatype `base.Except e a` with
constructors `base.ok` and `base.error`. It also declares
the cell instructions `base.refNew`, `base.refGet` and `base.refSet`. Python's environment
extends the base (§2).

**Signatures.** An instruction's signature is written in the environment DSL:

```
insn refGet [a] (cell : Ref a) : a                         -- type parameter a
insn add (lhs rhs : Value) (^err (exc : Value)) : Value    -- a successor named err
insn try [a] (&body : Completion a) : Completion a         -- a region named body
```

**Functions and blocks.** A function is a list of *blocks*. The first block is the entry,
and its parameters are the function's parameters. Each block has a *label* such as `bb.3`,
takes typed parameters, runs a sequence of instructions, and ends with one *terminator*.
Every value is defined exactly once, either as a block parameter or as an instruction
result, and has a type. Block parameters take the place of phi nodes.

**Instructions.** There are two kinds, and each defines a result:

| Kind | Meaning |
|---|---|
| `const` | a literal of a base type (`unit`, `bool`, `int`, `float`, `str`), or `const @m.f`, a `base.Code` pointer to the function `m.f` of the same module |
| `apply` | an application of a declared instruction, including a datatype constructor, at explicit type arguments |

**Successors.** An instruction may declare *successors*: blocks it transfers to instead of
falling through. A successor site is a label with a prefix of that block's arguments already
bound. The instruction supplies the rest. The `err` successor of a raising Python operation
supplies the exception. So `^h(%7)` passes `%7` and then the exception to block `h`.

**Terminators.** A block ends with an application of a *terminal* instruction: one that never
falls through and leaves by one of its successors. A terminal instruction has no result type.
The base declares the control flow:

```
terminal insn jump (^k)                      -- go to k
terminal insn branch (cond : Bool) (^t ^f)   -- t if cond holds, else f
terminal insn unreachable                    -- control never gets here
```

For each datatype `T`, `Env.addData` declares the terminal instruction `T.case` with the
datatype, so a hand-written `T.case` is rejected:

```
terminal insn T.case [params] (scrutinee : T params) (^c₁ (fields…)) …
```

It has one successor per constructor, in declaration order, and each receives that
constructor's fields after its own pre-bound arguments. `base.Except.case` has the
successors `ok (value : a)` and `error (err : e)`.

**Returning.** Each function and each region has an implicit exit label, `Label.exit`, whose
parameters are its result type. `ret v` is a `jump` to the exit passing `v`. No block is
labelled with the exit.

**Regions.** An instruction may own *regions*: nested lists of blocks, like MLIR's. A transfer
may name only a block of its own region, or that region's exit. An inner region's exit is its
own, so `ret` inside a region leaves the region with a value. Values defined outside are
visible inside.

**Well-formedness**, as `StrataMantle/WF.lean` checks it. These rules constrain the translator:
labels are unique function-wide; no transfer targets an entry block; every operand is
defined, with the type its use demands; every successor supplies exactly what its target's
parameters declare; a terminator applies a terminal instruction, and no other instruction
does. The checker does not yet check where a value is used: it accepts a use before its
definition, a use of a value outside the region that defines it, and a handler's use of the
result of the operation that failed. The translator must still make every use dominated by
its definition, because ref-to-reg will rely on it.

**Printed syntax.** This is what `Func.toString` prints. Each example in this document is in
that form. `--` comments and `…` elisions are added for the reader. Readable labels such as
`head.0` are what the translator passes to `freshLabel`. A function name prints with an `@`
prefix, in its definition and in a `const`. Each successor prints with a `^` prefix. A
terminator prints as an application without a result, so a case is
`base.Except.case[base.String, base.Int] %4 ^ok.0() ^err.0()`. The base's terminal
instructions drop `base.`: `jump ^done.0()`, `branch %0 ^bump.0() ^done.0()` and
`unreachable`. A jump to the exit prints as `ret %5`.

```
func @m.f(%0 : py.Value) -> base.Except(py.Value, py.Value) {
  entry.0(%0 : py.Value):
    %4 : base.Int = const int 1
    %5 : py.Value = py.intLit %4                       -- apply, no successors
    %6 : py.Value = py.add %0 %5 ^propagate.0()        -- err successor, nothing pre-bound
    %9 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value] %6
    ret %9                                             -- jump to the exit, passing %9
  propagate.0(%10 : py.Value):                         -- receives the exception
    …
}
```

## 2. Python's environment

The environment is `StrataPython/Mantle/Env.lean`, namespace `py`. The emission helpers
are in `StrataPython/Mantle/Build.lean`.

- **One value type.** Every Python value has type `py.Value`. Base types appear only where
  a value is not a Python value: a `base.String` attribute name, a `base.Int` literal before
  boxing, the `base.Bool` that a `branch` needs, and the `base.Unit` result of an operation
  that only acts.
- **Raising operations.** Every operation that can raise declares an `err` successor, which
  receives the exception as a `py.Value`. The operation's result is its success value. The
  translator passes the label of the enclosing handler as `err`.
- **Total operations** have no successors. These are the literals, `undef`, `isDefined`,
  `is`/`isNot`, `mkTuple`/`mkList`/`mkKwargs`, `listToTuple`, `mkSlice`, `tupleLen`,
  `dictLen`, `dictGet`, `dictFirstKey`, `dictDiscard`, `listAppend`, `isStopIteration`,
  `globalCell`, `mkClosure` and `unsupported`. `mkSet` and `mkDict` raise, because hashing a key runs `__hash__` and
  `__eq__`.
- **Cells.** A cell is a `base.Ref(py.Value)`, a mutable location. Every Python local is a
  cell: `refNew` creates it, `refSet` writes it and `refGet` reads it. A cell that has not
  been assigned holds `py.undef "x"`. A later *ref-to-reg* pass promotes cells that do not
  escape into SSA values and block parameters. The translator never decides block
  parameters for locals.
- **Globals.** `py.globalCell module name` is the cell of a module global: the same cell for
  the same arguments, read and written like a local's. It holds `undef` until the first
  assignment, and `del` writes `undef` back. `module` is always fully qualified (`"a.b"`).
- **Imports.** `py.importModule module` returns the module object, importing it and each
  package above it first if need be. `py.importFrom module name` imports `module` and reads
  its attribute `name`, falling back to the submodule `module.name` as CPython's
  `IMPORT_FROM` does. Both raise `ImportError`, or whatever the module body raises.
  `py.qualifiedRef module name` reads `module.name` at each use; the translator uses it only
  for builtins.
- **Definedness.** Only `isDefined`, `requireDefined` and `requireUndefined` may consume a
  value that could be `undef`. `requireDefined v excType msg` passes `v` through, or raises
  `excType(msg)` if `v` is undefined.
- **Completions.** `py.Completion` records how a protected block finished. It is a datatype
  whose five constructors are instructions:
  `completionNormal`, `completionReturn (value)`, `completionRaise (exc)`, `completionBreak`
  and `completionContinue`. `py.Completion.case` has five successors in that order. Only the
  `return` and `raise` successors receive a payload.
- **Closures.** `const @m.f` is a `base.Code`, and `py.mkClosure code cells…` pairs it with
  captured cells to make a callable `py.Value`. `py.call f args kwargs` calls any callable.
- **Function results.** A translated function returns `base.Except(py.Value, py.Value)`.
  `base.ok v` is a normal return and `base.error e` propagates an exception to the caller.
  `py.call` receives `error e` and transfers it to its own `err` successor.

## 3. Conventions

**Function shape.** Every function the translator emits is built by
`PyBuild.buildFuncTypedWith`, which also returns the body's result; the translator returns its
own state through it (§4).
Its parameters are:

| Function | Parameters, in order |
|---|---|
| a `def`, `lambda`, or class body | captured cells `base.Ref(py.Value)`…, then `args : py.Value` (a tuple) and `kwargs : py.Value` (a dict) |
| the module body | none |

`buildFuncTypedWith` installs `propagate.0(exc)`, which returns `base.error exc`. It is the
handler wherever no `try` or `with` encloses the code.

**Entry block.** In order: one `declareLocal` per local and cell variable of the scope
(§5.1), then the argument-binding prologue (§5.4), then the body. Every cell is declared in
the entry, so it dominates every use. A comprehension's iteration variables are the
exception (§6.8).

**Function names.** A Mantle module holds one Python module `m`, and is named `m`, one
segment per dotted component (`a.b`). Its functions are named under `m`, following the
scope's `__qualname__`. Function names and instruction names are separate namespaces, and a
function name prints with an `@` prefix: `@m.add` is a function, `py.add` an instruction. A
segment in angle brackets cannot collide with a Python identifier; the printer quotes it, as
in `@m.|<module>|`. The translator implements the first, second and last rows (`allocName`).

| Source | Name |
|---|---|
| module body | `m.<module>` |
| `def f` at top level, `def g` inside `f` | `m.f`, `m.f.g` |
| method `meth` of class `C`, body of `C` | `m.C.meth`, `m.C.<body>` |
| `lambda` | `m.f.<lambda>.k`, where `k` counts per enclosing function |
| a name the module already uses | a numeric suffix: a second `def f` is `m.f.1` |

**Annotations.** The translator wraps each statement and each expression in
`withRange node.ann`, which sets the builder's default annotation (`withInfo`). Everything the construct emits, including synthesized blocks and
prologue code, carries that source range.

**Reachability.** The builder has an *open block* when instructions can still be emitted
(`Build.State.label` is some label). A statement that ends the open block is `return`,
`raise`, `break` or `continue`, or a compound statement all of whose paths do so. After it,
the remaining statements of the same body are unreachable, and the translator skips them.
A join block is started only if some transfer targets it.

**Rejection.** The translator rejects any construct listed as unsupported, and, for now, any
construct it does not implement yet (§11). Rejection records a diagnostic at the construct's
range in `Result.diagnostics`, and translation continues so that every error is reported. A
result with a diagnostic is failed (`Result.ok` is false). A rejected expression becomes
`py.unsupported` applied to a `py.strLit` of the construct's name, which keeps the function
well formed. A rejected statement emits nothing. A rejected function (a generator or
`async def`) is emitted as a stub whose entry block returns `py.unsupported`. Consumers must
not analyse a failed result. A compile-time error that the scope pass reports (§5.1) is
handled the same way.

## 4. Translator state

The translator runs in
`TransM = ReaderT Ctx (StateT TState (PyM SourceRange))`, with
`PyM α = StateT Frame (BuildM Py.env α)` below it. `Build.State`, the generic builder state,
holds value ids, labels, the open block and the default annotation. `Frame` holds the
emission state of the Python builder. `Ctx` is fixed while one function is translated, and
`TState` accumulates:

| State | Field | Exists? | Set by |
|---|---|---|---|
| enclosing handler: the block every raising operation names as `err` | `Frame.handler : BlockValue` | yes | `buildFuncTypedWith` (`propagate.0`), `withHandler` and `withHandlerTo` (`try`, `with`, `for`) |
| locals: name ↦ cell | `Frame.locals` | yes | `declareLocal` |
| scope: the `PyScope.Table` and the current `ScopeId`, giving each name's kind (`local`, `cell`, `free`, `globalExplicit`, `globalImplicit`). Imports are `Table.imports`, a separate list of fully qualified targets | `Ctx.table`, `Ctx.scope` | yes | `PyScope.analyze` (§5.1), `transFunc` |
| the Python module name, the Mantle module name, the names some scope binds as globals, the function's `__qualname__` | `Ctx.module`, `Ctx.moduleName`, `Ctx.globals`, `Ctx.qualname` | yes | `translate`, `transFunc` |
| diagnostics | `TState.diagnostics` | yes | `reject` |
| functions to emit after the current one, and the names taken | `TState.pending : Array FuncJob`, `TState.funcNames` | yes | `defStmt`, `allocName` |
| exits stack (below) | `TState.exits : Array Exit` | yes, `loop` only | `withExit`: loops; later `try`/`finally`, `with`, `except … as` |
| the labels some emitted transfer names, for starting join blocks | `TState.targeted` | yes | `jump`, `branch` |
| exception being handled, for bare `raise` | `currentExc : Option ValId` | **add** | `except` bodies |
| namespace dict, inside a class body | `classNs : Option ValId` | **add** | class body functions |
| default annotation | `Build.State.info` | yes | `withRange` |

A `def` binds its name where it runs, and queues a `FuncJob`; `translate` emits the module
body first, then each queued function, in order.

The **exits stack** records every enclosing construct that a `break`, `continue` or `return`
must pass through, innermost last. `Exit` has the `loop` constructor; `cleanup` and `unbind`
are to add:

```
inductive Exit
  | loop    (brk cont : Label)    -- break → brk, continue → cont
  | cleanup (fin : Label)         -- try/finally or with: fin takes a py.Completion
  | unbind  (cell : ValId)        -- except … as e: clear e when leaving
```

**The exit walk** (`exitWalk`). An abrupt exit `k` (break, continue, or return `v`) is
emitted by walking the stack from the innermost entry outward:

| Entry | `break` | `continue` | `return v` |
|---|---|---|---|
| `loop brk cont` | `jump ^brk()`, stop | `jump ^cont()`, stop | skip |
| `cleanup fin` | `%c = py.completionBreak`, `jump ^fin(%c)`, stop | `py.completionContinue`, likewise | `py.completionReturn v`, likewise |
| `unbind cell` | write `undef` to `cell`, keep walking | same | same |
| stack empty | a diagnostic | a diagnostic | `emitReturn v` |

Exceptions do not use the walk. `Frame.handler` already names the right block at every
point, because each construct that intercepts exceptions installs its own handler.

## 5. Module, functions and names

### 5.1 Scopes

Name resolution runs once per module, before any emission:
`PyScope.analyze` (`StrataPython/Mantle/Scope.lean`) returns a `Table`, matching CPython
3.12's `symtable`. The table has one `Scope` per module, function, `lambda`, class body,
generator expression and list, set or dict comprehension, in preorder. Each scope records its kind, `__qualname__`, parameters,
cell variables (`cellVars`), free variables (`freeVars`), and a `Symbol` per name with one of
five kinds:

| Kind | Meaning |
|---|---|
| `local` | bound in this scope (assignment, augmented assignment, `for`/`with`/`except … as` target, `def`, `class`, `import`, parameter, walrus, `del`) and not declared `global` or `nonlocal`. At module level a `local` is a module global |
| `cell` | a function's `local` that a nested scope uses. It is the same cell, captured |
| `free` | bound in an enclosing function, or declared `nonlocal`. It arrives as a captured cell parameter. A function between the binding and the use gets the name as `free` too, and passes the cell on |
| `globalExplicit` | declared `global` |
| `globalImplicit` | bound in no enclosing function: a module global or a builtin. Which one is decided at run time |

The pass also:

- skips class bodies when resolving names in nested scopes, as Python does;
- mangles private names in a class (`__x` in class `C` is `_C__x`); symbols hold the
  mangled name;
- sets `Scope.needsClassCell` on a class body when a method reads `__class__` or `super`
  (any load of the name, not only a zero-argument call);
- reports CPython's compile-time scope errors (`nonlocal` with no binding, a name used before
  its `global` declaration, a duplicate parameter, the walrus restrictions in
  comprehensions, `'yield' inside list/set/dict comprehension` and `'yield' inside
  generator expression`), and the compiler's `keyword argument repeated`, as `syntaxError`
  diagnostics;
- rejects relative imports, `import *`, `match`, `type` statements and type parameters with
  `unsupported` diagnostics;
- lists every import in `Table.imports`, separately from the symbols. Each `Import` holds
  the bound name, its fully qualified target (`module "a.b"` or `member "a.b" "x"`), and the
  module the statement loads.

**Comprehensions.** A generator expression is a `comprehension` scope: a function whose one
parameter, `.0`, is the outermost iterable, evaluated by the enclosing scope. A list, set or
dict comprehension is an `inlinedComprehension` scope (PEP 709): a region of the enclosing
scope, which also evaluates its outermost iterable. Its symbols say how names resolve inside
it:

- `local` or `cell`: an iteration variable, bound in the region apart from any binding of
  the same name outside it. `Scope.regionLocals` lists them.
- `free`: the name as the enclosing scope resolves it. In a class body this skips the
  class dict.
- `globalExplicit` or `globalImplicit`: a global.

The enclosing scope also lists each name the comprehension uses that it does not already
have. A name the comprehension only reads keeps the enclosing scope's classification and
is not a cell. An iteration variable that a scope nested in the comprehension captures is
flagged `comp_cell` (`Symbol.uses.compCell`) in the enclosing scope. There it is a `cell`,
except in a class body, where it stays `local`.
A walrus target is the enclosing function's `local`, and a `cell` only if a nested scope
captures it; at module level it is a global. Lambdas and generator expressions nested in a
comprehension are children of the enclosing scope, with qualnames such as
`f.<locals>.<lambda>`.

The reference is CPython 3.12's `symtable` (3.13 gives the same output).
`StrataPythonTestExtra/PyScopeTest.lean` runs the pass over every program in
`StrataPythonTest/Mantle/mantle_tests/`, the translator's tests too, and compares it with
`NAME.symtable`, the program's `symtable` output, and `NAME.expected.scope`, a golden dump.
`e01`–`e21` are programs with compile-time errors. `p38` uses `type` statements, which the pass
rejects, so it has no `symtable` comparison.

**Reading a name.** The lowering depends on the name's kind and on the kind of scope it is
read in:

| Kind, scope | Lowering | Exception if unassigned |
|---|---|---|
| `local`, `cell`, `free`, in a function | `refGet` the cell, then `requireDefined` | `UnboundLocalError: cannot access local variable 'x' where it is not associated with a value`; for `free`, `NameError: cannot access free variable 'x' …` |
| `globalExplicit`, `globalImplicit`, or `local` at module level; not a builtin name | `readGlobal m "x"`: `refGet (globalCell m "x")`, then `requireDefined` | `NameError: name 'x' is not defined` |
| the same, `x` a builtin name that some scope binds as a global | `refGet (globalCell m "x")`, `isDefined`, then a branch. Defined: use the value. Undefined: `py.qualifiedRef "builtins" "x"` | none |
| the same, `x` a builtin name that no scope binds as a global | `py.qualifiedRef "builtins" "x"` | none |
| any kind, in a class body | §6.7 | |

An imported name is read as any other name of its kind: the import statement wrote its cell
(§6.1). The builtin names are those of CPython 3.12's `builtins` module
(`PyTranslate.builtinNames`). The names some scope binds as globals are those the module
binds, those a function declares `global` and binds, and `__name__` (`moduleGlobals`).

```
    %12 : py.Value = base.refGet[py.Value] %3
    %13 : base.String = const str "UnboundLocalError"
    %14 : base.String = const str "cannot access local variable 'y' where it is not associated with a value"
    %15 : py.Value = py.requireDefined %12 %13 %14 ^propagate.0()
```

The builtin fallback, for `len` read in a function:

```
    %20 : base.Ref(py.Value) = py.globalCell %18 %19   -- "m", "len"
    %21 : py.Value = base.refGet[py.Value] %20
    %22 : base.Bool = py.isDefined %21
    branch %22 ^join.0(%21) ^builtin.0()
  builtin.0():
    …                                                -- %25 = py.qualifiedRef "builtins" "len"
    jump ^join.0(%25)
  join.0(%26 : py.Value):
```

`requireDefined` is emitted on every read. Removing redundant checks is a later pass.
**Writing** a name is `refSet` on its cell: `writeCell` for a function's cell, `writeGlobal m
"x"` for a global or a module-level `local`. In a class body, writing is
`py.setItem ns "x" v` (§6.7).

### 5.2 Module body

The top-level statements become `m.<module>`, with no parameters. Every name the module
binds is a global: reads and writes go through `globalCell m "x"` (§5.1), and the body
declares no locals. Module-level `def`, `class` and `import` statements run in place and bind
their name when control reaches them. The function falls off the end with `emitReturnNone`.
`__name__` is a global holding `py.strLit m`.

### 5.3 `def` and `lambda`

At the definition site, in source order:

1. Evaluate the decorators, top to bottom.
2. Evaluate each non-constant default value into a fresh *default cell*.
3. Emit `const @m.f…` and `py.mkClosure code cells…`. The cells are the callee's free
   variables in `freeVars` order (§6.6), then its default cells. A top-level function has
   only default cells.
4. Apply the decorators bottom to top, each with `py.call d (mkTuple f) mkDict`.
5. Write the result to the name's cell (a `lambda` is an expression and has no name).

```
    %20 : base.Code = const @m.outer.inner
    %21 : py.Value = py.mkClosure %20 %3            -- %3: outer's cell for x
    %22 : base.Unit = base.refSet[py.Value] %4 %21  -- inner = …
```

Annotations are not evaluated, as under Python 3.14's deferred annotations.

**Python semantics to preserve:** defaults are evaluated once, at definition time, in the
enclosing scope. Free variables are bound late: a read sees the latest write to the cell.

### 5.4 The argument-binding prologue

A call passes one positional tuple and one keyword dict. Binding them to the source
signature is the callee's job, done by a branch-free *prologue* of ordinary instructions at
the top of the entry block. Each check raises, so the prologue stays in one block.
`PyTranslate.prologue` emits it. Each bound parameter is written to its cell, a
non-constant default is read from its default cell, and the raising checks name
`Frame.handler` as `err`. The translator implements constant defaults; it rejects
non-constant ones.

`fill` holds one slot per positional parameter: its default, or `undef` if it has none.
`pad` is the argument tuple padded to full length, so parameter `i` is `pad[i]` with no
bounds test. A parameter may arrive by keyword instead, so its value is
`kwargs.get(name, pad[i])`, one instruction and no branch; a positional-only parameter skips
that lookup, which excludes it from keyword matching. `*rest` and `**kw` are fresh, as in
CPython: `**kw` is `kwargs` with every named parameter discarded, leaving exactly the
unmatched keywords.

| Step | Lowering |
|---|---|
| fill | `fill = mkTuple [default or undef "p", …]`, one slot per positional parameter |
| pad | `pad = py.add args (getSlice fill (tupleLen args) None None)` |
| positional `p` at index `i` | `getItem pad i`, then `dictGet kwargs "p" ⟨that⟩`, then `dictDiscard kwargs "p"`. A positional-only parameter skips the keyword lookup |
| `*rest` | `getSlice args maxPos None None` |
| keyword-only `p` | `dictGet kwargs "p" (default or undef)`, then `dictDiscard` |
| `**kw` | `kwargs` after all the discards |
| check 1 | given both positionally and by keyword: `py.in`, `py.lt`, `py.mult`, then `requireAtMost … 0` |
| check 2 | an unexpected keyword (only without `**kw`): `dictFirstKey kwargs (undef)`, then `requireUndefined` |
| check 3 | too many positional arguments (only without `*rest`): `requireAtMost (tupleLen args) n` |
| check 4 | a required parameter is missing: `requireDefined` |

The checks run in CPython's error-precedence order, 1 to 4, after every value has been
computed, so a call wrong in several ways reports what CPython reports. Check 1 tests keyword
membership before the `dictDiscard` that consumes the name. `dictDiscard` mutates `kwargs` in
place. That is safe because every call site builds a fresh dict (§6.3).

The prologue differs from CPython only in error wording:

- several missing parameters are reported one at a time, where CPython reports them together
  ("missing 2 required positional arguments: 'x' and 'y'");
- a keyword naming a positional-only parameter is reported as an unexpected keyword, where
  CPython says "got some positional-only arguments passed as keyword arguments". With `**kw`
  it is absorbed into `**kw`, as in CPython.

### 5.5 `return`

Evaluate the value (`None` if absent), then perform the exit walk (§4). If no `cleanup` entry
is on the stack, the walk ends in `emitReturn v`, which emits `base.ok` and then `ret`, the
jump to the function's exit.

## 6. Statements and expressions

### 6.1 Simple statements

| Statement | Lowering | Semantics to preserve |
|---|---|---|
| `e` | evaluate it, then discard the result | |
| `pass` | nothing | |
| `x = e`, `a = b = e` | evaluate `e` once, then assign it to each target left to right | |
| target `x` | `refSet` on the cell (§5.1) | |
| target `o.a` | evaluate `o`, then `py.setAttr o "a" v` | Python evaluates the right-hand side first, then `o` |
| target `o[k]` | evaluate `o` and `k`, then `py.setItem o k v` | right-hand side first, then `o`, then `k` |
| target `a, b` / `[a, b]` | `t = py.unpackSeq v 2` (§8), then `getItem t i` for each target, recursively | an exact length check, `ValueError: not enough / too many values to unpack` |
| target `a, *b` | `py.unpackEx v before after` (§8) | |
| `x op= e` | read `x` once (evaluating `o` and `k` once for `o.a` and `o[k]`), apply the in-place operation, write back | in place: `xs += ys` mutates `xs`. Until in-place operations are declared (§8), the binary operation is used and the divergence is documented |
| `x: T = e` | as `x = e`. The annotation is not evaluated | `x: T` with no value only makes `x` local |
| `del x` | `requireDefined` (raises `NameError` or `UnboundLocalError`), then `refSet` of `undef "x"` | |
| `del o.a`, `del o[k]` | **rejected** until `py.delAttr` and `py.delItem` exist (§8) | |
| `assert c` | as `assert c, m`, with `AssertionError` called on no arguments | |
| `assert c, m` | `c` as a condition (§6.2). The true target continues; the false target evaluates `m`, then `py.call`s the `AssertionError` class on it, then raises (§7.1) | `c` is tested once; `m` is evaluated only when the assertion fails; `AssertionError` is the class itself, as CPython's `LOAD_ASSERTION_ERROR`, even if `builtins.AssertionError` is rebound |
| `global x`, `nonlocal x` | nothing: the scope pass makes `x` `globalExplicit` or `free` | |
| imports | below | |

**Imports.** Each `Import` in `Table.imports` is lowered where its statement is, and writes
the bound name's cell: `writeGlobal` at module level, `writeCell` in a function.

| Statement | Lowering | Binds |
|---|---|---|
| `import a` | `importModule "a"` | `a` |
| `import a.b.c` | `importModule "a.b.c"`, then `importModule "a"` | `a`, to the second result |
| `import a.b as c` | `importModule "a.b"` | `c` |
| `from a.b import x as y` | `importFrom "a.b" "x"` | `y` |
| `from . import x`, `import *` | **rejected** by the scope pass | |

`importFrom` runs once, at the import statement, and the bound value is a snapshot: a later
assignment to `a.b.x` does not change `y`. `a.b.f` after `import a.b` is two `py.attr` reads
on the module value.

### 6.2 `if`

```
    %9 : base.Bool = py.truthy %8 ^propagate.0()
    branch %9 ^then.0() ^else.0()
  then.0():
    …
    jump ^join.0()
  else.0():                -- the else body, or empty
    jump ^join.0()
  join.0():
```

`elif` is a nested `if` in the else branch. Truthiness is `py.truthy`, which raises, because
`__bool__` and `__len__` are arbitrary code.

**Conditions.** Every place Python tests a value for truth lowers the test to branches, as
CPython's `compiler_jump_if` does (`transCond`): `if`/`elif`, `while`, `x if c else y`,
`assert`, a comprehension's `if` and, once supported, a `match` guard. `not x` swaps the targets, `and`/`or`
branch on each operand, `x if c else y` branches on `c`, and a chained comparison branches on
each link. Any other test is `truthy` of its value. So `if (a and b) or c:` tests `a`,
`b` and `c` at most once each, while the value `(a and b) or c` tests `a` twice when it is
false, as in CPython.

### 6.3 Expressions

| Expression | Lowering |
|---|---|
| `1`, `1.5`, `"s"`, `b"s"`, `True`, `None` | `PyBuild.intLit` etc.: a `const` and its boxing operation |
| `...` | `py.qualifiedRef "builtins" "Ellipsis"` |
| complex literal, t-string | **rejected** |
| name | §5.1 |
| `a op b` | evaluate `a`, then `b`, then `py.add`/`sub`/`mult`/`div`/`floorDiv`/`mod`/`pow`. `@`, `<<`, `>>`, `&`, `\|`, `^` are **rejected** until declared (§8) |
| `-a`, `not a` | `py.uSub`, `py.not`. Unary `+` and `~` are **rejected** until declared |
| `a < b` (single comparison) | `py.lt`, …, `py.in`, `py.notIn`, `py.is`, `py.isNot` |
| `a < b < c` | evaluate `a`, `b`, then `%r = py.lt`. `truthy %r`, then branch: true evaluates `c` and compares `b` with `c`; false jumps to `join(%r)`. `b` is evaluated once |
| `a and b` / `a or b` | see the example below |
| `x if c else y` | `c` as a condition (§6.2). Each side jumps to `join(v)` |
| `f(…)` | see the calls paragraph below |
| `o.a` | `py.attr o "a"`. Inside a class, `a` is mangled, as in CPython (`self.__a` reads `_C__a`); a keyword argument name is not |
| `o[k]` | `py.getItem o k` |
| `o[i:j:s]` | `py.getSlice o i j s`, with `None` for an absent bound |
| `o[i:j, k]` (a slice inside a tuple) | `py.mkSlice i j None`, as CPython's `BUILD_SLICE`, then `k`, then `mkTuple`, then `py.getItem` |
| `(a, b)`, `[a, b]`, `{a, b}` | `py.mkTuple` / `mkList` / `mkSet` over the evaluated elements |
| `[a, *xs, b]`, `{a, *xs, b}` | as CPython: `mkList` (`mkSet`) of the elements before the first `*x`, then `listExtend` (`setUpdate`) for each `*x` and `listAppend` (`setAdd`) for each later element |
| `(a, *xs, b)` | the list display, then `listToTuple` |
| `{k: v, **d}` | as CPython: `py.mkDict k v …` for each run of pairs (keys and values interleaved, each key before its value), and `py.dictUpdate` for each `**d`, last one winning. The first run is the dict; a later run is built, then added by `dictUpdate` |
| a set of more than 30 elements, a long dict run | as CPython (`STACK_USE_GUIDELINE`): a set starts empty and adds each element as it is evaluated (`setAdd`). A dict run is cut into chunks of 17 pairs; a chunk of more than 15 pairs starts empty and adds each pair (`dictSet`), and each later chunk is added by `dictUpdate`. So an unhashable key raises before the next element is evaluated |
| `f"a{x}b"` | `py.strConcat` over `strLit` parts and `py.fmtValue x`. `{x!r}` applies builtins `repr` first (`str`, `ascii` likewise). `{x:spec}` calls builtins `format(x, spec)`, where `spec` is itself a joined string |
| `(x := e)` | evaluate `e`, `refSet` the target's cell, and use the value `e`. In a comprehension, the target is the enclosing function's local, a `cell` only if a nested scope captures it (§6.8) |
| `lambda` | §5.3, as an expression |
| comprehensions | §6.8 |
| `yield`, `await`, a generator expression, a starred expression elsewhere | **rejected** |

**Short-circuit operators.** A join block takes the expression's value as its single
parameter. Expression temporaries are the only values the translator passes through block
parameters.

```
    %5 : base.Bool = py.truthy %4 ^propagate.0()     -- a and b
    branch %5 ^and.0() ^join.0(%4)
  and.0():
    …                                                -- %8 = b
    jump ^join.0(%8)
  join.0(%9 : py.Value):
```

**Calls.** Evaluate the callee, then the positional arguments left to right, then the
keyword arguments, as CPython does. `args` is the tuple display of the positional arguments.
A lone `*x`, as in `f(*x, k=v)`, is evaluated in place, but `py.argsTuple f x` makes it a
tuple after the keyword arguments, as `CALL_FUNCTION_EX` does: `f(*g(), k=h())` calls `h()`
before it iterates `g()`. `kwargs` is built as a dict display is, but each run of `k=v` pairs is
a total `py.mkKwargs`, as its keys are `strLit`s, and each `**x` is `py.dictMerge f d other`. Merging rejects duplicate keys, as a call must.
Then emit `py.call f args kwargs`. A method call `o.m(x)` is `py.attr`, then
`py.call`: binding the method is `attr`'s job. `kwargs` is always a fresh dict.

```
    %14 : py.Value = py.mkTuple %12
    %15 : base.String = const str "k"
    %16 : py.Value = py.strLit %15
    %17 : py.Value = py.mkKwargs %16 %13
    %18 : py.Value = py.call %11 %14 %17 ^propagate.0()   -- f(x, k=y)
```

### 6.4 Loops

**`while c: B else: E`:**

```
    jump ^head.0()
  head.0():
    …                                    -- %4 = c
    %5 : base.Bool = py.truthy %4 ^propagate.0()
    branch %5 ^body.0() ^else.0()        -- ^exit.0() without an else
  body.0():                              -- exits += loop(exit.0, head.0)
    …
    jump ^head.0()
  else.0():                              -- E
    jump ^exit.0()
  exit.0():                              -- started only if targeted
```

**`for x in xs: B else: E`:**

```
    %9 : py.Value = py.getIter %8 ^propagate.0()
    jump ^head.0()
  head.0():
    %10 : py.Value = py.next %9 ^stop.0()                -- its own successor
    %11 : base.Unit = base.refSet[py.Value] %3 %10       -- x = …
    …                                                    -- B, raising to ^propagate.0()
    jump ^head.0()
  stop.0(%12 : py.Value):
    %13 : base.Bool = py.isStopIteration %12
    branch %13 ^else.0() ^propagate.0(%12)               -- anything else propagates
  else.0():
    jump ^exit.0()
  exit.0():
```

- `py.next`'s `err` successor is `stop`, not `Frame.handler`. The translator emits that one
  instruction under `withHandler stop`. Every operation in the body uses the enclosing
  handler. The loop's exhaustion edge and the body's exception edges are therefore different
  successors on different instructions, and neither can shadow the other.
- `stop` forwards anything that is not `StopIteration` to the handler in effect at the
  `for` statement.
- The target is assigned inside the loop, as §6.1 describes. A raising assignment uses the
  body's handler.
- `B` runs with `loop(exit, head)` pushed onto the exits stack. `break` skips `else`, and
  `continue` goes to `head`.

Loops are plain blocks. There is no transfer to the entry block, because `head` is always a
fresh block.

### 6.5 `break` and `continue`

These perform the exit walk (§4). Inside a `try` with a `finally` (or a `with`) inside the
loop, the walk reaches the `cleanup` entry first, so control goes to `fin(completionBreak)`
and the `finally` body runs before the loop exits.

### 6.6 Closures

A nested `def` or `lambda` becomes a separate function of the module (§5.3). Its leading
parameters are the cells it captures, then its default cells. The captured cells are in
`Scope.freeVars` order: the free names the scope uses, in order of first use, then the
names it only passes on to nested scopes, sorted by name. The `mkClosure` at the definition
site passes the same cells in the same order.

Capture emits no extra instructions. The inner function reads and writes the outer
function's own cell, which gives `nonlocal` and late binding. `mkClosure` takes
`base.Ref(py.Value)` operands, so capturing a value is a type error. A `const @m.f` naming a
function the module does not define fails `Module.WF`.

### 6.7 Classes

`class C(B1, B2, k=v): body` lowers to

```
C = __build_class__(<closure of m.C.<body>>, "C", B1, B2, k=v)
```

The result of `__build_class__` is applied to the decorators, then written to `C`'s cell.
The bases and keywords are evaluated left to right after the body closure is created.
`__build_class__` is `py.qualifiedRef "builtins" "__build_class__"`. Its model calls the
body closure with the new namespace dict as the only positional argument.

`m.C.<body>` is an ordinary function. Its prologue binds `ns` from `args[0]`, and
`classNs` (§4) holds `ns`. In the body, names are mangled (§5.1) and:

| Kind of `x` | Write | Read |
|---|---|---|
| `local` | `py.setItem ns (strLit "x") v` | `dictGet ns "x" (undef "x")`, `isDefined`, branch; if absent, the global read of §5.1 (`LOAD_NAME`) |
| `globalImplicit` | | the same as `local` |
| `globalExplicit` | `writeGlobal` | the global read of §5.1 |
| `free` | `writeCell` (`nonlocal`) | `dictGet ns`, then the captured cell if absent (`LOAD_FROM_DICT_OR_DEREF`) |

- Methods are closures (§6.6). They never capture class-scope names.
- The body returns `None`.
- The body does not yet store `__module__`, `__qualname__` or `__doc__` into `ns`, as
  CPython's class body does before the first statement (§9, Q9).
- Reads use `dictGet`, which is total and never calls `__getitem__`, while writes use
  `py.setItem`. They disagree when `__prepare__` returns a mapping that is not a `dict`, as
  `enum` does; CPython calls that mapping's `__getitem__` and `__setitem__` (§9, Q10).

Zero-argument `super()` and `__class__` are **rejected**. The scope pass marks the class
with `needsClassCell`. The cell must be created by the body and filled by `__build_class__`
(§9, Q6). `super(C, self)` works.

### 6.8 Comprehensions

List, set and dict comprehensions follow Python 3.12 (PEP 709): they are inlined into the
enclosing function. Each `for` clause is a `py.forEach` whose body is a region of that
function. No function is created.

`py.forEach` is planned (§8). The sketch, to be finalised:

```
insn forEach (iterable : Value) (&body (item : Value) : Unit) (^err (exc : Value)) : Unit
```

It iterates `iterable`, runs `body` once per item, and falls through when the iterator is
exhausted. An exception from `iter` or `next` goes to `err`. A region cannot name an outer
block, so the body cannot reach `Frame.handler`. As sketched, the body has no way to raise.
Finalising it means giving the body a result that carries an exception, such as
`py.raising Unit`, with `error e` forwarded to `err`.

`[e for x in xs if c for y in ys]` lowers to:

1. Evaluate `xs` in the enclosing scope, under the enclosing handler.
2. `acc = mkList` (`mkSet`, `mkDict`).
3. One cell per iteration variable (`x`, `y`): `refNew (undef "x")`. These cells belong to
   the comprehension. Inside it they shadow the enclosing scope's names, and they are not
   in `Frame.locals` afterwards. There is one cell per variable per evaluation, so closures
   created in the comprehension share it, as in CPython.
4. `forEach xs ^body ^err(H)`, `H` the enclosing handler. The body region, with its own
   `propagate` handler and an empty exits stack:
   - writes `item` to `x`'s cell;
   - for `if c`: `c` as a condition (§6.2). Its false successor ends the region;
   - for `for y in ys`: evaluates `ys` and emits a nested `forEach` whose `err` is the
     region's handler;
   - innermost: `py.listAppend acc e` (`setAdd`; `dictSet` with the key evaluated before the
     value), then ends the region. `setAdd` and `dictSet` raise `TypeError` on an unhashable
     element or key, to the region's handler.
5. The expression's value is `acc`.

- No completion crosses a region boundary: a comprehension contains no `return`, `break` or
  `continue`.
- A walrus target is the enclosing function's local, which the region can see. It is a
  `cell` only if a nested scope captures it. At module level it is a global.
- A `lambda` or generator expression inside the comprehension is a child of the enclosing
  scope: in `f`, its `__qualname__` is `f.<locals>.<lambda>`.
- In a class body, a free name inside the comprehension skips the class dict and resolves
  as in the scope enclosing the class. The outermost iterable is evaluated by the class
  body and sees the class's names.

Generator expressions keep their own scope. They and generator functions (any `yield`) are
**rejected**. The planned route is an opaque `py.mkGenerator` over a lifted function (§8).

### 6.9 Rejected outright

`async def`, `await`, `async for`, `async with`, `match`, `try`/`except*`, `type` aliases
and PEP 695 type parameters, `yield` and `yield from`, relative imports, and `import *`.
Each is rejected as §3 describes.

## 7. Exceptions, `finally` and `with`

### 7.1 `raise`

| Source | Lowering |
|---|---|
| `raise E` | `v = eval E`, `e = py.toException v` (§8: it instantiates a class and raises `TypeError` for a non-exception), then `jump ^handler(e)` |
| `raise E from C` | as above, plus `py.setAttr e "__cause__" c`. `__suppress_context__` is not modelled |
| bare `raise` inside `except` | `jump ^handler(currentExc)` |
| bare `raise` elsewhere | **rejected**. Python raises at run time based on the dynamic exception state, which this translation does not model |

`raise` is a `jump`. A Python function raises by transferring to `Frame.handler`, which is a
block taking the exception. At the outermost level that block is `propagate.0`, which
returns `base.error`.

### 7.2 `try`/`except`/`else`/`finally`

Write `S` for the exits stack and `H` for the handler in effect at the `try` statement.
Labels are allocated up front:

- `catch(exc)`, if there are `except` clauses;
- `fin(pending : py.Completion)` and `finRaise(exc)`, if there is a `finally`;
- `join`.

Let `H'` be `finRaise` if there is a `finally`, and `H` otherwise. Let `S'` be `S` with
`cleanup fin` pushed if there is a `finally`, and `S` otherwise.

| Part | Handler | Exits stack | Normal end |
|---|---|---|---|
| `try` body | `catch` if there are clauses, else `H'` | `S'` | `jump ^else()` if there is an `else`; otherwise as `else` would end |
| `catch(exc)`: the clause tests | `H'` | `S'` | see the clause chain below |
| clause body `i` | `H'`, or `clear_i` if `as e` | `S'` + `unbind e` | write `undef` to `e`, then `fin(completionNormal)` or `join` |
| `else` body | `H'`. The `except` clauses do not cover it | `S'` | `fin(completionNormal)` or `join` |
| `finRaise(exc)` | | | `%c = completionRaise exc`, `jump ^fin(%c)` |
| `fin(pending)`: the `finally` body, emitted once | `H` | `S` | dispatch `pending` |

**The clause chain** in `catch(exc)`, for each clause `except T as e`: evaluate `T`,
`%m = py.excMatch exc T` (§8), then `branch %m ^body_i() ^next_i()`. A bare `except:` jumps
straight to its body. If the last clause does not match, the chain ends with
`jump ^H'(exc)`. In body `i`, `currentExc` is `exc` and `e`'s cell holds `exc`. `clear_i(x)`
writes `undef` to `e`, then `jump ^H'(x)`.

**Dispatch** is the end of `fin`. `PyBuild.dispatch` emits one `py.Completion.case pending`,
with five successors: normal, return, raise, break and continue. Each successor performs,
from `S` and `H`, what the pending completion would have done at the position of the `try`
statement:

| Successor | Action |
|---|---|
| normal | `jump ^join()` |
| return `v` | the exit walk for `return v` from `S` |
| raise `e` | `jump ^H(e)` |
| break / continue | the exit walk from `S`. With no enclosing loop, its block is `unreachable` |

When a successor's action is a single transfer, the successor targets that block directly,
for example `propagate.0` for raise or `exit.0` for break. Otherwise it gets a fresh block.
`PyBuild.dispatchArms` takes each successor as either: `Arm.to l`, or `Arm.block base emit`
for a fresh block. `PyBuild.tryFinally` emits the whole lowering: the `try` body under
`protect fin`, which makes `finRaise`, then `fin`, then the dispatch.

**When the `finally` body exits abruptly.** Its own exit replaces the pending completion,
as in CPython; Python 3.14 (PEP 765) only adds a `SyntaxWarning` for `return`, `break` and
`continue` there. When it raises while an exception is pending, CPython also sets the new
exception's `__context__` to the pending one. So the target lowering protects the `finally`
body: a failure goes to a `superseded(pending, exc)` block, which `tryFinally (superseded :=
true)` emits and `PyBuildTest`'s `k` checks, and which chains `exc` to `pending` before
propagating it. The chaining operation belongs to the run-time exception state (§9, Q2).
`tryFinally`'s default, which runs the `finally` body under `H` with stack `S`, has the same
control flow without the chaining.

**Why a completion.** CPython 3.9 and later copy the `finally` body once per exit, with no
bound on the copies, and exponentially many when nested `finally` bodies themselves exit
abruptly; up to 3.8 it emitted one copy. Mantle emits the body once, at the cost of a
linear dispatch on the completion. V8 and Kotlin's coroutines dispatch on a token the same
way. The JVM's `jsr`/`ret` was abandoned because its targets were dynamic, which made
verification intractable; a completion's targets are all static.

Example: c1 (§10). The prologue is elided, and `cleanup` is read as a global.

```
  entry.0(%0 : py.Value, %1 : py.Value):
    …
    %8 : base.Int = const int 1
    %9 : py.Value = py.intLit %8
    %10 : py.Completion = py.completionReturn %9        -- return 1 → exit walk
    jump ^fin.0(%10)
  finRaise.0(%11 : py.Value):                            -- the try body's handler
    %12 : py.Completion = py.completionRaise %11
    jump ^fin.0(%12)
  fin.0(%13 : py.Completion):                            -- finally, emitted once
    …                                                    -- cleanup(), ^propagate.0()
    py.Completion.case %13 ^join.0() ^ret.0() ^propagate.0() ^unreachable.0() ^unreachable.1()
  ret.0(%20 : py.Value):
    %21 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value] %20
    ret %21
  unreachable.0():
    unreachable
  unreachable.1():
    unreachable
  join.0():
    …                                                    -- falls off: return None
```

### 7.3 `with`

`with E as t: B`, where `H` and `S` are as in §7.2:

1. Evaluate `mgr = E`. Then `enter = py.attr mgr "__enter__"` and
   `exit = py.attr mgr "__exit__"`, both under `H`.
2. `v = py.call enter () {}`, under `H`.
3. Protected region: handler `wexc`, stack `S` + `cleanup fin`. It assigns `t = v` (an
   assignment that raises still runs `__exit__`), then runs `B`. A normal end is
   `jump ^fin(completionNormal)`.
4. `wexc(exc)`: `ty = py.call builtins.type (exc)`, then `r = py.call exit (ty, exc, None)`,
   both under `H`. Then `b = py.truthy r` and `branch b ^join() ^H(exc)`. A true result suppresses the
   exception, and a false result re-raises the original exception.
5. `fin(pending)`: `py.call exit (None, None, None)` under `H`, then dispatch `pending` as in
   §7.2. The raise successor cannot be reached on this path, but it must exist, so it goes to `H`.

The exception path calls `__exit__` with the exception and never builds a completion. Every
other path goes through `fin`, which calls `__exit__` once. `with a, b: B` is
`with a: with b: B`. Python looks `__enter__` and `__exit__` up on the type and raises
`TypeError` if either is missing. `py.attr` looks them up on the instance (§9, Q5).

## 8. Gaps in the environment and builder

**Operations the rules need that `Py.env` does not declare:**

| Operation | Signature (DSL) | Needed by |
|---|---|---|
| `forEach` | `insn forEach (iterable : Value) (&body (item : Value) : Unit) (^err (exc : Value)) : Unit`, a sketch: the body's result must carry an exception (§6.8) | comprehensions |
| `excMatch` | `insn excMatch (exc type : Value) (^err (e : Value)) : Bool` | `except T` (the alternative is `py.call` builtins `isinstance`, then `truthy`) |
| `toException` | `insn toException (val : Value) (^err (e : Value)) : Value` | `raise E` |
| `unpackSeq`, `unpackEx` | `(val : Value) (n : Int) (^err …) : Value` (a tuple); `(val : Value) (before after : Int) (^err …) : Value` | tuple targets |
| binary operators | `matMult`, `lShift`, `rShift`, `bitAnd`, `bitOr`, `bitXor`, as `add` | `@ << >> & \| ^` |
| unary operators | `uAdd`, `invert`, as `uSub` | `+a`, `~a` |
| in-place operators | `iadd` … `ipow` and the bitwise ones, as `add` | `x op= e` |
| `delAttr`, `delItem` | as `setAttr`/`setItem` without `val` | `del o.a`, `del o[k]` |
| `mkGenerator` | `insn mkGenerator (code : Code) (cells : Ref Value…) : Value` | generators (stage 1, opaque) |

**Declarations to fix:**

- `unsupported` takes its construct name as a `py.Value`; the other name-carrying operands
  are `base.String`.

**Builder (`PyBuild`) and translator (`PyTranslate`):**

- The scope and the exits stack live in the translator's state, `TransM` (§4). `Exit` lacks
  `cleanup` and `unbind`, and the state lacks `currentExc` and `classNs`.
- The prologue is `PyTranslate.prologue` (§5.4). It has no default cells.
- `PyBuild.buildFuncTypedWith` builds a function and returns its body's result. `transFunc`
  declares only `args` and `kwargs`; captured cells before them are to add.
- `Frame.handler` is a `BlockValue`, so a handler can pre-bind arguments (`withHandlerTo`).
  Under `Override` nothing needs that; a chaining policy's `superseded` block does.
- `dispatch` and `dispatchArms` take `Label`s. Direct successors that pre-bind arguments need
  `BlockValue`s.
- `tryFinally`, `protect` and `dispatchArms` run their bodies in any `MonadPy` monad, so the
  translator can pass `TransM` bodies. The translator does not call them yet.
- No `raiseTo exc` helper (`jump ^handler(exc)`). `exitWalk` handles `loop` entries only.
- `PyM` has no wrapper for `Build.region`, which `forEach` needs (§6.8).

## 9. Open questions

1. **Regions.** Statements use plain blocks plus completions. Regions for loops and `try`
   are a future refinement, and need no new completion machinery.

   | Construct | Now | Refinement |
   |---|---|---|
   | `if`, `and`/`or`, `x if c else y` | blocks | none |
   | `while`, `for` | blocks | a terminal `py.loop` op with a body region, shaped like `demo.loop` in `SuccTest` |
   | `try`, `with` | blocks plus completions | `py.try` with body and handler regions returning `py.Completion`, shaped like `reg.try` in `RegionTest`. The outside dispatches the completion |
   | comprehensions | `forEach` regions (§6.8) | decided |

   A region cannot name an outer label, so `propagate.0`, a loop's `exit` and an outer `fin`
   are out of reach. Every abrupt exit from a region becomes a returned completion, with
   its own handler inside: §7 moved to a region boundary.
2. **Exception chaining in `finally`.** The `superseded` block must set `__context__`, and
   the `finally` body must see the pending exception as the one being handled
   (`sys.exc_info()`). Both need the run-time exception state, which is not designed yet.
3. **Definedness.** Should definedness stay as `py.undef` values in cells, or become
   `Ref (Option Value)`? Only `undef`, `isDefined`, `requireDefined` and `requireUndefined`
   would change.
4. **Module objects and imports.** *Resolved.* A module value is the result of
   `py.importModule`, written to the bound name's cell. `from a import x` is
   `py.importFrom`, evaluated once at the import, so the binding is a snapshot. `a.b.f` is
   `py.attr` on the module value (§6.1).
5. **Special-method lookup.** `with`, and implicitly `truthy`/`getIter`, look methods up on
   the type in CPython. `py.attr` on the instance differs when an instance attribute shadows
   the method.
6. **`__class__` cell.** Zero-argument `super()` needs a cell created by the class body and
   filled by `__build_class__`. The scope pass sets `needsClassCell` on a class when one of its
   methods loads the name `super` or `__class__`, whether or not `super` is called with no
   arguments. `base.refNew` creates the cell and `py.mkClosure` captures it, but no
   instruction turns a `base.Ref(py.Value)` into a `py.Value`, so the body cannot store it as
   `ns["__classcell__"]` for `__build_class__` to fill. That needs such an instruction, a body
   that returns the cell, or an operation that installs it.
7. **Unpacking.** Should unpacking use two operations (`unpackSeq` and `unpackEx`), or one
   with an optional star position?
8. **Global fallback.** *Resolved.* The scope pass classifies a module global and a builtin
   alike as `globalImplicit`, and the split is made at run time: read the global cell, then
   `isDefined`, then `qualifiedRef "builtins" name` if undefined (§5.1).
9. **Implicit class-body stores.** CPython's class body first stores `__module__` (the
   module's `__name__`) and `__qualname__` into the namespace, and `__doc__` if the body
   starts with a docstring. §6.7 should emit these as `py.setItem`s at the top of the body.
10. **Namespace reads.** Class-body reads use the total `dictGet` and writes use `py.setItem`.
    A namespace from `__prepare__` that is not a `dict` needs reads through its `__getitem__`,
    a raising operation that treats `KeyError` as absent.

## 10. Acceptance tests

Each case is an exception edge that an earlier translator lowered wrongly while still
passing its well-formedness check. Each becomes a golden test, plus an interpreter check that
counts `cleanup()` calls. The repros are `c1`–`c7` and `t30_loop_try_nested` in
`StrataPythonTest/Mantle/mantle_tests/`, listed in `mantle_tests.txt` as not yet supported.

| Case | Python | Wrong lowering | Fixed by |
|---|---|---|---|
| c1 | `try: return 1` / `finally: cleanup()` | the return skipped `cleanup()` | §5.5 and §4: `return` walks to `fin(completionReturn 1)`. The return successor returns |
| c2 | `try:` / `for x in xs: return x` / `finally: cleanup()` | same, from inside the loop | the walk skips the `loop` entry and reaches the `cleanup` entry |
| c3 | `for x in xs:` / `try: break` / `finally: cleanup()` / `return 0` | `break` jumped straight past `cleanup()` | §6.5: `fin(completionBreak)`. The break successor targets `exit` |
| c4 | as c3, with `continue` | `continue` skipped `cleanup()`, exhaustion re-entered the loop, and `return 0` was dead | §6.5: the continue successor targets `head`. §6.4: exhaustion is `next`'s own `^stop` |
| c5 | `for x in xs:` / `try: cleanup()` / `finally: note()` / `return 0` | the `finally` captured `next()`'s `StopIteration`, and the loop exit was dead | §6.4: `py.next ^stop` is emitted outside the `try`'s handler |
| c6 | `for x in xs: boom()` / `return 0` | `boom()`'s `ValueError` ended the loop normally | §6.4: body operations raise to `Frame.handler`, never to `stop`, and `stop` re-raises anything that is not `StopIteration` |
| c7 | `with acquire() as r: return r` | `__exit__` was skipped | §7.3: `return` walks to the `with`'s `fin`, which calls `__exit__(None, None, None)`, then the return successor returns |
| t30 case 6 | `for m in xs:` / `try: raiser()` / `except StopIteration: note(9); continue` / `finally: cleanup()` | the back edge's vacuous exception edge left 21 blocks dead | §6.4 and §7.2: the clause's `continue` goes through `fin`, the back edge is a plain `jump` with no exception edge, and `raiser()`'s `StopIteration` reaches `catch`, not `stop` |
| t30 `nested_return` | `for p in outer:` / `try:` / `for q in inner:` / `try: if check(q): return q` / `finally: note(12)` / `finally: cleanup()` / `return 0` | neither `finally` ran, and there was no normal exit | the inner `fin`'s return successor walks from its own `S`, reaching the outer `cleanup`, so `note(12)` runs, then `cleanup()`, then the return. Exhausting `outer` reaches `return 0` |

These checks apply to all of them. `Module.WF` holds. Every block is reachable from the
entry, except handler blocks that no operation names. No `finally` or `__exit__` body is
emitted more than once.

## 11. Coverage

*Implemented* marks what `PyTranslate.translate` lowers. It rejects every other construct with
a diagnostic.

| Construct | Section | Status |
|---|---|---|
| module body; top-level `def` with positional, positional-only, keyword-only, `*args` and `**kwargs` parameters and constant defaults; prologue; `return` | §5.2–§5.5 | specified; implemented |
| nested `def`, `lambda`, decorators, non-constant defaults | §5.3 | specified |
| name resolution (all five kinds, mangling, compile-time errors) | §5.1 | specified; implemented (`PyScope.analyze`, CPython 3.12 model) |
| local names | §5.1 | specified; implemented |
| cell and free names | §5.1 | specified |
| global names, `global`, builtins | §5.1 | specified; implemented |
| `import`, `from … import` | §6.1 | specified; implemented |
| relative import, `import *` | §6.1 | unsupported (rejected by the scope pass and the translator) |
| expression statement, `pass`, assignment to a name (chained too) | §6.1 | specified; implemented |
| assignment to an attribute or subscript | §6.1 | specified |
| tuple and starred targets | §6.1 | specified, open question (`unpackSeq`, Q7) |
| augmented assignment | §6.1 | specified, open question (in-place operators); implemented on names, with the binary operation |
| annotated assignment | §6.1 | specified; implemented on names |
| `del x`, `assert` | §6.1 | specified |
| `del o.a`, `del o[k]` | §6.1 | unsupported |
| `nonlocal` | §6.6 | specified |
| `if` / `elif` / `else` | §6.2 | specified; implemented |
| literals, `...`, `+ - * / // % **`, `-a`, `not a`, comparisons (chained too), `and`, `or`, `x if c else y` | §6.3 | specified; implemented |
| conditions (`transCond`) | §6.2 | specified; implemented for `if`, `while` and `x if c else y` |
| calls, with keywords, `*` and `**` | §6.3 | specified; implemented |
| displays and unpacking in them | §6.3 | specified; implemented |
| attribute, subscript, slice (inside a tuple too) | §6.3 | specified; implemented |
| f-strings, walrus | §6.3 | specified |
| complex literal, t-string | §6.3 | unsupported |
| `@ << >> & \| ^`, unary `+`, `~` | §6.3 | unsupported |
| `while` / `else`, `break`, `continue` | §6.4–§6.5 | specified; implemented |
| `for` / `else` | §6.4 | specified |
| closures | §6.6 | specified |
| `class`, bases, keywords, decorators | §6.7 | specified |
| zero-argument `super()`, `__class__` | §6.7 | unsupported (Q6); the scope pass sets `needsClassCell` |
| list, set and dict comprehensions | §6.8 | specified, open question (`forEach` not declared; its body's result); scoping implemented (`inlinedComprehension`) |
| generator expressions, `yield` | §6.8 | unsupported; a generator function is a stub |
| `raise`, `raise … from` | §7.1 | specified, open question (`toException`) |
| bare `raise` | §7.1 | specified inside `except`; unsupported elsewhere |
| `try` / `except` / `else` | §7.2 | specified, open question (`excMatch`) |
| `finally` | §7.2 | specified, open question (Q2) |
| `with`, several items | §7.3 | specified, open question (Q5) |
| `async`, `await`, `match`, `except*`, `type`, PEP 695 | §6.9 | unsupported; an `async def` is a stub |
