# Translating Python to Dyn

This document specifies how each Python construct lowers into Dyn, the project's typed SSA
intermediate representation. It is written for whoever implements the translator from the
Python AST (`StrataPython.stmt` / `StrataPython.expr`) to a Dyn `Module` over Python's
environment. Section 1 introduces as much Dyn as the examples need. Dyn itself is
specified in [`Dyn.md`](./Dyn.md).

The scope is the Python subset the front end analyses: functions, classes, closures,
control flow, exceptions, `with`, and comprehensions. Generators, `async` and `match` are
rejected (§6.9). The gaps found in the environment and builder while writing this design
doc are listed in §8. §12 gives the rules by which a PySpec model, a description of a library
without its code, is represented in Dyn.

**The translator** is `PyTranslate.translate` in `StrataPython/Dyn/Translate.lean`. §11
marks what it implements, and the module docstring has a recipe for adding a construct.
`pydyn dyn FILE` prints the diagnostics and the module for a `.py` or Python Ion file.
The tests are the programs `NAME.py` in `StrataPythonTest/Dyn/dyn_tests/`.
`StrataPythonTestExtra/DynTranslateTest.lean` runs every one, as listed in
`StrataPythonTest/Dyn/dyn_tests.txt`, and compares each one marked supported with its
golden, `NAME.expected.dyn` beside `NAME.py`.

**Design decisions.** Every local is a cell declared in the entry block. The translator does
no SSA construction: promoting cells to SSA values is a later ref-to-reg pass. Control flow is
plain blocks plus completions (§4, §7). The one region-based construct is the comprehension
(§6.8). Loops and `try` as regions are a future refinement (§9, Q1). Name resolution and
comprehension scoping follow CPython 3.12.

## 1. Dyn in brief

**Environments and programs.** An *environment* declares types and instructions. A
*program* is a module of functions written against one environment. The *base*
environment declares the datatype `base.Unit` with the one constructor `base.unit`,
`base.Bool`, `base.Int`, `base.Float64`, `base.String`, `base.Sequence a`, `base.Ref a` (a
mutable cell), `base.Fn as r` (a code pointer to a function taking `as` and returning `r`)
and the datatype `base.Except e a` with constructors `base.ok` and `base.error`. It also
declares the cell instructions `base.refNew`, `base.refGet` and `base.refSet`, and
`base.callCode`, a call through a `base.Fn`. The Python lowering takes code pointers only to
build closures, with `py.mkClosure`. Python's environment extends the base (§2).

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
| `const` | a literal of a base type (`unit`, `bool`, `int`, `float`, `str`), or `const @m.f`, a pointer to the function `m.f` of the same module, at its code type `base.Fn as r` |
| `apply` | an application of a declared instruction, including a datatype constructor, at explicit type arguments |

**Successors.** An instruction may declare *successors*: the places it may transfer to instead
of falling through, each with a payload, the values it passes. What fills a successor is a
*target* (`Target.Raw`): a label with a prefix of that block's arguments already bound. The
instruction supplies the rest, after them. The `err` successor of a raising Python operation
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
own, so `ret` inside a region leaves the region with a value.

**Well-formedness**, as `StrataDyn/WF.lean` checks it. These rules constrain the translator:
labels are unique function-wide; no transfer targets an entry block; every operand is
defined, with the type its use demands; every successor supplies exactly what its target's
parameters declare; a terminator applies a terminal instruction, and no other instruction
does. Every use must be in scope, as [Dyn](./Dyn.md#1-overview) describes under
*Scoping*.

**Printed syntax.** This is what `Module.format` prints, constants folded into their uses,
and what `Module.read` reads back;
[Dyn](./Dyn.md#2-printed-form) describes it. Each example in this document is in that
form. `--` comments and `…` elisions are added for the reader. Readable labels such as
`head.0` are what the translator passes to `freshLabel`. An application's operands are in
parentheses, left out when there are none. A constant is written where it is used:
`py.intLit(1)`. A function name prints with an `@` prefix, in its definition and where a
constant refers to it. Each successor prints with a `^` prefix. A terminator prints as
an application without a result, so a case is
`base.Except.case[base.String, base.Int](%4) ^ok.0() ^err.0()`. The base's terminal
instructions drop `base.`: `jump ^done.0()`, `branch(%0) ^bump.0() ^done.0()` and
`unreachable`. A jump to the exit prints as `ret(%ret.0)`. A literal is untagged, and its form
fixes its type: `1` is a `base.Int`, `"k"` a `base.String`.

```
func @m.f(%x.0 : py.Value) -> base.Except(py.Value, py.Value) {
  entry.0(%x.0 : py.Value):
    %int.0 : py.Value = py.intLit(1)                    -- apply, no successors
    %add.0 : py.Value = py.add(%x.0, %int.0) ^propagate.0()  -- err successor, nothing pre-bound
    %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%add.0)
    ret(%ret.0)                                         -- jump to the exit, passing %ret.0
  propagate.0(%exc.0 : py.Value):                       -- receives the exception
    %exc.1 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.0)
    ret(%exc.1)
}
```

## 2. Python's environment

The environment is `StrataPython/Dyn/Env.lean`, namespace `py`. The emission helpers
are in `StrataPython/Dyn/Build.lean`.

- **One value type.** Every Python value has type `py.Value`. Base types appear only where
  a value is not a Python value: a `base.String` attribute name, a `base.Int` literal before
  boxing, the `base.Bool` that a `branch` needs, and the `base.Unit` result of an operation
  that only acts.
- **Raising operations.** Every operation that can raise declares an `err` successor, which
  receives the exception as a `py.Value`. The operation's result is its success value. The
  translator passes the label of the enclosing handler as `err`.
- **Total operations** have no successors. These are the literals, `undef`, `isDefined`,
  `is`/`isNot`, `mkTuple`/`mkList`/`mkKwargs`, `listToTuple`, `mkSlice`, `tupleGet`,
  `listAppend`, `isStopIteration`, `strConcat`, `globalCell`, `mkClosure`, `assertionError`,
  `pushExcInfo`, `pushPending`, `popExcept`, the `Completion` constructors and `unsupported`.
  `mkSet` and `mkDict` raise, because hashing a key and comparing it with a stored key may run
  `__hash__` and `__eq__`. Of the operations for contracts (below), all are total except
  `isInstance`, `typeIsSubclass`, `len`, `reSearch` and the quantifiers. Some operations assume
  something of their operands, such as that the index of a `tupleGet` is in range, and
  `Env.lean` lists them. Where the assumption fails, the result is not defined, so a contract
  region that applies the operation there is not well defined.
- **Effects.** Each operation declares its effect, an upper bound on what it may do
  ([Dyn](./Dyn.md#1-overview), *Effects*): `pure`, such as `is` or a literal; `reads`,
  such as `listToTuple`; `calls`, which may run code that the IR does not show, such as a dunder
  method in `add` or `truthy`, or a built-in iterator's `__next__` in `in`; or `writes`, such as
  `call` or `setItem`. A contract applies no `writes` operation. An operation that raises an
  exception of its own reads the exception being handled, which becomes the new exception's
  `__context__` (§7.1), so it is never `pure`. Three operations stand for a Python check that
  uses a cache, and none of them fills it: `py.isInstance` gives what `isinstance` gives in the
  current state, the caches of `ABCMeta`'s checks included, but does not fill them;
  `py.typeIsSubclass` neither reads nor fills them; and `py.reSearch` does not use the cache of
  compiled patterns of `re`.
- **Operations for contracts.** A contract of a Python function, such as one of a PySpec model,
  uses operations that the translator does not emit. Their docstrings in `Env.lean` state what
  each one means.
  - *Arguments.* A function receives `args` and `kwargs`. `py.argOf(args, kwargs, pos, name,
    default)` is the value that the call binds to a parameter, with `pos` being -1 for a
    keyword-only one. `py.extraKwargs(kwargs, names…)` is the dict that a `**kw` parameter
    receives. `py.bindsTo(args, kwargs, nPos, varKw, names…)` says whether binding raises no
    `TypeError` for a parameter given twice, an unexpected keyword or too many positional
    arguments.
  - *Tests.* `py.stdClass(module, name)` is a class of the standard library, whatever the program
    rebinds. `py.isInstance` is `isinstance`, and `py.typeIsSubclass(v, cls)` tests `type(v)`
    against `cls` by its MRO and by the standard library's registrations and hooks only.
    `py.len` is `len`, and `py.reSearch(pattern, s)` is whether `re.search` finds a match.
    `py.strIsOneOf(v, lits…)` and `py.intIsOneOf(v, lits…)` test for one of a few literals, and
    `py.dictKeysWithin(d, keys…)` tests that a dict has only the given keys.
    `py.isImmutableScalar(v)` tests that the type of `v` is exactly one of the built-in types
    `int`, `float`, `complex`, `bool`, `str`, `bytes` and `NoneType`, whose objects hold no
    mutable state.
  - *Quantifiers.* `py.allIn`, `py.anyIn`, `py.allItems` and `py.anyItems` run a body over the
    elements of a list, tuple, set or frozenset, the keys of a dict, or the entries of a dict.
    The body returns `base.Except(py.Value, base.Bool)`. A failure in it goes to a propagating
    block, so the quantifier raises and the clause takes its failure value. The quantifier raises
    if the body fails for any member, whatever the others give. CPython's `all(...)` may stop
    at a false member before reaching the one that raises, but then a `requires` clause is
    `false` and a `free ensures` clause `true`, so this errs only toward the failure value.
  - *Locations*, of type `base.Loc`, which a frame computes at the call: `py.attrLoc(obj, name)`,
    an attribute, wherever `obj` stores it; `py.itemLoc(obj, key)`, an entry of a dict;
    `py.objLoc(obj)`, every location of `obj`; `py.reachLoc(obj)`, every location other than a
    `__class__` of `obj` and of every object that `obj` reaches through what objects store (the
    values of their attributes that are locations, and their elements, keys, values and internal
    state), never holding or following an attribute of a class or a module; and
    `py.instanceState`, every attribute other than `__class__` of every object that is neither a
    class nor a module, and `py.reachLoc` of each such attribute's value. Neither holds a closure
    cell's contents. A model's frame names `py.instanceState` (§12.5), so a call of a library
    function may change the attributes of these objects and what they reach.

  Three rules make these tests stricter than the Python they stand for. So such a test may stand
  for the Python test only at a positive position of a `requires` clause. Everywhere else, such
  as under `not` or in the condition of an implication or an `if`, and in every `free ensures`
  clause, the Python test is used: the chain of `py.eq`, or `py.isInstance`.
  - `py.bindsTo` holds only if every key of `kwargs` is exactly a `str`, not an instance of a
    subclass, and `py.argOf`, `py.extraKwargs` and `py.dictKeysWithin` compare a key's
    characters. A subclass may override `__eq__`: CPython 3.12 binds such a keyword with that
    `__eq__` in a Python function, and by its characters in a built-in one.
  - `py.strIsOneOf` and `py.intIsOneOf` hold only for an exact `str` or `int`. For those, `==`
    compares characters or values, so `strIsOneOf(x, "A", "B")` implies `x == "A" or x ==
    "B"`. `bool` is not an `int` here.
  - A declared type's test is `py.typeIsSubclass(v, C)` and then, only if it holds,
    `py.isInstance(v, C)`. The pair is stricter than `isinstance(v, C)`, but `typeIsSubclass`
    alone is not. It reads `type(v)`, not `v.__class__`, and counts no registration or hook that
    the program makes, so `typeIsSubclass(Mock(spec=int), int)` is false while
    `isinstance(Mock(spec=int), int)` is true. It evaluates the MRO that CPython stores for the
    type, and the standard library's hooks over that MRO, and it never runs a metaclass's
    `__mro__` property. But a metaclass's `__instancecheck__` or `__mro__` property, a program's
    `__subclasshook__`, a `__class__` that raises, or an ABC's cache can make `isinstance` false
    or make it raise where `typeIsSubclass` holds.

  One choice is a trusted modeling assumption: a quantifier ranges over what the container
  stores. A subclass that changes how it iterates or reads its members, such as by overriding
  `__iter__`, `items` or `__getitem__`, is quantified over its storage. With `class
  D(dict): __iter__ = lambda s: iter(["zzz"])`, CPython 3.12 gives `True` for `all(k == "zzz"
  for k in D(a=1))`, and `py.allIn` gives `false`.
- **Cells.** A cell is a `base.Ref(py.Value)`, a mutable location. Every Python local is a
  cell: `refNew` creates it, `refSet` writes it and `refGet` reads it. A cell that has not
  been assigned holds `py.undef "x"`. The *ref-to-reg* pass (`docs/Dyn.md` §3) promotes
  most cells that no closure captures to SSA values and block parameters. A cell that a
  comprehension reads before writing it, or that a comprehension writes and the code after it
  reads before assigning it again, stays a cell. A promoted local that is read before it is
  assigned then reads its `py.undef` value, and `py.requireDefined` still raises. The
  translator never decides block parameters for locals. The translator lowers frame
  introspection as ordinary calls that are given no cells: `locals()`, `vars()`, `dir()`,
  `eval`, `exec`, `breakpoint()`, and any frame object (from `sys._getframe`, `inspect`, a trace
  function, a traceback or a generator). These read or write a frame's locals, so the
  translation does not keep their meaning, and ref-to-reg may promote cells they observe. A
  planned admission pass must reject the programs that use them before ref-to-reg runs. Until it
  exists, ref-to-reg is wrong on such programs (the corpus test pins the golden functions that
  call them).
- **Globals.** `py.globalCell module name` is the cell of a module global: the same cell for
  the same arguments, read and written like a local's. It holds `undef` until the first
  assignment, and `del` writes `undef` back. `module` is always fully qualified (`"a.b"`).
  `py.loadGlobal module name` reads a name as CPython's `LOAD_GLOBAL` does: the global cell
  if it is defined, else the builtin, else it raises `NameError`.
- **Imports.** `py.importModule module` returns the module object, importing it and each
  package above it first if need be. `py.importFrom module name` imports `module` and reads
  its attribute `name`, falling back to the submodule `module.name` as CPython's
  `IMPORT_FROM` does. Both raise `ImportError`, or whatever the module body raises.
  `py.qualifiedRef module name` reads `module.name` at each use; the translator uses it only
  for builtins that are not names in the source, such as `__build_class__`.
- **Definedness.** Only `isDefined` and `requireDefined` may consume a value that could be
  `undef`. `requireDefined v excType msg` passes `v` through, or raises `excType(msg)` if `v` is
  undefined. One exception is a prologue's defaults tuple (§5.4): it holds `undef` for a
  parameter without a default, `py.mkTuple` builds it, and `py.bindArgs` reads it.
- **Completions.** `py.Completion` records how a protected block finished. It is a datatype
  whose five constructors are instructions:
  `completionNormal`, `completionReturn (value)`, `completionRaise (exc)`, `completionBreak`
  and `completionContinue`. `py.Completion.case` has five successors in that order. Only the
  `return` and `raise` successors receive a payload.
- **Closures.** `const @m.f` is a `base.Fn(as, base.Except(py.Value, py.Value))`, with `as`
  `m.f`'s parameter types: its cells, then `args` and `kwargs`. `py.mkClosure[cs] code cells…`
  pairs it with the cells it captures, one operand per element of `cs`, the cells' types, to
  make a callable `py.Value`:
  `reads insn mkClosure [(cs : list)] (code : Fn [*cs, Value, Value] failing) (*cells : cs) : Value`.
  `py.call f args kwargs` calls any callable.
- **Function results.** A translated function returns `base.Except(py.Value, py.Value)`.
  `base.ok v` is a normal return and `base.error e` propagates an exception to the caller.
  `py.call` receives `error e` and transfers it to its own `err` successor.

## 3. Conventions

**Function shape.** Every function the translator emits is built by
`PyBuild.buildFuncTypedWith`, which checks it and also returns the body's result; the
translator returns its own state through it (§4).
Its parameters are:

| Function | Parameters, in order |
|---|---|
| a `def`, `lambda`, or class body | captured cells `base.Ref(py.Value)`…, then `args : py.Value` (a tuple) and `kwargs : py.Value` (a dict) |
| the module body | none |

`buildFuncTypedWith` installs `propagate.0(exc)`, which returns `base.error exc`. It is the
handler wherever no `try` or `with` encloses the code. In a function where nothing can raise
to it, nothing reaches it, and the builder drops it, as it drops every block the entry cannot
reach.

**Entry block.** In order: one `declareLocal` per local and cell variable of the scope
(§5.1), then the argument-binding prologue (§5.4), then the body. Every cell is declared in
the entry, so it dominates every use. A comprehension's iteration variables are the
exception (§6.8).

**Scoping.** The well-formedness check computes each body's dominator tree, so the translator
leaves dominance to it. A use out of scope makes the function not well formed, an internal
error (§3) that names the use and a path to it that avoids its definition. A value is used
directly outside the block that defines it only where that block dominates the use; otherwise
it travels in a cell, a block parameter or a successor argument. Every local's cell is
declared at the top of the entry, before the argument-binding prologue (§5.4), and a global's
cell is fetched where it is used, so each cell dominates its uses.

**Function names.** A Dyn module holds one Python module `m`, and is named `m`, one
segment per dotted component (`a.b`). Its functions are named under `m`, following the
scope's `__qualname__`. Function names and instruction names are separate namespaces, and a
function name prints with an `@` prefix: `@m.add` is a function, `py.add` an instruction. A
segment in angle brackets cannot collide with a Python identifier; the printer quotes it, as
in `@m.|<module>|`. The translator implements every row (`allocName`).

| Source | Name |
|---|---|
| module body | `m.<module>` |
| `def f` at top level, `def g` inside `f` | `m.f`, `m.f.g` |
| method `meth` of class `C`, body of `C` | `m.C.meth`, `m.C.<body>` |
| `lambda` | `m.f.<lambda>`; a second one gets the last row's suffix |
| a name the module already uses | a numeric suffix: a second `def f` is `m.f.1` |

**Annotations.** The translator wraps each statement and each expression in
`withRange node.ann`, which sets the builder's default annotation (`withInfo`) to an `Info`
with that range. Everything the construct emits, including synthesized blocks and prologue
code, carries that source range.

**Reachability.** The builder has an *open block* when instructions can still be emitted
(`Build.State.body.label` is some label). A statement that ends the open block is `return`,
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

**Internal errors.** A misuse of the builder, a function that is not well formed, and a
function name emitted twice are each an internal error. A function whose build fails is
replaced by a stub that takes the same parameters and whose entry block ends in
`unreachable`, and of two functions of one name the first is kept, so the translator always
returns a checked module. Such a module is for diagnostics only: the run has failed.

## 4. Translator state

The translator runs in
`TransM = ReaderT Ctx (StateT TState (PyM Info))`, with
`PyM α = StateT Frame (BuildM Py.env α)` below it. `Build.State`, the generic builder state,
holds value ids, labels, the open block and the default annotation. `Frame` holds the
emission state of the Python builder. `Ctx` is fixed while one function is translated, and
`TState` accumulates:

| State | Field | Exists? | Set by |
|---|---|---|---|
| enclosing handler: the block every raising operation names as `err` | `Frame.handler : PyTarget [Py.Value]` | yes | `buildFuncTypedWith` (`propagate.0`), `withHandler` and `withHandlerTo` (`try`, `with`, `for`) |
| the function's exit, which `return` and a propagated failure leave by | `Frame.exit : PyTarget [Py.failing]` | yes | `buildFuncTypedWith` |
| locals: name ↦ cell | `Frame.locals` | yes | `declareLocal` |
| scope: the `PyScope.Table`, the current `ScopeId` and its `Scope` (with the `__qualname__`), giving each name's kind (`local`, `cell`, `free`, `globalExplicit`, `globalImplicit`). Imports are `Table.imports`, a separate list of fully qualified targets | `Ctx.table`, `Ctx.scope`, `Ctx.cur` | yes | `PyScope.analyze` (§5.1), `transFunc` |
| the Python module name, the Dyn module name, the names some scope binds as globals | `Ctx.module`, `Ctx.moduleName`, `Ctx.globals` | yes | `translate` |
| diagnostics | `TState.diagnostics` | yes | `reject` |
| functions to emit after the current one, and the names taken | `TState.pending : Array FuncJob`, `TState.funcNames` | yes | `defStmt`, `allocName` |
| exits stack (below) | `TState.exits : Array Exit` | yes | `withExit`: loops, `except` clause and `finally` bodies, `try`/`finally`, `with` |
| the labels some emitted transfer names, for starting join blocks | `TState.targeted` | yes | `jump`, `branch` |
| the `__init__`s of the class body being emitted, for its declared fields | `TState.inits` | yes | closure |
| exception an `except` body handles, for bare `raise` | `Ctx.handled : Option ValId` | yes | `except` bodies; a `finally` body resets it |
| namespace, inside a class body | `Ctx.classNs : Option ValId` | yes | class body functions |
| default annotation | `Build.State.info` | yes | `withRange` |

A `def` binds its name where it runs, and queues a `FuncJob`; `translate` emits the module
body first, then each queued function, in order.

The **exits stack** records every enclosing construct that a `break`, `continue` or `return`
must pass through, innermost last:

```
inductive Exit
  | loop    (brk cont : Label)    -- break → brk, continue → cont
  | handler (prev : ValId) …      -- an except clause or finally body: leave the handler
  | cleanup (fin : Label)         -- try/finally or with: fin takes a py.Completion
```

**The exit walk** (`exitWalk`). An abrupt exit `k` (break, continue, or return `v`) is
emitted by walking the stack from the innermost entry outward:

| Entry | `break` | `continue` | `return v` |
|---|---|---|---|
| `loop brk cont` | `jump ^brk()`, stop | `jump ^cont()`, stop | skip |
| `cleanup fin` | `%c = py.completionBreak`, `jump ^fin(%c)`, stop | `py.completionContinue`, likewise | `py.completionReturn v`, likewise |
| `handler prev` | leave the handler (§7.2), keep walking | same | same |
| stack empty | | | `emitReturn v` |

A `break` or `continue` with no `loop` entry is a syntax error that the scope pass reports
(§5.1), and is not walked.

Exceptions do not use the walk. `Frame.handler` already names the right block at every
point, because each construct that intercepts exceptions installs its own handler.

## 5. Module, functions and names

### 5.1 Scopes

Name resolution runs once per module, before any emission:
`PyScope.analyze` (`StrataPython/Dyn/Scope.lean`) returns a `Table`, matching CPython
3.12's `symtable`. The table has one `Scope` per module, function, `lambda`, class body,
generator expression and list, set or dict comprehension, in preorder. Each scope records its kind, `__qualname__`, parameters,
cell variables (`cellVars`), free variables (`freeVars`), whether it is a generator (its first
`yield`, as CPython's `CO_GENERATOR`), and a `Symbol` per name with one of five kinds:

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
  generator expression`), and the compiler's `keyword argument repeated`, `starred assignment
  target must be in a list or tuple`, `multiple starred expressions in assignment`,
  `'return' outside function`, `'yield' outside function` (and `'yield from'`), `default
  'except:' must be last`, `'break' outside loop` and `'continue' not properly in loop`, as
  `syntaxError` diagnostics;
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
`StrataPythonTest/Dyn/dyn_tests/`, the translator's tests too, and compares it with
`NAME.symtable`, the program's `symtable` output, and `NAME.expected.scope`, a golden dump.
`e01`–`e23` are programs with compile-time errors. `p38` uses `type` statements, which the pass
rejects, so it has no `symtable` comparison.

**Reading a name.** The lowering depends on the name's kind and on the kind of scope it is
read in:

| Kind, scope | Lowering | Exception if unassigned |
|---|---|---|
| `local`, `cell`, `free`, in a function | `refGet` the cell, then `requireDefined` | `UnboundLocalError: cannot access local variable 'x' where it is not associated with a value`; for `free`, `NameError: cannot access free variable 'x' …` |
| `globalExplicit`, `globalImplicit`, or `local` at module level | `py.loadGlobal m "x"`: the cell `globalCell m "x"` if it is defined, else the entry `"x"` of the `builtins` module's dict | `NameError: name 'x' is not defined` |
| any kind, in a class body | §6.7 | |

An imported name is read as any other name of its kind: the import statement wrote its cell
(§6.1). `loadGlobal` is CPython's `LOAD_GLOBAL`: whether `x` is a global or a builtin is
decided at each read, so a global assigned from another module and a builtin added at run time
(`builtins.log = print`) are both found.

```
    %12 : py.Value = base.refGet[py.Value](%3)
    %15 : py.Value = py.requireDefined(%12, "UnboundLocalError", "cannot access local variable 'y' where it is not associated with a value") ^propagate.0()
```

`len` read in a function:

```
    %20 : py.Value = py.loadGlobal("m", "len") ^propagate.0()
```

`requireDefined` is emitted on every read of a local. Removing redundant checks is a later pass.
**Writing** a name is `refSet` on its cell: `writeCell` for a function's cell, `writeGlobal m
"x"` for a global or a module-level `local`. In a class body, writing is
`py.setItem ns "x" v` (§6.7).

### 5.2 Module body

The top-level statements become `m.<module>`, with no parameters. Every name the module
binds is a global: reads and writes go through `globalCell m "x"` (§5.1), and the body
declares no locals. Module-level `def`, `class` and `import` statements run in place and bind
their name when control reaches them. The function falls off the end with `emitReturnNone`.
`__name__` is a global holding `py.strLit m`, and `__doc__` one holding the module's docstring,
or `None` if it has none. A read or `del` of another module attribute that CPython defines
(`__annotations__`, `__builtins__`, `__cached__`, `__file__`, `__loader__`, `__package__`,
`__path__`, `__spec__`) is rejected, because the translation has no value for it: `loadGlobal`
would find the `builtins` module's value or raise `NameError`. So is a write to `__builtins__`.
The exception is `__annotations__` in a module or class body that sets it up (§6.1), and in
the functions of such a module.

### 5.3 `def` and `lambda`

At the definition site, in source order:

1. Evaluate the decorators, top to bottom.
2. Evaluate each non-constant default value into a fresh *default cell*.
3. Evaluate the parameter annotations, in CPython 3.12's order (positional, positional-only,
   `*args`, keyword-only, `**kwargs`), then the return annotation.
4. Emit `const @m.f…`, at `m.f`'s code type, and `py.mkClosure[cs] code cells…`, with `cs`
   the cells' types, `m.f`'s parameter types but `args` and `kwargs`. The cells are the ones
   the callee captures, in `capturedVars` order (§6.6), then its default cells. A top-level
   function has only default cells.
5. If there are annotations, store them as `f.__annotations__`: a dict from each mangled
   parameter name, and `"return"`, to its annotation. With none, nothing is stored, and the
   run-time model gives `{}`, as CPython does.
6. Apply the decorators bottom to top, each with `py.call d (mkTuple f) mkKwargs`.
7. Write the result to the name's cell (a `lambda` is an expression and has no name).

```
    %21 : py.Value = py.mkClosure[[base.Ref(py.Value)]](@m.outer.inner, %3)
      -- %3: outer's cell for x
    %22 : base.Unit = base.refSet[py.Value](%4, %21)  -- inner = …
```

The annotations are evaluated in the enclosing scope, as in CPython 3.12, which Python 3.14
changes (§9, Q11).

**Python semantics to preserve:** defaults are evaluated once, at definition time, in the
enclosing scope. Free variables are bound late: a read sees the latest write to the cell.

### 5.4 The argument-binding prologue

A call passes one positional tuple and one keyword dict. Binding them to the source
signature is the callee's job, done by a branch-free *prologue* at the top of the entry block.
`PyTranslate.prologue` emits it. In a class, a private parameter's name is mangled everywhere,
its keyword included, as in CPython: `def m(self, __x)` in class `C` takes the keyword `_C__x`.

A function's prologue builds its defaults with `py.mkTuple`, applies `py.bindArgs` to its `args` and
`kwargs`, and takes each parameter, `*args` and `**kw` from the result with `py.tupleGet`. The
prologue binds as CPython 3.12 does, with one difference in the defaults: a constant default is
rebuilt at each call, while CPython evaluates it once, at the `def`. So for `def f(a=1000)`,
CPython's `f() is f()` is `True`, but the translation builds a new `1000` at each call. The corpus
program `i11_constant_default` pins this. When binding fails, the prologue raises the `TypeError`
that CPython raises, in CPython's order, but the text of the message is not specified. CPython's
text names the function's current `__qualname__`, which a program may change, as `functools.wraps`
does.

A program that reads, assigns or deletes a function's `__defaults__`, `__kwdefaults__` or
`__code__` is not admitted (an admission rule), since the translated function keeps the defaults
and the code of its `def`. Reading counts, since reading `__kwdefaults__` hands out the dict
that a later call reads. The corpus program `i09_assigned_defaults` pins today's translation
of one.

The defaults tuple has one entry per named parameter, positional ones first, then keyword-only ones:
a constant default, evaluated in the prologue itself at each call; a non-constant default, read from
its default cell, which the `def` filled (§5.3); or `undef` for a parameter without a default.
`py.bindArgs` names `Frame.handler` as `err`, and each value it gives is written to its parameter's
cell.

| Step | Lowering |
|---|---|
| defaults | `d = mkTuple [default or undef "p", …]`, one entry per named parameter |
| binding | `b = bindArgs args kwargs d nPosOnly nPos varPos varKw "p" …` |
| named `p` at index `i` | `tupleGet b i` |
| `*rest` | `tupleGet b n`, with `n` the number of named parameters |
| `**kw` | `tupleGet b n`, or `tupleGet b (n + 1)` after a `*rest` |

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
| target `o[i:j:s]` | evaluate `o`, `i`, `j` and `s`, then `py.setItem o (py.mkSlice i j s) v`, with `None` for an absent bound | as CPython's `STORE_SLICE`, which calls `__setitem__` with a slice |
| target `a, b` / `[a, b]` | `t = py.unpackSeq v 2`, then `py.tupleGet t i` for each target, recursively. Each target is evaluated when it is assigned | an exact length check, `ValueError: not enough / too many values to unpack` |
| target `a, *b` | `py.unpackEx v before after`, then as above. The starred target receives a list | the compiler rejects a starred target outside a tuple or list, and two in one (§5.1) |
| `x op= e` | read `x` once (evaluating `o` and `k` once for `o.a` and `o[k]`), apply the in-place operation (`py.iAdd` … `py.iBitXor`), write back | in place: `xs += ys` mutates `xs` |
| `x: T = e` | as `x = e`. In a module or class body, `T` is then evaluated and, for a simple name, stored as `__annotations__["x"]`, as CPython 3.12 does. The body starts with `SETUP_ANNOTATIONS` (`__annotations__ = {}` if absent) when it holds an annotated assignment anywhere outside a nested `def` or `class`. In a function, `T` is not evaluated | `x: T` with no value assigns nothing: in a function it only makes `x` local; in a module or class body it still stores `T`. `o.a: T` and `o[k]: T` evaluate `o` and `k`, then `T`, as CPython does. `@dataclass`, `NamedTuple` and `TypedDict` read `__annotations__`. `from __future__ import annotations` is rejected (§9, Q11) |
| `del x` | `requireDefined` (raises `NameError` or `UnboundLocalError`), then `refSet` of `undef "x"` | a global is not looked up in `builtins` |
| `del o.a`, `del o[k]`, `del o[i:j:s]` | evaluate `o` and `k`, then `py.delAttr o "a"` or `py.delItem o k`, with `py.mkSlice` for a slice | |
| `del a, (b, c)` | delete each target left to right, element by element | no unpacking |
| `assert c` | as `assert c, m`, raising the `AssertionError` class itself | |
| `assert c, m` | `c` as a condition (§6.2). The true target continues; the false target loads `py.assertionError`, the `AssertionError` class, evaluates `m`, then `py.call`s the class on it and raises the result with `py.toException` (§7.1) | `c` is tested once; `m` is evaluated only when the assertion fails; `AssertionError` is the class itself, as CPython's `LOAD_ASSERTION_ERROR`, even if `builtins.AssertionError` is rebound |
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
    %9 : base.Bool = py.truthy(%8) ^propagate.0()
    branch(%9) ^then.0() ^else.0()
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
| `...` | `py.ellipsisLit`, as CPython's `LOAD_CONST` |
| complex literal, t-string | **rejected** |
| name | §5.1 |
| `a op b` | evaluate `a`, then `b`, then `py.add`/`sub`/`mult`/`matMult`/`div`/`floorDiv`/`mod`/`pow`/`lShift`/`rShift`/`bitAnd`/`bitOr`/`bitXor` |
| `-a`, `+a`, `~a`, `not a` | `py.uSub`, `py.uAdd`, `py.invert`, `py.not` |
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
| `f"a{x}b"` | as CPython's `FORMAT_VALUE` and `BUILD_STRING`: a total `py.strConcat` over `strLit` parts and fields, or the lone part itself. A field `{x!r:spec}` evaluates `x`, then `spec` (itself an f-string, `""` if absent), then applies `py.repr` (`py.str`, `py.ascii`), then `py.fmtValue x spec`. None of these looks up a builtin: CPython ignores `builtins.repr = …` here |
| `(x := e)` | evaluate `e`, write it to `x` (§5.1), and use the value `e`. In a comprehension, the target is the enclosing function's local, a `cell` only if a nested scope captures it (§6.8) |
| `lambda` | §5.3, as an expression |
| comprehensions | §6.8 |
| `yield`, `await`, a generator expression, a starred expression elsewhere | **rejected** |

**Short-circuit operators.** A join block takes the expression's value as its single
parameter. Expression temporaries are the only values the translator passes through block
parameters.

```
    %5 : base.Bool = py.truthy(%4) ^propagate.0()     -- a and b
    branch(%5) ^and.0() ^join.0(%4)
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
    %14 : py.Value = py.mkTuple(%12)
    %16 : py.Value = py.strLit("k")
    %17 : py.Value = py.mkKwargs(%16, %13)
    %18 : py.Value = py.call(%11, %14, %17) ^propagate.0()   -- f(x, k=y)
```

### 6.4 Loops

**`while c: B else: E`:**

```
    jump ^head.0()
  head.0():
    …                                    -- %4 = c
    %5 : base.Bool = py.truthy(%4) ^propagate.0()
    branch(%5) ^body.0() ^else.0()        -- ^exit.0() without an else
  body.0():                              -- exits += loop(exit.0, head.0)
    …
    jump ^head.0()
  else.0():                              -- E
    jump ^exit.0()
  exit.0():                              -- started only if targeted
```

**`for x in xs: B else: E`:**

```
    %9 : py.Value = py.getIter(%8) ^propagate.0()
    jump ^head.0()
  head.0():
    %10 : py.Value = py.next(%9) ^stop.0()                -- its own successor
    %11 : base.Unit = base.refSet[py.Value](%3, %10)       -- x = …
    …                                                    -- B, raising to ^propagate.0()
    jump ^head.0()
  stop.0(%12 : py.Value):
    %13 : base.Bool = py.isStopIteration(%12)
    branch(%13) ^else.0() ^propagate.0(%12)               -- anything else propagates
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
and the `finally` body runs before the loop exits. The scope pass reports one outside a loop
(§5.1); a loop does not count inside a nested `def` or `class`, or in its own `else`.

### 6.6 Closures

A nested `def` or `lambda` becomes a separate function of the module (§5.3). Its leading
parameters are the cells it captures, then its default cells. The captured cells are in
`capturedVars` order: `Scope.freeVars`, the free names the scope uses, in order of first use,
then the names it only passes on to nested scopes, sorted by name. A class body also
captures its `free_class` names (§6.7), in the same order of first use. The `mkClosure` at the definition
site passes the same cells in the same order.

Capture emits no extra instructions. The inner function reads and writes the outer
function's own cell, which gives `nonlocal` and late binding. `mkClosure` takes one operand
per element of its type argument, each a `base.Ref(py.Value)`, so capturing a value is a type
error. A `const @m.f` naming a
function the module does not define fails `Module.Raw.WF`.

### 6.7 Classes

`class C(B1, B2, k=v): body` lowers to

```
C = __build_class__(<closure of m.C.<body>>, "C", B1, B2, k=v)
```

The result of `__build_class__` is applied to the decorators, then written to `C`'s cell.
The bases and keywords are evaluated left to right after the body closure is created.
`__build_class__` is `py.qualifiedRef "builtins" "__build_class__"`. Its model calls the
body closure with the namespace `__prepare__` returns as the only positional argument.

`m.C.<body>` is an ordinary function. Its prologue binds `ns` from `args[0]`, and
`classNs` (§4) holds `ns`. In the body, names are mangled (§5.1) and:

| Kind of `x` | Write | Read |
|---|---|---|
| `local` | `py.setItem ns (strLit "x") v` | `getOptionalItem ns "x" (undef "x")`, `isDefined`, branch; if absent, the global read of §5.1 (`LOAD_NAME`) |
| `globalImplicit` | | the same as `local` |
| `globalExplicit` | `writeGlobal` | the global read of §5.1 |
| `free` | `writeCell` (`nonlocal`) | `getOptionalItem ns`, then the captured cell if absent (`LOAD_FROM_DICT_OR_DEREF`) |

- Methods are closures (§6.6). They never capture class-scope names. A name the body binds
  that a method reads from an enclosing function is `free_class` (`Uses.freeClass`): the body
  captures that function's cell only to pass it on.
- The body returns `None`.
- Before the first statement, the body stores `__module__` (a read of `__name__`) and
  `__qualname__`, sets up `__annotations__` if it holds an annotated assignment (§6.1), and
  stores `__doc__` if it starts with a docstring, as CPython 3.12 does (§9, Q9).
- The namespace is any mapping `__prepare__` returns, as `enum`'s is, so the body uses the
  mapping protocol, as CPython does (§9, Q10). A read is `getOptionalItem`, which calls
  `__getitem__` and treats a `KeyError` as absent. A write is `py.setItem`. `del x` is
  `py.delItem`, and any exception it raises becomes `NameError`, as `DELETE_NAME` does.

**Zero-argument `super()` and `__class__`.** The scope pass marks a class with
`needsClassCell` when a method loads `super` or `__class__`. Then the class statement makes
the `__class__` cell, `refNew (undef "__class__")`, before the body closure. The body
captures it like a free variable (`capturedVars`), and the methods capture it from the body.
After `__build_class__` returns, and before the decorators run, the statement writes the class
to the cell, so `__class__` is the undecorated class, as in CPython. In a method, `__class__`
reads the cell, and `super()` is `super(__class__, p)`, `p` the first positional parameter.
`super().x` reads the cell, then `p`, as CPython's `LOAD_SUPER_ATTR` does. A bare `super()`
is a call in CPython, which checks `p` first, then the cell, and raises `RuntimeError`
("super(): arg[0] deleted", "super(): empty __class__ cell"); it is lowered in that order,
with those errors. CPython also compiles `super().__class__`, and every `super().x` in a
module whose symbol table names `super` (`s = super`, or `global super` in any function), as
such a call, and so does the translator. Where CPython raises
`RuntimeError` at run time, `super()` in a function with no positional parameter, in a class
body or outside a class, it is rejected. It is rejected too if the module may rebind `super`,
which CPython would then call with no arguments. A class nested in a method has two
`__class__` cells: its own, which its methods capture, and the method's, which its body
reads.

This differs from CPython mainly in one way. CPython fills the cell inside `type.__new__`,
before `__set_name__` and `__init_subclass__` run. Here it is filled after `__build_class__`
returns, so a `super()` or `__class__` that runs while the class is created (in
`__set_name__`, `__init_subclass__` or a metaclass) finds the cell undefined (§9, Q6;
`m_super_hook.py`). And the cell holds whatever `__build_class__` returns: CPython's cell
holds the class `type.__new__` makes, and stays empty if the metaclass never calls it; and
CPython raises `RuntimeError` ("__class__ not set …") when a metaclass drops
`__classcell__`.

**Declared shapes.** Each class body's function states the class's declarations as
attributes (`docs/Dyn.md` §2), which `StrataPython/Dyn/Shape.lean` computes, for Pylate to
check the class's declared shape (`Pylate/doc/POMAD.md` §4.9) against what its code does.
They state what the source declares, before any decorator or metaclass runs, written as it
is written: no name is resolved, so a consumer such as Pylate must decide what `TypedDict`,
`ClassVar` or `int` denote, from the bindings it follows. Private names are
mangled, as the compiler does. All of a class's facts are on one function, its body's
`m.C.<body>`:

| Key | Value |
|---|---|
| `py.bases`, `py.keywords`, `py.decorators` | the bases, the class keywords (`[{name = "metaclass", value = E}, …]`, `**kw` with the name `unit`) and the decorators, top to bottom, if any |
| `py.fields` | always present, possibly empty, so that a function with `py.fields` is a class body: every declared field, in source order, `{name = "x", type = E}`. A field is an annotated simple name of the body, outside nested `def`s and `class`es, with `default = E` if it has a value; or a `self.x: T` of an `__init__` of the body that is not a stub, has no decorator and does not bind its first parameter again, outside its nested `def`s and `class`es, with or without a value, marked with that function, `in = @m.C.__init__`, so that a field belongs to one `__init__` when a class has several. One under a compound statement has `conditional = true`; this is syntactic, so a field of an `__init__` without it may still be unset when the `__init__` returns or raises before reaching it. A name annotated twice is listed twice; in `__annotations__`, the last annotation wins |
| `py.slots` | each assignment statement to `__slots__` (`=`, `+=` or annotated), in source order, `{value = E}`, with `augmented = true` for `+=`, `unpacked = true` if it is one name of a tuple or list target, and `conditional = true` under a compound statement, if any; any other binding of `__slots__` is in `py.bindings` |
| `py.bindings` | every other binding of a name in the body, outside nested `def`s and `class`es, statement by statement in source order, if any; within a statement, its assignment expressions come first; those in a handler's exception type come just before its `except` binding. An assignment `x = E` is `{name = "x", value = E}`, with `augmented = true` for `x += E`, where `value` is the right operand, and `unpacked = true` for one name of a tuple or list target, where `value` is the whole right-hand side. Any other binding is `{name = "x", binding = K}`, `K` one of `"def"`, `"class"`, `"import"`, `"for"`, `"with"`, `"except"`, `"del"` and `":="`; `except … as x` is followed by a `"del"` of `x` after its handler, as CPython unbinds it there. `conditional = true` marks a binding that may not run: one under a compound statement, a `for` target, one in a handler's exception type, and an assignment expression in an operand of `and` or `or` after the first, in a branch of `a if c else b`, in a comparison of a chain after the first, or in an `assert` message. A field and an assignment statement to `__slots__` are in `py.fields` and `py.slots` instead. Names that the class statement binds itself (`__module__`, `__qualname__`, `__doc__` for a docstring, `__annotations__`, `__classcell__`) are not listed. An Enum's members, a `ctypes.Structure`'s `_fields_` and a Pydantic `model_config` are found here. The captures of a `match` and the name of a `type` alias are not listed. The translator rejects both statements, so the translation fails anyway |

A name the body declares `global` or `nonlocal` is bound outside the class, so no key states
it: not its bindings, its `__slots__` assignments or its `__init__`'s fields.
The keys do not record their order relative to each other. So when a class body binds a
name under two keys, such as `x: int = 1` (a field) followed by `x = "s"` (a binding), the
attributes don't say which binding comes last.

An annotation is stated as an expression that the class body evaluates, so a private name
in it is mangled. Under `from __future__ import annotations`, CPython instead stores each
annotation's source text unmangled: `x: __T` in `class C` gives `'__T'`, but the attribute
states `"_C__T"`. The translator rejects that import, so the translation fails anyway.

An `__init__` binds its first parameter again with a binding in its body, such as an
assignment or an import, or with a nested function or class body whose `nonlocal` reaches
it. A bare annotation of the parameter, such as `self: T`, counts too. A decorated `__init__`
declares no fields, because a decorator such as `@classmethod` can make its first parameter
something other than the instance. What an `__init__` stores to `self` is not stated: it is
in the function's code, to be checked against `py.fields`.

A PySpec model's class body (`StrataPython/Dyn/PySpec/Module.lean`) also states
`py.initFields`: the fields that the model's stub `__init__` assigns, `{name, trustedType, in =
@…__init__}`, apart from `py.fields`, because no code states them (§12.10). A model's field
records carry `trustedType` instead of `type`, so that a trusted type never shares a key with
an annotation that nothing checks.

An expression `E` is a name or attribute chain as a string (`"typing.Optional"`),
`{name = E, args = [E, …]}` for a subscript, `{union = […]}` for `A | B | …` (the `|`
operator, also in a value), a list `[E, …]`, `{tuple = [E, …]}`,
`{call = E, args = [E, …], keywords = […]}`, `{op = "*", args = [E, E]}`
for another binary operator and `{op = "-", args = [E]}` for a unary one, a constant (a
boolean, an integer, a float, `unit` for `None`, `{str = "s"}`, `{ellipsis = unit}`), or
`{expr = "Lambda"}` for any other expression, by its `ast` class name.

### 6.8 Comprehensions

List, set and dict comprehensions follow Python 3.12 (PEP 709): they are inlined into the
enclosing function. Each `for` clause is a `py.forEach` whose body is a region of that
function. No function is created.

```
insn forEach (iterable : Value) (&body (item : Value) : raising Unit) (^err (exc : Value)) : Unit
```

It iterates `iterable`, runs `body` once per item, and falls through when the iterator is
exhausted. An exception from `iter` or `next` goes to `err`. A region cannot name an outer
block, so the body cannot reach `Frame.handler`. Instead the body returns `error e`, which
`forEach` forwards to `err`, and `ok ()` to go on. `PyBuild.forEach` emits it.

`[e for x in xs if c for y in ys]` lowers to:

1. Evaluate `xs` in the enclosing scope, under the enclosing handler.
2. `acc = mkList` (`mkSet`, `mkDict`).
3. One cell per iteration variable (`x`, `y`): `refNew (undef "x")`. These cells belong to
   the comprehension. Inside it they shadow the enclosing scope's names, and they are not
   in `Frame.locals` afterwards. There is one cell per variable per evaluation, so closures
   created in the comprehension share it, as in CPython.
4. `forEach xs ^body ^err(H)`, `H` the enclosing handler. The body region, with its own
   `propagate` handler:
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

Generator expressions keep their own scope. They and generator functions (any `yield` the
function evaluates, which the scope pass records in `Scope.generator`) are **rejected**. The planned route is an opaque `py.mkGenerator` over a lifted function (§8).

### 6.9 Rejected outright

`async def`, `await`, `async for`, `async with`, `match`, `try`/`except*`, `type` aliases
and PEP 695 type parameters, `yield` and `yield from`, relative imports, and `import *`.
Each is rejected as §3 describes.

## 7. Exceptions, `finally` and `with`

### 7.1 `raise`

| Source | Lowering |
|---|---|
| `raise E` | `v = eval E`, `e = py.toException v`, then `jump ^handler(e)`. `toException` instantiates a class and raises `TypeError` for a non-exception, as CPython's `RAISE_VARARGS` does |
| `raise E from C` | `v = eval E`, `c = eval C`, `e = py.toException v`, `py.setCause e c`, then `jump ^handler(e)`. `setCause` instantiates a class too, sets `__suppress_context__`, and raises `TypeError` for a cause that is neither an exception nor `None` |
| bare `raise` inside an `except` body of the same function | `jump ^handler(exc)`, `exc` being the exception the innermost enclosing `except` body handles (`Ctx.handled`). Nested `try` statements in that body do not change it, because each handler restores the exception being handled when it ends. A `finally` body inside it is elsewhere (§7.2) |
| bare `raise` elsewhere | `e = py.handledExc`, then `jump ^handler(e)`. `handledExc` reads the exception being handled at run time (§7.2), which an `except` body in a caller may have set, and raises `RuntimeError` if there is none |

`raise` is a `jump`. A Python function raises by transferring to `Frame.handler`, which is a
block taking the exception. At the outermost level that block is `propagate.0`, which
returns `base.error`.

**`__context__`.** An exception that an operation raises itself while another is being
handled (§7.2) gets that one as its `__context__`, unless it is that one, as in CPython.
`py.toException` sets it too, because the `jump` of a `raise` cannot. An exception that comes
out of a callee keeps its `__context__`, and so does one that `py.handledExc` or the direct
jump of a bare `raise` raises again. `Py`'s module docstring gives the details.

### 7.2 `try`/`except`/`else`/`finally`

Write `S` for the exits stack and `H` for the handler in effect at the `try` statement.
Labels are allocated up front:

- `catch(exc)` and `unwind(exc)`, if there are `except` clauses, and `clear_i(exc)` for each
  clause `i` with `as e`;
- `fin(pending : py.Completion)`, `finRaise(exc)` and `superseded(exc)`, if there is a
  `finally`;
- `join`.

Let `H'` be `finRaise` if there is a `finally`, and `H` otherwise. Let `S'` be `S` with
`cleanup fin` pushed if there is a `finally`, and `S` otherwise.

| Part | Handler | Exits stack | Normal end |
|---|---|---|---|
| `try` body | `catch` if there are clauses, else `H'` | `S'` | `jump ^else()` if there is an `else`; otherwise as `else` would end |
| `catch(exc)`: `prev = py.pushExcInfo exc`, then the clause tests | `unwind` | `S'` | see the clause chain below |
| clause body `i` | `unwind`, or `clear_i` if `as e` | `S'` + `handler prev` | leave the handler, then `fin(completionNormal)` or `join` |
| `unwind(x)` | | | `py.popExcept prev`, then `jump ^H'(x)` |
| `else` body | `H'`. The `except` clauses do not cover it | `S'` | `fin(completionNormal)` or `join` |
| `finRaise(exc)` | | | `%c = completionRaise exc`, `jump ^fin(%c)` |
| `fin(pending)`: `prev = py.pushPending pending`, then the `finally` body, emitted once | `superseded` | `S` + `handler prev` | `py.popExcept prev`, then dispatch `pending` |
| `superseded(exc)` | | | `py.popExcept prev`, then `jump ^H(exc)` |

**The clause chain** in `catch(exc)`, for each clause `except T as e`: evaluate `T`,
`%m = py.excMatch exc T`, then `branch %m ^body_i() ^next_i()`. A bare `except:` jumps
straight to its body. If the last clause does not match, the chain ends with
`jump ^unwind(exc)`. In body `i`, `Ctx.handled` is `exc`, and `e` holds `exc`. `clear_i(x)`
unbinds `e`, then `jump ^unwind(x)`.

**The exception being handled** is run-time state, as in CPython. `py.pushExcInfo exc` makes
`exc` the exception being handled and returns the previous one, `prev`, as CPython's
`PUSH_EXC_INFO` does. Every way out of the handler restores `prev` with `py.popExcept`, as
CPython's `POP_EXCEPT` does: `unwind`, which every failure and an unmatched exception reach,
and *leaving the handler*, which is how a clause ends normally and how the exit walk passes its
`handler` entry. Leaving the handler is `py.popExcept prev`, then unbinding `e` if the clause
binds it, both under `H'`, the handler around the `try`, as in CPython.

**In the `finally` body**, the exception being handled is the pending one on the exceptional
path, as in CPython, which runs that path's copy of the body after `PUSH_EXC_INFO`. The body
is emitted once, so the push depends on the path at run time: `py.pushPending pending` makes
the exception of a `raise` completion the one being handled, and leaves the state as it is
for the other completions. It returns `prev` like `pushExcInfo`, and every way out of the
body restores it: the normal end before the dispatch, the exit walk through the `handler prev`
entry, and `superseded`. A bare `raise` in the body reads `py.handledExc`, since `Ctx.handled`
cannot tell the paths apart.

**Unbinding `e`** is CPython's `e = None; del e`. For a local, free or global name, it writes
`undef` to the cell. In a class body, it stores `None` in the namespace, then deletes it.

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
`protect fin`, which makes `finRaise`, then `fin`, then the dispatch, then `superseded`. A
`finally` body that always exits abruptly has no dispatch.

**When the `finally` body exits abruptly.** Its own exit replaces the pending completion,
as in CPython; Python 3.14 (PEP 765) only adds a `SyntaxWarning` for `return`, `break` and
`continue` there. When it raises while an exception is pending, CPython also sets the new
exception's `__context__` to the pending one. CPython does this through the exception being
handled: on the exceptional path it runs the `finally` body after `PUSH_EXC_INFO`, so §7.1's
rule sets `__context__` where the body raises. So a failure in the body goes to
`superseded(exc)`, which restores the exception handled before and raises `exc` to `H`, with
no chaining of its own. A `return`, `break` or `continue` in the body restores it too, then
walks from `S`.

**Why a completion.** CPython 3.9 and later copy the `finally` body once per exit, with no
bound on the copies, and exponentially many when nested `finally` bodies themselves exit
abruptly; up to 3.8 it emitted one copy. Dyn emits the body once, at the cost of a
linear dispatch on the completion. V8 and Kotlin's coroutines dispatch on a token the same
way. The JVM's `jsr`/`ret` was abandoned because its targets were dynamic, which made
verification intractable; a completion's targets are all static.

Example: c1 (§10). The prologue is elided, and `cleanup` is read as a global.

```
  entry.0(%args.0 : py.Value, %kwargs.0 : py.Value):
    …
    %int.1 : py.Value = py.intLit(1)
    %comp.0 : py.Completion = py.completionReturn(%int.1)    -- return 1 → exit walk
    jump ^fin.0(%comp.0)
  finRaise.0(%exc.0 : py.Value):                             -- the try body's handler
    %comp.1 : py.Completion = py.completionRaise(%exc.0)
    jump ^fin.0(%comp.1)
  fin.0(%pending.0 : py.Completion):                         -- finally, emitted once
    %prev.0 : py.Value = py.pushPending(%pending.0)
    …                                                        -- cleanup(), ^superseded.0()
    %pop.0 : base.Unit = py.popExcept(%prev.0)
    py.Completion.case(%pending.0) ^join.0() ^ret.0() ^propagate.0() ^unreachable.0() ^unreachable.1()
  ret.0(%val.0 : py.Value):
    %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%val.0)
    ret(%ret.0)
  unreachable.0():
    unreachable
  unreachable.1():
    unreachable
  superseded.0(%exc.1 : py.Value):                           -- cleanup() raised
    %pop.1 : base.Unit = py.popExcept(%prev.0)
    jump ^propagate.0(%exc.1)
  join.0():
    …                                                        -- falls off: return None
```

### 7.3 `with`

`with E as t: B`, where `H` and `S` are as in §7.2, follows CPython 3.12's `BEFORE_WITH`
and `WITH_EXCEPT_START`:

1. Evaluate `mgr = E`. Then `enter = py.enterMethod mgr` and `exit = py.exitMethod mgr`,
   both under `H`. They look `__enter__` and `__exit__` up on the type, in that order, and
   raise CPython's `TypeError` if one is missing.
2. `v = py.call enter () {}`, under `H`.
3. Protected region: handler `wexc`, stack `S` + `cleanup fin`. It assigns `t = v` (an
   assignment that raises still runs `__exit__`), then runs `B`. A normal end is
   `jump ^fin(completionNormal)`.
4. `wexc(exc)`: `prev = py.pushExcInfo exc`, then, under `unwind`,
   `r = py.exitWithExc exit exc`, which calls `exit(type(exc), exc, exc.__traceback__)`, and
   `b = py.truthy r`. Then `branch b ^suppress() ^unwind(exc)`. A true result suppresses the
   exception: `suppress` is `py.popExcept prev`, then `jump ^join()`. `unwind(x)` is
   `py.popExcept prev`, then `jump ^H(x)`, so a false result re-raises the original
   exception.
5. `fin(pending)`, emitted only if some exit reaches it: `py.call exit (None, None, None)`
   under `H`, then dispatch `pending` as in §7.2. The raise successor cannot be reached on this
   path, but it must exist, so it goes to `H`.

The exception path calls `__exit__` with the exception and never builds a completion. Every
other path goes through `fin`, which calls `__exit__` once. `with a, b: B` is
`with a: with b: B`.

## 8. Gaps in the environment and builder

**Operations the rules need that `Py.env` does not declare:**

| Operation | Signature (DSL) | Needed by |
|---|---|---|
| `mkGenerator` | `insn mkGenerator [(as : list)] (code : Fn as failing) (cells : Ref Value…) : Value` | generators (stage 1, opaque) |

**Declarations to fix:**

- `unsupported` takes its construct name as a `py.Value`; the other name-carrying operands
  are `base.String`.

**Builder (`PyBuild`) and translator (`PyTranslate`):**

- The scope and the exits stack live in the translator's state, `TransM` (§4).
- `PyBuild.buildFuncTypedWith` builds and checks a function and returns its body's result.
- Blocks are `BlockRef`s and transfers `Target`s, so Lean checks what a jump passes against
  what its block takes. `Frame.handler` is a `Target` that takes the exception, and may
  pre-bind arguments of its block before it (`withHandlerTo`).
- `dispatch` and `dispatchArms` take `Target`s, in `py.Completion.case`'s successor order.
- `tryFinally`, `protect` and `dispatchArms` run their bodies in any `MonadPy` monad, so the
  translator passes `TransM` bodies. `forEach` does the same, for comprehensions.
- `exitWalk` handles `loop`, `handler` and `cleanup` entries.

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
2. **Exception chaining in `finally`.** *Resolved.* On the exceptional path, the `finally`
   body runs with the pending exception as the one being handled, as in CPython, through
   `py.pushPending` (§7.2). `sys.exc_info()` sees it, §7.1's rule sets `__context__` where
   the body raises, and a bare `raise` there reads `py.handledExc`. `superseded` does no
   chaining of its own.
3. **Definedness.** Should definedness stay as `py.undef` values in cells, or become
   `Ref (Option Value)`? Only `undef`, `isDefined` and `requireDefined` would change.
4. **Module objects and imports.** *Resolved.* A module value is the result of
   `py.importModule`, written to the bound name's cell. `from a import x` is
   `py.importFrom`, evaluated once at the import, so the binding is a snapshot. `a.b.f` is
   `py.attr` on the module value (§6.1).
5. **Special-method lookup.** *Resolved.* CPython looks special methods up on the type, and
   `py.attr` on the instance would differ when an instance attribute shadows the method.
   `with` uses `py.enterMethod` and `py.exitMethod`, which look up on the type (§7.3), and
   operations such as `truthy` and `getIter` do the lookup themselves.
6. **`__class__` cell.** *Resolved*, with one difference from CPython. CPython's body
   creates the cell and stores it as `ns["__classcell__"]` for `type.__new__` to fill, but no
   instruction turns a `base.Ref(py.Value)` into a `py.Value`. So the class statement creates
   the cell and fills it after `__build_class__` returns (§6.7). A `super()` that runs while
   the class is created finds the cell undefined. Filling it in time would need an operation
   that installs the cell in the namespace.
7. **Unpacking.** *Resolved.* Two operations: `unpackSeq` for a target without a starred
   element and `unpackEx` for one with it, as CPython's `UNPACK_SEQUENCE` and `UNPACK_EX`.
8. **Global fallback.** *Resolved.* The scope pass classifies a module global and a builtin
   alike as `globalImplicit`, and the split is made at run time by `py.loadGlobal`, which
   reads the global cell, then `builtins`, as CPython's `LOAD_GLOBAL` does (§5.1).
9. **Implicit class-body stores.** *Resolved.* The body first stores `__module__` (the
   module's `__name__`) and `__qualname__` into the namespace, then `__annotations__ = {}` if
   it holds an annotated assignment, then `__doc__` if it starts with a docstring, as
   CPython's class body does (§6.7).
10. **Namespace reads.** *Resolved.* Class-body reads use `getOptionalItem`, which calls the
    namespace's `__getitem__` (§6.7).
11. **Annotations and Python 3.14.** Annotations follow 3.12: they are evaluated eagerly, in
    module and class bodies, into `__annotations__` (§6.1). Python 3.14 (PEP 649) instead
    compiles each module, class and function's annotations into a lazy `__annotate__`
    function, run when `__annotations__` is first read. Moving to 3.14 changes:
    - the translator: `setupAnnotations`, `findAnn`, the store of each annotated assignment
      and the store of a function's `__annotations__` give way to one `__annotate__` closure
      per module, class and function;
    - conditional annotations: 3.14 records which annotated assignments ran
      (`__conditional_annotations__`), so `if c: x: int` adds `x` only if the branch ran;
    - the scope pass and `scope_symtable.py` (which refuses 3.14 today): 3.14's annotation
      scopes, which can see the class's names;
    - the runtime model: 3.14's `type.__annotations__`, which calls `__annotate__`.

    `from __future__ import annotations` makes 3.12 store each annotation's source text,
    unevaluated. It is rejected for now: the translator would need that text. Parameter and
    return annotations are evaluated at the `def`, as in 3.12 (§5.3); 3.14 makes them lazy
    too.

## 10. Acceptance tests

Each case is an exception edge that an earlier translator lowered wrongly while still
passing its well-formedness check. Each becomes a golden test, plus an interpreter check that
counts `cleanup()` calls. The repros are `c1`–`c7` and `t30_loop_try_nested` in
`StrataPythonTest/Dyn/dyn_tests/`. `dyn_tests.txt` lists them all as supported.

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

These checks apply to all of them. `Module.Raw.WF` holds. Every block is reachable from the
entry: the builder drops the others, such as the `catch` of a `try` body that cannot fail. No
`finally` or `__exit__` body is emitted more than once.

## 11. Coverage

*Implemented* marks what `PyTranslate.translate` lowers. It rejects every other construct with
a diagnostic.

| Construct | Section | Status |
|---|---|---|
| module body; `def`, nested too, and `lambda`, with positional, positional-only, keyword-only, `*args` and `**kwargs` parameters, defaults, annotations and decorators; prologue; `return` | §5.2–§5.5 | specified; implemented |
| name resolution (all five kinds, mangling, compile-time errors) | §5.1 | specified; implemented (`PyScope.analyze`, CPython 3.12 model) |
| local names | §5.1 | specified; implemented |
| cell and free names | §5.1 | specified; implemented |
| global names, `global`, builtins | §5.1 | specified; implemented |
| `import`, `from … import` | §6.1 | specified; implemented |
| relative import, `import *` | §6.1 | unsupported (rejected by the scope pass and the translator) |
| expression statement, `pass`, assignment to a name (chained too) | §6.1 | specified; implemented |
| assignment to an attribute or subscript | §6.1 | specified; implemented |
| tuple and starred targets | §6.1 | specified; implemented |
| augmented assignment | §6.1 | specified; implemented |
| annotated assignment | §6.1 | specified; implemented |
| `del` | §6.1 | specified; implemented |
| `assert` | §6.1 | specified; implemented |
| `nonlocal` | §6.6 | specified; implemented |
| `if` / `elif` / `else` | §6.2 | specified; implemented |
| literals, `...`, every binary and unary operator, comparisons (chained too), `and`, `or`, `x if c else y` | §6.3 | specified; implemented |
| conditions (`transCond`) | §6.2 | specified; implemented |
| calls, with keywords, `*` and `**` | §6.3 | specified; implemented |
| displays and unpacking in them | §6.3 | specified; implemented |
| attribute, subscript, slice (inside a tuple too) | §6.3 | specified; implemented |
| f-strings | §6.3 | specified; implemented |
| walrus | §6.3 | specified; implemented |
| complex literal, t-string | §6.3 | unsupported |
| `while` / `else`, `break`, `continue` | §6.4–§6.5 | specified; implemented |
| `for` / `else` | §6.4 | specified; implemented |
| closures | §6.6 | specified; implemented |
| `class`, bases, keywords, decorators | §6.7 | specified; implemented |
| zero-argument `super()`, `__class__` | §6.7 | specified; implemented (Q6) |
| list, set and dict comprehensions | §6.8 | specified; implemented |
| generator expressions, `yield` | §6.8 | unsupported; a generator function is a stub |
| `raise`, `raise … from` | §7.1 | specified; implemented |
| bare `raise` | §7.1 | specified; implemented |
| `try` / `except` / `else` | §7.2 | specified; implemented |
| `finally` | §7.2 | specified; implemented |
| `with`, several items | §7.3 | specified; implemented |
| `async`, `await`, `match`, `except*`, `type`, PEP 695 | §6.9 | unsupported; an `async def` is a stub |

## 12. Contracts and PySpec models

PySpec (`StrataPython/Specs/`) describes a library without its code. A PySpec model is a
Python module whose functions have no body. A function's contract is made of `assert`
statements and the decorators `@requires`, `@admit`, `@ensures` and `@modifies`. A class may
have the decorators `@invariant` and `@exhaustive`. A module may declare ghosts with
`ghost(...)`. `Specs.lean` reads a model into an array of `Signature`s. This section gives the
rules by which a translation from PySpec represents each construct of that array in Dyn. It
builds on Dyn's contracts ([Dyn](./Dyn.md#1-overview): *Contracts*, *Extern functions*,
*Frames*, *Ghost state*) and on Python's operations for contracts (§2). It does not lower
anything to Strata Core.

The translation from PySpec (§12.13) comes with changes to PySpec: those that `py.invariants`
needs (§12.6), and those that make what `Specs.lean` drops visible to the translation (§12.7).
The admission work provides the admission rules of §12.11, the model's part included. This
section left two questions to the translation, which §12.13 answers:

* What the translation does when names from two model modules clash. For example, a function
  `put_item` of the module `servicelib.Storage` and a method `put_item` of a class `Storage` of
  the module `servicelib` would both be `@servicelib.Storage.put_item` (§12.1).
* Whether an `@admit` on an overload stub rejects the model, as ToLaurel's `unsupportedAdmit`
  does, or becomes a `free ensures` clause that applies only when the dispatch argument is the
  stub's literal.

*PySpec's meaning* of a clause is the CPython 3.12 meaning of the Python source that it came
from, except where `Specs.lean` already fixed another meaning. For example, `Specs.lean` turns
both `x == None` and `x is None` into one form, and that form means identity. A declared type
means what PEP 484 says: the values that a type checker accepts for it. For example, `x: float`
accepts an `int`.

**The direction rule.** Nothing checks a model's clauses against code, so they are trusted.
Each rule below therefore errs in one direction only:

* A `requires` clause may be stronger than PySpec's meaning, never weaker. A weaker one would
  make the model's `free ensures` clauses trusted at calls that the modeler never covered.
* A `free ensures` clause may be weaker than PySpec's meaning, never stronger.
* A frame may be larger than PySpec's meaning, never smaller. A smaller one would let a consumer
  assume that a location keeps its value where the library may change it.

The exceptions are the trusted modeling assumptions of §12.9.

### 12.1 The model module

* **Module.** A model module, such as `servicelib.Storage`, is a Dyn module of the same name.
  It holds an extern for each function and method, its ghosts, and its module body
  `@|servicelib.Storage.<module>|`, a defined function. A verifier takes the model's modules
  together with the program's, and the program's `py.importModule("servicelib.Storage")` runs
  the module body. The model stands for the library, as PySpec already assumes.
* **Module body.** It is a module body as §5.2 describes. It sets `__name__`, but not `__doc__`:
  the model's docstring isn't the library's, so the module's `__getattr__` makes `__doc__` an
  unknown value, as for any name that the model leaves out. It binds each function's global
  cell to `py.mkClosure[[]](@servicelib.Storage.f)`. It builds each class with
  `__build_class__` (§6.7). It binds the module's `__getattr__` (below). It binds
  each name that the source imports from another model module, such as `from .Storage import
  Storage`, with `py.importFrom`. It binds no name that the source imports from the standard
  library, such as `Dict` from `typing`: the module's `__getattr__` makes such a name an
  unknown value.
* **The module body never raises.** This is about the IR module body that the translation
  writes. An exception there would make all code after `import servicelib` unreachable to a
  verifier. So the body uses only the names that the model defines, the builtins and other
  model modules. The translation rejects a model whose body would need anything else, such as
  an unresolved base or class variable. An import cycle between model modules rejects the
  model too: a `py.importFrom` of a name that the other module has not bound yet would raise
  `ImportError`. The IR module body evaluates no annotations: PySpec reads them as the types
  of a stub file, so an annotation such as `-> C` inside the class `C` means `C`, although
  CPython would raise `NameError` evaluating it there.
* **What PySpec reads.** The model's module body must not run code that PySpec doesn't read,
  since that code could raise, such as `1 // 0`, or change what the model means, such as
  `setattr(typing, 'Unpack', dict)`. So PySpec rejects:
  * an expression statement at module level, other than a constant or a `ghost(...)` form;
  * an expression statement in a class body, other than a constant;
  * a value of a class field other than an int, bool, float or `None` literal, such as
    `x: int = f()`;
  * an assignment whose value has a `|` that CPython can't evaluate, such as `"Foo" | int`
    or `None | None`;
  * a binding of a name that PySpec reads as its own form, such as `requires` or `ghost`, or of
    `Exception`, which a class base reads as the builtin.
  * a private name `__x` in a class body, which CPython renames to `_C__x`, as a name, an
    attribute, a `def`, `class` or parameter name, or in an annotation or a default, also in
    the body's functions and lambdas;
  * an argument of a `ghost(...)` form or a contract decorator that runs at import, but that
    PySpec doesn't read: a `**` mapping, an argument after the first that is neither a lambda
    nor a constant, or a default value of a lambda's parameter, such as
    `@requires(lambda x=f(): x > 0)`;
  * a `|` in a ghost's `type=` that CPython can't evaluate, as in an assignment;
  * a name in an annotation, a default, a decorator or a base in a class body that the class
    body bound before it: after `K = B`, CPython reads `def get(self) -> K` as returning a `B`,
    but PySpec reads the module's `K`;
  * an unquoted name of a class in its own body, or in the body of a class nested in it, when
    the name had a binding before the class statement, such as a builtin or an import:
    in `class TimeoutError(Exception)`, CPython reads `-> TimeoutError` as the builtin, but
    PySpec reads the model class; `-> "TimeoutError"` names the model class in both;
  * an import of a module that PySpec models itself, such as `typing`, when the search path has
    its own module or package of that name, as a source or a compiled file, which CPython
    imports instead.

  PySpec reads annotations as a stub does (PEP 484), so an annotation that only raises at
  import is accepted. For example, `def clone(self) -> C` in the body of `class C` raises
  `NameError` in CPython 3.12 when `C` has no earlier binding, and PySpec reads it as returning a
  `C`. The `init=` of a function's `@ghost`, other than a constant, runs at import, but PySpec
  reads it when the function is called, so PySpec records it as a dropped clause.

  The rules on a binding of PySpec's own forms and on private names are known completeness
  gaps. They reject a model of a library that defines such a name itself, such as `requires`
  in `importlib.metadata`, and a model class with private members.
* **Function or method.** It is an extern that takes `(%args.0 : py.Value, %kwargs.0 :
  py.Value)` and returns `base.Except(py.Value, py.Value)`, as a translated function does (§3).
  The method `put_item` of the class `Storage` of the module `servicelib.Storage` is
  `@servicelib.Storage.Storage.put_item`. A method's receiver is position 0 of `%args`.
* **Class.** It is a class body function, such as `@|servicelib.Storage.Storage.<body>|`, which
  binds `ns` from its first argument, as a translated class body does (§6.7). Like a translated
  class body, it first stores `__module__`, a read of `__name__`, and `__qualname__`, such as
  `"Storage"`. Then it stores in `ns` the synthesized `__init__` and `__getattr__` (below), and
  then, in source order, its methods' closures, its fields' values, its class variables and its
  nested classes; PySpec records where each one is. The class body must bind each name only
  once, so that the class's facts and its namespace agree. A field's value, as in `x: int = 0`,
  must have the field's type, and the field's name must not be a dunder name such as
  `__slots__`. A class variable `X = Y` reads `Y` as CPython's class body does: from the
  namespace as bound so far, then the module's globals, then the builtins. The class body
  carries the class's facts (§12.10).
* **Nested class.** A class nested in a class, such as `_Exceptions` in the class `Database` of
  the module `servicelib.Database`, is built in the outer class's body, as CPython builds it,
  and stored in the outer class's namespace. Its `__qualname__` is `"Database._Exceptions"`. Its
  name is its real path, such as `servicelib.Database.Database._Exceptions`, in its functions'
  names and in facts. Generated code reads it through its outer class: `base.refGet` of the
  outer class's global cell, and then `py.attr(outer, "_Exceptions")`.
* **Overloaded methods.** An `@overload` method inside a class, `__init__` included, is not a
  dispatch, and PySpec gives it no procedure. The class body binds its name to a synthesized
  extern, such as `@servicelib.Storage.Storage.m`, with no clause and no frame. So a call of it
  accepts any arguments, returns an unknown value and may change any location. That is weaker
  than the stubs' contracts, so it is sound. Binding nothing would be unsound: `obj.m` would
  then find a model base's method `m`, and a consumer would trust that method's contract. Under
  `@exhaustive`, the class's `__getattr__` accepts the name too (below). A contract on such a
  stub, or an `assert`, `if` or `for` in its body, rejects the model, since nothing would carry
  it.
* **A name defined twice.** Two plain definitions of one method name in a class reject the
  model: `Specs.lean` reports "C.m is already defined".
* **A stub's `__init__`.** It is a method like any other: `Specs.lean` reads its parameters, its
  asserts and its decorators. Its `self.f = self._C()` assignments declare fields (§12.10), and
  they are not part of its contract. ToLaurel gives it its own procedure too, but neither Laurel
  front end checks that procedure's contract at any call yet. The card "Laurel front ends: Check
  model constructor contracts" tracks this.
* **Synthesized `__init__`.** When neither the class's stub nor a model base's stub defines
  `__init__`, plainly or as overloads, the class gets a synthesized extern `__init__`. When a model
  base's stub defines one, the class inherits it, as CPython does, and gets none. An overloaded
  `__init__` is bound as *Overloaded methods* says, not to a synthesized `__init__`, whose frame
  would leave out the stubs' `@modifies` targets. The synthesized `__init__` accepts any arguments
  after its receiver. Like every method, it has its receiver's presence clause, `requires "'self' is
  required"` (§12.2), and its receiver's declared type (§12.3). Its clause `free ensures
  "synthesized __init__ of 'C'"` says that it returns `None` when it returns, and its frame is the
  model frame (§12.5). Without it, `Storage("x")` would raise `TypeError`, since `object.__init__`
  takes no arguments, and make the code after it unreachable.
* **Unmodeled names.** The module body binds a module `__getattr__` (PEP 562), and each class
  body stores a class `__getattr__`. Each is a synthesized extern with no `ensures` clause and
  the frame `writes()`. They cover a module's names and an instance's names: a name that the
  model does not define, such as `servicelib.extra` or `obj.extra`, is an unknown value, as
  PySpec makes it. Without them, `servicelib.extra()` or `obj.extra()` would raise
  `AttributeError` in the model, even where the real library has the name.
* **Names that `__getattr__` does not cover.** A class's own names, such as `C.extra`, and names
  read through `super()`, such as `super().extra`, are not covered. CPython looks a missing class
  attribute up only on the metaclass, and `super()` looks a name up only in the class
  dictionaries along the MRO, so neither calls the class's `__getattr__`. So in the model, both
  raise `AttributeError`, even where the real library has the name. By §12.9, the library has
  such a name only through a class without a model or through the metaclass. A synthesized metaclass
  with a `__getattr__` would cover `C.extra`, but it is unsound: a model class with an ABC base
  would get a metaclass conflict, and `type(C) is type` would be false. A program that reads
  such a name is not admitted (§12.11). Until the admission rule exists, the model raises
  `AttributeError` there, as `ContractModelTest` pins.
* **`@exhaustive`.** It is not a decorator that the class statement applies. It gives the
  class's `__getattr__` the clause `requires "Unknown method of 'C'"`. It holds when the name
  is defined and is one of the fields that the class or one of its model base classes declares,
  or the name of an overloaded method of one of them: `py.isDefined(name)`, and then
  `py.strIsOneOf(name, names…)`. So an unlisted name is an obligation of the caller, as V1's
  static error is, never a trusted `AttributeError`.
* **Overloads.** The overloads of a module function `connect` become one synthesized extern
  `@servicelib.connect`. Overloads of a method are not dispatched (*Overloaded methods*,
  above). PySpec doesn't read an `@overload` stub's body, so an `assert`, `if` or `for` in it,
  at any depth, rejects the model. So does a stub whose first parameter isn't positional or
  has another name than the first stub's. Step 4 drops each stub's presence and type clauses of
  the parameter named like the first stub's first parameter, and the dispatch argument reads
  that name, so such a stub would lose the clauses of its own parameter of that name. A base
  whose first parameter isn't positional or has another name rejects the model too: calls bind
  to the base at run time, so with stubs `put(kind: Literal["a"])` and a base `put(mode: str)`,
  `put(mode="a")` meets the base's clauses but not the dispatch on `kind`. Let `v`
  be the dispatch argument, `py.argOf(%args.0, %kwargs.0, 0, paramName,
  py.undef(paramName))`. When the module has no
  non-overload `connect`, the extern has, in this order:
  1. the binding clause of §12.2, once and with no condition, when all the stubs have the same
     parameters;
  2. the presence clause of §12.2 for the dispatch parameter, so that the next clause tests a
     value that is defined;
  3. the dispatch clause, `requires "'connect' called with unknown string"`, which is
     `py.strIsOneOf(v, lit₁, …)`;
  4. for each stub `i`, its clauses for its own parameters, each as a `requires` clause that
     applies only when `v == litᵢ`: its binding clause, unless it came first, then its presence
     clauses, its declared types, its schemas and its preconditions, as §12.2 orders them. The
     dispatch parameter's presence and type are steps 2 and 3, so they are not repeated. Each
     clause reads a parameter with `py.argOf` at the stub's own position and name, and its
     message is the stub's message with " for 'litᵢ'" added, such as `"'region' is required for
     'storage'"`. These clauses rely on the dispatch clause, which made `v` an exact `str`.
     ToLaurel drops a stub's preconditions; keeping them is stronger, so it is sound;
  5. for each stub, `free ensures "overload of 'connect' for 'litᵢ'"`: on `ok r`, if `v ==
     litᵢ`, then `r` passes the test of a return type for `Cᵢ` (§12.3), with `Cᵢ` read as
     *Class identity* says;
  6. the frame: the three regions that start the model frame (§12.5), `py.instanceState`,
     `py.reachLoc(%args.0)` and `py.reachLoc(%kwargs.0)`, then every stub's `@modifies`
     targets. Each target applies only when `v == litᵢ`, as the stub's clauses do, and gives
     `py.instanceState` otherwise, which the frame already holds. So at a call that another stub
     covers, it reads no parameter that the call may lack. ToLaurel drops these targets;
     dropping them would make the frame too small, which is unsound.

  When the module also has a non-overload `connect`, that function is the base, and its contract
  comes first. The extern then has the base's `requires` clauses, in the order of §12.2 and with
  no condition; then steps 2 to 4, where a stub's binding clause is left out when the stub's
  parameters are the base's; then the base's `free ensures` clauses, with no condition; then
  step 5. Its frame is the base's frame (§12.5) plus every stub's `@modifies` targets, each
  applying only when `v == litᵢ`, as in step 6.

  Nothing says whether the result is a new object.
* **Type alias or imported name.** It has no declaration. It resolves names in declared types
  (§12.3) and in `isinstance` (§12.4).
* **Module ghost.** A ghost `g` is a ghost `@|servicelib.Storage.<ghost>.g|` that holds a
  `py.Value`. The `<ghost>` segment keeps its name apart from every function's name.
  * A literal initializer is a region that returns the literal. A float literal is the double
    nearest to its decimal, as Python's `float(s)` gives.
  * Every ghost's invariant starts with `py.isDefined(v)`: a ghost holds a Python value, never
    `py.undef`, also after a call that may change it and when it has no initializer.
  * The declared type adds to the invariant, by the rule for a return type (§12.3), only when
    every atom of its declared type gives `py.isInstance(v, py.stdClass(m, n))` or
    `py.is(v, None)`. Any other atom adds nothing. Such an atom has no test, such as `Any` or
    `BinaryIO`, or it is a model class. Nothing checks yet that the program never rebinds a
    model class's global cell (§12.9), and an invariant must hold in every state. For example,
    `type=BinaryIO` and `type=Union[int, BinaryIO]` add nothing, and neither does a ghost
    without `type=`.
  * A model whose initializer the declared type does not accept is rejected, as ToLaurel's
    `ghostInitializerError` does. Otherwise the invariant would contradict the initial value.
* **Function-level `@ghost`.** It is not represented: no contract can name it. But CPython
  evaluates its `init=` when it imports the model, so an `init=` other than a constant rejects
  the model (`dropped-clause`), on every definition of the name, also one that a later
  definition replaces, and on an overload stub.

### 12.2 Parameters and the order of the `requires` clauses

* **Parameter.** A parameter `x` at position `i` is `py.argOf(%args.0, %kwargs.0, i, "x", d)`.
  `i` is -1 for a keyword-only parameter. `d` is `py.noneLit` for `= None`, and `py.undef("x")`
  for no default. In an `ensures` clause, the parameter is read inside `base.old`, so that it is
  the argument as given, even if a frame covers `%kwargs`.
* **Parameters that reject the model.** A stub with a `*args` parameter, a positional-only
  parameter, or a type comment on a parameter rejects the model: `Specs.lean` reports an error
  for each. This includes a stub `__init__(self, *args, **kwargs)`.
* **`**kw: Unpack[TD]`.** Used as a value, it is `py.extraKwargs(%kwargs.0, names…)`, with
  `names` the named parameters, and it is read inside `base.old` in an `ensures` clause. So
  `kw["F"]` is `py.getItem` of that dict. Its closed keys are `py.dictKeysWithin(%kwargs.0,
  names…, fields…)`, with `fields` those of `TD`. It gets no test of its declared type, since
  `py.extraKwargs` gives a dict.
* **Any other `**kw`.** A `**kw` without a type rejects the model: PySpec reports "**kwargs
  requires type annotation". A `**kw: Any` is accepted, and gets no test. A `**kw` of any other
  type that is not a TypedDict rejects the model, as ToLaurel's `kwargsExpansionError` does, and
  so does a `**kw: TD` without `Unpack`, since `TD` would then be the type of each value.
* **The order of the `requires` clauses.**
  1. `requires "arguments bind to 'f'"`, which is `py.bindsTo(%args.0, %kwargs.0, nPos, varKw,
     names…)`. A method's name is qualified by its class, as in `'Storage.put_item'`.
  2. For each parameter without a default, the receiver included, `requires "'x' is
     required"`, which applies `py.isDefined` to `py.argOf(…, "x", py.undef("x"))`.
  3. For each parameter, the receiver included, its declared type (§12.3), as `requires
     "declared type of parameter 'x'"`.
  4. For each parameter, its schema (§12.3), as `requires "schema of parameter 'x'"`. For a
     `**kw` with a TypedDict, its closed keys follow, as `requires "keywords of 'f' are
     declared"`.
  5. The preconditions: the body's `assert`s, then the `@requires` lambdas, in PySpec's order.

  Each later clause relies on the earlier ones. `py.argOf` and `py.extraKwargs` give CPython's
  binding only once `py.bindsTo` holds, and an `ensures` clause relies on all the `requires`
  clauses. Until clause 2 has held, a value that may be `undef` is used only by `py.isDefined`.
* **Precondition.** A body `assert` or a `@requires` is `requires "<message>" { … }`, with the
  assert's message as the message, and an f-string's expression parts written as their source
  text. A precondition without a message, such as a `@requires`, is named `"precondition i"`,
  with `i` its position among the preconditions, counted from 0, as ToLaurel names it.
* **`if c:` and `else:` around asserts.** Each assert's clause is `implies c P` or `implies (not
  c) P`, written with branches (§12.4).
* **`for` around asserts.** Each assert gives one quantifier (§12.4).

### 12.3 Postconditions and types

* **`@admit`.** It is `free ensures "admitted postcondition of 'f'"`. It cases on the result: on
  `error`, the clause is `true`, so the model may raise. This differs from ToLaurel, where a
  model never raises. It relies on the program keeping the model's declared types and
  changing the library's state only through model calls (§12.9).
* **`@ensures` on a model.** It is rejected, as ToLaurel does.
* **Return type.** It is `free ensures "return type of 'f'"`, before the `@admit` clauses, so
  that they may rely on it. It relies on the program keeping the model's declared types (§12.9,
  *The program keeps the declared types*). ToLaurel puts it after them. On `ok`, it is the
  coarse test of the declared type (below), never its schema. There is no clause for `-> None`.
  An atom without a test makes the whole union `true`, which is weaker, so it is sound. A
  Literal atom is tested as its class: `py.isInstance(v, py.stdClass("builtins", "str"))`, or
  `"int"`. A `bytes` atom accepts `bytes`, `bytearray` or `memoryview`, as PEP 484 promotes
  them, which is weaker than the parameter's test, so it is sound. A class atom is tested with
  `py.isInstance` alone, except for a model class `C`: it gives the pair,
  `py.typeIsSubclass(result, C)` and then, only if it holds, `py.isInstance(result, C)`. This is
  a trusted assumption (§12.9). It is what lets a call of a method on the result meet that
  method's receiver test (below). So a proof that a call on the result meets that receiver test,
  too, relies on *Model returns* and on the program keeping the declared types (§12.9). For a
  binary operator's or a comparison's special method, such as `__add__`, `__radd__` or `__eq__`,
  and for `__length_hint__`, the test also holds when the result is `NotImplemented`,
  `py.isInstance(result, py.stdClass("types", "NotImplementedType"))`. Such a method may return
  it whatever its declared type: an operator's method for an operand that it doesn't handle,
  after which CPython tries the other operand's method, and `__length_hint__` for no hint.
* **Declared parameter type.** Each atom gives a test:

  | Atom | Test |
  |---|---|
  | `int` | the class `int`; a `bool` passes too |
  | `float` | `float` or `int` |
  | `complex` | `complex`, `float` or `int`, PEP 484's numeric tower |
  | `bytes` | `bytes` only: in Python 3.12, PEP 688 ends the promotion of `bytearray` and `memoryview`, so accepting them would be weaker than the declared type |
  | `str`, `bool`, `bytearray`, `dict`, `Exception` | its class |
  | a model class, or a class of another model module | that class, read from its module's global cell when the clause runs (*Class identity*, below) |
  | `None` | `py.is(v, None)` |
  | a Literal | `py.strIsOneOf` or `py.intIsOneOf` |
  | a TypedDict | `dict`, and the TypedDict's schema |
  | `List`, `Sequence`, `MutableSequence` | `list`, `collections.abc.Sequence`, `collections.abc.MutableSequence` |
  | `Dict`, `Mapping`, `MutableMapping` | `dict`, `collections.abc.Mapping`, `collections.abc.MutableMapping` |
  | `Generator` | `collections.abc.Generator`, with no element test, since iterating would consume it |

  * A test against a class `C` is `py.typeIsSubclass(v, C)` and then, only if it holds,
    `py.isInstance(v, C)`. The pair is stricter than `isinstance` (§2). A union of classes is
    one such test on a tuple of classes. This form is used for a parameter's declared type and
    its schema, and for a model class in a return type (above) or in an overload's clause
    (§12.1). Any other atom of a return type, a ghost's invariant and `isinstance` use
    `py.isInstance` alone.
  * `Any` anywhere in the union means no test.
  * A parameter with a `None` default passes when it is `None` or passes the test.
  * The receiver's declared type is its class `C`: `py.typeIsSubclass(self, C)`, with `C` read
    as *Class identity* says. It holds at a call `obj.m(…)` when `type(obj)` is `C` or a
    subclass of `C`. It has no `py.isInstance`, since a method is looked up on `type(obj)`, not
    on `obj.__class__`.
  * An atom without a test, such as `BinaryIO` or an imported name that resolves to no class,
    is dropped from its union, which is stronger, so it is sound. A type made only of such atoms
    gives `false`, and the clause's message says that the declared type has no runtime test, as
    in "declared type of parameter 'f' (BinaryIO) has no runtime test".
* **Schema.**
  * `List[T]`, `Sequence[T]` and `MutableSequence[T]`: `py.allIn(v)`, whose body tests `T` on
    the element.
  * `Dict[K, V]`, `Mapping[K, V]` and `MutableMapping[K, V]`: `py.allItems(v)`, whose body
    tests `K` on the key and then `V` on the value. `Any` has no test, so the schema of
    `Dict[str, Any]` tests only that each key is a `str`.
  * A TypedDict: each required key is in it, and the value of each key that is present passes
    its type.
  * Element types nest: `Dict[str, List[str]]` tests each value as a list of `str`s.
  * For a `str`, a `range` or a mapping that is not a dict, the quantifier raises, so the clause
    is `false`, which is stronger, so it is sound.
* **Class identity.** A clause reads a model class from its module's global cell when it runs,
  with `base.refGet` of `py.globalCell(module, name)` and then `py.requireDefined`. A nested
  class is read through its outer class, as §12.1 says. A program that rebinds
  `servicelib.Storage.Storage` changes what the clauses test, as it would for a library that
  looks its classes up at call time. A library that bound the class earlier, as
  `from m2 import C` does, still returns instances of the old class, so the program must not
  rebind it (§12.9).

### 12.4 Expressions

* **Names.** A name is a quantifier's binder, else a parameter, else a module ghost. A
  parameter with the name of a ghost that the contract mentions rejects the model, as ToLaurel's
  `ghostShadowedByParam` does. A parameter is read as §12.2 says, a ghost is `base.refGet` of
  its cell `ghost @|m.<ghost>.g|`, and a binder is its region's parameter.
* **Literals.** They are `py.intLit`, `py.boolLit`, `py.noneLit` and `py.floatLit`.
* **Operators.**
  * `d[k]` is `py.getItem`, and `"k" in c` is `py.in(py.strLit("k"), c)`.
  * `len(x)` is `py.len`.
  * A comparison or `in` is the matching `py.*` comparison, except for `None` (below).
  * The arithmetic is `py.add` to `py.pow`, and `py.uSub`.
  * `compile(p).search(s) is not None` is `py.reSearch(p, s)`.
  * `and`, `or`, `not` and `implies` test each operand with `py.truthy`, and combine the
    results with branches, in Python's order.
  * Each raising operation's failure goes to the clause's failure block.
* **Quantifiers.**
  * `all(… for x in xs)` is `py.allIn(xs)`, and `any(…)` is `py.anyIn(xs)`.
  * `for k in d` and `for k in d.keys()` are `py.allItems(d)`, which ignores the value.
  * `for v in d.values()` is `py.allItems(d)`, which ignores the key.
  * `for k, v in d.items()` is `py.allItems(d)`, and `any` is `py.anyItems(d)`.
  * A guard `if G` is a branch in the body. Under `all`, the body gives `true` when `G` does not
    hold.
  * A binder that shadows its collection, as in `all(len(Keys) >= 1 for Keys in Keys)`, needs
    nothing: the collection is evaluated outside the body.
* **`result`.** It is the `ok` value of the clause's argument. The translation rejects a model
  that uses `result` in any clause other than an `@ensures` or an `@admit`.
* **`OLD(e)`.** `base.old` covers the old part: the largest subexpression around `OLD(e)` that
  uses neither `result` nor a value that the clause reads after the call, outside `OLD`. A
  quantifier's binder may be used in the old part ([Dyn](./Dyn.md#1-overview), *`old` in
  `ensures` clauses*). For example:
  * `len(OLD(xs)) == len(xs) + 1` compares `old { len(xs) }` with `len(xs) + 1`;
  * `allocated == OLD(allocated) + 1` compares `allocated` with `old { allocated + 1 }`;
  * `len(OLD(d)["k"])` is `old { len(d["k"]) }`.

  The operation that combines the old part with a value read after the call runs after the
  call, on the object that the old part gave. So the old region ends with `py.isImmutableScalar`
  of its value. When that holds, the region returns `ok` of the value. Otherwise, it returns
  `error` of the value, so `base.old` fails and the clause takes its failure value, which is
  `true` in a `free ensures` clause: the clause assumes nothing. For example, for a list `xs`,
  `OLD(xs) == xs` is represented, and it assumes nothing. The check applies only to PySpec's
  `OLD`, not to a parameter that a clause reads inside `base.old` (§12.2).

  An `OLD`'s old part may read only *covered state*, which the frame covers at every call
  (§12.5). Covered state is:
  * what a `@modifies` target names, and what is rooted at it, such as a ghost's contents when
    `@modifies` lists the ghost;
  * what an argument reaches, the receiver included, along a path of items and declared fields
    (§12.10), when declared types show that every object on the path is neither a class nor a
    module. For example, `len(OLD(xs))` reads covered state for a list parameter `xs`, and so
    does `OLD(self.count)` for a declared field `count`.

  A class variable is not covered, nor is any other attribute of a class or a module, such as a
  module global, nor the contents of a ghost that `@modifies` does not list. A model is rejected
  when an `OLD`'s old part reads any state outside covered state. Reading a parameter itself
  (§12.2) is not a read of state. For example, `allocated == OLD(allocated) + 1` in
  `GhostOld.py` is accepted, since `@modifies(lambda: allocated)` lists the ghost. For a ghost,
  ToLaurel's `ghostOldWithoutModifies` rejects the model too. The frame keeps other state
  unchanged, so a clause such as `self.total == OLD(self.total) + 1`, where `total` is a class
  variable that `@modifies` does not list, would assume `false` at every call.
* **`isinstance(x, T)`, with `T` a bare name.** `T` is resolved in the model's scope, as CPython
  resolves it when the lambda runs, and the test is `py.isInstance`:
  * a parameter or a binder named `T` rejects the model;
  * a class that the module defines at its top level is that class (*Class identity*, §12.3);
  * a name of a class that is nested only inside another class is unresolved, which rejects the
    model: a lambda's body does not see a class's scope, so CPython 3.12 raises `NameError`;
  * an imported name is `py.stdClass(module, name)` for a class of the standard library, and
    that model's class for another model module; anything else rejects the model;
  * a type alias is its definition if that is a class or a union of classes. A TypedDict, a
    Literal or a generic rejects the model, since CPython raises `TypeError` for them;
  * a name of `builtins` is `py.stdClass("builtins", T)`;
  * anything else rejects the model.
* **`x is None` and `x == None`.** PySpec has one form for both, and it is `py.is(x, None)`; `x is
  not None` and `x != None` are `py.isNot(x, None)`. `compile(p).search(s) is None` is the
  negation of `py.reSearch(p, s)`. This differs from CPython only for a class whose `__eq__` says
  that an object equals `None`.
* **`s.f`, `s["f"]` and `kw["f"]`.** PySpec has one form for all three, which is an item or an
  attribute:
  1. `s` is the `**kw` parameter: an item of the `**kw` dict.
  2. In a `requires` clause: an item, since `Specs.lean` allows no attribute read there.
  3. `s` is declared as a TypedDict or a `Dict` or `Mapping` with `str` keys: an item. If `f` is
     an attribute of `dict`, such as `keys` or `get`, the model is rejected.
  4. `s` is declared as a model class, or is the parameter of an invariant, whatever its name:
     an attribute, `py.attr(s, "f")`. If the class or one of its bases lists `__getitem__`, the
     model is rejected.
  5. Otherwise, such as for `Any`, a union, or a type that cannot be computed, the model is
     rejected.

  The subject's type is computed as ToLaurel's `specTypeOf?` computes it. In cases 1 to 4, the
  other reading would raise in CPython, except for one case: a model class that is not
  exhaustive and has an unlisted `__getitem__`, subscripted with a string literal in an
  `@admit` or in a `@modifies` target.
* **`x == "A" or x == "B"`.** PySpec has one form for it, `enumMember`. In a `requires` clause,
  at a positive position, it is `py.strIsOneOf(x, "A", "B")`, which is stronger than `==` for a
  class with its own `__eq__`, so it is sound. Elsewhere, such as under `not` or in the condition
  of an implication or an `if`, and in every `free ensures` clause, it is the chain of `py.eq`
  in Python's order, which is the source's meaning. The other stricter tests of §2 follow the
  same rule: `py.intIsOneOf`, and `py.typeIsSubclass` followed by `py.isInstance`. The one
  exception is a model class in a return type, whose pair a trusted assumption covers (§12.3,
  §12.9).
* **`x != "A"`.** PySpec has one form for `x != "A"` and `not (x == "A")`, which differ for a
  class with its own `__eq__` or `__ne__`. At a positive position of a `requires` clause, both
  must hold: `not py.truthy(py.eq(x, "A"))`, and then `py.truthy(py.notEq(x, "A"))`. Elsewhere,
  either one suffices. Each choice is the stronger one where the direction rule needs it.

### 12.5 Frames

* **The model frame.** Every function and method that the model declares has `writes`, with
  these locations, each as one frame region: `py.instanceState` first, then
  `py.reachLoc(%args.0)` and `py.reachLoc(%kwargs.0)`, then the locations of its `@modifies`
  targets.
  * `py.instanceState` holds every attribute, other than `__class__` and a closure cell's
    `cell_contents`, of every object that is neither a class nor a module, and `py.reachLoc` of
    the value of each such attribute, at the call.
  * `py.reachLoc(obj)` holds every location, other than a `__class__`, of `obj` and of every
    object that `obj` reaches at the call through what objects store, but no attribute of a
    class or a module (§2).
  * So the two argument regions hold everything that an argument reaches, the receiver
    included, such as the position of a file or of an iterator that the call receives. An
    `int`, a `str` or another immutable scalar reaches nothing, so it adds nothing.

  A synthesized `__getattr__` has `writes()`, since looking a name up changes nothing (§12.9).
  An overloaded method's extern has no frame, and an overload's extern has the frame of §12.1.
  No model has a `reads` frame.
* **Targets.** A target adds the locations that the model frame may not hold already. A target
  names an object or a slot. A slot is a place that holds a value, such as an attribute, an
  entry or a ghost's cell. The *containers* of a target are the objects that its path reads a
  slot from: for `self.backend.registry`, they are `self` and `self.backend`.
  * A parameter `x` names an object. It gives `py.objLoc(x)`, every location of `x`. This adds
    the attributes of `x` when `x` is a class or a module, which `py.reachLoc` does not hold.
  * Every other target names a slot. When declared types show that every container is neither
    a class nor a module, the argument regions already hold the slot and what its value
    reaches. The target then gives its own location only if computing it needs no raising read,
    and nothing otherwise. For example, `@modifies(lambda self: self.items)` gives
    `py.attrLoc(self, "items")`, and the frame covers `self.items.append(x)` anyway.
    `@modifies(lambda d: d["a"]["k"])`, for a parameter `d: Dict[str, Dict[str, int]]`, gives
    nothing, since its own location would need a raising read of `d["a"]`. The declared types
    are those of the parameters, which their clauses test, of the fields (§12.10), which the
    program must keep (§12.9, *The program keeps the declared types*), and of the
    ghosts, which their invariants state.
  * Otherwise, the target gives its own location, and `py.reachLoc` of the value that the slot
    holds at the call. That region reads the value with raising reads, whose failures go to a
    block that ends in `unreachable`, and it fails where the slot is empty at the call, so that
    the whole frame states nothing. For example, `@modifies(lambda self: self.backend.registry)`,
    where the field `backend` has no declared type, gives both regions: `self.backend` may be a
    class, whose attributes no argument region holds.
  * The own location of `p.f` is `py.attrLoc(p, "f")` or `py.itemLoc(p, "f")`, by the rule for
    `s.f` in §12.4. Where that rule cannot decide, the target gives both: a larger frame is
    sound, while a clause would be rejected there.
  * The own location of `d[k]`, with a key that is not a literal, is `py.objLoc(d)`, which is
    larger, so it is sound.
  * A ghost `g` gives `base.cellLoc` of the ghost's cell, and `py.reachLoc` of the object that
    the ghost holds, a read that cannot fail. A target rooted at a ghost, such as `g["k"]` or
    `g.f`, gives these two too. Its containers start at the ghost's object, and it gives its own
    location and its value's region by the two bullets above, with the ghost's region in place
    of the argument regions.
  * The own location of any other target, such as `x["a"]["k"]` for a parameter `x: Any`, is a
    region that computes it with raising reads, whose failures go to `unreachable`.
  * A consumer that cannot show that a region's raising reads succeed at a call treats the call
    as one that may change any location ([Dyn](./Dyn.md#1-overview), *Frames*).
  * A bare name that is neither a parameter nor a ghost rejects the model.
* **Abstract containers.** A target may be rooted at a parameter that is declared with an
  abstract container type, such as `Mapping`, `MutableMapping`, `Sequence` or `MutableSequence`.
  Then that parameter's declared type is tested as the matching built-in class, `dict` or
  `list`, so that `py.itemLoc` and `py.objLoc` name the parameter's own storage. A region that
  applies `py.itemLoc` to an object that may not be a dict is not well defined, so the call may
  change any location unless the consumer shows that the object is a dict.

### 12.6 Class invariants

`@invariant(lambda self: P)` is recorded, never enforced. The class body carries the fact
`py.invariants`, a list with one entry per `@invariant` decorator, from top to bottom. An entry
has one of two forms.

* **A predicate**, `{fn = @|m.C.<invariant>.i|}`, with `i` the entry's position in the list.
  The invariant is a small defined function of the model module, `(%self.0 : py.Value) ->
  base.Bool`, whose body is `P` as written. The invariant's parameter, whatever its name, is
  `%self.0`.
  * If `P` names module ghosts, the function's parameters after `%self.0` are the contents of
    those ghosts, in their declaration order, and the entry is `{fn = @…, ghosts = [ghost
    @|m.<ghost>.g|, …]}`, in the same order.
  * `P` uses the forms of a `free ensures` clause (§12.4), so the predicate means what the source
    states, up to the modeling assumptions of §12.9.
  * A failure in `P` goes to `unreachable`.
  * The translation emits only operations whose effect is not `writes`. The checker does not
    check this, since the function is an ordinary function.
* **An untranslated text**, `{source = "lambda self: self.x >= 0", untranslated = true}`: the
  whole lambda as it is written, recorded when the translation cannot turn `P` into Dyn. Each
  rule of §12.4 that would reject the model records the invariant as its source text instead.

**Meaning.** An entry `{fn = @f, ghosts = [g₁, …, gₙ]}` is a predicate only when `@f` takes
`1 + n` parameters of type `py.Value` and returns a `base.Bool`. Its parameter at position `k`
after `%self.0` receives the contents of `gₖ`, and the translation lists the ghosts in their
declaration order. Any other entry states nothing: a consumer assumes nothing from it, and a
check of it fails, as for a region that the consumer cannot show well defined. From a predicate,
a consumer likewise relies on nothing that it cannot show well defined. This representation does
not say where a class invariant holds, and a program may change an instance's attributes. So a
consumer assumes a class invariant nowhere. Nothing calls these functions. A predicate that
receives a ghost's contents as a parameter does not use the ghost, which only contracts may do.

Here, from `StrataPythonTest/Dyn/contract_models/invariant_untranslated.dyn`, the class `C`
has a predicate entry and an untranslated entry, whose source text has a line break and a string
literal:

```
func @|m.C.<body>|(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
  #[py.bases = ["m.Base"]]
  #[py.fields = [{name = "kind", trustedType = "builtins.str"}, {name = "request", trustedType = {expr = "TypedDict"}}]]
  #[py.invariants = [{fn = @|m.C.<invariant>.0|}, {source = "lambda self: (self.kind\n  != \"x\")", untranslated = true}]]
  …
}
func @|m.C.<invariant>.0|(%self.0 : py.Value) -> base.Bool {
  entry.0(%self.0 : py.Value):
    %count.0 : py.Value = py.attr(%self.0, "count") ^fail.0()
    %int.0 : py.Value = py.intLit(0)
    %ge.0 : py.Value = py.gtE(%count.0, %int.0) ^fail.0()
    %ok.0 : base.Bool = py.truthy(%ge.0) ^fail.0()
    ret(%ok.0)
  fail.0(%e.0 : py.Value):
    unreachable
}
```

**Changes to PySpec.** `py.invariants` holds every invariant that a model's author wrote, since
PySpec makes three changes (§12.13). A lambda whose one parameter is not named `self` is accepted,
with that parameter as `self`. A lambda with no parameter, or with two or more, rejects the model.
And PySpec keeps each invariant's source text, in `ClassDef` and in its Ion form, so that a
condition that it cannot translate can be recorded as text.

### 12.7 What PySpec dropped, and what cannot be represented

* **A dropped precondition or `@modifies` target.** `Specs.lean` drops an `assert` that it
  cannot translate (`pySpecDroppedAssertion`), and a `@requires` or `@modifies` lambda that it
  cannot translate. Either rejects the model. A dropped precondition would make the model's
  `requires` clauses weaker than its source, and a dropped target would make its frame too
  small. Either would make the `free ensures` clauses trusted at calls that the modeler
  excluded. For example, `Specs.lean` has no form for a string literal in an ordering, so it drops
  `assert x > "a"`, and the model is rejected. `Specs.lean` records each dropped clause in
  `FunctionDecl.dropped` (§12.13).
* **A dropped `@admit`.** It only weakens the model, so the model is not rejected.
* **A clause that the translation cannot represent.** It rejects the model. The translation
  never drops a clause, as ToLaurel does not drop an `@admit`. An invariant that the translation
  cannot represent is recorded as its source text instead (§12.6).

### 12.8 An example

`acquire` of `StrataPythonTestExtra/Specs/dispatch_test/servicelib/GhostOld.py`, abridged:

```python
ghost(name="resources", type=Dict[str, int])
ghost(name="allocated", type=int, init=0)

@modifies(lambda: resources)
@modifies(lambda: allocated)
@admit(lambda name, result: name in resources)
@admit(lambda name, result: allocated == OLD(allocated) + 1)
def acquire(name: str) -> None: ...
```

Its second `@admit` clause and its frame are:

```
    free ensures "admitted postcondition of 'acquire'" {
      post.1(%r.1 : base.Except(py.Value, py.Value)):
        base.Except.case[py.Value, py.Value](%r.1) ^ok.1() ^raised.1()
      ok.1(%result.1 : py.Value):
        %allocated.0 : py.Value = base.refGet[py.Value](ghost @|servicelib.GhostOld.<ghost>.allocated|)
        %old.0 : py.Value = base.old[py.Value, py.Value] ^fail.2() {
          old.1():
            %allocated.1 : py.Value = base.refGet[py.Value](ghost @|servicelib.GhostOld.<ghost>.allocated|)
            %int.0 : py.Value = py.intLit(1)
            %add.0 : py.Value = py.add(%allocated.1, %int.0) ^propagate.0()
            %scalar.0 : base.Bool = py.isImmutableScalar(%add.0)
            branch(%scalar.0) ^scalar.0() ^mutable.0()
          scalar.0():
            %res.1 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%add.0)
            ret(%res.1)
          mutable.0():
            %res.2 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%add.0)
            ret(%res.2)
          propagate.0(%exc.1 : py.Value):
            %err.0 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.1)
            ret(%err.0)
        }
        %eq.0 : py.Value = py.eq(%allocated.0, %old.0) ^fail.2()
        %ok.4 : base.Bool = py.truthy(%eq.0) ^fail.2()
        ret(%ok.4)
      raised.1(%exc.2 : py.Value):
        ret(true)
      fail.2(%e.2 : py.Value):
        ret(true)
    }
    writes({
      loc.0():
        %l.0 : base.Loc = py.instanceState
        ret(%l.0)
    }, {
      loc.1():
        %l.1 : base.Loc = py.reachLoc(%args.0)
        ret(%l.1)
    }, {
      loc.2():
        %l.2 : base.Loc = py.reachLoc(%kwargs.0)
        ret(%l.2)
    }, {
      loc.3():
        %l.3 : base.Loc = base.cellLoc[py.Value](ghost @|servicelib.GhostOld.<ghost>.resources|)
        ret(%l.3)
    }, {
      loc.4():
        %resources.1 : py.Value = base.refGet[py.Value](ghost @|servicelib.GhostOld.<ghost>.resources|)
        %l.4 : base.Loc = py.reachLoc(%resources.1)
        ret(%l.4)
    }, {
      loc.5():
        %l.5 : base.Loc = base.cellLoc[py.Value](ghost @|servicelib.GhostOld.<ghost>.allocated|)
        ret(%l.5)
    }, {
      loc.6():
        %allocated.2 : py.Value = base.refGet[py.Value](ghost @|servicelib.GhostOld.<ghost>.allocated|)
        %l.6 : base.Loc = py.reachLoc(%allocated.2)
        ret(%l.6)
    })
```

The frame's regions give, in order, `py.instanceState`, what the arguments reach, the cell of the
ghost `resources`, what the dict that it holds reaches, the cell of the ghost `allocated`, and what
the object that it holds reaches. The whole model is
`StrataPythonTest/Dyn/contract_models/ghost_old.dyn`.

### 12.9 Trusted modeling assumptions

Besides the trust base ([Dyn](./Dyn.md#1-overview), *The trust base*), a model trusts
these assumptions. Some of them are about the program, not the library: *The library runs no
program code*, *The program keeps the declared types*, *The program changes the library's state
only through model calls*, the reading of `x == None` as identity, and the quantifier over a
container subclass. No stage checks them yet. §12.11 lists the admission rules that will check
some of them.

* The model module stands for the library: its body, its classes and their facts (§12.1).
* A model class's stub, with the stubs of its model bases, lists every method and class attribute
  that the library's class has, including those that it inherits from library bases that the
  model leaves out, such as the `__getattribute__` of such a base. So a model base answers for a
  name that a subclass's stub doesn't define, as CPython's lookup along the MRO does (§12.1,
  §12.11). For example, when `C`'s stub omits `close` and `B`'s stub defines it, the model trusts
  that the library's `C` doesn't override `close`, so `C().close()` gets `B.close`'s contract.
  A base that the model leaves out counts as a library base, whether or not it comes from the
  standard library, so the stub must list what the class inherits from it. For example, when the
  library has `class C(io.IOBase, B)` and the model has `class C(B)`, CPython's `C().close` is
  `_io._IOBase.close`, so `C`'s stub must list `close`. This doesn't cover the standard-library
  classes that the model's own MRO has, such as `object` or a `dict` base that the stub names:
  the admission rules count their names as not defined (§12.11).
* When neither the class's stub nor a model base's stub defines `__init__`, the library's
  `__init__` accepts any arguments after its receiver, returns `None`, and changes only what the
  model frame allows, as the synthesized one says. An unmodeled name is an unknown value whose
  lookup changes nothing, as the synthesized `__getattr__` says (§12.1).
* Instantiating a model class goes through the `__new__` that the model's bases give.
* `isinstance` and `issubclass` on model classes, and reading `obj.__class__` on model
  instances, behave as for `type` and `object`.
* Defining a program subclass of a model class runs no library code.
* A generator argument's element type is not tested (§12.3).
* A clause reads a model class when it runs (*Class identity*, §12.3).
* A quantifier over a container subclass that overrides iteration ranges over the container's
  storage, not over what its iteration yields (§2).
* `x == None` is read as identity (§12.4).
* A model function or method whose declared return type is a model class `C` returns an
  instance of `C` or of a subclass, by its own type (PEP 484's meaning of the annotation). The
  same holds for each model class of a union return type, such as `Optional[C]`. So the clause of
  a return type, and the clause of an overload, test the result with `py.typeIsSubclass` too
  (§12.1, §12.3).
* In an `@admit` or a `@modifies` target, `s["f"]` on an instance of a model class that is not
  exhaustive is the attribute `f`, even if the class has an unlisted `__getitem__` (§12.4).
* The model frame. A model call changes only `py.instanceState`, what its arguments reach, as
  `py.reachLoc` of `%args.0` and of `%kwargs.0` says, and the locations of its `@modifies`
  targets. `py.instanceState` holds every attribute, other than `__class__` and a closure cell's
  `cell_contents`, of every object that is neither a class nor a module, and everything that
  such an attribute reaches at the call, as `py.reachLoc` says. So a model call changes none of
  the following, unless `@modifies` lists it:
  * an attribute of a class or a module (a module global), however it is reached;
  * an object's `__class__`;
  * a ghost;
  * a local variable, or a variable that a closure captures. The model frame holds no closure
    cell's contents, so no argument and no attribute reaches such a variable, not even through a
    function's `__closure__`;
  * an element, a key or a value that an object stores, unless an argument, or an attribute of
    an object that is neither a class nor a module, reaches that object at the call.

  For example, a list that only a local variable holds keeps its elements, unless the call
  receives the list, as an argument or inside one. So does an instance of `class L(list)` that
  no attribute and no argument reaches.
* *The library runs no program code.* A model call runs no code that the program defines. So the
  program gives the library no callable, such as a bound method like `results.append`, and no
  generator that the program defines; the other places that speak of a generator argument mean
  one that the library made. And the library calls no method that a program class defines, on
  any object that it receives or holds: a method that a program subclass of a model class
  overrides, a method or special method of a program subclass of a built-in class, such as
  `lower` of a `str` subclass or `__hash__` of a key, a property, `__getattr__`, or a finalizer
  (`__del__`) when the library drops the object. Such code can change a module global, a class
  attribute or a closure cell, which the model frame says the call doesn't change. It can also
  give the library values of other types: for `class S(str)` whose `lower` returns `5`,
  `norm(S("A")) -> str`, which returns `s.lower()`, returns `5`. No stage checks this yet.
* A library changes no state through a weak reference, a memoryview or a function's
  `__closure__` cells. Through `__closure__`, a library can change the variables
  that a closure captures without calling the closure. The model frame holds no closure cell's
  contents, so it doesn't allow this change.
* A library changes no program function's `__defaults__`, `__kwdefaults__` or `__code__`, which
  the translated function does not read (§5.4).
* An overload stub's `@modifies` targets describe only the calls that select the stub (§12.1).
* *Model values.* When a model function or method returns a value, or the library stores a value
  in a model field, each part of the value that the library made, at any depth, is at that
  moment an instance of the type declared at its position (by `isinstance`, so subclasses are
  allowed), with the return test's promotions (§12.3): a `float` may be an `int`, a `complex` a
  `float` or an `int`, a `bytes` a `bytearray` or a `memoryview`, and a `Literal` any value of
  its class. So every element of a `List[int]` is an `int`, `True` included; every element of a
  `List[float]` is a `float` or an `int`, as botocore gives a JSON `1` for a double; every value
  of a `dict[str, list[int]]` is a `list` of `int`s, although the IR's return test checks only
  the `dict`; and an element of a `List[Literal["A", "B"]]` may be any `str`, as botocore gives
  an enum value that the model doesn't list. The trust says nothing about a part that the
  program wrote or passed to the library, through any alias: such a part keeps the type that the
  program gave it. Positions typed `Any`, a type variable, or a lazy type (`Iterator`,
  `Generator`, `Iterable`, dict views) stay open. A TypedDict has every required key, and each
  declared key's value has its declared type; keys that the model doesn't declare may be
  present, and their values are open. The trust says nothing about a value after the program or
  the library changes it. After a later model call, a part that the call's frame doesn't hold
  keeps its value; the trust says nothing about a part that the frame holds.
* *Model returns.* Whatever the program passed to the library before, each value that a model
  call returns, and each value that a declared model field holds before and after each model
  call, and when the program reads it, has its declared type at every position, except the parts
  that the program itself wrote into a value that crosses the library boundary (*The program
  keeps the declared types*). A value has its declared type as *Model values* reads it, and, at
  a position whose type is a model class `C`, `type(v)` is `C` or a subclass of `C`, as the
  return test reads it (§12.3). A model whose library can return or keep a program-supplied
  value of another type is a wrong model, and fixing it is the modeler's duty. For example, a
  class `Box` has a field `xs: List[int]`, its `add(x: Any)` appends `x` to `xs`, and its
  `first() -> int` returns `xs[0]`. Then `add` must declare `x: int`.
* *The program keeps the declared types.* The following rely on the program keeping the model's
  declared types: the return types of the model's functions (§12.3) and overloads (§12.1), the
  `@admit` clauses (§12.3), the fields' `trustedType` facts (§12.10), and the frames and the
  check of `OLD`, which use the fields' types (§12.4, §12.5). Here a value has its declared type
  when it passes the test of a parameter of that type (§12.3). So for a model class `C`,
  `type(v)` is `C` or a subclass of `C`, and `Mock(spec=C)` is not one. The program keeps the
  declared types when:
  * it writes a model object's fields only with values of their declared types, by any means,
    such as `setattr`, `__dict__` or `vars()`;
  * it binds or deletes no attribute of a model class, methods included, by any means, such as
    `C.n = "s"`, `C.first = lambda self: "s"`, `del C.first`, `setattr`, `delattr` or
    `vars()`, and binds no name that the body of a model class binds, other
    than a method, in a subclass, such as `class Sub(C): n = "s"` or
    `class Sub(Database): _Exceptions = Other`;
  * it rebinds or deletes no name of a model module, by any means, such as `m2.C = int`
    (*Class identity*, §12.3), `lib.DEFAULT = "s"` or `setattr(lib, "DEFAULT", "s")`, and
    binds or deletes no attribute of a module that the library's code uses, `builtins`
    included, such as `json.loads = f`, nor replaces the library in `sys.modules` or through an
    import hook;
  * it makes instances of model classes only through the model's own constructors and
    factories, not through `C.__new__(C)`, `object.__new__`, `copy.copy`, `copy.deepcopy` or
    `pickle`, which give an instance whose fields the library never set;
  * no program code that touches the library's state or a value that crosses the library
    boundary runs concurrently with a model call, in another thread or in a signal handler;
  * the arguments that it passes have their declared types at every depth. The parameter's
    clauses test this at the call (§12.2), but not the fields of a model object, the
    receiver's included, nor the elements of a generator;
  * it writes into a value that it passed to the library, or that the library returned or
    holds, through any alias, only values of the declared types. For example, after
    `c.set_xs(xs)` and `xs.insert(0, "s")`, `c.first() -> int` returns `"s"`;
  * it shadows no model field with a property or another descriptor, and defines no
    `__getattribute__`, `__getattr__`, `__setattr__` or `__delattr__` in a subclass of a model
    class (§12.11);
  * it assigns no `__class__` of an object that the library made or holds, and no `__bases__`
    of a model class.

  For example, after `c.xs = "s"`, `c.get_xs() -> List[int]`, which returns `self.xs`, returns
  `"s"`, but the IR assumes a `list`. No stage checks any of this yet. The IR still assumes
  these clauses after every call, and its frames use the fields' types. So it is an open
  obligation: a verifier's result can be trusted only after a check of the program has
  discharged it.
* *The program changes the library's state only through model calls.* An `@admit` clause states
  what the library does, and that depends on the library's own state. So a program write of a
  value of the declared type can make the clause false. For example, for `used() -> int` with
  `@admit(lambda self, result: result <= self.capacity)`, the library's `used()` returns
  `len(self._items)`. When `c` holds three items and the program sets `c.capacity = 0`, `used()`
  returns `3`, but the IR assumes `3 <= 0`. A
  write to the library state that a ghost stands for does the same to a clause that reads the
  ghost. So an `@admit` clause relies on the program writing no field of a model object, and no
  other state that the library keeps, other than through model calls. No stage checks this yet.
* The IR's semantics never frees an object, so it never runs a finalizer. A library class's
  finalizer (`__del__`) is assumed to have no effect that the program can observe.

### 12.10 Facts in a model

A model has no code to check its facts against, so a consumer that uses them trusts them, but
only as far as §12.9 (*Model values* and *Model returns*) says, and only if the program keeps
the declared types (§12.9). For example, a field's `trustedType` holds before and after each
model call, but not for a part that the program wrote into it (*The program keeps the declared
types*). A class body's facts are those of §6.7, with these differences:

* `py.fields` is always present, `py.bases` is present when the class has bases,
  `py.initFields` is present when the stub's `__init__` assigns fields, and `py.invariants`
  (§12.6) is present when it has invariants. A model states no other key.
* A field is `{name = "x", trustedType = E}`, with `default = V` when the class body gives it
  a literal value, as in `x: int = 0`. Its `trustedType` is the model's trusted fact. A
  translated class's field record (§6.7) never has `trustedType`: its `type` is the annotation
  as written, which nothing checks. `py.fields` holds the fields that the class body
  declares. A field from `self.f = self._C()` in a stub's `__init__` is in `py.initFields`
  instead, as `{name = "f", trustedType = E, in = @…__init__}`, apart from `py.fields`, because no code
  states it. PySpec gives it the type `m._C`, with `m` the module, whatever
  class `_C` belongs to. The translation resolves `_C` as `self._C` resolves it: in the
  namespace of the class, then in those of its model bases in MRO order, where it is a nested
  class or a class variable bound to a class. The field's type is that class's real path. A
  model in which `_C` resolves to no class is rejected. For example, `self.exceptions =
  self._Exceptions()` in the class `Database` of `servicelib.Database` has PySpec's type
  `servicelib.Database._Exceptions`, and gives `{name = "exceptions", type =
  "servicelib.Database.Database._Exceptions", in = @servicelib.Database.Database.__init__}`.
* Names are fully qualified, such as `"builtins.int"`, since PySpec has resolved them. A nested
  class's name is its real path (§12.1). A translated class's facts are written as the source
  writes them (§6.7).
* A TypedDict atom, which the notation of §6.7 cannot write, is `{expr = "TypedDict"}`, which
  states nothing.

Every other part of a fact follows §6.7, including its rule that a flag appears only when it is
true.

### 12.11 Programs that admission rejects

For some programs, the model may answer differently from the library, so the admission pass
rejects them. The admission work provides each whole rule: the facts that it needs from the
model, such as the names and the special methods that each model class defines, and the check
of the programs. For a model class `C`, a program is rejected when it does one of these:

* It reads a name that the model does not define from `C`, such as `C.extra`, or through
  `super()` in a subclass of `C`, such as `super().extra` (§12.1).
* It applies, to an instance of `C`, an operation that CPython performs through a special method
  of the instance's type, unless a model class or a program class defines exactly the special
  method that CPython looks up first for that operation, as below. CPython looks such a method up
  on the type, so the synthesized `__getattr__` never runs. These are the exact conditions:
  * The special method is the one that CPython looks up first. For example, `bool(C())` needs
    `__bool__`, even when `C` defines `__len__`, and `1 + C()` needs `__radd__`.
  * CPython walks the instance's MRO, and the first class whose own dict holds the method's name
    answers. It must be a model class or a program class. A model class answers for each of its
    subclasses whose stub doesn't define the method (§12.9). A class that is neither a model
    class nor a program class, such as `object`, `dict` or a library class without a model,
    stops the walk. For example, for `class M(dict, Base)`, `len(M())` uses `dict.__len__`, so
    `Base.__len__` doesn't count.
  * Some names are in a class's dict without being defined in the model: an overloaded method,
    and `__hash__ = None`, which CPython stores in every class that defines `__eq__` without
    `__hash__`. Such a name also stops the walk, and the method counts as not defined.
  * Where CPython uses several methods, each one is defined as above. For example, `with` uses
    `__enter__` and `__exit__`.

  The rule covers every operator and comparison, `len`, `iter` and `for`, `next`, `in`,
  subscripting, a call, `with`, truth tests (`if`, `not`, `and`, `or`, `bool`), `hash` and use as
  a dict key or a set element, `str`, `repr`, `format` and f-strings, numeric conversions,
  attribute assignment and deletion, and `await`. It also covers the descriptor protocol: an
  instance of `C` stored as a class attribute of a program class, for which CPython calls
  `__set_name__`, `__get__`, `__set__` or `__delete__`. For example, when `C` defines none of
  `__len__`, `__iter__`, `__getitem__` and `__bool__`, `len(C())` and `iter(C())` raise
  `TypeError` in the model, and `bool(C())` is `True`.
* It reads `vars(obj)` or `obj.__dict__`, where `obj` is an instance of `C`.
* It subscripts `C`, as in `C[int]`, or gives class keywords to a subclass of `C`, as in `class
  Mine(C, flag=1)`.
* It defines a subclass of `C` that overrides, with a descriptor such as a property, a field
  that the model declares or an attribute that the model's clauses read. It also defines a
  subclass of `C` that defines `__getattribute__`, `__getattr__`, `__setattr__` or
  `__delattr__`. Such a class reads or stores attributes elsewhere than `py.instanceState` and
  `py.attrLoc` say, so the frames and the check of `OLD` (§12.4) would be wrong.
* It defines a class that derives from `C` and from `type` or `types.ModuleType`. Such a class
  makes classes or modules that are instances of `C`, and the frames do not hold their
  attributes (§12.5).

Each rule holds however the program reaches the operation or the read, including inside the
builtins and the standard library. For example, `sorted` compares with `<`, `print` calls `str`,
`[a] == [b]` compares `a` with `b`, `getattr(C, "x", None)` reads `C.x`, and `copy.copy` reads
special methods of the instance's type.

### 12.12 The hand-written models

`StrataPythonTest/Dyn/contract_models/` holds models written by hand by these rules: one for
each of seven PySpec fixtures, and four written for the test.
`StrataPythonTestExtra/ContractModelTest.lean` reads each one against `Py.env`, which checks it,
and compares the printed module with the file without its comment lines. It also checks that one
change to each file is rejected with its rule's message, and that every predicate entry of
`py.invariants` has its predicate's parameters, and that ref-to-reg accepts every model and
changes none. With CPython 3.12, it checks that the names that
a model class defines leave `C.extra` and `super().extra` raising `AttributeError`, `len(C())`
and `iter(C())` raising `TypeError`, and `bool(C())` true (§12.11).
Each file's first comment names its fixture, or says that the file was written for the test.
For a fixture, it also says where the model is stronger or weaker than ToLaurel's translation of
the same fixture.

### 12.13 The translation from PySpec

`StrataPython/Dyn/PySpec/` translates PySpec models by the rules above. `Load.lean` reads a
model module, every model module it imports, and every module that its types name when PySpec
wrote it (`M.C` after `import M`), with PySpec's front end and a fresh cache of its Ion files.
`Resolve.lean` builds one table of the set, and `Mro.lean` computes the MRO of its classes.
`Check.lean` turns each clause into a checked form, in which every decision of §12.4 is made, and
`Emit.lean` writes that form as blocks. `Contract.lean` assembles each extern's contract, and
`Module.lean` the module bodies, the class bodies with their facts, the ghosts, the overloads and
the invariant predicates.
`lake exe pydyn pyspec SEARCH_PATH MODULE` prints the modules of a set.

The translation is all or nothing: any rejection rejects the whole set, so no module refers to
one that is missing. Each rejection has a rule ID, such as `dropped-clause` or `old-uncovered`,
and a message that names the declaration. Signatures from an Ion file without PySpec's current
format version are refused, since an older PySpec may not have recorded what it dropped.

The module body must never raise (§12.1), so a class statement that CPython can't run rejects the
model:

* `class-mro`: CPython can't order the class's bases, as for `class Z(X, Y)` with `X(A, B)` and
  `Y(B, A)`;
* `class-base`: a standard-library base other than a class of `builtins` that accepts
  subclasses, such as `bool` or `typing.Protocol`, since the body reads it with
  `py.qualifiedRef` (§2);
* `class-bases`: two standard-library classes other than `object` in the MRO. This is stronger
  than CPython, which accepts some pairs, such as two exceptions with the same layout;
* `unbound-base` and `rebound-base`: a base of the module that isn't bound yet when the class
  statement runs, or whose name the module binds more than once;
* `unresolved-name`: a class variable that reads a name that isn't bound yet;
* `init-field-class`: a field from `self.f = self._C()` whose `_C` names no class as §12.10
  resolves it, or another class than the table's `m._C`;
* `field-two-types`: a field that the class body declares with two different types, or that
  the stub's `__init__` also assigns, with another class than the declaration's;
* `field-value`: a field's value that doesn't have the field's type, or a field with a value
  and a dunder name;
* `rebound-name`: a name that the class body binds more than once, e.g. a method whose name a
  class variable takes;
* `special-binding`: a class variable, a nested class or a field that binds `__init__` or
  `__getattr__`, which the translation builds from a method or synthesizes.

Two declarations that give the same IR name reject the model: `duplicate-name` within a module,
and `name-clash` across the set's modules, such as a function `put_item` of `servicelib.Storage`
and a method `put_item` of a class `Storage` of `servicelib`. A contract on an `@overload` stub of
a method rejects the model with `overload-method-contract`. An `@admit` on an overload stub of a
module function is a `free ensures` clause that applies only when the dispatch argument is the
stub's literal, after the stub's return-type clause (§12.1, step 5).

A few forms that PySpec reads have a CPython meaning that the IR's form doesn't give, and each
rejects the model:

* `condition-value`: `and`, `or`, an implication, a regex search, `x == "A" or x == "B"` or
  `x != "A"` where a value is needed, as in `(x or 3) == result`, where CPython gives an
  operand, a match object or the result of `__ne__`. The last two are also rejected under a
  `not`, an `and`, an `or` or a quantifier whose result is used as a value, as in
  `(not (x != "A")) == result`, since their bool depends on the reading;
* `shadowed-builtin`: a call of `len`, `isinstance`, `all`, `any` or `compile` when the module
  binds that name, as `len = int` does;
* `duplicate-binder`: a quantifier that binds one name twice, as `for k, k in d.items()` does;
* `overload-dispatch`: two overload stubs with the same literal, whose clauses would contradict,
  or stubs, or the base, that name their first parameter differently (§12.1, *Overloads*);
* `init-subclass`: a model class that declares `__init_subclass__`, as a method or a class
  variable, which runs library code when a subclass is defined.

PySpec records each clause that it could not read faithfully (`FunctionDecl.dropped`): a clause
that it couldn't translate, an assert whose meaning depends on what it doesn't read, and a
clause with a call that means something else in CPython, such as `len(s, x=1)`, `len(s)` where
`len` is a parameter, or `compile(p)` without `from re import compile`. After a skipped
statement that can bind a name or change an object, every later assert is recorded. If a loop
body holds such a statement, every assert of that body is recorded too. A recorded assert,
`@requires`, `@ensures` or `@modifies` rejects the model. A recorded `@admit` only weakens it:
PySpec leaves it out, even where it translates, so that ToLaurel doesn't assume it either.

PySpec reads the names of the `typing` module in annotations by syntax only, with no other name
resolution:

* `Optional[T]` reads as `Union[T, None]`, and `Optional` with more than one type is an error.
* `typing.X[...]` reads as `X[...]` only through a name that `import typing` binds, such as
  `typing` or the `t` of `import typing as t`. A subscript through any other module name is an
  error.
* A typing name is a name that `import typing` or `from typing import ...` binds. Any other
  binding of it, before or after the import, at the module's top level or in a class body,
  rejects the model, e.g. `def List(): ...` with `from typing import List`. Repeating the same
  typing import is not another binding, and neither is a field without a value, `List: int`.
  The rule doesn't rely on PySpec reading the bindings in source order.

After some rebindings, PySpec keeps an earlier meaning of other names: after a `def` or a
class-body binding of a builtin type name or of a model class, and after a rebinding of another
module's alias. For example,
after `import import_test.service.module as m` and `m = 0`, PySpec still reads `m.ServiceClass`
as that module's class, where CPython raises `AttributeError`. `SpecsTest` pins this case
(`rebound_module_attr`), and a method named `dict` before `-> dict` (`method_named_dict`).

`StrataPythonTestExtra/PySpecDynTest.lean` translates each set that
`StrataPythonTest/Dyn/pyspec_models.txt` lists, and compares each module with its golden in
`StrataPythonTest/Dyn/pyspec_models/`. For a rejected set, it compares the rule IDs with the
list, and the rejections with their messages with a golden there.
