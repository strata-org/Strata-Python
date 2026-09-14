# Pylate

**Pylate** — the Python lattice engine. The lattice is the load-bearing part: the
order is `Fset.Sub`, `join` is pointwise, and the whole five-completion argument
turns on `none` being bottom.

Pylate implements the **POMAD** — the Python Object Model Abstract Domain. POMAD
is the abstract mathematical object; Pylate is the engine that realizes it.

Specifically, Pylate implements a **restricted** POMAD, in two ways:

- **the class layer is static** — every declared class's shape and MRO are fixed
  at their declarations and cannot change during execution
- **there is no metaclass layer** at all

Those two restrictions are what the admission rules exist to enforce, and they are
why decorators, metaclasses and the attribute-protocol overrides are rejected
rather than analysed. `doc/POMAD.md` outlines the future work to extend the domain
with more dynamism at the class and metaclass/decorator layers, which is what
would let those checks be relaxed.

Pylate is an abstract interpreter for a subset of Python. The subset is defined
so that the object shapes and MROs match their declarations and are static
throughout execution for every class declared in the program.
The analyzer rejects programs that do not satisfy these restrictions.
For accepted programs, for every program variable and every heap location,
it computes an abstract value that tracks:

- **initialization** — bound, unbound, or unbound on some paths
- **types** — the set of runtime types the value may have
- **values** — the program literals it may equal, in Python spelling: `7`, `1.5`,
  `True`, `None`, `'ab'`, `b'ab'`. The completeness marker is **per tag**, so a
  value can be exactly `1` on its `int` side while its `str` side is unknown
- **aliasing** — the heap objects it may point to, and whether that set is a
  must-alias or a may-alias
- **size** — for containers: an exact element count where one is known,
  otherwise non-empty-but-uncounted, empty, or unknown. Emptiness is the
  projection of this, not a separate domain
- **callables** — the functions and classes it may denote, by name

While computing those values it resolves every operation against them, so at each
invocation point it also produces an upper bound on two things: **the dispatch
targets the call can reach**, and **the exceptions the operation can raise**.

Both bounds err in one direction. Pylate can report a target or an exception that
never occurs at runtime. It cannot miss one that does.

A call whose receiver resolves to a single target is devirtualized. One that
resolves to several is reported as a split, with the targets listed. Conditions
the abstract values cannot settle — whether an index is in range, whether a key is
present — become obligations for an SMT solver.

`doc/ALGORITHM_AND_SOUNDNESS.md` is how the states are computed and what is
rejected. `doc/READING_THE_OUTPUT.md` reads a rendered page table by table.
This file is the map.

## Layout

The engine, in dependency order. Nothing below depends on anything above it.

| | what lives here | lines |
| --- | --- | --- |
| `Domains/` | the abstract values above, their lattices, and `NodeId` | 1,516 |
| `Cells/` | the heap: typed cell names, state, join, recency | 480 |
| `Engine/` | carrying state through a program; the exception policy | 901 |
| `Syntax/` | the object language: the Ion front end, nodes, kinds, admission | 3,061 |
| `Rules/` | **the rules themselves** — start here | 1,916 |
| `RuleLang/` | the language those rules are written in | 3,215 |
| `Tables/` | semantic parameters that are not rules | 1,681 |
| `Transfers/` | the protocol walks that consult rules and tables | 5,631 |

`Syntax/` is also the front door. A program arrives as binary Ion — CPython's own
`ast`, serialized to the Strata Python dialect by `strata_python py_to_strata` —
and reaches the analyzer through two files. `Label.lean` relabels the imported
`stmt SourceRange` tree to `stmt Pos`, giving every node its `NodeId` and its line
and column. `Check.lean` then fuses admission with lowering, so a rejected program
is never analysed.

And everything that tests and documents it, nested here so that all of Pylate is
one subtree of the host package:

| | what lives here | |
| --- | --- | --- |
| `Tests/` | 16 Lean suites, run by `lake test` | 5,248 lines |
| `harness/` | the Python gates, probes, generators and renderer | 52 files |
| `corpus/` | the programs under analysis, grouped by why they exist | 250 programs |
| `doc/` | this design material | 7 documents |

Plus three files that are each the only member of their role, so a directory
would be worse than a root file:

- `Machine.lean` — the `M` monad: obligations, machine raises, the resolution
  cache, annotation entailment
- `Analyzer.lean` — the driver: `runProgram`, function inlining, entry points
- `Emit.lean` — the log writer, over `Lean.Data.Json`. `doc/READING_THE_OUTPUT.md` reads its output
  field by field; the normative schema, `RENDER_SPEC.md`, has not been carried into
  this package yet, and `Emit.lean` and `harness/render_log.py` still cite it by
  section

## Reading order, if you are here to change something

**Adding a builtin method, or fixing what one returns** → `Rules/Builtins.lean`,
which holds 147 of the 196 rules. This is almost always the answer.

Every soundness defect this project has had was a missing entry — a tag absent
from a list, an operation with no arm — and never a wrong algorithm. So the rule
sets and the tables both carry coverage obligations that
`RuleLang/Validate.lean` enforces at *load*, and an omission is a validation
error rather than a silent claim at analysis time.

**Fixing what a protocol yields per tag** → `Tables/BuiltinOutcomes.lean`, the
outcome of six protocols across 21 tags. **A TypedDict mutation** →
`Tables/ShapePolicy.lean`. These are semantic parameters rather than rules,
which is why they are not in `Rules/`.

**Adding a syntax form** → `Rules/SyntaxPlans.lean`. One `Plan` per admitted
constructor; 30 of the 49 are plans rather than code. If the form needs control
flow — a fixpoint, suspension, five-way routing — it becomes a declared engine
escape instead, which `RuleLang/Validate.lean` counts (`engine-body=19`) so the
number cannot grow unnoticed.

**Changing what a protocol does** → `Transfers/`. Hand-written Lean, and staying
that way for the reason the last two sections give.

**Rejecting or admitting a construct** → `Syntax/Check.lean`, which fuses
admission checking with lowering so a rejected program is never analysed.

Whatever you change, it needs a case in `harness/gates/rule_validity.py`. See below.

## How a rule is shown to be right

A rule is a claim about what CPython does. `harness/gates/rule_validity.py` checks it
against CPython, one rule at a time: it runs a small admitted module under this
interpreter, runs the same module through the analyzer, and requires the second
to contain the first. Whatever CPython raised must appear at that line, and every
name CPython left bound must carry a tag covering its runtime type.

The cases hold no expected values. CPython is the oracle, so a case can only be
wrong by failing to reach the rule — never by recording a wrong answer.

Two inventories decide what needs a case, and neither is written by the tests.
The 196 rule keys come from `pylate --dump-rules`, straight out of the rule sets.
The transfers have no table to enumerate, so each observable step carries a
`CLAIM <id>:` marker in its docstring, and the gate reads those. Every one of the
228 must have a case or the gate fails and names it. Add a rule or a `CLAIM` with
no case and it goes red, which is the property worth having: the same "a missing
entry, never a wrong algorithm" failure mode that `Validate.lean` catches at
load, caught here against the runtime.

`--tight` reports the opposite direction — outcomes the analyzer admits that the
input could not take. Those are precision, not soundness, and are expected: a
join over both arms of an `if`, or a loop target that admits `unbound` because
the loop may not run.

## Why the transfers are not rules

A rule says what an operation yields: `str.upper` returns a `str`, `list.append`
returns `None` and can raise nothing, a subscript on a `bytes` yields an `int`.
That is a table row, and 196 of them live in `Rules/`.

A transfer is what Python does to *reach* that answer, and in Python reaching it
is itself a program. `len(x)` calls `x.__len__`, which is arbitrary user code: it
can raise, mutate `x`, or return a non-integer, and each of those changes what the
caller sees. `a + b` tries `a.__add__(b)`, and if that returns `NotImplemented`
tries `b.__radd__(a)`, and the order flips when `b`'s class derives from `a`'s.
`x in c` tries `__contains__`, then `__iter__`, then `__getitem__` with an
`IndexError` meaning end-of-sequence. `for` calls `__iter__` then `__next__` until
`StopIteration`, which is an exception used as a normal control-flow signal.

None of that is a value a table can hold. It is control flow over the abstract
state: which candidate runs next, what the heap looks like after a user hook ran,
which raise the protocol swallows and which escapes, where each of the five
completions goes. `Rules/` describes the destination; `Transfers/` is the road.

The rule of thumb the split follows: if the answer depends only on the operand
types, it belongs in `Rules/` or `Tables/`. If reaching the answer runs user code
or branches on the abstract state, it belongs in `Transfers/`.

## Why the transfers are Python-specific

Every layer above `Transfers/` would survive being pointed at another language.
Abstract values, a heap of typed cells, five completions, a fixpoint, the rule
language: none of that mentions Python.

The transfers do, in a way that is not incidental:

| | the Python fact it encodes |
| --- | --- |
| `Expressions` | binary operators are two dunder calls with a reflection rule, and the reflected one goes *first* when the right operand's class derives from the left's; truth is `__bool__` then `__len__` then true |
| `Iteration` | `StopIteration` is an exception that means "stop", not "error" — and a class with `__getitem__` but no `__iter__` is still iterable, with `IndexError` as its stop signal |
| `Objects` | attribute lookup consults the instance, then the MRO in linearization order, and a miss in both is an `AttributeError` |
| `Dict` | a TypedDict is structural: the declared key set is a *shape*, and a write to an undeclared key breaks it |
| `Calls` | arguments bind positionally then by keyword, defaults evaluate once at definition, and annotations are assumptions in the body but obligations at the call |
| `Statements` | `try`/`except`/`else`/`finally` routes five completions, and `finally` runs on all of them |

Rewrite that table for another language and you have rewritten the transfers.
Which is the honest limit of the design: the tables and the rule language port,
and the protocol walks are the part that is really about Python.
