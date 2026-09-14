# The algorithm, and where soundness comes from

`../README.md` is the module map and says what is computed. This document explains
how the abstract states are computed, and which constructs are rejected because
they cannot yet be analysed soundly.

Two things carry the result. **Inlining every call and rejecting what cannot be
inlined**, so there is no interprocedural summary to get wrong — there are no
summaries. And **the output is checked downstream**: every tag claim is emitted as
a switch branch with an `assert false` catch-all, so the verifier re-establishes
the fixpoint rather than trusting it.

## The pipeline

| stage | owner | result |
| --- | --- | --- |
| parse | `strata_python py_to_strata` (CPython's own `ast`, serialized to the Strata Python dialect) | binary Ion |
| import | `StrataDDM.Program.fromIon`, then `Syntax/Label.lean` | typed Strata AST, `Pos` per node |
| admission, fused with lowering | `Syntax/Check.lean` | `Program`, or a violation list |
| abstract interpretation | `Analyzer.lean` driving `Transfers/` | one log per abort policy |
| render | `harness/render_log.py` | HTML per program |

Pylate's output is data, not a proof and not an encoding. What consumes it is a
lowering into the **Laurel** Strata dialect, which is where verification happens;
that lowering is a separate step and is not in this directory.

Admission and lowering are one pass, so a rejected program is never analysed:
there is no window in which a construct outside the subset is being interpreted
by transfers that were not written for it.

## Abstract interpretation

State is an environment, a heap of typed cells keyed by allocation site, and a
size per collection location. Values carry tags, points-to sets, callable names,
a literal bag, and a witness bit.

### How a state is addressed

Everything the analysis records — an abstract state, a residual, an obligation,
an allocation site — is keyed by position, so what counts as a position decides
what can be told apart. Three types carry it, each adding what the one before it
cannot express.

**`NodeId`** identifies a syntax node by its **path** from the module root: the
sequence of argument indices taken to reach it, so `[0, 2, 1]` is "command 0,
argument 2, argument 1". The Strata AST indexes arguments positionally, which
makes the path canonical — a property of where the node sits, not of the order a
traversal reached it. Two consequences matter. An edit elsewhere in the file
leaves an id alone, so goldens churn only for the subtree that moved. And a
*synthetic* site — the element of a materialized container, a field of a
materialized object — is the real site's path extended under a reserved index, so
it cannot collide with any node's path or with another synthetic site. Not
"probably does not collide": cannot.

`Loc.site` is a `NodeId`, and the heap hashes it on every lookup, so the path is
stored innermost-first (extension is a cons, and every parent's tail is shared by
its descendants) with the hash folded in as it grows and cached.

**`PP`** is a program point: either a node, or a **join** that node induces. A
join needs no identity space of its own — it is the owning node plus which join
it is, and all nine kinds are derivable from the AST with no CFG construction:

```
ifMerge · loopHead · loopExit · breakTarget · continueTarget
handlerEntry i · handlerMerge · finallyEntry · finallyMerge
```

The join kind is not decoration: **one node owns several states**, and without it
they collide. Every statement is snapshotted at its own node key
(`Statements.lean`), so a `while` node already holds its pre-loop state — and the
fixpoint then produces a loop-head invariant, a loop exit, a break target and a
continue target. Five states, one node id. A `try` holds its entry state plus a
handler entry per clause, a handler merge, a finally entry and a finally merge.
Keying by node alone would join all of them, which is the same collapse that
keying by line caused, just relocated.

A second thing follows from naming them, but is not yet built: a claim can be
attached to a join. An obligation like "`break` and `continue` from inside a
handler feed the correct loop exits" is about the state at one particular join.
Those states are now recorded and emitted (below), so such a check has data to run
against — but no check currently reads them.

**`Addr`** is a `PP` plus the **call sites that led to it**, innermost first. The
analysis is context-sensitive by inlining, so one syntactic node is reached once
per call chain and the node alone does not identify a state:

```
foo → bar → x         frames = [call bar in foo,  decl foo]
foo → qux → bar → x   frames = [call bar in qux,  call qux in foo,  decl foo]
```

Both have the same point — `x` in `bar` — and differ only in the frames. This is
one path abstraction rather than two notions: a call site is a node, so it is
identified by its node path, and two calls on one source line are two frames. The
frame stack carries a running digest, so forming an address and hashing it are
both O(1).

Keying on anything coarser merges contexts. That is not only a precision cost:
the state map lives in the analysis context rather than being threaded like the
completion record, so a coarse key lets a value established on one call path be
read on another.

### What the addressing does *not* do

The joins are addressable, not load-bearing for control flow. `snapJoin` records
a state the transfer already computed by joining; it does not route anything. The
lattice operations, their operands and their positions are what they were before
the join points existed, so no precision was gained or lost by naming them.

Making them load-bearing would mean replacing the AST-recursive interpreter with
a worklist over addresses — state living *at* an address, read from predecessors
and written to successors, with explicit widening at `loop-head`. The edge
relation itself is cheap, since the nine kinds already name every merge; the
interpreter is the work. The payoff would be dischargeable obligations at joins
and precision that is not available today at all (keeping arms unmerged past a
merge, selective widening), rather than recovering anything currently lost.

The cheap intermediate step is a cross-check: a join's recorded state should equal
the join of its contributing arms' recorded states. That runs on the emitted data
below and needs no rewrite.

### Reading the addressing out

The log's `points` field is the `states` map as data: one entry per address, with
its line, its node, its join kind, its call frames, and the state. `lines` is the
same map joined by source line, so it cannot answer "what did *this* loop head
hold under *that* call chain" — `points` can. The rendered page carries it as a
`program points` table.

```
3.2.1@handler-entry:0 < 4.1     L18   join=handler-entry:0   frames=[4.1]
3.2.1 < 4.1                     L18   join=-                 frames=[4.1]
1.2.1 < 3.2.1.0.0.0.0.0 < 4.1   L8    join=-                 frames=[3.2.1.0.0.0.0.0, 4.1]
```

The first two are the same line and the same node, separated only by the join
kind. The third is two calls deep.

Statements complete in one of **five** ways, carried as one record:

```
normal · returned · broke · continued · raised
```

Two properties make that work: `none` is bottom, so an empty slot *proves* no
path left that way rather than meaning "unknown"; and `join` is pointwise, so no
slot can contaminate another. Compound statements route completions by copying
the record and erasing slots — `{ body with normal := none }` is literally how
handlers are separated from fallthrough — and that is sound precisely because
`none` is bottom.

Loops and comprehensions are fixpoints. Everything else is a `Plan`: data
describing what a node does, interpreted by one executor. 30 of the 49 syntax
constructors are plans; the other 19 are declared engine escapes, counted by
`RuleLang/Validate.lean` so the number cannot grow unnoticed.

## Calls: inlining, not summaries

Verified rather than assumed. `f(x: int) -> int: return x` called as `f(7)`
yields the literal `7`; the declared interface is only `int`, so the actual
argument was propagated through the body. `return 5` yields `5`.

It is **context-sensitive per call site**. Mutual recursion shows the chains:

```
contexts: ['a:1', 'a:1 > b:2', 'a:7', 'a:7 > b:2', ...]
```

`b` is analysed separately under each caller. That rendering names a call site by
line, which is enough to read but not to key on — the states themselves are keyed
by `Addr`, so two calls sharing a line are still two contexts and may print the
same label twice. Virtual calls inline per candidate:
a receiver that may be two classes gives `{obj:A: A.m, obj:B: B.m}` and a
`case-split` obligation, rather than widening to `any`.

Recursion is **rejected** (`recursive-call`). Summarising a call already on the
stack needs a contract, and there is none — see `RECURSION_CONTRACTS.md` for the
measurements that show the previous optimistic summary was unsound in three
independent ways.

## What the result rests on

Five mechanisms, in descending order of how much they carry:

**1. Exhaustive inlining.** No call is summarised, so no summary can be wrong.
Side effects and allocations inside a callee are analysed directly.

**2. Rejection.** What cannot be modelled is refused, not approximated:
recursion, `__getattr__` and the other attribute-protocol overrides, decorators,
metaclasses, `global`, nested functions, `del` on a subscript, multi-generator
comprehensions, walrus, `async`. 119 of the 250 corpus programs exist to be
rejected, and each states which rules must fire.

**3. Aborts for what is modelled but unprovable.** A machine raise in a category
the policy aborts stops the analysis with an obligation rather than continuing on
an assumption. `contract` is deliberately not a policy category, so an annotation
violation always aborts and is uncatchable.

**4. Coverage obligations checked at load.** Every soundness defect this project
has had was a missing entry, never a wrong algorithm — so rule sets and tables
carry coverage conditions that `RuleLang/Validate.lean` enforces when the rules
compile. An omission is a validation error, not a silent claim at analysis time.

**5. The output is re-checked downstream.** Tag claims are emitted as switch
branches with `assert false` catch-alls, so a claim the analysis got wrong becomes
a reachable assertion rather than a trusted fact. See below.

The one direction that matters is containment: the analyser may report an outcome
that does not occur; it may not miss one that does.

## The asymmetry worth naming

**The rule EDSL is a contract language for operations, and Python source has no
way to say any of what it says.**

The cleanest way to read a rule is as behaviour at the *interface* of an
operation, in two halves:

- **what it checks on the abstract state** — argument contracts, receiver tags,
  whether a key is present, whether a separator is non-empty
- **what updates it makes to the abstract state** — the cells it grows or clears,
  the size and emptiness it establishes, the names it binds

Both halves are declared, and both are machine-checked: `RuleLang/Compile.lean`
validates that a declared update names a cell the target class actually has, and
`Validate.lean` requires coverage so an operation cannot silently lack a rule.

The update half has a fixed vocabulary:

```
Mutation = grow · clear · emptiness · sizeOfChildren · bind · unbind
```

Twelve builtin rules declare mutations, so `list.append`'s effect on the element
summary and on the collection's size is *specified*, not inferred from a body —
there is no body to inspect.

That asymmetry explains most of the design:

| | builtins | user code |
| --- | --- | --- |
| effects known by | a declared, checked contract | analysing the body |
| how a call is handled | apply the rule | inline it |
| recursion | not applicable | must be rejected |
| unanalysable body | never — the rule *is* the model | no vocabulary exists, so reject |

Contract-only mode for user functions is therefore not a new idea in this engine;
it is the *existing* rule vocabulary made writable at the source level. That is
the shortest description of what the contract language should be.

## Why aliasing cannot replace the value set

Every Python value is an object, including `int`, `str` and `float`, so it is
reasonable to ask why the points-to domain does not simply subsume the literal
bag: an `int` would be a location, and equal ints would be the same location.

It cannot, for two reasons that pull in opposite directions.

**Equal scalars are not one object, and which ones are is implementation-defined.**
CPython interns small integers and some strings, and separately deduplicates
constants within a single code object. So:

```python
1000 is 1000            # True  -- one code object, constants deduplicated
c = 1000; e = 1000      # True  -- same
c is int("1000")        # False -- computed, so a different object
5 is int("5")           # True  -- small-int cache
"hello" is "".join(["hel","lo"])   # False
```

Identity therefore is not a function of the value, and modelling scalars as
locations would make the analysis depend on interning behaviour that is a CPython
implementation detail rather than language semantics.

**Immutability makes aliasing unobservable anyway.** For the immutable core types
there is no operation that can tell two equal objects apart *except* `is` and
`id`. Nothing can be written through them, so a shared location and two distinct
locations have identical observable behaviour for every other operation.

Together those say: for scalars the value is what matters and the location is
not usefully knowable. So scalars are modelled as values with **no location**,
and the price is that `is` on them cannot be decided. Verified — the analyser
answers unknown `bool` for all of `5 is 5`, `1000 is 1000`, and `"x" is "x"`,
rather than guessing from the values. Locations are reserved for the mutable,
identity-bearing objects where aliasing is observable and a write through one
name is visible through another.

## Why a pre-fixpoint is not a silent wrong answer

A construct the analysis cannot summarise soundly does not produce a subtly wrong
result; it produces a **pre-fixpoint** — a claim that some tag combination cannot
occur when it can. That is the failure mode rejection exists to avoid, and it is
also the failure mode the downstream encoding catches.

### The two sort regimes

The log's `sorts` field reports which one was used, and they differ in exactly
what the downstream encoding is allowed to lean on.

Pylate does not encode anything itself. It emits data — including a **sort plan**
describing how each binding should be declared — and a separate step lowers the
program into the **Laurel** Strata dialect using it. Laurel is what reaches a
solver; Pylate never does. `Emit.lean` cites `SMT_ENCODING.md` for the regimes, and
neither that spec nor the lowering is in this package, so the concrete sort name
below is deliberately not asserted here.

A Python variable can hold values of different types at different times, so the
encoding needs one sort that can represent all of them. That is the **universal
value sort**: a single Laurel sort into which every Python value is injected,
carrying a discriminator for its type. A binding declared at that sort can hold an
`int` or a `str` or a reference, and asking which it is means *testing* the
discriminator rather than reading it off the declaration.

That is what makes the analysis checkable:

| `--sorts checked` (default) | `--sorts residual` |
| --- | --- |
| every binding is declared at the universal `PyValue` sort | bindings are carved into per-flavour ADTs, and native sorts where monomorphic |
| a fixpoint tag claim becomes a **switch branch**, with a catch-all that is `assert false` | a tag the analysis missed is **unrepresentable** — the catch-all is vacuous |
| the operational semantics **checks** the fixpoint | carrier completeness is **trusted** |
| larger encoding | smallest encoding, and needs the fixpoint certificate plus transfer soundness |

So under the default, an analysis result is not an assertion the verifier accepts.
Saying "`x` is an `int` here" compiles to "switch on `x`'s discriminator; the `int`
branch does the work; every other branch asserts false." If the analysis reached a
pre-fixpoint and `x` can really be a `str`, a real execution takes the `str`
branch and the verifier reports the violated assertion.

Under `--sorts residual` that safety net is gone by construction: if `x` is
declared at an ADT with only an `int` constructor, there is no `str` branch to
reach, so the missed tag cannot be caught. That is the trade the mode names.

That is what makes rejection a schedule rather than a correctness cliff: a
construct is refused while its contract does not exist, and if one were admitted
early the catch-all is what would find it.

## Constructs rejected for now, and why

| construct | why it cannot be summarised yet |
| --- | --- |
| **recursion** | the callee is already on the stack, so the summary would need its result, raises and frame, checked. Measured: assuming the return annotation lost both the deeper levels' writes and the base case's raise — `RECURSION_CONTRACTS.md` |
| `__getattr__`, `__setattr__` and the other attribute-protocol overrides | the lookup itself becomes user code |
| decorators, metaclasses | the class object a name denotes is computed — `POMAD.md` |
| `global`, nested functions, `del` on a subscript, multi-generator comprehensions, walrus, `async` | outside the modelled state shape |

119 of the 250 corpus programs exist to be rejected, and each states which rules
must fire.

## Precision left on the floor

Sound, and known to be blunter than necessary.

- the legacy joined `Exc` view collapses per-raise state at four remaining sites
- non-relational across variables: `x is y` correlations, and a handler's
  `e`-class ↔ other-variable pairing
- comprehension elements lose literals: `[f(3) for …]` has no `3` in `elem`
- per-rule tightness is measured and reported, never asserted, so a rule that
  quietly widened would pass every gate

## One thing that is not yet either

Contract-only stubs (`def f(...) -> T: ...`) answer from the return annotation and
leave the heap untouched. Measured: `zs = [1]; stub_mutates(zs)` still reads
`elem = int` with literal `1`, though the stub may append anything. That is a
claim a real execution can contradict, so it belongs with recursion — havoc the
argument-reachable heap, or reject until the frame vocabulary exists.

## How the posture is verified

Differential against a live CPython run, one direction: *abstract ⊇ concrete*.

| gate | asserts |
| --- | --- |
| `admission` | 250 programs' accept/reject verdict and exact violation-rule set |
| `validity` | 220 cases over 228/228 inventory entries (196 rules + 32 transfer `CLAIM`s): raised class, bound-name tags, line reachability |
| `conformance` | 579 differential scenarios, 10 skipped on this interpreter |
| `catchall` | 154 (tag, operation) pairs — 11 tags × 14 operations — both directions |
| `corpus` | 249 golden digests across three policies, and the HTML |
| `coverage` | 196 manifest entries exercised by the golden logs |
| `comp-precision` | 560 two-sided checkpoints |
| `pylateTests` | 16 Lean suites, 295 assertions, including the load-time coverage conditions |

They run inside `brazil-build` and fail it.

## Where the posture must change

The moment a body is admitted that will not be analysed — an import, a `.pyi`
stub, third-party code, a C extension beyond the modelled builtin surface —
inlining stops being available and a summary becomes load-bearing. At that point
the contract language is required, and its default must be inverted from the
obvious one:

> an unspecified heap effect means **havoc**, not "no effect".

Getting that default backwards is exactly the current stub bug.
