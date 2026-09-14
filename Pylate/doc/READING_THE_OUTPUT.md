# Reading the analyzer's output

A guided walkthrough of one rendered page, table by table, using
`corpus/baseline_assignment_target_order.strict.html` as the worked example.
`../README.md` is the module map and says what the analyzer computes; this says
how to read what it produced. Regenerate the page with
`python3 harness/gates.py --fast`, then open
`corpus/index.html` and follow the link for this program.

This document explains every table on the rendered page, in the order the page
presents them, and records what the analyzer gets right and wrong on this
program. It is not a specification: `render_log.py` is the authority on what each column
contains, and `resid_status.py` on what a status means. Column semantics below
were read out of those two; the numbers were read out of a current run of
`harness/pipeline.py` on this program. (`RENDER_SPEC.md`, cited by `Emit.lean`
and `render_log.py` as the normative schema, has not been carried into this
package.)

## The program under test

```python
def store() -> str:
    box = Box()
    try:
        fail_target(box)[late_index(box)] = 1
        return "missed-target-error"
    except LookupError:
        return box.value
```

Python evaluates a subscript assignment in the order value, target receiver,
target index. `fail_target(box)` therefore runs its side effect (setting
`box.value` to `"target-evaluated"`) and raises `LookupError`; `late_index` never
runs, and the store never happens. CPython returns `'target-evaluated'`
(verified by running the file). The page must reproduce that reasoning, and the
useful test is whether it does so for the right reason.

## Page shape

One page covers one program under one abort policy. Each source line that has
analysis carries an annotation block in a fixed order: the residual table, then
one `state at ...` panel per site, then the handlers table if the line opens a
`try`, then the `entry:` panel. The global tables close the page: the dispatch
table, the sort plan, and `program points` — every address the analysis keyed a
state on, which is the one table that is not per line.

## Header strip

```
dispatch sites 3 | resolved 2 | deferred to SMT 0 |
abort policy strict (all machine raises abort) |
sorts checked: 3/5 monomorphic, 1 flavor
```

`abort policy strict` means every interpreter-generated exception is turned into
an assertion failure rather than modeled as control flow. On this program the
policy changes nothing: the only exception is an explicit `raise`, which no
policy rewrites. The `strict`, `eafp`, and `audit` logs carry identical
summaries, identical obligations, and an empty `machine_raises` list. That makes
this program a control case; contrast it with any program that indexes a dict,
where the three pages diverge.

`dispatch sites 3` counts operations; the `3/5` in the sort line counts bindings
in the sort plan. Different things that happen to share a digit.

## Residual table

```
status | sub-expression | operation | receiver tag | result
```

One row per (receiver tag, outcome) pair, so a site with three possible receiver
types produces three rows. The first three columns print only on the first row
of a group: a blank cell means "same site as the row above". State this before
anything else, because it is the main reason the table is misread.

| column | content |
|---|---|
| `status` | verdict for the whole site, derived by `status_of` and never stored |
| `sub-expression` | the source text the site dispatches on, truncated at 60 characters |
| `operation` | `<kind> <desc>`, plus `[strong]`/`[weak]` when the site mutates, plus a `via <chain>` prefix, plus `=> <value>` for the site result |
| `receiver tag` | the abstract type the row is about (`obj:Box`, `func`, `str`), or `code`, which marks an outcome produced by the callee body rather than a receiver type |
| `result` | the target that tag resolves to (`fail_target`, `field`, `store`), or `raise <Cls>` / `abort <Cls>` in red |

Status is **derived, never stored**, and `harness/resid_status.py` is the single
derivation — the analyzer's report, the renderer and the summary counters all
import it, and `Emit.lean` mirrors it as `residStatus`/`isDispatchSite`.

| badge | condition |
|---|---|
| `RESOLVED` | exactly one target and no error edge, so it compiles to a direct call or field access |
| `MAY_RAISE` | one target but an exception edge survives: no type test needed, but a guard is |
| `SPLIT(n)` | n distinct targets survive — a case split for the solver |
| `UNKNOWN` | an unknown tag reaches the site |
| `MUST_RAISE` | no normal target: every live tag is an error row |
| `UNREACHABLE` | the site's own operation never ran, because an operand raised first |
| `setattr`, `setitem` | a store, which resolves no target and so gets no dispatch verdict |
| `contract` | a verification boundary rather than an operation |

`MAY_RAISE`, `UNREACHABLE` and `contract` are the three the bare derivation has no
room for, added by `render_status`. An empty status now prints nothing rather than
falling back to a fixed word.

### Call-context labels

`via store:16 > Box.__init__:17` is a per-context slice, printed only when the
site was analyzed under more than one call chain. The format is
`<function>:<line>`, where the line is the call site for an inlined context and
the definition line for a standalone entry-point analysis. Every function is
analyzed both ways, which is why most rows on this page appear twice:
`store:16` is `store` analyzed as an entry point (`def` on line 16) and
`store:25` is `store` inlined from `result = store()` on line 25.

## variables

```
variable | type tags | value | init | points-to | size | alias
```

| column | content |
|---|---|
| `variable` | the name |
| `type tags` | possible runtime types joined by `\|`, with `fn{...}`/`cls{...}` for function and class values; `BOT` when the set is empty |
| `value` | the program literals the value may equal, in Python spelling: `7`, `1.5`, `True`, `None`, `'ab'`, `b'ab'`. `1 \| 2` is one of two. A trailing `*` marks a tag whose values are *not* enumerated, so `7` means exactly seven and `*` means an unknown number. `-` means the value has no literal to report |
| `init` | binding status derived from the `unbound` tag: `bound`, `maybe unbound`, `definitely unbound` |
| `points-to` | the may-points-to set, or `-` for non-references; `(witness: weak stores)` when the value stands for several objects |
| `size` | the element count of each collection this points to: a number when exact, `positive` when non-empty but uncounted, `unknown` otherwise. A count belongs to a *location*, so a may-alias over two collections of different lengths shows both |
| `alias` | `must -> Box@3.2.0.1^` when the value provably denotes that one object, otherwise `may` |

The `unbound` tag is dropped from `type tags` and surfaced in `init` instead, so
a clean type column can still mean "may be unbound". `alias` reports `must` only
when the points-to set is a single recent location, the tags are a subset of that
location's tag, and the value is not a witness (`alias_col`,
`render_log.py:270`).

## heap (reachable cells)

```
cell | type tags | value | init | points-to | update
```

| column | content |
|---|---|
| `cell` | `Class@site^.field`, where `site` is the allocating node's path — `Box@3.2.0.1^.value` |
| `type tags` | as above; `BOT` means never assigned on any path |
| `value` | the literal bag, read exactly as in the variables table |
| `init` | from the `uninit` tag: `init`, `maybe uninit`, `uninit` |
| `points-to` | what the field points to |
| `update` | `strong (mult 1)` for a most-recent block, `weak (summary)` for a summary block |

A synthetic `.nonempty` cell appears when a collection is *definitely* non-empty;
it is redundant with a non-zero `size` and is kept because readers depend on it.

Only cells reachable from the environment appear, which is why the list changes
length down the page.

## The two panel kinds

`entry: ...` is the invariant before the line executes; the one-line summary
shows the environment, and expanding it gives the two tables above.
`state at <sub-expression>` is the state at one specific site, mid-statement,
with one panel per site in evaluation order. Line 19 carries both, and comparing
them is the point of the example.

## Line-by-line commentary

**Line 3, `self.value = "initial"`.** The residual is a `setattr` with two
context slices (`store:16 > Box.__init__:17` and `store:25 > Box.__init__:17`),
both resolving `obj:Box` to `store`, both marked `[strong]`. The heap panel shows
`Box@3.2.0.1^.value | BOT | uninit`: before the store the field has no value, so the
tag set is empty and `init` reports `uninit`. This is the clearest row on the
page for the `uninit` machinery.

**Line 6, `def fail_target(...)`.** A `contract` row, `fail_target entry`, whose
`errors` carry `code -> LookupError`: the body always raises. This produces the
`guaranteed-error` obligation at L6. A contract is a verification boundary, not an
operation, so it is not a dispatch site and gets no dispatch verdict.

**Line 7, `box.value = "target-evaluated"`.** Three context slices: the
standalone `fail_target:6` plus the two inlined chains through `store`. The entry
panel shows the join across those contexts,
`box={Box@3.2.0.1^,Box@1000000.0.0^}`, with `alias` reading `may`. `Box@3.2.0.1`
is the real object from `store`, allocated at the node with that path;
`Box@1000000.0.0` is the parameter materialized for the standalone entry-point
analysis. `1000000` is `NodeId.synthMarker`, the reserved index synthetic sites
hang under — it is not a line number, and it reads like one, which is a rendering
wart worth fixing. Colleagues
will read the joined panel against the `[strong]` marker and object; that
tension is explained in defect 4.

**Line 8, `raise LookupError()`.** No residual, two state panels. Both
`.value` cells now read `str`, so the strong update took effect in each context.

**Lines 12 and 13, `late_index`.** A `setattr` resolving `obj:Box` to `store`,
one context only (`late_index:11`), with parameter `Box@1000000.1.0^`. These panels
exist because `late_index` is analyzed as its own entry point. They are not
evidence that anything called it, and someone will assume they are.

**Line 17, `box = Box()`.** `entry: (empty frame)`, the state before the
allocation.

**Line 18, `try:`.** The handlers table, `reaching exception | handler match`,
with one row: `LookupError | caught by except LookupError (line 21)`. One row per
class that reaches the `try`; uncaught classes say so instead. This row is where
the page shows the exception is handled rather than escaping.

**Line 19, the assignment.** One site: `call fail_target(..)`, badged
`MAY_RAISE`, with `func` resolving to `fail_target` and `code` resolving to
`raise LookupError`. The callee was identified and it can raise, which is exactly
what that badge means. The store itself produces no residual — the receiver
raised, so `setitem` never ran. No row anywhere
on this line mentions `late_index`, and no context slice of the form
`store:* > late_index:*` exists in the log. The analyzer proves the index
expression is never evaluated, which is the property the example exists to test.

**Line 22, `return box.value`.** `RESOLVED`, `getattr .value => str`, `obj:Box`
resolving to `field`. The heap shows
`Box@3.2.0.1^.value | str | init | strong (mult 1)`: because the update on line 7
was strong, `"initial"` was replaced rather
than joined. The HTML shows only the tag, but the log records
`string_literals: ["target-evaluated"]` with `string_open: false` for that cell.
The analyzer pins the exact CPython answer. Mention the log when anyone asks
about literal-level precision.

**Line 25, `result = store()`.** `RESOLVED`, `call store(..) => str`, `func`
resolving to `store`. Correct here; the global table below is not.

## Global dispatch table

```
receiver tag | operation | resolves to
```

The file aggregated into one row per (tag, operation), which is the
devirtualization manifest handed downstream. `resolves to` renders from the
target kind: a `code` label with its definition line, `raise <Cls>`,
`abort <Cls>`, `construct <Class>`, `builtin rule <R>`, `deferred to solver`, or
`heap cell (no code runs)` for kind `field`.

Two of the six rows on this page put `code` in the receiver-tag column. See
defect 1.

## Sort plan, flavors, bindings

The sort plan line states the trust position, and it should be read out rather
than summarized: under `checked`, every binding takes the universal value sort,
and tag claims appear only as switch branches with assert-false catch-alls, so
the operational semantics checks the fixpoint. The `residual` mode instead carves
per-flavor algebraic data types and trusts carrier completeness.

`flavors` lists each distinct multi-tag union (here one, `any|str`). `bindings`
gives `carrier | tags | sort` per binding. Two of the five bindings are
polymorphic, and both are `.value` fields of materialized entry-point parameters
(`Box@1000000.0.0`, `Box@1000000.1.0`) whose incoming field value is
unconstrained.
The real program never stores a non-`str` there. The `3/5 monomorphic` figure is
therefore degraded by entry-point analysis artifacts rather than by the program.

## Devirtualization

`RESOLVED` marks a site with exactly one possible target and no possible error, so
a consumer can compile it to a direct call or a direct field access with no type
test and no exception edge. The requirement that the site cannot raise is what
makes the count meaningful: honest exception reporting lowers the score, and a
high score obtained by hiding exceptions would be worse than a low one.

What counts as a site is a denylist, not an allowlist, in
`harness/resid_status.py` (mirrored as `isDispatchSite` in `Emit.lean`):
`setattr`, `setitem`, `name`, `identity` and `contract` are excluded. Stores
resolve a target but pose no dispatch question; a name read and an identity test
are not dispatched at all; a contract is a boundary. Everything else counts,
including the protocol operations that resolve `__bool__`, `__contains__` and
`__eq__`, so the `deferred` headline agrees with the derived `deferred-dispatch`
and `case-split` obligations.

On this program that admits the call on 25, the call on 19 and the `getattr` on
22 — three, of which two are `RESOLVED`. The header says 3, which is the rule
applied exactly.

## Recency: `^` and `*` across a loop

`Box@3.2.0.1^` is the most-recently-allocated block at the site whose node path
is `3.2.0.1`, and permits strong updates; `Box@3.2.0.1*` is the summary block,
stands for an unbounded number of objects, and permits only weak updates. `~w` on
a value marks a witness, which stands for several objects.

There is no separate rule for what a reference means outside a loop, because `^`
does not mean "allocated in this iteration". It means "no allocation at this site
has executed since this reference was created". `allocate`
(`Engine/Update.lean`) maintains exactly that: on each allocation at a site it
renames every existing reference to that site's most-recent block into the summary
block — across the environment, the heap's values and the heap's keys — then
returns a fresh most-recent block. The aging happens at the allocation, not at the
loop join and not at the loop exit.

Two consequences answer the question directly. First, a variable whose last
assignment is the allocation itself stays `^` after the loop: no allocation at
that site can have run between the assignment and the exit, so nothing aged it,
and a strong update through it remains sound. Second, a reference that survives
an allocation becomes the summary:

```python
for _ in range(n):
    x = Box()          # site s
    keep.append(x)     # element cell holds Box@s^
```

On the next iteration `alloc` renames the element cell to `Box@s*`, and the
append then adds the new `Box@s^`. Outside the loop, `keep`'s element cell holds
`{Box@s^, Box@s*}` while `x` still holds `Box@s^`. A conditional assignment
produces the same split on the variable itself:

```python
for _ in range(n):
    if cond:
        x = Box()      # site s
```

Here the path where `cond` was false in the final iteration carries an object
that a later allocation aged, so outside the loop `x` holds
`{Box@s^, Box@s*}`, `alias` reports `may`, and the strong-update test refuses
because the target set has two members. A loop that may run zero times contributes its own path to the exit
join, which shows up in the `init` column as `maybe unbound` rather than in the
recency marker.

The licensing rule is worth stating explicitly, since it is what the `update`
column asserts: a strong update requires a single target location, that location
recent, and the receiver not a witness. Any structure holding a `Loc` that
`allocate` does not scan would break the multiplicity-1 claim, so a new
`Loc`-holding field needs the same rename treatment.

## Soundness assessment

The reported result is correct, and correct for the right reason. The analyzer
evaluates the target receiver, applies its side effect, propagates the
`LookupError`, never evaluates the index, never performs the store, routes the
exception to the line 21 handler, and reads back
`Box@3.2.0.1.value = "target-evaluated"` as a single string literal with
`string_open: false`. That matches CPython exactly.

Three defects sit in the reporting layer rather than in the abstract
interpretation. None of them is unsound; all three are attribution or rendering.

**1. `code` appears in the receiver-tag column.** The row
`code | call fail_target(..) | raise LookupError`, and the matching one on the
`contract fail_target entry`, put a non-receiver marker where a receiver type
belongs. Nothing unsound follows — the outcome reported for the statement is
right — but the global table ends up stating a dispatch rule for a receiver tag
no value can carry.

**2. `[strong]` is a site-level claim shown against a joined state.** `updates`
is stored on the residual, not per context: line 7 carries `updates=['strong']`
while all three context slices carry `updates=None`. The panel beside it shows
the join, `box={Box@3.2.0.1^,Box@1000000.0.0^}` with `alias` reading `may`. Read
literally the page claims a strong update through a two-element may-alias set. Per
context each points-to set is a singleton, so the engine is doing the sound thing,
but the page cannot distinguish that from the unsound one. Rendering `updates` per
context, or labeling the panel as a join, would close the gap. The `program
points` table now makes the per-context states inspectable, which is most of what
is needed to check it.

**3. The synthetic-site marker renders as a bare number.** A materialized
entry-point parameter reads `Box@1000000.0.0^`, where `1000000` is
`NodeId.synthMarker` — the reserved argument index synthetic sites hang under, not
a source position. It reads like a line number. A `#`-prefixed rendering would fix
it, at the cost of re-blessing every golden that mentions one.

### Fixed since this walkthrough was first written

- **A user function named `store` reported as a heap access.** The target
  vocabulary shared an untagged string namespace with user-chosen function names,
  so a function called `store` rendered as `heap cell (no code runs)`.
  `Emit.lean`'s `dispatchTable` now classifies by the site's *kind*, so a name
  cannot impersonate a protocol sentinel.
- **A call site badged `setattr`.** The status derivation fell through to the empty
  string for "one target, can also raise", and the badge helper printed a fixed
  word for an empty status. That state now has its own badge, `MAY_RAISE`, and an
  empty status prints nothing.
- **The site count disagreeing with the counting rule.** Both now come from one
  module, `harness/resid_status.py`, mirrored in `Emit.lean`; the header reads 3
  and the rule gives 3.

## Points to close on

Every row is an over-approximation: an extra row is precision loss, never a claim
that Python performs that operation. The three policy pages are identical for
this program because the only exception is an explicit `raise`, so pair it with a
dict-indexing example when demonstrating what the abort policy does.
