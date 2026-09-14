# What a contract language must offer to analyse recursion soundly

Recursion is rejected (`recursive-call`). This records why the previous treatment
was unsound, and what a contract would have to state for the rejection to be
lifted.

## What the analyser used to do

At a recursive re-entry it filed a `recursion-widened` obligation and returned
the declared return annotation:

```lean
if context.callStack.contains rule.qualifiedName then
  oblige position "recursion-widened" "...assumed the declared return annotation"
  return Flow.ofNormal (<- recursionValue rule) state
```

Three assumptions are packed into that one line: the deeper levels **return**
something the annotation covers, **raise** nothing, and **write** nothing. All
three are false in general, and the first is the only one that was even
acknowledged.

## The measurements

Both cases were run against CPython.

### Writes from the cut-off levels are lost

```python
def descend(xs: list[int], n: int) -> int:
    if n > 0:
        xs.append(n)
        return descend(xs, n - 1)
    return 0

ys = [9]
descend(ys, 3)
```

CPython leaves `ys == [9, 3, 2, 1]`. The analyser reported the element literals
as `['3','9']` with the open marker **empty** — a *closed* claim that the elements
are exactly 9 and 3. The first level was inlined, contributing `3`; levels two and
three were cut off, so `2` and `1` vanished.

Note this is invisible if every level writes the same value — an earlier version of
this test appended a constant `7` and the analyser looked correct.

### Raises from the cut-off levels are lost

```python
def raiser(n: int) -> int:
    if n > 0:
        return raiser(n - 1)
    raise KeyError("bottom")
```

CPython raises `KeyError`. The analyser reported `may_raise: []` and no error edge
at the call: the cut-off returns `Flow.ofNormal`, which asserts the recursive call
cannot raise. The base case's raise is only reachable through the recursion, so it
was never seen.

## What the contract must carry

The cut-off summarises an unbounded number of remaining calls, so the contract has
to be **inductive**: assumed at the recursive call, and re-established by the
body. That is assume-guarantee, and it is why `recursion-widened` was filed as an
obligation — a proof owed, never discharged.

Five components. Only the first exists today.

| component | today | why recursion needs it |
| --- | --- | --- |
| **result** — the abstract value returned | return annotation | the value at the cut-off |
| **raises** — classes that may escape | assumed none | the base case's raise is invisible otherwise |
| **frame** — locations that may change | nothing | bounds what deeper levels may touch |
| **written values** — per writable location, the values it may take | nothing | without it, a closed literal claim survives an unbounded number of writes |
| **allocation** — may it create objects reaching the result or frame | nothing | recency needs to know whether a fresh block appears |

The sound default with none of them is **result `any`, raises ⊤, havoc everything
reachable from the arguments**. The old behaviour was not a conservative
approximation of that; it was an optimistic one.

## Two properties that matter more than the field list

**It must be checked, not merely assumed.** The engine has to run the body under
the assumed contract and verify the body's own result, raises and writes are
contained in it. Otherwise the contract is an axiom a user can get wrong. That is
one extra fixpoint iteration, not a new algorithm.

**The frame must be relative, not absolute.** A signature cannot name heap
locations — allocation sites are analysis artifacts. What it can name is
reachability from parameters: `writes xs.elem`, `writes self.*`, `writes nothing`.
That composes with the argument annotations already present, and
`Engine/Update.lean`'s reachability is the function that interprets it.

## This is the rule language, exposed

The vocabulary already exists for builtins:

```
Mutation = grow · clear · emptiness · sizeOfChildren · bind · unbind
```

Twelve builtin rules declare mutations; `RuleLang/Compile.lean`'s `mutationErrors`
checks each names a cell the target class has. So the frame language is written,
validated, and in use — just not reachable from Python source. A contract language
for user functions is that vocabulary made writable, plus the raises and result a
rule already states.

## Scope

The same contract serves two callers, which is why they are one feature:

- a call whose body is **already on the stack** (recursion)
- a call whose body **does not exist** (a stub, an import, third-party code)

Contract-only stubs are implemented and currently share the same hole: they answer
from the return annotation and leave the heap untouched. Measured: `zs = [1];
stub_mutates(zs)` still reads `elem = int` with literal `1`. Until the frame
vocabulary exists they should havoc argument-reachable heap, or be rejected as
recursion is.
