# Backlog: making Pylate match CPython exactly

**Goal.**  Bring Pylate to a state where all constructs in the subset are supported and Pylate simulates CPython's static scope resolution, its lowering-determined semantics, its MRO, and its operational semantics soundly and as precisely as possible.

This document lists every deviation found so far by running Pylate on our 700+ 
construct test coprus each with the measurement that witnesses the deviation.
It is written to be handed to an agent working in the Brazil workspace.

**Provenance.** Every program was executed. The package was cloned and all **778
programs** in the ten semantic-witness corpora of `PyHardMiningAgents/findings/`
were run, with Pylate's output compared against a live CPython 3.13.5 run on the
same program. Nothing below is inferred from a corpus digest. Where a
characterization belongs to another team's document rather than to a measurement,
the text attributes it. Nothing was verified under `brazil-build`; all
measurements come from a standalone build of `Pylate/`, which is possible because
that directory imports nothing from Strata.

The raw per-program results are in `doc/sweep/sweepall.json` and the harness that
produced them in `doc/sweep/sweepall.py`. `LOWERING_ALIGNMENT.md` has the
per-mechanism detail for `ast-bytecode-lowering`.

### What the sweep found

| CPython | Pylate | programs |
| --- | --- | --- |
| passes | rejected, outside the subset | 373 |
| passes | accepted, but aborts | 312 |
| crashes | accepted, aborts correctly | 36 |
| passes | accepted with obligations | 24 |
| crashes | rejected | 22 |
| passes | accepted, clean | 5 |
| **crashes** | **accepted, does not abort** | **3** |
| timeout at 15s | counted under its Pylate verdict | 3 |

Of the 61 programs CPython rejects, Pylate handles 58. The three it does not are
**A0** plus two `cross-version-semantics` PEP 649 annotation-timing witnesses,
which crash on 3.13 and would not on 3.14 — the version pin is why they appear,
not a defect (C7).

The 312 over-rejections are the magnitude of the §A list: programs CPython runs
cleanly that Pylate refuses.

### Per corpus

| corpus | programs | crash, Pylate aborts | crash, Pylate rejects | CPython passes | **crash, not refused** |
| --- | --- | --- | --- | --- | --- |
| `laurel-encoding-soundness` | 476 | 1 | 1 | 474 | 0 |
| `ast-bytecode-lowering` | 135 | 0 | 0 | 135 | 0 |
| `cpython-modeling` | 50 | 0 | 0 | 50 | 0 |
| `mypy-unsoundness` | 48 | 24 | 14 | 9 | **0** |
| `monty-strata-overlap` | 26 | 0 | 2 | 23 | 0 |
| `ty-unsoundness` | 17 | 10 | 5 | 1 | **1** |
| `awstasks-mcp-restrictions` | 12 | 0 | 0 | 11 | 0 |
| `cross-version-semantics` | 7 | 0 | 0 | 5 | **2** |
| `cbmc-py-differential` | 4 | 1 | 0 | 3 | 0 |
| `monty-cpython-divergence` | 3 | 0 | 0 | 3 | 0 |

The two type-checker corpora are the sharp test, because their programs are built
to crash under CPython while the checker reports clean. **Of the 38 crashing
programs in `mypy-unsoundness`, Pylate refuses all 38.** Of the 16 in
`ty-unsoundness`, it refuses 15; the one that slips is A0.

`laurel-encoding-soundness` programs are encoding-divergence demonstrations rather
than crashers, so almost all pass under CPython; what they measure here is how much
of that corpus Pylate admits — 206 rejected, 263 admitted with an abort, 5 without.

Two directories are excluded: `aws-mcp-code-action-corpus` and
`code-action-verification`, 3008 directories of generated programs. They measure
admission rate on real code, a different question from exactness. Also skipped:
`cbmc-equivalence` (C harnesses, no Python), `monty-security` (empty scaffold),
`strata-benchmarks-triage` (scaffold). The package README tabulates nine corpora;
the tree has fifteen.

**One defect, and it was found by running the programs rather than probing.** A0
came out of `ty-unsoundness/003` executed as published. An earlier pass over these
corpora read each digest and probed Pylate on the named root causes, and concluded
no unsoundness existed. That was an artifact of the method: a hand-written probe
tests the reading of a finding rather than the finding itself, and it passed. The
lesson is recorded because it applies to anything added to this list — witness a
deviation with a program, not with a probe.

**The other engines' dominant root causes largely do not apply**, measured one probe
each in §E1. Pylate's own gaps are fewer and different in kind, concentrated in §A.
Do not import another engine's fix list.

The scoping half has an exact specification worth working against directly:
`cpython-modeling/formal-model/scoping_inference_rules.md` gives CPython's
`symtable.c` classification as eight inference rules over five binding categories
(Fast, Deref, Global, Name, ClassDeref) with an explicit precedence order. **Item
A1 below is its Rule 5 (GLOBAL-IMPLICIT).** That document is the target for
"simulate Python scoping exactly".

---

## How to read the categories

An **over-rejection** is a program CPython runs cleanly that Pylate aborts on. It
is *sound* — a refusal, not a wrong answer — but it makes ordinary Python
unanalysable, so it is the class that most limits usefulness.

A **precision gap** means Pylate's answer contains CPython's but is wider than it
needs to be. Sound; costs proof strength downstream.

A **declared approximation** is an unsound simplification that is *filed as an
obligation* rather than hidden. Sound only if the obligation is discharged.

A **diagnostic defect** is a wrong or contradictory message with a correct
underlying analysis.

---

## A. Over-rejections — refuses correct Python

### A0. A violated return annotation makes the value BOTTOM, discharging everything downstream

Read together with **A0b** below, which states why a bottom is containable in
principle and why that containment does not yet hold in practice.

Found by running `ty-unsoundness/003_unknown_launders_through_return_annotation/program.py`
as published. A hand-written probe of the same rule missed it, which is why this
sits above A1.

```python
def src():          # unannotated: body returns "s"
    return "s"
def f() -> int:     # annotation says int
    return src()
v = f()
assert v == 999999                      # false assertion   -> NO obligation
bogus: int = v + 1                      # str + int         -> NO obligation, no TypeError
oops: int = d["definitely-missing"]     # certain KeyError   -> NO obligation, no KeyError
```

`status: accepted`. `machine_raises: []`. The only obligations are two
`return-annotation` ones. CPython raises `TypeError`.

**Mechanism**, from the residual table: `src()` resolves correctly to
`tags=['str'] strlits=['s']`, but `f()` comes back
`tags=[] strlits=[] open=[]` — **bottom**. The annotation check finds `str`
against a declared `int` and yields an empty normal completion instead of either a
hard error or the body's actual value. Everything after the call is therefore
unreachable, and unreachable code discharges every later obligation for free.

This is the failure mode `AGENTS.md` names as the priority defect — *"makes
admitted normal code unreachable and can vacuously discharge later
obligations"* — reached through the annotation path rather than the
bound-builtin-call path. It is the same shape as the `super()` bottom defect fixed
earlier in this work (`SUBSET_DEFINITION.md` §8), and it is worth checking whether
any other check can produce bottom the same way.

**What it should do instead.** The finding's own text states the requirement:
*"this is exactly why PyHard must `assert` a hint, never `assume` it."* Since every
call is inlined, the body's value is in hand, so there are only two defensible
answers and bottom is neither:

1. tags disjoint from the annotation → a **hard error** through `contract`, as
   `param-annotation-violated` already does for parameters;
2. tags overlapping → keep the **body's** value, not the annotation's, and leave
   the obligation.

*Also caught by this:* two `cross-version-semantics/3.13_to_3.14` witnesses
(`witness_annotation_nameerror`, `witness_deferred_annotation`) land in the same
bucket, though those are the PEP 649 timing difference of C7 rather than this
defect.

### A0b. Unreachability must be *emitted*, or the assert-false safety net does not exist

**The containment argument.** Pylate is being built to be sound once it has
converged. Before convergence it does not have to be, because the Laurel lowering
is supposed to instrument every location Pylate calls unreachable with
`assert false`. If the program actually reaches one, the verifier reports a
violated assertion. Under that arrangement a bottom like A0's costs precision and
usability, not end-to-end soundness: the analysis stops being informative, but it
cannot make a wrong program verify. This is the same mechanism
`ALGORITHM_AND_SOUNDNESS.md` describes for tag claims, where a missed tag becomes a
reachable `assert false` branch rather than a trusted fact.

**The gap: the log does not say which locations are unreachable.** Measured on the
A0 program against a reachable control with the same statements:

| | `lines` snapshots | residual rows | residual kinds |
| --- | --- | --- | --- |
| reachable control | 2–8 | 1, 3, 4, 5, 7 | `binop`, `comparison`, `getitem`, `call`, `contract` |
| after an A0 bottom | 2, 4, 5 | 1, 3, 4, 5 | `call`, `contract` **only** |

The statements in dead code emit **nothing**: no `binop` row for `v + 1`, no
`comparison` row for the assertion, no `getitem` row for the certain `KeyError`.
They are *absent*, not flagged. A `reached` field does exist on residual rows, but
nothing carries it for these statements because no row is produced.

So absence is the only signal, and absence is ambiguous — a line is also missing
from `lines` when it never snapshots at all (the `line == 0` path, `def` headers,
blank lines). A lowering cannot distinguish "unreachable, emit `assert false`" from
"nothing to instrument here", which means **the safety net is currently not
implementable from Pylate's output**.

**Stated as a requirement.** This is a soundness requirement on the Pylate/Laurel
interface, and it has two acceptable discharges. Either is sufficient; doing both
is better.

> **R1.** Pylate logs a result for **absolutely every location**, unreachable ones
> included — so a location with no abstract-domain information cannot occur.
>
> **R2.** The Laurel encoder inserts `assert false` **by default** at any location
> that carries no abstract-domain information — so an omission fails closed instead
> of vanishing.

R2 is the stronger of the two, because it survives a *bug* in Pylate rather than
only a designed gap: under R1 alone, any future path that forgets to log is silently
unchecked again, whereas under R2 forgetting to log is the safe direction.

One wrinkle worth settling before implementing R2 on its own: "location" has to be
defined, or it will fire on lines that legitimately carry no information — `def`
headers, blank lines, the `line == 0` operator and `expr_context` nodes that
`snap` deliberately skips. That is the argument for pairing them: **R1 makes Pylate
enumerate the location set explicitly, and R2 makes anything in that set without
information fail closed.** With the two together, absence is no longer ambiguous
and no longer silent.

Until one of them exists, the containment argument above is an intention rather
than a property, and A0 is a soundness hole in the pipeline rather than a
precision defect in one component.

Note the two halves are independent and should land in that order: A0b makes any
bottom safe, A0 stops this particular bottom from happening.

### A1. A function cannot read a module global — **highest priority**

```python
x: int = 7
def f() -> int:
    return x        # Pylate: NameError abort, "no binding reaches this point"
                    # CPython: 7
```

The module environment is not in scope while a function body is inlined. Works at
module level; works when the value is passed as a parameter; the annotation makes
no difference; not type-specific (a module `list` behaves the same).

This is CPython's `GLOBAL_IMPLICIT` classification in `symtable.c:analyze_name`: a
name read but never bound in the local scope resolves to the module namespace.
`global`/`nonlocal` *statements* are rejected, but a plain global *read* is
ordinary Python and no rule claims otherwise.

**Impact, measured:** 4 of the 17 admitted `program_supported.py` files in the
lowering corpus abort for this reason alone (009, 031, 032, 034).

**The corpus blind spot, stated precisely.** Using CPython's own `symtable` as the
oracle over all 250 corpus programs, Global-Implicit reads inside a function split
two ways:

| the name denotes | programs |
| --- | --- |
| a module-level **declaration** — class, `def`, import | **62** — these work; Pylate resolves them through the class table and `c.funcs`, not the environment |
| a module-level **data binding** — a variable | **0** ← the gap |

So the corpus reads module-level globals constantly; it just never reads a module
*variable* from inside a function. That is also the mechanical reason A1 exists:
declarations have their own resolution paths and only the env-backed data path
lacks the fallback. An earlier draft of this document said "zero of 250 corpus
programs exercise it", which was true of A1 but wrong as a sentence about globals.

**Exactness requires:** an unassigned name falls back to the module binding. The
classification logic is already right — it correctly reports `UnboundLocalError`
when the name *is* assigned later in the function, and `NameError` when it is
genuinely absent. Preserve that: `UnboundLocalError` is a subclass of `NameError`,
so the choice changes handler routing.

*Regression to add:* reading a module `int`, a module `list`, and a module class
instance from inside a function; plus the negative case, `x = 1` / `def f(): y = x;
x = 2`, which must stay `UnboundLocalError`.

### A2. `list ==` and `tuple ==` abort with TypeError

```python
a: list[int] = [1, 2]
r: bool = a == [1, 2]     # Pylate: TypeError abort.  CPython: True
```

Isolated by type: `list == list` and `tuple == tuple` abort; `int`, `str` and
`dict` equality are fine. Rows are missing from the equality dispatch table.

**Impact:** fires on any `assert xs == [...]`, which is why it hit two lowering
supported programs (004, 038). This is `cpython-modeling/008_comparison`, whose
soundness note is that `do_richcompare` collapses to native predicates when the
types are known — and here they are known.

### A3. Augmented assignment is rejected outright — **highest leverage for testability**

`x += 1` is refused with `unsupported-node`: *"augmented assignment requires
Python's in-place operator protocol."*

**Impact is mostly indirect and large.** Every published probe that counts side
effects writes `counter[0] += 1`, so this single rejection makes **four** lowering
mechanisms untestable (#11 chained-comparison single-eval, #14 default-argument
timing, #15 for-loop iter-once, #31 dict key-before-value) and rejects **two**
`cpython-modeling` supported programs (002 in-place operators, 004 attribute
write). `cpython-modeling/002` states the intended model directly: in-place
operators collapse to *mutation* for a mutable type and *rebind* for an immutable
one once the type is known — which is exactly the information Pylate has.

Two independent tasks, do not conflate them:
1. Rewrite the blocked probes with `counter[0] = counter[0] + 1` so the four
   mechanisms become testable **now**, without any subset change.
2. Separately, model `+=` per `binary_iop1`: mutate-in-place for list/dict/set,
   rebind for int/str/tuple.

### A4. For-loop variables are not proved bound after the loop

`for i in [1,2,3]: ...` then reading `i` gives `maybe-unbound` and an
`UnboundLocalError` abort; CPython gives `3`. For-loop variables **leak** — the
exact counterpart to the comprehension isolation that *is* verified (#26), and the
asymmetry is the point of that pair. Pylate will not prove a literal list
non-empty, so it will not prove `i` bound.

### A5. A dict store does not discharge the following read

`d[1] = 99` then `d[1]` files `key-membership` and a `KeyError` abort even though
the key was just written. The value is right (`lit=99`); the obligation is
avoidable.

Note the contrast with the *legitimate* case: `lst[i]` and `d[key]` with a
symbolic index or key genuinely may raise, and the abort there is the policy
correctly demanding a proof (`cpython-modeling/006` supported).

### A10. Default arguments are unmodelled, so any call using one aborts

```python
def f(n: int = 5) -> int:
    return n

f(7)   # clean:  explicit = int lit=7        CPython 7
f()    # ABORT TypeError:  defaulted = any   CPython 5
```

The default value is never bound, so the parameter arrives as `any`, fails its own
`param-annotation` check, and aborts under `contract=abort`. Every obligation in
the chain is individually reasonable; the missing step is evaluating the default.

Not limited to mutable defaults — a plain `int = 5` is enough. Defaults are
pervasive in ordinary Python, so this is the widest over-rejection in this
document after A1.

**Two constraints to honour when adding it**, both from
`ast-bytecode-lowering/#14` and `pyhard-frontend-divergence.md` Rule C:

1. Defaults are evaluated **once, at definition time**, in the enclosing scope,
   left to right — not per call.
2. The resulting object is **shared across calls**. `def f(x: list[int] = [])`
   accumulates: `f(1); f(2)` leaves the same list holding both. Binding a fresh
   value per call would be unsound with respect to CPython, and it is the classic
   Python gotcha, so it will appear in real code.

This cannot currently be got wrong, because defaults are not modelled at all —
measured, `x` and `y` both read `any` where CPython gives `[7, 9]` for each.

### A11. `"ab" * 3` aborts with OverflowError

```python
c = "ab" * 3     # Pylate: abort OverflowError, "binop Mult: (str,int) -> abort OverflowError"
                 # CPython: 'ababab'
```

String repetition is guarded as a potential `OverflowError` and aborts under
`arith=abort`. The guard is defensible in principle — a huge repeat count does
raise — but it fires on a literal count, so it should be discharged when the
count is a known small literal. `int + float`, `True + 1`, `list + list` and
`tuple + tuple` all produce correct tags, so this is a single missing
discharge, not a dispatch gap.

### A13. `isinstance` does not narrow an attribute read

```python
class Box:
    def __init__(self) -> None:
        self.v: int | str = 1
def go(b: Box) -> int:
    if isinstance(b.v, int):
        return b.v + 1      # Pylate: dispatch-any, "operator + has an unknown
                            #   operand"; result OPEN=int.  CPython: 2
```

The narrowing applies to plain names but not to `obj.field`, so the field stays
`any` inside the guarded branch and the operator defers. Note the contrast with
§E: narrowing *invalidation* after an effect works correctly — this is the
opposite failure, too little narrowing rather than too much.

Also worth checking while here: the union-annotated field appears as `any` in the
dispatch row (`(any,int)->deferred`) rather than as `int|str`, which may be the
actual root cause.

### A12. `raise ... from ...` is rejected

`unsupported-node`. CPython's `__cause__`/`__context__`/`__suppress_context__`
behaviour is lowering-determined (`ceval.c:do_raise`) and is
`ast-bytecode-lowering/#35`. Exception chaining is observable from admitted code,
so exactness eventually requires modelling it.

---

## B. Precision gaps

| # | gap | measured |
| --- | --- | --- |
| B1 | for-else after `break` | a loop that breaks with `found = 2` and has `else: found = 99` yields `lit=1,2,3,99` where CPython gives `2`. Sound, but the value set **contains the naive answer**, which is what mechanism #16 exists to exclude. The `break` edge should bypass the else-completion |
| B2 | loop trip counting | counting `finally` runs across a loop that breaks gives `lit=0 OPEN=int` where CPython gives `2` |
| B3 | return-annotation widening | a value returned through a declared `-> int` loses its literal: `f()` returning `5` reads as `int OPEN=int`. Verified pre-existing and independent of `super()` |
| B4 | comprehension element literals | `[f(3) for …]` has no `3` in `elem` |
| B5 | per-line state joins | `atL : HashMap Nat AState` is keyed on **line**, so every node on one line shares a joined `AState`. Re-keying to node id would give per-subexpression states — an output-side change, no effect on verdicts |

---

## C. Declared approximations

| # | approximation | note |
| --- | --- | --- |
| C1 | generators analysed eagerly | every generator files `special-method: generator <name> analyzed eagerly: suspension interleaving asserted away`. Values come back open, so nothing is under-approximated. Decide: keep with the obligation, or reject as recursion is — the difference from recursion is that here the obligation *is* filed |
| C2 | PEP 479 not modelled | CPython converts a `StopIteration` escaping a generator body into `RuntimeError`. Pylate surfaces a `RuntimeError` at the call but via the generic error-guard, so the outcome set is right and the reason is not established. `next(iter([]))` aborts under `exhaustion=abort` |
| C3 | contract-only stubs | `def f(...) -> T: ...` answers from the annotation and leaves the heap untouched; measured, `zs = [1]; stub_mutates(zs)` still reads `elem = int` with literal `1`. Default must be havoc, not no-effect |
| C4 | `attr-missing` store residue | admission checks the union over all classes, so a name that is a field of some *other* class is admitted and files `attr-missing`. For a slots-complete or frozen receiver the store now aborts; otherwise both edges are kept. See `SUBSET_DEFINITION.md` §1 |

---

## C5. Unannotated parameters and returns are accepted

Measured: `def f(x) -> int` and `def g(y: int)` (no return annotation) are both
admitted with **no obligation**, and `f(1) + g(2)` analyses cleanly.

`ty`'s finding 001/002 say a verifier should reject these, because an unannotated
parameter becomes implicit `Unknown` and then absorbs every operation — the
dominant family in that corpus (001–009). **Pylate is structurally immune while
every call is inlined**: the parameter's value comes from the caller's actual
argument, so there is no annotation to launder through and nothing is trusted.
That is worth recording as a *reason*, not a coincidence.

It stops being true the moment a body is not inlined — a stub, an import, or
contract-only mode. Then the annotation is all there is, and an unannotated
parameter is exactly ty's door 1. `stub-without-return-annotation` covers the
return side for stubs; the parameter side is uncovered. Same family as C3.

*To do when contracts land:* require full annotations on any function whose body
will not be analysed, parameters included.

## C6. `TypeGuard` is covered only incidentally

`from typing import TypeGuard` is rejected by the blanket `import` rule, so PEP 647
predicates cannot appear. `ty` finding 014 is the sharpest case in that corpus —
ty adopts a user-declared `TypeGuard[int]` as fact **without ever reading the
predicate body**, and it is a shared mypy ∩ ty hole because PEP 647 delegates
correctness to the author by design.

Since `SUBSET_DEFINITION.md` §3 calls the import rule *"the single most valuable
rule to lift"*, this needs a rule of its own before that happens. A `TypeGuard`
or `TypeIs` return annotation must be refused explicitly, not by side effect.

## A9. Annotation violations are checked unevenly

Pylate **does** check annotations against inferred values. An earlier draft of this
document said "Pylate never evaluates annotations", which conflated *not evaluating
annotation expressions as runtime code* (the PEP 649 point in C7) with *not
checking them*. It checks them — just not uniformly. Measured:

| case | result |
| --- | --- |
| `def f(x: int)` called `f("s")` | **`param-annotation-violated`** — *"no value the caller can pass satisfies the annotation on x"* — plus a `TypeError` abort under `contract=abort`, so it is uncatchable |
| `def f() -> int: return "s"` — **must** violate | `return-annotation` obligation, **no abort** |
| `def f(b: bool) -> int: return "s" if b else 1` — **may** violate | **the identical obligation**, no strength distinction |
| `self.n: int = "s"` — field annotation | **nothing at all** |
| annotation satisfied | silent, no false positive |

Two gaps:

1. **Returns do not distinguish must-violate from may-violate, and never
   escalate.** A function whose returned tag set is *disjoint* from its annotation
   is a definite type error and should abort as the parameter case does; today it
   files the same soft obligation as a one-path violation.
2. **Field annotations are unchecked.** `self.n: int = "s"` produces no obligation,
   which is a silent hole rather than a soft one.

**Inlining makes this cheap rather than hard.** Because the actual value is in hand
at the store and at the return, the may/must split is just whether the value's tag
set is disjoint from the annotation (must) or merely overlaps its complement (may)
— the same computation `param-annotation-violated` already performs. The `contract`
policy category is deliberately outside `policyCategories` so a contract violation
always aborts uncatchably; the return and field paths simply do not use it.

*To do:* compute the disjointness split at the return and at every annotated store,
escalate must-violations through `contract`, keep may-violations as obligations.
`SUBSET_DEFINITION.md`'s posture that annotations are *checked* rather than assumed
holds for parameters today and should hold for all three.

## C7. "Exactly" needs a version, and ours are inconsistent

`cross-version-semantics/ANALYSIS.md` states the constraint bluntly — **a
version-agnostic Python semantics is not possible for a sound verifier** — but
`cpython-modeling/formal-model/version_behavior.md` bounds how much it costs:
**26 of 30 mechanisms are identical across 3.11–3.14**, including *all* scoping,
*all* evaluation order and *all* control flow. Its summary is "opcodes change;
semantics don't". So this is a documentation-honesty item, not a correctness risk.
Four models would have to branch on version:

| transition | what changed | PEP |
| --- | --- | --- |
| 3.11 → 3.12 | comprehension frame identity; `locals()` inside a comprehension | 709 |
| 3.12 → 3.13 | `locals()` identity vs fresh snapshot; `f_locals` write-through proxy | 667 |
| 3.13 → 3.14 | annotation evaluation eager → lazy; `NameError` moves from def-time to access-time | 649 |

**Three of the four are moot for Pylate** and for a good reason: `locals()` and
`vars` are banned builtins, `sys._getframe` is unimportable, and frame
introspection is outside the subset — so the 3.11→3.13 differences have no witness
in admitted code. That doc says exactly this: *"If the verifier restricts to pure
value-and-effect semantics… then only the 3.13→3.14 annotation change is
relevant."*

**The fourth is not moot, and there is a pin mismatch to resolve.** PEP 649 makes
annotations lazy thunks in 3.14: an effectful annotation fires at
`__annotations__`-access time rather than def time, and a `NameError` in an
annotation moves from definition to access. Meanwhile:

- the corpora pin **CPython 3.14.3** (`323c59a5e3`),
- Pylate's `inventory` gate reports **CPython 3.13.5**,
- and the differential probes in this document ran against the local 3.13.

So the oracle Pylate is checked against sits on the *earlier* side of the one
version boundary that matters to it. Pylate does not *evaluate* annotation
expressions as runtime code — it reads them as static types and checks values
against them (A9) — so no current claim is wrong. But the mismatch means the
gates cannot see a PEP 649 divergence even in principle.

(The two docs disagree on the PEP number for lazy annotations — 649 in one, 749
in the other. Both are real: 649 defers evaluation, 749 amends the
implementation.)

*To do:* pick a version and state it. If 3.14, the `inventory` and `conformance`
oracles need to move with it; if 3.13, say so and record that annotation-timing
exactness is scoped to ≤3.13. Either way `SUBSET_DEFINITION.md` should name the
pinned interpreter, since "matches CPython" is otherwise underdetermined.

## D. Diagnostic defects

**D1. A proven assertion still leaves an `AssertionError` edge.** In
`cpython-modeling/010` supported, Pylate reports both:

```
L8  assert: asserted condition holds
L6  guaranteed-error: contract make_point entry: code -> AssertionError
```

Those contradict. If the condition is proven, the `AssertionError` outcome should
be bottom, not a guaranteed error on the enclosing function.

**D2. `unreported-outcome` fires on every asserting program** —
*"AssertionError is an outcome of this statement but no site reports it"* appears
in essentially every admitted program containing an `assert`. Uniform enough to be
noise; likely the same root cause as D1.

**D3. `dispatch-any` is an obligation, not a rejection.** The bytecode-admission
design argues an external contract that cannot bound the tag set should be an
admission rejection rather than a precision loss, since an unbounded tag set means
a dispatch site has no arms to generate.

---

## E. What is verified correct — do not regress it

Worth stating so a fix does not trade one of these away.

| area | verified |
| --- | --- |
| scoping | local-shadows-global → `UnboundLocalError` (not the global's value); parameter shadowing; a method referencing its own class name; assigned-in-`try` read-after → `UnboundLocalError`; `del` → NULL slot with the right subclass chosen over a later `NameError` clause |
| comprehensions | iteration variable does not leak, at function and module scope; the outermost iterable resolves in the enclosing scope, so `[xs for xs in xs]` works |
| control flow | `return` in `finally` replaces both a pending return and a pending `break`; ternary does not evaluate the untaken branch; bare `raise` outside a handler → `RuntimeError`; `and`/`or` yield the **operand**, not a bool |
| MRO and dispatch | inherited fields resolve through the MRO including diamonds; `super()` resolves per receiver tag, so a cooperative diamond gets `Right.m` where the enclosing class alone would give `Base.m`; virtual calls emit one arm per candidate with a `case-split` |
| interprocedural | contexts are full call chains, so `foo → bar → baz` and `foo → qux → baz` keep separate states, and so do two outer paths through a shared inner call site |
| the unsound boundary cases | all six `cpython-modeling` boundary programs are rejected, and by the right rules: monkey-patched `__add__` and a rebound method → `shape-store`; `__getattr__` and `__new__` → `hook-override`; class-level mutable counter → `class-body-stmt`; `import random` → `import` |

### E1. Other engines' dominant root causes that do **not** apply

Measured, one probe each. This is the bulk of the ~575 findings, and it is why the
other fix lists should not be imported wholesale.

| other engine's root cause | Pylate |
| --- | --- |
| **mypy Problem 1** — narrowing not invalidated after an effect (their corpus calls this its dominant gap) | **correct.** Narrow `b.v`, call `b.clobber()` setting it to `str`, then `b.v + 1` → `guaranteed-error: (str,int) -> TypeError`, matching CPython. Corpus-wide: all 38 crashing `mypy-unsoundness` programs are refused |
| **mypy Problem 3** — narrowing survives a subscript reassignment | **correct.** `d["k"] = "s"` after narrowing → `(str,int) -> TypeError` |
| **mypy Problem 4** — instance fields not definitely assigned | **correct.** `init-missing` / `init-conditional` / `uninit-field`, verified for the inherited case too |
| **Laurel finding 385** — operator catch-all returns `Hole`, so type-error programs verify. *"The single most critical issue"* | **correct.** `str + int` → `guaranteed-error: (str,int) -> abort TypeError`. Pylate's missing pair yields TypeError, not an unconstrained value |
| **Laurel RC5 / #273** — SMT div/mod ≠ Python `//` `%`; `-7//2` → -3 not -4 | **not applicable.** Pylate widens to `int OPEN=int` and claims no concrete value, so it cannot get the sign convention wrong. *Forward-looking:* if constant folding is ever added for `//` and `%`, it must floor toward −∞ and take the divisor's sign |
| **Laurel** — float as exact Real, so `0.1+0.2==0.3` over-proves | **not applicable.** `bool OPEN=bool`, no claim |
| **Laurel #41/369** — dict equality order-dependent | **not applicable.** `bool OPEN=bool`, no claim |
| **Laurel #398** — `isinstance` uses exact classname, inheritance fails | **correct.** `isinstance(Derived(), Base)` → `lit=1`, via the MRO |
| **Laurel RC3** — value semantics, no aliasing | **not applicable.** Pylate has a points-to domain with recency |
| **Laurel RC4** — exceptions as values, no propagation; handlers unreachable | **not applicable.** Five completions with `raised` first-class and per-raise-point handler entry |
| **cbmc-py §6** — subscript *store* emits no IndexError | **correct.** `lst[5] = 9` → `bounds: sequence store index within length` + IndexError |
| **cbmc-py §7** (their KNOWNBUG) — exceptions nested in `if`/`while`/`for` bodies missed | **correct.** `x // y` inside an `if` → ZeroDivisionError detected |
| **cbmc-py §8** — `Optional[T]` collapses to `T`, None erased | **correct.** `x: int \| None` → `bool/int/none`, `(none,int) -> TypeError` |
| **cbmc-py §12b** — no `UnboundLocalError` (assignment-makes-local) | **correct**, see the scoping row above |
| **cbmc-py §12c** — comprehension over a non-literal iterable silently drops the assignment | **correct.** `ys = [v for v in xs]` over a parameter keeps `ys = list` |
| **cbmc-py §11b** — inherited `@property` returns nondet | **correct.** Resolves through the MRO |
| **cbmc-py §3 / addendum A** — `id()` unmodelled, `is` ignores aliasing, small-int interning | **not applicable by restriction.** `id` is banned and `is` is confined to `True`/`False`/`None`, which is exactly the sidestep those docs recommend |
| **cbmc-py §2** — 64-bit int default | **not applicable.** No fixed width is claimed |
| **cbmc-py §5** — `finally` not rerouted for return/break | **correct**, see the control-flow row above |

---

## E2. Side-effecting `__eq__` and `__bool__` are modelled, not rejected

`cpython-modeling`'s triage recommends *AST checks* rejecting `__eq__` with side
effects (008) and `__bool__` with side effects (009). Pylate instead **models**
them, which is strictly stronger. Measured:

| | Pylate | CPython |
| --- | --- | --- |
| `__eq__` return value | `same = bool lit=True` — dispatched, result consumed | True |
| `__eq__` heap effect (`self.hits = 7`) | `lit=7` — the effect propagates to the caller | 7 |
| `__eq__` read-modify-write (`self.calls + 1`) | `int` with `open=["int"]` — sound, literal lost | 1 |
| `__eq__` result used to narrow a branch | **both branches taken** (`lit=111,222`) even for a constant `False` | 222 |
| `__bool__` with a side effect | `special-method: truthiness via one-step __bool__/__len__` obligation, effect applied | — |

The only gap is the last-but-one row: a user `__eq__` returning a *constant* is not
used to prune the branch. Sound, and a precision item rather than a correctness one.

**A note on reading these logs.** `after` above is `{"tags":["int"], "literals":[],
"open":["int"]}`. An empty `literals` list with a **non-empty `open`** means "some
int, literals unknown" — a sound widening. An empty `literals` with an empty `open`
would be a closed claim. Any triage of this domain has to read both fields; reading
`literals` alone makes a sound widening look like a precise wrong answer.

## E3. Negative indexing is correct

`cbmc-equivalence` verified with CBMC that list subscript hits iff
`-len <= i < len`. Measured: `lst[-1]` on a 3-element list is accepted with no
abort; `lst[-4]` gets `bounds` plus an `IndexError` abort. The only imprecision is
that `lst[-1]` yields the whole element set rather than the last element.

The same corpus independently confirms A3: `a[i] += x` is recorded as *"Naive WRONG
(double eval), correct VERIFIED"* — a CBMC proof that the naive desugaring is
unsound, which is the constraint A3.2 must honour.

## E4. `awstasks-mcp-restrictions` measures the 02 fragment, not Pylate

That corpus compares a real validator's restrictions against the PyHard fragment
and identifies a "stricter group" — constructs the validator admits that PyHard
rejects — as the only thing limiting workload coverage. It lists comprehensions,
multiple inheritance, generators, `super()`, and `__eq__`/`__hash__` overrides.

**Pylate admits all five.** The analysis is against
`synthesis/02-fragment-and-restrictions.md`, and Pylate has moved past it. Its
conclusion that comprehensions and aliased mutation are the high-frequency blockers
does not describe Pylate, which admits comprehensions and has a points-to domain
with recency. Worth telling that team before the estimate is used for planning.

## F. Still untested

1. **Six lowering mechanisms** whose probes are blocked: #11, #14, #15, #31 (all by
   `+=`), #32 (needs a side-effect-order probe), #39 (blocked by `is`; aliasing was
   inconclusive from tags alone).
2. **Four `cpython-modeling` boundary programs** not fetched: 002, 004, 006, 009.
3. **Four lowering `program_supported.py`** not fetched: 037, 043, 044, 045.
4. **MRO differential testing.** `Domains/MroOrder.lean` has 39 theorems and no
   `sorry`, but the proved order has not been differentially tested against
   `type(x).__mro__` on a generated class-hierarchy corpus. The proofs establish
   internal consistency, not agreement with CPython.
5. **The `formal-model/` directory** in `cpython-modeling` — small-step rules,
   `scoping_rules.py`, `scoping_validator.py`, `flag_algebra.py`. These are
   executable models of the very semantics in question and were not looked at;
   they are the natural oracle for a differential harness.

---

## Suggested order

1. **A0b / R1+R2** emit a result for every location, and make the encoder default
   to `assert false` where information is absent. This is the safety net every
   other item in this document leans on, and it does not exist yet.
2. **A0** the bottom-producing return-annotation check. With A0b in place this is
   a precision and usability defect; without it, a wrong program can verify.
3. **A1** global reads — four over-rejections, the deepest of them, and Rule 5 of
   the scoping spec. Target `scoping_inference_rules.md` directly.
4. **A3.1** rewrite the `+=`-blocked probes — unblocks four mechanisms with no
   product change; do this before A3.2 so the model change has tests.
5. **A2** `list`/`tuple` equality rows, and **A6** the `str * int` discharge —
   both small, both fire on ordinary code.
6. **D1/D2** the assertion edge — likely one root cause, and it pollutes every log.
7. **A13** narrowing on attribute reads — check first whether the union-annotated
   field is arriving as `any`, which may be the real cause.
8. **A3.2** model `+=` per `binary_iop1`: mutate for list/dict/set, rebind for
   int/str/tuple.
9. **A10** model default arguments — bound once at definition, shared across
   calls. Second-widest over-rejection after A1.
10. **A9** escalate must-violated return annotations and check field annotations —
   the parameter path already proves the machinery works.
11. **C7** pin the interpreter version explicitly — cheap, and until it is done
   "matches CPython" is underdetermined.
12. **B1** for-else, then the remaining precision rows.

Items in **E** are regression risks throughout, and **E1** especially: several of
those correct behaviours are exactly what a careless fix to A1, A2 or A7 would
break. In particular, do not weaken narrowing invalidation (E1 rows 1–2) while
adding narrowing to attribute reads (A7) — Pylate currently gets the hard half of
that right and the easy half wrong, and the temptation is to trade them.

## What a differential harness should look like

The single highest-value piece of infrastructure not yet built. Three of the
corpora ship runnable witnesses, and `cpython-modeling/formal-model/` ships
executable models — `scoping_rules.py`, `scoping_validator.py`, `small_step.py`,
`flag_algebra.py`. Those are an oracle for exactly the semantics in question and
were not used here; every measurement in this document is a hand-written probe.

A harness that ran the published witnesses against Pylate and diffed the verdict
against CPython would turn this document into a gate. The corpus blind spot in A1
— **zero of 250 corpus programs read a module global** — is the argument for it:
nine green gates coexisted with an entire class of ordinary Python being
unanalysable.
