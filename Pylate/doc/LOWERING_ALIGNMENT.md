# Alignment with Python semantics defined by lowering

Some Python behaviour is not in the language reference as such — it is a
consequence of how CPython's compiler lowers the AST to bytecode. `symtable.c`
decides what a name means; `compile.c` decides what order things happen in and
where `finally` blocks get inlined. A model built from the grammar alone gets
those wrong.

`PyHardMiningAgents/findings/ast-bytecode-lowering` enumerates **45** such
mechanisms, each with a `rule.md`, a `program_supported.py`, and a
`program_boundary.py` written so that *a naive model gets it wrong*. This document
records where Pylate stands against all 45 and what is left to do.

Method: the boundary programs were run through the subset checker and, where
admitted, through the analysis, with the result compared against a live CPython
run. Every claim below is a measurement, not a reading of the code. Where a probe
had to be rewritten (because the published one used a construct Pylate rejects for
an unrelated reason) that is stated.

Note the findings directory is internally inconsistent: `FINDINGS.md` and the
tree both have 45 mechanisms, while `SUCCESS_CRITERIA.md` still says 30.

## Headline

**No unsoundness was found** — no mechanism produced a Pylate claim that a live
CPython run contradicts. But one **functional gap** was found by probing beyond the
published boundary programs: a function cannot read a module-level name (§6). It
aborts rather than answering wrongly, so it is sound, and no corpus program
exercises it.

The rest of the work is of three kinds: six mechanisms are **untested** because
their probes are blocked, two have a **precision gap**, and three rest on a
**declared approximation** filed as an obligation rather than modelled.

| outcome | count |
| --- | --- |
| verified correct against CPython | 10 |
| covered by rejection — the construct is outside the subset | 24 |
| accepted, sound, **precision gap** | 2 |
| accepted, sound, **declared approximation** | 3 |
| **untested** — probe blocked by an unrelated rejection | 6 |

That tally is from the boundary programs. Running the **supported** programs — which
all pass under CPython — surfaces a different and larger class of problem: **7 of
the 17 admitted supported programs abort on code CPython runs cleanly**, from three
causes (§0). Global reads from a function body account for four of them.

## 0. Running the whole corpus, not just the boundary programs

The first pass ran only the `program_boundary.py` files, which test for *wrong
answers*. Running the `program_supported.py` files tests something different and
more useful: they all pass under CPython, so any abort Pylate raises on one is an
**over-rejection** — a program the analyser refuses that it ought to handle.

38 of the 45 supported programs were run (four were not fetched; three are
version-gated behind `exec`).

| | count |
| --- | --- |
| rejected at admission — construct outside the subset | 21 |
| accepted and clean | 10 |
| **accepted but aborts on a program CPython runs cleanly** | **7** |

Seven over-rejections from **three** causes, and they are the highest-value
findings in this document because they are ordinary Python:

| cause | programs | detail |
| --- | --- | --- |
| **a function reads a module global** | 009, 031, 032, 034 | `NameError` abort, *"name read `log`: unbound"*. Four of the seven. Same defect as §6 |
| **`list ==` and `tuple ==`** | 004, 038 | `TypeError` abort on `result == [2, 4, 6]`. Isolated: `list == list` and `tuple == tuple` abort; `int`, `str` and `dict` equality are fine. The equality dispatch table is missing those two rows, and this fires on any `assert xs == [...]` |
| **`StopIteration` / PEP 479** | 024 | `next(iter([]))` aborts under `exhaustion=abort`; CPython converts it to `RuntimeError` inside a generator |

One case initially counted here is **not** an over-rejection: 022's
`guaranteed-error: contract compute_value entry: code -> RuntimeError` is accurate
— that function does always raise — and the analysis still reports the assertion
as holding.

Also, every accepted program files `unreported-outcome: AssertionError is an
outcome of this statement but no site reports it`. That is diagnostic noise on
`assert`, not a finding, but it is uniform enough to be worth silencing.

*To do, in priority order:* the global-read fallback (§6), then the `list`/`tuple`
equality rows, then a decision on PEP 479. The first two together account for six
of the seven.

## 1. Verified correct

Measured: Pylate's answer matches CPython's.

| # | mechanism | evidence |
| --- | --- | --- |
| 4 | comprehension outermost-iter asymmetry | `xs = [7,8]; [xs for xs in xs]` admitted with no unbound obligation — the iterable resolves in the enclosing scope |
| 6 | `__class__` cell synthesis for `super()` | not modelled but **replaced**: the owner is baked in at lowering as `@super:<Owner>`. This is why `super-form` requires the first parameter to be `self` — see `SUBSET_DEFINITION.md` §8 |
| 9 | assignment target order | `d[1] = 99` then `d[1]` → `lit=99`, CPython 99 |
| 12 | boolean short-circuit **value** | `cfg or {}` → `dict`, not `bool`; `1 or 2` → `lit=1`; `0 or 7` → `lit=7`. `and`/`or` yield the operand |
| 22 | return in `finally` replaces | → `lit=2`, CPython 2 |
| 26 | comprehension variable isolation | `i = 99; [i for i in [1,2,3]]; return i` → `lit=99`, no leak, at function *and* module scope |
| 34 | ternary condition-first | `boom() if c else safe()` with `c=False` → `lit=5`, CPython 5; the untaken branch is not taken |
| 36 | bare `raise` outside a handler | `RuntimeError(model)`, caught → `lit=1`, CPython 1 |
| 38 | `return` in `finally` replaces a pending `break` | → `lit=7`, CPython 7 |
| 42 | `del` leaves a NULL slot | `UnboundLocalError`, and the handler table picks the `UnboundLocalError` clause over a later `NameError` one — correct, since the former is a subclass |

## 2. Covered by rejection

The mechanism cannot fire because the construct is refused at admission. Sound by
absence; nothing to do unless the subset widens.

| # | mechanism | rule |
| --- | --- | --- |
| 1, 2, 3, 5, 7, 41, 43 | name classification, cell promotion, class-scope opacity, walrus escape, annotation scopes, global/nonlocal retroactive, star-import | `global-stmt`, `nonlocal-stmt`, `walrus`, `nested-function`, `class-body-stmt`, `import-star`, `unsupported-node` |
| 8, 33, 40 | call-argument order with splats, splats in displays, `UNPACK_EX` starred-gets-list | `starred-arg` |
| 10 | augmented-assignment single-eval | `unsupported-node` — *"augmented assignment requires Python's in-place operator protocol"* |
| 13 | decorator anti-parallel order | `function-decorator` |
| 17, 18, 37 | `__exit__` before `__enter__`, multi-item LIFO, break/continue through `with` | `with-stmt` |
| 19 | exception-type lazy eval | *"except clause must name a single exception class"* — a computed handler type is refused, so the ordering question cannot arise |
| 20 | except-as implicit deletion | `handler-name-collision`. Worth noting the rule exists **for this mechanism**: the handler target is unbound when the handler ends, so a program using `e` afterwards is refused rather than analysed |
| 23 | `except*` splitting | `unsupported-node` |
| 27, 28 | class body as a function, closure creation | `class-body-stmt`, `nested-function` |
| 29, 30, 44 | pattern matching, import lowering, async await points | `match-stmt`, `import`, `async-construct` |
| 35 | exception chaining | *"raise ... from ... is outside the subset"* |

## 3. Precision gaps — sound, blunter than the mechanism

**#16 for-else / while-else.** The `else` clause must not run after a `break`.
Measured: a loop that breaks with `found = 2` and has `else: found = 99` yields
`r = int lit=1,2,3,99` where CPython gives `2`. The value set is a superset, so
this is sound — but it **contains the naive answer**, which is exactly what the
mechanism exists to rule out. Pylate does not establish that `break` skips the
`else`.

*To do:* make the `break` edge bypass the else-completion so `99` is excluded.

**#21 finally on every exit path.** Measured: counting `finally` executions across
a loop that breaks on the third iteration gives `r = int lit=0 OPEN=int` where
CPython gives `2`. Sound, but the loop fixpoint does not count iterations, so the
probe cannot confirm the `finally` ran on the break path — only that it may have.
Distinct from #22/#38, which *are* verified because their answers do not depend on
a trip count.

*To do:* a probe whose result does not require counting — e.g. a flag set in
`finally` — to confirm the break path runs it at all.

**Also observed, not one of the 45:** `d[1] = 99` followed by `d[1]` still files
`key-membership` and a `KeyError` abort, despite the key having just been written.
The value is right; the obligation is avoidable.

## 4. Declared approximations

**#24, #25, #45 — generators.** Generators *are* admitted (`yield`, `yield from`),
and every one files:

```
special-method: generator <name> analyzed eagerly: suspension interleaving asserted away
```

That is the honest posture — the approximation is an obligation to discharge, not
a silent claim — and the returned values are open (`int OPEN=int`), so nothing is
under-approximated. Two specifics:

- **#24 (PEP 479)** — CPython converts a `StopIteration` escaping a generator body
  into `RuntimeError`. Pylate does surface a `RuntimeError` at the call, but by way
  of the generic error-guard rather than by modelling the conversion. The outcome
  set is right; the reason is not established.
- **#25, #45** — delegation via `yield from` and frame preservation across yields
  both return `int OPEN=int` where CPython gives `3`. Sound, uninformative.

*To do:* decide whether generators should keep the eager approximation with the
obligation, or be rejected as recursion is. `RECURSION_CONTRACTS.md` has the
argument for the latter; the difference here is that the obligation *is* filed, so
this is not the silent case that rejection was introduced for.

## 5. Untested — the probe is blocked

These six are the real gap in this audit. Each published boundary program is
rejected for a reason **unrelated to its mechanism**, so the mechanism is neither
confirmed nor refuted. Five are blocked by one rule.

| # | mechanism | probe blocked by | status of the mechanism itself |
| --- | --- | --- | --- |
| 11 | chained-comparison single-eval | `counter[0] += 1` → `unsupported-node` | chained comparison **is** admitted: `0 < mid() < 10` → `bool`. Single-evaluation of the middle operand is a side-effect property and remains unchecked |
| 14 | default-argument def-time timing | `call_count[0] += 1` → `unsupported-node` | unchecked |
| 15 | for-loop `iter()`-once | `self.iter_calls += 1` → `unsupported-node` | unchecked, and this is the mechanism a past soundness defect touched (`for` over a user iterable running zero iterations) |
| 31 | dict key-before-value | `state['count'] += 1` → `unsupported-node` | dict literals with computed key and value **are** admitted; the order is unchecked |
| 32 | f-string segment order | admitted, but the published probe's assertion is on a side-effect trace | f-strings are admitted; segment order unchecked |
| 39 | chained assign shares one object | `assert a is b` → `identity-comparison` | `a = b = []` is admitted; whether a mutation through `a` is visible through `b` was inconclusive from tags alone |

**The single highest-value item in this document:** four of these six are blocked
by the *same* rejection — augmented assignment. Every published probe counts side
effects with `counter[0] += 1`. Rewriting them to accumulate with
`counter[0] = counter[0] + 1` would make four mechanisms testable in one change,
with no subset change at all.

*To do, in order:*

1. Rewrite the probes for **11, 14, 15, 31** without `+=`, and for **39** without
   `is`. Then re-run and classify.
2. Write a side-effect-order probe for **32** that does not need `+=`.
3. Add the surviving programs to the corpus so regressions are caught. The
   boundary programs are unusually good corpus material precisely because they are
   constructed to fail a naive model.

## 6. Scoping — one real gap, found by probing further

An earlier draft of this document claimed the scoping cluster had no gaps. That was
wrong, and the error was methodological: the 45 boundary programs only probe the
mechanisms *they* were written for, and mechanism #1 (name classification) is nine
rules, of which the published probe exercises a few. Probing the rest found a
defect.

### The gap: module globals are invisible inside function bodies

A function that reads a module-level name is refused. Measured:

| program | Pylate | CPython |
| --- | --- | --- |
| `x = 7` / `def f() -> int: return x` | `NameError` abort, *"definitely-unbound: read of x: no binding reaches this point"* | `7` |
| same with `x: int = 7` | `NameError` abort — the annotation makes no difference | `7` |
| `cfg: list[int] = [1,2]` / `def f() -> int: return len(cfg)` | `NameError` abort | `2` |
| `x: int = 7` / `def f(v: int) -> int: return v` called `f(x)` | correct, `lit=7` | `7` |
| `x: int = 7; y: int = x` at module level | correct, `y = lit 7` | `7` |

So the binding exists and module-scope reads work; what is missing is that the
module environment is not in scope while a function body is inlined. This is
CPython's `GLOBAL_IMPLICIT` classification — a name that is read but never bound in
the local scope resolves to the module namespace. `global` and `nonlocal`
*statements* are rejected, but a plain global *read* is ordinary Python and nothing
in `SUBSET_DEFINITION.md` §3 claims it is outside the subset.

The direction is sound: it is an abort, a refusal to analyse, not a wrong value. But
it makes any function that reads a module-level constant unanalysable.

**No corpus program catches this.** Scanned all 250: functions reading a
module-level binding they do not also assign locally — **zero**. That is why nine
green gates coexist with the gap.

*To do, and this is the largest item in the document:*

1. Thread the module environment into function inlining, so an unassigned name
   falls back to the module binding. The classification logic is already correct —
   see below — so this is a lookup fallback, not new analysis.
2. Add corpus programs for it. Reading a module `int`, a module `list`, and a
   module class instance from inside a function; plus the negative case that must
   keep working, `g1` below.

### What *is* correct, and worth not breaking

The local-versus-global classification itself is right, including the exception
class it picks — which is the subtle part:

| program | Pylate | CPython |
| --- | --- | --- |
| `x = 1` / `def f(): y = x; x = 2` | **`UnboundLocalError`** | `UnboundLocalError` |
| `x = 7` / `def f(): return x` | `NameError` (wrong outcome, but the right *class* for its model) | `7` |
| parameter shadowing a module global | correct, `lit=42` | `42` |
| a method referring to its own class name | correct, `lit=1` | `1` |
| assigned in `try`, read after, exception path taken | `UnboundLocalError` | `UnboundLocalError` |

The first row is the classic trap: because `x` is assigned later in the function,
the earlier read is a *local* read, not a global one, so it is `UnboundLocalError`
and **not** the module's `1`. Pylate gets that right, and picks
`UnboundLocalError` there while picking `NameError` for the not-found case. That
distinction matters for handler routing, since `UnboundLocalError` is a subclass of
`NameError`. Any fix to the lookup fallback must preserve it.

### A second, smaller gap: for-loop variables

`for i in [1,2,3]: ...` then reading `i` after the loop gives `maybe-unbound` and an
`UnboundLocalError` abort, where CPython gives `3`. For-loop variables **leak** —
that is the counterpart to the comprehension isolation verified in #26, and the
asymmetry is the whole point of that pair. Pylate cannot prove the iterable
non-empty, so it will not prove `i` bound. Sound, and over-restrictive on a literal
list.

### Standing

Of the 11 scoping mechanisms: three verified (4, 26, 42), seven hold by rejection
(1 *partially* — see above — plus 2, 3, 5, 7, 41, 43), one by replacement (6). The
`analyze_name` chain does collapse for the rejected constructs; it does not
collapse for `GLOBAL_IMPLICIT`, which is the case above.

## 7. What is not covered by this audit

- The `program_supported.py` files were not run. Only the boundary programs were,
  on the grounds that a naive model fails those and passes the supported ones.
- Mechanisms rejected by construct were probed with minimal hand-written programs
  rather than the published ones, since the verdict is a rejection either way.
- `#39` aliasing was inconclusive rather than verified.
- Nothing here was run under `brazil-build`. All measurements come from a
  standalone build of `Pylate/` (it imports nothing from Strata, so it can be built
  outside the Brazil workspace); see `staging-builds-only-under-brazil` in the
  session memory for the mechanics.
