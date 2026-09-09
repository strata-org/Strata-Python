# Interpret expectations — V2 front end

**This directory holds the expectations for the V2 front end** (Resolution →
Translation → Elaboration → Core). The V1 front end (Python → Laurel → Core) has
its own set in [`../expected_interpret_v1/`](../expected_interpret_v1).

V2 runs the whole corpus, `../tests/test_*.py`; V1 runs only the 310 hand-written
cases. Both go through `pyInterpret` — concrete execution, **no verification** —
from `../../StrataPythonTestExtra/InterpretGoldenTest.lean`. Regenerate with
`../run_py_interpret.sh [--v2] --update`.

## How a case joins a suite

Unlike the analyze goldens, membership is not "has a `.expected`". Every case this
front end runs has a place in the table below, and the sidecar records the
*outcome*, not the membership:

| Sidecar | Meaning |
|---|---|
| *(none)* | the case runs to completion and exits 0 |
| `<case>.expected` | the case fails, and its output matches this regex |
| `<case>.skip` | the case is not run; the file holds the reason |

So a case that fails under one front end and passes under the other has a file in
only one of the two directories, and the `V1/V2 divergence` line compares whole
cases rather than the files present in either.

## The imported corpus is V2-only

The 1,168 imported regression cases run under V2 only. V1 is slated for deletion, so
a second baseline for them would be a maintenance cost with no consumer, and their
V1 expectations were dropped rather than carried. `../expected_interpret_v1/`
therefore covers only the 310 hand-written cases, and the `V1/V2 divergence` line is
computed over those 310.

## `.desired`, and what marks an imported case

`<case>.desired` records what a case *ought* to conclude. That is a property of the
Python program, not of a front end, so it lives only here;
`../completeness_report.py` reads it together with this directory's `.expected` set.

It doubles as the marker for "imported": every one of the 1,168 imported cases has a
`.desired` and none of the 310 hand-written ones does, so `run_py_interpret.sh`
tests for it to decide what the V1 run skips. A newly imported case is V2-only
automatically, with no list to maintain.

## Why the V2 set lives at the unqualified path

This matches [`../expected_laurel/README.md`](../expected_laurel/README.md), which
made the same choice for the analyze goldens, for the same reason: this directory
held the V1 expectations, and V2 was added by **rewriting these files in place** and
copying the V1 ones out to `../expected_interpret_v1/`, rather than renaming this
directory to `expected_interpret_v2/` and starting a fresh one.

Git pairs a delete with an add to report a rename, so moving the directory would
have shown the V1→V2 change as a pile of unreviewable additions next to an
unchanged rename. Keeping the paths and changing the contents makes each case's
expectation a **content diff** in review.

## Regenerating

```
cd StrataPythonTest
./run_py_interpret.sh --update          # V1 set, ../expected_interpret_v1/ (310 cases)
./run_py_interpret.sh --v2 --update     # V2 set, this directory (all 1478)
```

Never hand-edit these files, but note what `--update` does *not* do: a stored
pattern that still matches is kept byte for byte, so a deliberately relaxed pattern
survives. Only a pattern that no longer matches is rewritten, from the failure's
first line, with assertion identifiers, `byteIdx` values and Ion source spans
(`file.python.st.ion(2532-2575)`), Lean source locations in a panic
(`StrataPython.Resolution:1739:7`) and generated type variables (`$__ty2468`)
relaxed -- all of them move for reasons unrelated to the case, so they must never be
matched literally. Each `--v2` run
ends with a `V1/V2 divergence: N of M case(s) differ` line, over the 310 cases both
front ends run; driving N to zero is the point of the V2 work.

## Status

Generated against mainline `c82e16c`. Of the 310 cases both front ends run,
**124 differ**.

| | V1 (310 cases) | V2 (310) | V2 (1168 imported) | V2 (all 1478) |
|---|---:|---:|---:|---:|
| runs to completion | 215 | 200 | 133 | 333 |
| fails with a recorded expectation | 81 | 105 | 1035 | 1140 |
| skipped | 14 | 5 | 0 | 5 |

On the shared 310, V2 executes **15 fewer** cases than V1: it fails on 43 that V1
runs to completion, and passes on 27 that V1 fails plus one V1 skips. Nothing in the
V1 baseline moved -- `../expected_interpret_v1/` is byte-identical to mainline's
`expected_interpret/`, so every difference below is V1-versus-V2, not a regression.

The divergence is not cosmetic; the recurring categories across the whole V2 run, in
order of how many cases they account for:

- **V2 declines to produce Core at all** — 682 cases, nearly half the corpus, fail
  with `V2 pipeline produced no Core: [...]`. This is the single dominant gap. The
  bracketed diagnostics name the construct in each case.
- **The entry point is missing or mis-shaped.** 102 cases fail with
  `procedure '__main__' not found` and 144 with
  `procedure '__main__': expected N arguments, got 0` — V2 either emits no
  `__main__` wrapper or emits one that takes parameters the runner does not supply.
- **Assertions that no longer evaluate.** 103 cases fail with
  `assert (assert(N)) condition did not reduce to bool` and 16 more with the
  `assume` form, against 54 that report a genuine `Assertion assert(N) failed` —
  most V2 runs that reach an assertion still cannot evaluate its condition.
- **Two panics.** `PANIC at StrataPython.Resolution.resolveMatchCase` on two cases.
  A panic is a bug, not a contract — these are the highest-value entries here.
- **Terse diagnostics.** Five cases (the `test_chained_compare*` family) fail with
  an output of just `false`, which makes for a nearly contentless expectation.
- **Where V2 is ahead.** Of the 310 cases both front ends run, 27 fail under V1 and
  pass under V2, and `test_nested_function_lifting` is skipped outright by V1 (the
  interpreter's V1 Laurel path does not support nested functions) while V2 executes
  it. The five `test_nested_function_*_rejection` cases are also skipped under V1 but
  produce V2's intentional, specific rejection messages, so they are asserted here
  rather than skipped.

These files record what each front end does today so that further changes are
reviewable; they are not an endorsement of the current behaviour. `PANIC`,
`Core type checking failed` and `V2 pipeline produced no Core` entries in particular
are bugs to fix, not contracts to preserve.

The remaining skips are environmental — "Difference in behavior between local and CI
runs", plus `test_str_slice`, whose slice asserts cannot reduce because `Str.Substr`
is uninterpreted in the concrete interpreter (mainline skips it for the same reason). Everything else runs: an
expectation recording an internal error is a legitimate current result, and skipping
it would hide drift, promotions and newly revealed unsoundness.

Two things to know before re-baselining from a dry run. The dry run builds more than
one platform (AL2023_x86_64 and AL2023_aarch64), and at least one case
(`test_model_soundness_437_bool_equals_int_cross_tag_program`) has been seen to
differ between them, so a green local run does not prove a green dry run. And on a
mismatch the runner prints the actual failure line beside the expected pattern —
without that, a failure reproducing only on a build host cannot be diagnosed from
the log.
