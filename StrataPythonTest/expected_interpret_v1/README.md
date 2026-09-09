# Interpret expectations — V1 front end

Expectations for the V1 front end (Python → Laurel → Core), the shipping pipeline,
run concretely by `pyInterpret` with no verification. Regenerate with
`cd StrataPythonTest && ./run_py_interpret.sh --update`.

These files are copies of what used to live in `../expected_interpret/`, which now
holds the **V2** expectations. For why the two sets sit at those paths — and what
currently differs between them — see
[`../expected_interpret/README.md`](../expected_interpret/README.md).

## Only the hand-written cases

This set covers the 310 hand-written cases, not the 1,168 imported regression cases,
which run under V2 only. V1 is slated for deletion, so a second baseline for the
imported corpus would be a maintenance cost with no consumer.

The runner tells the two apart by the presence of `../expected_interpret/<case>.desired`:
every imported case has one and no hand-written case does. So a newly imported case
is V2-only automatically and nothing here needs updating.

Note that a case with no file here is not outside the suite: absence means the case
is expected to run to completion. Nothing in this directory is shared with V2 — and
`.desired` and `../completeness_report.py` cover V2 only, since the cases they
describe are exactly the ones this set does not run.

## Status

81 cases carry an expectation and 14 are skipped, so 215 of the 310 run to
completion. Of the 310, **124 differ** from V2; `./run_py_interpret.sh --v2` prints
that count.

Six of the skips are the `test_nested_function*` family, which the interpreter's V1
Laurel translation path does not support; three are heap-parameterized entry
procedures; four differ between local and CI runs; and `test_str_slice` cannot
reduce its slice asserts because `Str.Substr` is uninterpreted in the concrete
interpreter.
