# Analyze goldens — V2 front-end

**This directory holds the goldens for the V2 front-end** (`pyAnalyzeV2`:
Resolution → Translation → Elaboration → Core). The V1 front-end
(`pyAnalyzeLaurel`) has its own full set in [`../expected_laurel_v1/`](../expected_laurel_v1).

Both front-ends run over the same corpus, `../tests/test_*.py`, from
`../../StrataPythonTestExtra/AnalyzeGoldenTest.lean`. A test belongs to a
front-end's suite iff that front-end's directory has a `<name>.expected` for it;
the two sets are expected to cover the same tests.

## Why the V2 set lives at the unqualified path

Historically this directory held the V1 goldens, and it was the only golden set.
V2 was added by **rewriting these files in place** and copying the V1
expectations out to `../expected_laurel_v1/`, rather than renaming this directory
to `expected_laurel_v2/` and starting a fresh one.

That is deliberate. Git pairs a delete with an add to report a rename, so moving
the directory would have shown the V1→V2 change as a pile of unreviewable
additions next to an unchanged rename. Keeping the paths and changing the
contents makes each test's expectation a **content diff** in review, so you can
read exactly how the V2 front-end changes that test's result. The V1 copies
under `../expected_laurel_v1/` are pure additions, which need no review — they
are byte-identical to what used to be here.

## Regenerating

```
cd StrataPythonTest
./run_py_analyze.sh --update          # V1 set, ../expected_laurel_v1/
./run_py_analyze.sh --v2 --update     # V2 set, this directory
```

Never hand-edit these files. Each run ends with a
`V1/V2 divergence: N of M golden(s) differ` line; driving N to zero is the point
of the V2 work.

## Status

Generated against mainline `4eec827`, where 218 of the 225 goldens differ
between the two front-ends. The divergence is not uniformly cosmetic —
recurring categories, roughly in order of how much they affect the reported
outcome:

- **Assertion labels are lost.** V1 reports the user-supplied label
  (`✅ pass - class without __init__`); V2 reports `assert(…)`.
- **Fewer verification conditions are emitted.** V1 checks constructor
  preconditions and declared return types (`✅ pass - precondition`,
  `(C@m ensures) Return type constraint`); V2 emits no such VCs, so its
  `DETAIL:` counts are lower for the same program.
- **Precision regressions.** Over the diverging tests V1 reports 174
  `Analysis success` / 38 `Inconclusive`, V2 reports 169 / 41.
- **New user errors.** V2 reports `RESULT: User error` on five tests V1
  accepts. Four are resolution failures for names V1 resolves — `real` in
  `test_float_literal`, `test_power` and `test_unary_plus_float`, `Client` in
  `test_missing_models` — and one is a spurious type mismatch
  (`expected 'int', got 'string'` in `test_reassign_different_type`).
- **Lost user-error detection.** Conversely, V2 misses the user errors V1
  reports for `test_class_no_init_extra_args` and `test_user_error_metadata`, so
  those two `.user_errors.expected` goldens exist only in the V1 set. Likewise
  the two tests V1 reports as `RESULT: Known limitation` — `test_is_non_none`
  and `test_is_not_non_none` — come back as `Analysis success` under V2.
- **One internal error.** `test_field_write` fails V2 type checking with
  "Impossible to unify Any with int".

These goldens record what V2 does today so that further changes to it are
reviewable; they are not an endorsement of the current behaviour. `RESULT:
Internal error` and `RESULT: User error` entries in particular are bugs to fix,
not contracts to preserve.
