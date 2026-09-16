"""Compare pyInterpret's outcome per method against CPython's, and report.

Every selected method runs clean under CPython -- the corpus is CPython's own passing
suite -- so the interpreter reaching a different conclusion is a finding.

Buckets, classified BY EXIT CODE. The package review policy in AGENTS.md is that
translator diagnostics on stderr are not a stable interface: consumers use the exit
code and the `RESULT:`/`DETAIL:` lines only, never message wording.

  agree           ran to completion, as CPython did (exit 0)
  untranslatable  Strata could not translate the program (exit 1): coverage, not
                  correctness
  needsTriage     a runtime problem (exit 2) where CPython ran clean
  error           anything else, including a timeout
Two buckets are EXCLUSIONS rather than results -- the comparison is not valid for
them, so no conclusion about Strata is drawn:

  oracleNotClean  CPython itself does not run the method cleanly -- it fails, errors,
                  or is SKIPPED. Some CPython tests assert on bytecode, which differs by
                  build, and a skip-only decorator is still live in the oracle run even
                  though it is dropped from the generated program. Either way this is a
                  property of the corpus and the machine, not of Strata, and a method
                  CPython never ran states no expectation to compare against.
  loweringBroken  the GENERATED program does not behave as the original did under
                  CPython, so the lowering changed the program's meaning.

`loweringBroken` is the empirical guard on everything else here. Predicting statically
which transforms preserve meaning turned out to be a losing game -- `__qualname__`
encodes the enclosing scope, a helper assigning to `self.X` becomes a local write --
so instead every generated program is run against the original and the ones that
diverge are excluded. The count is reported rather than hidden, because driving it down
is how coverage grows.

`pyInterpret` emits no `RESULT:` line, so the exit code is all there is -- and exit 2
covers BOTH an assertion the interpreter evaluated to false (a possible semantic bug)
and an expression it could not reduce (a coverage gap). Those are the two cases this
suite most wants to separate, so the raw message is carried in `detail` for a human,
and the split is a triage step. Making it reliable needs `pyInterpret` to emit a
`RESULT:` line the way `pyAnalyze*` does.

Triage matters because an assertion coming back false is often the interpreter
silently treating an unmodelled operation as a no-op or as identity rather than
getting Python wrong: `b is not b.replace(b'', b'')` is false because
`bytearray.replace` is unmodelled and hands back the same object. Of the first nine
such cases, exactly one (`'%d' % False == '0'`) was a genuine semantic bug.

WHAT FAILS THE RUN: a difference from the recorded baseline, and nothing else.

`baseline.txt` records the bucket for every method, and is checked in. A finding does
not fail the run -- a construct Strata cannot handle is the point of the suite -- but a
CHANGE does, in either direction:

  * a method that used to `agree` and now does not is a regression, and the diff says
    which one;
  * a method that used to be a gap and now agrees is an improvement, and updating the
    baseline records it, so the file doubles as a coverage log.

Without this the suite would print a wall of numbers that nobody could act on, and a
regression would look exactly like the status quo. Regenerate with
`run_cpython_oracle.sh --update`.

The two EXCLUSION buckets are recorded in the baseline like any other, but a method
moving into or out of one is ignored by the diff. Both depend on the machine rather than
on Strata -- which CPython tests skip or assert on bytecode, and which generated programs
need a C-API hook, a warnings filter or a platform library -- so a move says nothing
about the code, while a genuine appearance or disappearance still fails.

`oracleMissing` is NOT excluded: it means the oracle produced no outcome for a method at
all, which is a harness malfunction and has to be able to fail the run.
"""
from __future__ import annotations

import json
import pathlib
import sys


BASELINE = pathlib.Path(__file__).parent / "baseline.txt"


def baseline_path() -> pathlib.Path:
    return BASELINE

# Buckets where no conclusion about Strata is drawn AND membership depends on the
# machine rather than on the code: which CPython tests skip or assert on bytecode, and
# which generated programs depend on a C-API hook, a warnings filter or a platform
# library. A transition into or out of one of these is ignored by the baseline diff.
#
# `oracleMissing` is deliberately NOT here. It means the oracle produced no outcome at
# all, which is a harness malfunction that has to be visible.
_EXCLUDED = {"oracleNotClean", "loweringBroken"}

_MISSING = "__missing__"


def read_baseline() -> dict[str, str]:
    if not baseline_path().exists():
        return {}
    out = {}
    for line in baseline_path().read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        stem, _, bucket = line.partition(" ")
        out[stem] = bucket.strip()
    return out


def write_baseline(rows: list[dict]) -> int:
    # EVERY row is recorded, excluded buckets included. Omitting them made a method that
    # is excluded here look like a brand-new method on a machine where it runs, which
    # fails just as loudly as the churn the exclusion was meant to avoid. Recording all
    # of them and ignoring the transitions in the diff is symmetric.
    keep = sorted((r["stem"], r["bucket"]) for r in rows)
    header = [
        "# Outcome per CPython test method, as recorded. One line: <stem> <bucket>.",
        "#",
        "# Regenerate with `run_cpython_oracle.sh --update`. A difference from this file",
        "# fails the run, in either direction: a method that stops agreeing is a",
        "# regression, and one that starts agreeing is an improvement worth recording.",
        "#",
        "# `agree` means pyInterpret ran the method to completion as CPython did.",
        "# `untranslatable` and `needsTriage` are coverage gaps, which is the expected",
        "# state for most methods -- see README.md. The two exclusion buckets",
        "# (oracleNotClean, loweringBroken) ARE recorded, but a method moving into or",
        "# out of one is ignored by the diff, because that depends on the machine.",
        "",
    ]
    baseline_path().write_text("\n".join(header + [f"{s} {b}" for s, b in keep]) + "\n")
    return len(keep)


def main(argv: list[str]) -> int:
    """compare.py <selection.json> <oracle.json> <build-dir> <report.json> [--update]"""
    selection = json.loads(pathlib.Path(argv[1]).read_text())
    oracle = json.loads(pathlib.Path(argv[2]).read_text())
    build = pathlib.Path(argv[3])
    report_path = pathlib.Path(argv[4])

    engines = json.loads((build / "engines.json").read_text())
    by_stem = {m["stem"]: m for m in selection["methods"]}
    cpython: dict[str, str] = {}
    cpython_detail: dict[str, str] = {}
    for f in oracle["files"]:
        cpython.update(f["outcomes"])
        cpython_detail.update(f.get("detail", {}))

    rows = []
    buckets: dict[str, int] = {}
    for r in engines["results"]:
        m = by_stem.get(r["stem"])
        if m is None:
            continue
        oc = cpython.get(r["stem"], _MISSING)
        if oc == _MISSING:
            # NO oracle outcome at all -- oracle.py stopped before reaching this method,
            # usually because a whole file errored. That is a harness malfunction, not a
            # property of CPython, so it must NOT share the excused `oracleNotClean`
            # bucket: doing so let a method recorded as `agree` vanish from the
            # comparison instead of being reported.
            bucket, detail = "oracleMissing", "no oracle outcome recorded"
        elif oc != "clean":
            bucket, detail = "oracleNotClean", cpython_detail.get(r["stem"], oc)
        elif r.get("generatedUnderCPython") == "timeout":
            # `error`, not `loweringBroken`: an excluded bucket would hide it.
            bucket, detail = "error", r.get("generatedDetail", "")
        elif r.get("generatedUnderCPython") == "failed":
            bucket, detail = "loweringBroken", r.get("generatedDetail", "")
        elif r.get("parseTimeout"):
            # `error` rather than `untranslatable`: a timeout is a harness or performance
            # problem, and `error` is not an excluded bucket, so it shows in the diff.
            bucket, detail = "error", "py_to_strata timed out"
        elif not r["parse"]:
            bucket, detail = "untranslatable", "py_to_strata: " + r.get("parseDetail", "")
        else:
            kind = r["interpret"]
            detail = r.get("interpretDetail", "")
            bucket = {"ran": "agree", "untranslatable": "untranslatable",
                      "runtimeProblem": "needsTriage"}.get(kind, "error")
        buckets[bucket] = buckets.get(bucket, 0) + 1
        rows.append({"stem": r["stem"], "file": m["file"], "method": m["method"],
                     "interpret": r.get("interpret"), "cpython": oc,
                     "bucket": bucket, "detail": detail})

    report = {
        "cpython": selection.get("cpython", ""),
        "methods": len(selection["methods"]),
        "assertions": sum(m["assertionCount"] for m in selection["methods"]),
        "elapsedSeconds": engines.get("elapsedSeconds"),
        "buckets": buckets,
        "rows": rows,
    }
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    total = sum(buckets.values()) or 1
    print(f"\ncompare: {len(selection['methods'])} methods, "
          f"{report['assertions']} assertions")
    for b in ("agree", "untranslatable", "needsTriage", "error", "oracleMissing",
              "oracleNotClean", "loweringBroken"):
        if b in buckets:
            print(f"  {b:<17}{buckets[b]:>5}  ({100*buckets[b]/total:.1f}%)")

    excluded = [r for r in rows if r["bucket"] in _EXCLUDED]
    if excluded:
        n_low = sum(1 for r in excluded if r["bucket"] == "loweringBroken")
        n_orc = len(excluded) - n_low
        print(f"\nEXCLUDED ({len(excluded)}) -- the comparison is not valid for these, "
              f"so no conclusion is drawn:")
        print(f"  loweringBroken {n_low:>4}  the generated program does not behave as "
              f"the original")
        print(f"  oracleNotClean {n_orc:>4}  CPython itself does not run it cleanly")
        for r in excluded[:8]:
            print(f"    [{r['bucket']}] {r['file']}::{r['method']}: "
                  f"{r['detail'][:70]}")
        if len(excluded) > 8:
            print(f"    ... and {len(excluded)-8} more (see report.json)")

    triage = [r for r in rows if r["bucket"] == "needsTriage"]
    if triage:
        print(f"\nNEEDS TRIAGE -- interpreter hit a runtime problem where CPython ran "
              f"clean ({len(triage)}); exit 2 does not say whether the assertion was "
              f"false or the expression could not be reduced:")
        for r in triage[:15]:
            print(f"  {r['file']}::{r['method']}: {r['detail'][:90]}")
        if len(triage) > 15:
            print(f"  ... and {len(triage)-15} more (see report.json)")

    compared = sum(v for k, v in buckets.items() if k not in _EXCLUDED)
    print(f"\ncompared {compared} of {len(rows)} methods "
          f"({len(rows)-compared} excluded)")

    if "--update" in argv:
        n = write_baseline(rows)
        print(f"\nbaseline updated: {n} methods recorded in {baseline_path().name}")
        return 0

    baseline = read_baseline()
    if not baseline:
        print(f"\nNO BASELINE: {baseline_path().name} is missing. Create it with "
              f"`run_cpython_oracle.sh --update`.")
        return 1

    now = {r["stem"]: r["bucket"] for r in rows}
    # Omitting a bucket from the baseline FILE is not enough on its own. A method that
    # moves into `oracleNotClean` on another machine simply disappears from `now`, which
    # the diff below would read as "method gone" and fail on -- reintroducing exactly
    # the cross-platform churn the exclusion exists to prevent. So a transition into or
    # out of a not-baselined bucket is ignored, while a real disappearance still fails.
    regressed, improved, changed, added, removed = [], [], [], [], []
    for stem in sorted(set(now) | set(baseline)):
        was, is_ = baseline.get(stem), now.get(stem)
        # An excluded bucket on EITHER side is machine-dependent, so the move says
        # nothing about Strata. The run still prints every excluded method and its
        # count, so this hides no information -- it only stops it failing the build.
        if was in _EXCLUDED or is_ in _EXCLUDED:
            continue
        if was is None:
            added.append((stem, is_))
        elif is_ is None:
            removed.append((stem, was))
        elif was != is_:
            (improved if is_ == "agree" else
             regressed if was == "agree" else changed).append((stem, was, is_))

    if not (regressed or improved or changed or added or removed):
        print(f"baseline: {len(baseline)} methods, no change")
        return 0

    print(f"\nBASELINE DIFF -- `run_cpython_oracle.sh --update` to record:")
    for label, items in (("REGRESSED (was agree)", regressed),
                         ("improved (now agree)", improved),
                         ("changed", changed)):
        if items:
            print(f"  {label}: {len(items)}")
            for stem, was, is_ in items[:10]:
                print(f"    {stem}: {was} -> {is_}")
    for label, items in (("new method", added), ("method gone", removed)):
        if items:
            print(f"  {label}: {len(items)}")
            for stem, b in items[:10]:
                print(f"    {stem}: {b}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
