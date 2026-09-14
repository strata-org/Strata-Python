#!/usr/bin/env python3
"""Assert the admission outcome of every corpus program against a stated manifest.

    python3 harness/gates/admission.py
    python3 harness/gates/admission.py --verbose
    python3 harness/gates/admission.py --bless      # restate the manifest

`harness/data/admission_expected.json` says, per program, whether the subset
checker must accept or reject it, and for a rejection exactly which violation
rules it must report. That is the accept/reject half of the expectation story,
stated rather than implied by a digest: `expected.json` pins a rejection as a
hash of its rule multiset, so reading it tells you nothing about *why* a program
is rejected, and a rule set that changes into another of the same size is a
digest change with no explanation attached.

It runs the checker itself rather than reading the logs `run_all.py` leaves
behind: those would pass against a stale file, which is the failure mode a gate
exists to prevent.

Admission is decided by the lowering, before any policy applies and without the
fixpoint, so this uses `pylate --check-only` and each program is checked once.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import paths  # noqa: E402

MANIFEST = paths.data("admission_expected.json")


def corpus_programs() -> list[str]:
    """Every corpus program, keyed the way the manifest keys them."""
    found = []
    for root, _dirs, files in os.walk(paths.CORPUS):
        for name in sorted(files):
            if not name.endswith(".py") or name.startswith("gen_"):
                continue
            if name.endswith((".annotated.py", ".checked.py")):
                continue
            if "__pycache__" in root:
                continue
            found.append(os.path.relpath(os.path.join(root, name), paths.CORPUS))
    return sorted(found)


def admission_of(key: str) -> dict:
    """Run the checker on one program and report what it decided."""
    source = os.path.join(paths.CORPUS, key)
    with tempfile.TemporaryDirectory() as directory:
        stem = key.replace(os.sep, "_")
        # Whichever front end is active -- the Strata AST by default.
        ast_path = paths.make_analyzer_input(source, os.path.join(directory, stem))
        log_path = os.path.join(directory, f"{stem}.log.json")
        # `--check-only` stops after lowering and admission. The verdict does not
        # depend on the policy or the fixpoint, and skipping the analysis is what
        # takes this gate from ~105s to a couple of seconds -- almost all of that
        # was analysing one 4,000-line program it never needed to analyse.
        subprocess.run([paths.PYLATE, ast_path, "--src", source,
                        "--check-only", "-o", log_path],
                       check=True, capture_output=True)
        with open(log_path, encoding="utf-8") as handle:
            log = json.load(handle)
    if log["status"] == "rejected":
        return {"key": key, "admission": "rejected",
                "violations": sorted({v["rule"] for v in log["violations"]})}
    return {"key": key, "admission": "accepted"}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--bless", action="store_true",
                        help="rewrite the manifest from what the checker does now")
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    args = parser.parse_args()

    paths.guard(binary=True, corpus_dir=True)
    programs = corpus_programs()
    with concurrent.futures.ProcessPoolExecutor(args.jobs) as pool:
        actual = {r["key"]: r for r in pool.map(admission_of, programs)}

    if args.bless:
        with open(MANIFEST, encoding="utf-8") as handle:
            existing = json.load(handle)
        existing["programs"] = {
            key: ({"admission": "rejected", "violations": r["violations"]}
                  if r["admission"] == "rejected" else {"admission": "accepted"})
            for key, r in sorted(actual.items())}
        with open(MANIFEST, "w", encoding="utf-8") as handle:
            json.dump(existing, handle, indent=1, sort_keys=True)
            handle.write("\n")
        print(f"blessed {len(actual)} admission expectations")
        return 0

    with open(MANIFEST, encoding="utf-8") as handle:
        expected = json.load(handle)["programs"]

    failures: list[str] = []
    for key in sorted(set(expected) | set(actual)):
        want, got = expected.get(key), actual.get(key)
        if want is None:
            failures.append(f"{key}: in the corpus but not the manifest")
            continue
        if got is None:
            failures.append(f"{key}: in the manifest but not the corpus")
            continue
        if want["admission"] != got["admission"]:
            failures.append(
                f"{key}: manifest says {want['admission']}, "
                f"checker says {got['admission']}"
                + (f" ({', '.join(got.get('violations', []))})"
                   if got["admission"] == "rejected" else ""))
            continue
        if want["admission"] == "rejected":
            # The rule *set* has to match. A rejection for a different reason is
            # not the expectation being met, even though the verdict agrees.
            missing = sorted(set(want["violations"]) - set(got["violations"]))
            extra = sorted(set(got["violations"]) - set(want["violations"]))
            if missing or extra:
                detail = []
                if missing:
                    detail.append(f"no longer reports {', '.join(missing)}")
                if extra:
                    detail.append(f"now also reports {', '.join(extra)}")
                failures.append(f"{key}: rejected, but {'; '.join(detail)}")
        elif args.verbose:
            print(f"ok  {key}")

    rejected = sum(1 for v in expected.values()
                   if v["admission"] == "rejected")
    print(f"{len(programs)} programs: {rejected} must be rejected, "
          f"{len(programs) - rejected} must be accepted")
    for failure in failures:
        print(f"FAIL {failure}")
    if not programs:
        print("FAIL no corpus programs found -- nothing was checked")
        return 1
    print(f"{len(failures)} admission expectations violated")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
