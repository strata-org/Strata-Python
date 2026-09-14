"""Precision oracle over the comprehension cross product.

For every EXPECT checkpoint in `corpus/generated/comp.py` -- (unit, line, residual kind,
descriptor fragment, expected status) -- locate the residual at that line with
that kind whose descriptor contains the fragment, classify it, and compare with
the expectation. ABSENT when no matching residual exists at the line.

The check is two-sided, which is what makes it worth keeping alongside the
goldens. An expected RESOLVED that comes back SPLIT or MAY_RAISE is a precision
regression: the analysis widened. An expected SPLIT or MAY_RAISE that comes back
RESOLVED is an unsound narrowing: a live tag was dropped. The goldens catch
*change*; only this catches change in the wrong direction.

Ported from the top-level `comp_precision.py`, which ran against the Python
analyzer. That analyzer is gone, so the subject is now the Lean pipeline -- the
engine that actually ships. The checkpoints, the classification, and the
two-sidedness are unchanged, so a mismatch here means the same thing it always
did.

Runs under `audit`, deliberately. A machine raise that aborts contributes an
obligation and no exceptional continuation, so under `strict` a residual's error
rows would reflect the policy rather than the analysis. `audit` models every
category, which is the state these checkpoints describe.

Run: python3.13 harness/gates/comp_precision.py [path/to/comp.py]
"""
from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import tempfile

import sys as _sys, os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import paths
paths.on_path()
HERE = paths.CORPUS
ROOT = paths.PACKAGE

from resid_status import residual_status  # noqa: E402  (needs ROOT on the path)

PIPELINE = paths.PIPELINE


def classify(residual: dict) -> str:
    """The status name a checkpoint is written against."""
    status = residual_status(residual)
    if status == "" and residual["errors"] and residual["cases"]:
        return "MAY_RAISE"
    if status == "MUST_RAISE":
        return "MUST_RAISE"
    return status


def expectations(path: str) -> list[tuple]:
    """`EXPECT` from the corpus file itself, which is generated alongside it."""
    spec = importlib.util.spec_from_file_location("comp_corpus", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return list(module.EXPECT)


def analyze(path: str) -> dict:
    """The Lean pipeline's log for one file."""
    with tempfile.TemporaryDirectory() as work:
        base = os.path.splitext(os.path.basename(path))[0]
        run = subprocess.run(
            [sys.executable, PIPELINE, path, "--logs-only",
             "--policy", "audit", "-o", os.path.join(work, "out.html")],
            capture_output=True, text=True)
        log_path = os.path.join(work, base + ".log.json")
        if run.returncode != 0 or not os.path.exists(log_path):
            raise SystemExit(
                f"{path}: pipeline failed\n{run.stdout}\n{run.stderr}")
        with open(log_path) as handle:
            return json.load(handle)


def main() -> int:
    # `comp.py` is generator output, so it lives with the other generated
    # programs rather than at the corpus root.
    path = (sys.argv[1] if len(sys.argv) > 1
            else os.path.join(HERE, "generated", "comp.py"))
    checkpoints = expectations(path)
    log = analyze(path)

    by_line: dict[int, list[dict]] = {}
    for residual in log["residuals"].values():
        by_line.setdefault(residual["line"], []).append(residual)

    mismatches = []
    for (name, line, kind, fragment, expected) in checkpoints:
        candidates = [r for r in by_line.get(line, [])
                      if r["kind"] == kind and fragment in r["desc"]]
        got = classify(candidates[0]) if candidates else "ABSENT"
        if got != expected:
            mismatches.append((name, line, kind, expected, got,
                               candidates[0]["cases"] if candidates else {}))

    for (name, line, kind, expected, got, cases) in mismatches:
        print(f"MISMATCH {name} L{line} {kind}: expected {expected}, "
              f"got {got}  cases={cases}")
    total = len(checkpoints)
    print(f"\n{total} checkpoints, {total - len(mismatches)} match, "
          f"{len(mismatches)} mismatches")
    return 1 if mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
