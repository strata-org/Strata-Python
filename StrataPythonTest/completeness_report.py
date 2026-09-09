#!/usr/bin/env python3
"""Render the Completeness Report from checked-in Desired and Expected data.

Runs no tool. Reads the `.desired` and `.expected` sidecars and classifies the gap
between them, which is a separate judgement from the test outcome: the suite passes
when Actual matches Expected, and says nothing about whether Expected is any good.

Both sidecars are read from `expected_interpret/`, the V2 set. The cases carrying
a `.desired` are the imported regression corpus, which runs under V2 only -- V1 is
slated for deletion -- so there is no V1 column to report.

    python3 completeness_report.py                 # summary to stdout
    python3 completeness_report.py --detail        # list every case per bucket
    python3 completeness_report.py --out report.md # write markdown

The report is only meaningful for a build whose Expected-versus-Actual run is
green. It treats Expected as Actual, so a stale baseline -- a change that updated
the front end without re-baselining -- reads as a phantom regression or a phantom
soundness issue. Generate it after the tests pass, not before.

Soundness is directional. Declining to answer is always allowed; asserting
something false is not. So an Expected that is an error is incompleteness, while an
Expected that contradicts Desired is a defect.
"""

from __future__ import annotations

import argparse
import pathlib
import sys
from collections import Counter, defaultdict

HERE = pathlib.Path(__file__).resolve().parent
# The cases with a `.desired` run under V2 only, so both sidecars come from its set.
EXPECTED_DIR = HERE / "expected_interpret"
TESTS_DIR = HERE / "tests"

def is_answered(expected: str) -> bool:
    """Did the front end give an answer about the program, or decline?

    An answer means it evaluated the assertion and reported it false, which the
    interpreter prints as "Assertion assert(N) failed!". Everything else is a
    refusal to answer -- an unsupported construct, a translation failure, or

        assert (assert(N)) condition did not reduce to bool

    which is the model failing to evaluate the condition at all. That distinction
    decides whether a gap is unsoundness or incompleteness, so it must not rest on
    the presence of "assert": both forms contain it.
    """
    return "Assertion" in expected and "failed" in expected

BUCKETS = ("correct", "imprecise-sound", "unsound", "no-answer")


def read_token(path: pathlib.Path) -> str | None:
    if not path.is_file():
        return None
    return path.read_text(encoding="utf-8").split("#", 1)[0].strip() or None


def classify(desired: str | None, expected: str | None) -> tuple[str, str]:
    """Classify one Desired-versus-Expected pair.

    `expected` is None when no baseline exists, which means the case is expected
    to pass.
    """
    if desired is None or desired == "unknown":
        return ("imprecise-sound", "unknown — Desired not yet established")

    passes = expected is None
    answered = bool(expected and is_answered(expected))

    if desired == "clean":
        if passes:
            return ("correct", "clean — no bug, none reported")
        if answered:
            return ("unsound", "false-alarm — finding reported on correct code")
        return ("no-answer", "tool-error — declined to answer")

    if desired == "detected":
        if answered:
            return ("correct", "detected — real bug reported")
        if passes:
            return ("unsound", "verified-false — program has a bug, verified clean")
        return ("no-answer", "tool-error — declined to answer")

    if desired in ("rejected", "unsupported-gap"):
        if passes:
            return ("unsound", "admitted-out-of-subset — should be refused, accepted")
        if answered and desired == "rejected":
            return ("unsound", "analysed-out-of-subset — answered on a program it should refuse")
        return ("correct", "rejected — correctly refused")

    return ("imprecise-sound", f"unrecognised Desired: {desired}")


def collect() -> list[tuple[str, str | None, str | None, str, str]]:
    rows = []
    for desired_file in sorted(EXPECTED_DIR.glob("*.desired")):
        name = desired_file.stem
        if not (TESTS_DIR / f"{name}.py").is_file():
            continue
        desired = read_token(desired_file)
        expected_file = EXPECTED_DIR / f"{name}.expected"
        expected = (
            expected_file.read_text(encoding="utf-8").strip()
            if expected_file.is_file()
            else None
        )
        bucket, label = classify(desired, expected)
        rows.append((name, desired, expected, bucket, label))
    return rows


def render(rows, detail: bool) -> str:
    total = len(rows)
    by_bucket = defaultdict(list)
    for r in rows:
        by_bucket[r[3]].append(r)

    L = ["# Completeness Report — V2 front end", ""]
    L.append(f"{total} cases. Desired versus Expected, read from the checked-in")
    L.append(f"sidecars in `{EXPECTED_DIR.name}/`. No tool was run.")
    L.append("")
    L.append("Only meaningful for a build whose Expected-versus-Actual run is green:")
    L.append("this treats Expected as Actual, so a stale baseline reads as a phantom")
    L.append("regression.")
    L.append("")
    L.append("| Bucket | Meaning | Cases | Share |")
    L.append("|---|---|---:|---:|")
    for b, desc in (
        ("correct", "Desired == Expected"),
        ("imprecise-sound", "Desired != Expected, Expected still an allowed answer"),
        ("unsound", "Desired != Expected, and Expected is incorrect"),
        ("no-answer", "Expected is an error, not a result"),
    ):
        n = len(by_bucket[b])
        L.append(f"| {b} | {desc} | {n} | {100 * n / total:.1f}% |")
    L.append(f"| | **total** | **{total}** | |")
    L.append("")

    for b in BUCKETS:
        rs = by_bucket[b]
        if not rs:
            continue
        L.append(f"## {b} ({len(rs)})")
        L.append("")
        for label, n in Counter(r[4] for r in rs).most_common():
            L.append(f"- {n} — {label}")
        L.append("")
        if detail:
            for label, _ in Counter(r[4] for r in rs).most_common():
                names = sorted(r[0] for r in rs if r[4] == label)
                L.append(f"### {label} ({len(names)})")
                L.append("")
                L.extend(f"- `{n}`" for n in names)
                L.append("")
    return "\n".join(L) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--detail", action="store_true", help="list every case per bucket")
    ap.add_argument("--out", type=pathlib.Path, help="write markdown to this path")
    args = ap.parse_args()

    rows = collect()
    if not rows:
        print(f"no .desired sidecars found under {EXPECTED_DIR}", file=sys.stderr)
        return 1

    text = render(rows, args.detail)
    if args.out:
        args.out.write_text(text, encoding="utf-8")
        print(f"wrote {args.out}")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
