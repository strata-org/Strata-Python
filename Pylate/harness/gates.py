#!/usr/bin/env python3
"""Run the soundness and precision gates, in tiers.

    python3 harness/gates.py --fast     # ~15s: per-commit
    python3 harness/gates.py --full     # ~110s: pipeline
    python3 harness/gates.py --fuzz     # minutes: on demand
    python3 harness/gates.py --list

The tiers exist because the runtimes differ by a hundredfold and two gates
account for most of it -- `comp_precision` is 70s and `cpython_conformance` 26s
of a 111s full run. The fast tier drops those two and still covers per-rule
soundness against CPython, the precision measurement, all 229 corpus goldens
with their HTML, the catch-all probe, and the method inventory.

The Lean suites are not here: `lake test` runs them, and this exits non-zero if
the analyzer is not built, so the intended order is

    lake build && lake test && python3 harness/gates.py --fast
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paths  # noqa: E402

#: name -> (script, args, tier, what it asserts)
GATES: list[tuple[str, list[str], str, str]] = [
    ("inventory", ["known_methods_oracle.py"], "fast",
     "builtin method inventory against dir()"),
    ("admission", ["admission.py"], "fast",
     "every program's accept/reject verdict and its violation rules"),
    ("validity", ["rule_validity.py"], "fast",
     "every rule's claim contains CPython, and every rule has a case"),
    ("catchall", ["catchall_oracle.py"], "fast",
     "154 (tag, operation) pairs, both directions"),
    ("precision", ["rule_precision.py"], "fast",
     "obligation and excess-edge measurement"),
    ("corpus", ["run_all.py", "--check"], "fast",
     "229 corpus digests, and writes every HTML render"),
    ("coverage", ["run_all.py", "--coverage"], "fast",
     "the coverage manifest against the golden logs"),
    ("conformance", ["cpython_conformance.py"], "full",
     "579 differential cases against CPython"),
    ("comp-precision", ["comp_precision.py"], "full",
     "560 two-sided precision checkpoints"),
    ("fuzz", ["cpython_conformance.py", "--fuzz"], "fuzz",
     "the generated fuzz corpus"),
]

TIERS = {"fast": ["fast"], "full": ["fast", "full"],
         "fuzz": ["fast", "full", "fuzz"]}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--fast", dest="tier", action="store_const",
                        const="fast")
    parser.add_argument("--full", dest="tier", action="store_const",
                        const="full")
    parser.add_argument("--fuzz", dest="tier", action="store_const",
                        const="fuzz")
    parser.add_argument("--only", action="append",
                        help="run just these gates, by name")
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()

    if args.list:
        for name, _, tier, what in GATES:
            print(f"  {name:16s} {tier:5s} {what}")
        return 0

    selected = [g for g in GATES if g[2] in TIERS[args.tier or "fast"]]
    if args.only:
        wanted = set(args.only)
        selected = [g for g in GATES if g[0] in wanted]
        if not selected:
            print(f"gates: no such gate {sorted(wanted)}", file=sys.stderr)
            return 2

    # The analyzer must exist, or every gate fails the same uninformative way.
    paths.guard(binary=True, corpus_dir=True, lean=True)

    failed: list[str] = []
    started = time.time()
    for name, argv, _, _ in selected:
        script = os.path.join(paths.GATES, argv[0])
        begin = time.time()
        run = subprocess.run([sys.executable, script, *argv[1:]],
                             capture_output=True, text=True)
        took = time.time() - begin
        mark = "ok  " if run.returncode == 0 else "FAIL"
        tail = (run.stdout.strip().splitlines() or [""])[-1]
        print(f"{mark} {name:16s} {took:6.1f}s  {tail[:88]}")
        if run.returncode != 0:
            failed.append(name)
            # A failing gate's own output is the diagnosis, so it is not summarised.
            sys.stdout.write(run.stdout[-4000:])
            sys.stderr.write(run.stderr[-2000:])

    total = time.time() - started
    print(f"\n{len(selected)} gates, {len(failed)} failed, {total:.1f}s total")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
